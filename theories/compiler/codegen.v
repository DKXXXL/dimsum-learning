Require Export iris.algebra.lib.gmap_view.
Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.filter.
Require Import refframe.product.
Require Import refframe.seq_product.
Require Import refframe.link.
Require Import refframe.prepost.
Require Import refframe.proof_techniques.
Require Import refframe.imp.
Require Import refframe.asm.
Require Import refframe.imp_to_asm.
Require Export refframe.compiler.monad.
Require Export refframe.compiler.linear_imp.

Local Open Scope Z_scope.

Set Default Proof Using "Type".
(*
optimizations:

fn f() :=
  local x
  x ← 1;
  g(!x + !x);
  x ← 2;
  return !x

optimize to:

fn f() :=
  let x := 1;
  g(x + x);
  let x := 2;
  return x

1 + 1 → 2

if 1 then e1 else e2
->
e1


compilation chain:

1. make let-names unique (each name is only assigned once)
2. translate nested expressions to linear expressions
3. optimize linear
3.1. propagate values and let-bindings
3.2. reuse dead let-names
4. translate to asm

*)

Module ci2a_codegen.

(** * initial definitions *)
Inductive error :=
| UnsupportedExpr (e : expr)
| UnknownOperand (e : expr)
| UnknownFunction (f : string)
| UnboundVariable (v : string)
| LocInCode
| NotImplemented (s : string)
| AssertionFailed (s : string)
| TooManyArgs
.

Definition variable_registers : list string :=
  ["R19"; "R20"; "R21"; "R22"; "R23"; "R24"; "R25"; "R26"; "R27"; "R28"; "R29"].

Inductive place :=
| PReg (r : string) | PStack (slot : N).

(** * state of the pass *)
Record state := State {
  s_f2i : gmap string Z;
  s_stacksize : N;
  s_places : gmap string place;
  s_saved_registers : list (string * N);
  s_sp_above : bool; (* tracks whether sp currently points to above the stack or below *)
}.
Global Instance eta_state : Settable _ := settable! State <s_f2i; s_stacksize; s_places; s_saved_registers; s_sp_above>.
Add Printing Constructor state.

Definition s_stack_places (s : gmap string place) : list N :=
  omap (λ '(_, p), if p is PStack slot then Some slot else None) (map_to_list s).

Lemma s_stack_places_insert s a p :
  s !! a = None →
  s_stack_places (<[a:=p]> s) ≡ₚ (if p is PStack slot then [slot] else []) ++ (s_stack_places s).
Proof. move => ?. rewrite /s_stack_places map_to_list_insert //; csimpl. by destruct p. Qed.

Definition initial_state (f2i : gmap string Z) : state := State f2i 0 ∅ [] true.

Definition M := compiler_monad state (list_compiler_monoid deep_asm_instr) error.

(** * pass *)
Definition alloc_stack (sz : N) : M N :=
  s ← cget;
  cassert (AssertionFailed "alloc_stack: s_sp_above is not true") (s.(s_sp_above) = true);;
  cput (s <| s_stacksize := (s.(s_stacksize) + sz)%N |>);;
  mret s.(s_stacksize).

Definition move_sp (above : bool) : M unit :=
  s ← cget;
  cassert (AssertionFailed "move_sp: already at the right place") (s.(s_sp_above) ≠ above);;
  cappend [Aadd "SP" "SP" (ImmediateOp $ if s.(s_sp_above) then - Z.of_N s.(s_stacksize) else Z.of_N s.(s_stacksize))];;
  cput (s <| s_sp_above := above |>);;
  mret tt.

(* for stack slot [slot] returns offset that one needs to add to SP to
reach the slot *)
Definition stack_offset (slot : N) : M Z :=
  s ← cget;
  mret ((if s.(s_sp_above) then 0 else Z.of_N s.(s_stacksize)) - Z.of_N slot - 1).

Definition read_stack (r : string) (slot : N) : M unit :=
  o ← stack_offset slot;
  cappend [Aload r "SP" o];;
  mret tt.

Definition write_stack (r : string) (slot : N) : M unit :=
  o ← stack_offset slot;
  cappend [Astore r "SP" o];;
  mret tt.

Definition clear_mem (r : string) (sz : Z) : M unit :=
  cappend [Amov "R1" (ImmediateOp 0)];;
  cmap (seqZ 0 sz) 0 (λ _ o, cappend [Astore "R1" r o]);;
  mret tt.

Definition read_var (r : string) (v : string) : M unit :=
  s ← cget;
  p ← cassert_opt (UnboundVariable v) (s.(s_places) !! v);
  match p with
  | PReg r' =>
      cappend [Amov r (RegisterOp r')]
  | PStack slot =>
      read_stack r slot
  end.

Definition write_var (r : string) (v : string) : M unit :=
  s ← cget;
  p ← cassert_opt (UnboundVariable v) (s.(s_places) !! v);
  match p with
  | PReg r' =>
      cappend [Amov r' (RegisterOp r)]
  | PStack slot =>
      write_stack r slot
  end.

Definition save_r30 : M unit :=
  slot ← alloc_stack 1;
  write_stack "R30" slot;;
  s ← cget;
  cput (s <| s_saved_registers := ("R30", slot) :: s.(s_saved_registers)|> );;
  mret tt.

Fixpoint allocate_places (ns : list string) (regs : list string) : M unit :=
  match ns with
  | [] => mret tt
  | n::ns => match regs with
           | [] =>
               slot ← alloc_stack 1;
               s ← cget;
               cput (s <|s_places := (<[n := PStack slot]> $ s.(s_places))|> );;
               allocate_places ns regs
           | r::regs =>
               (* save callee save register *)
               slot ← alloc_stack 1;
               write_stack r slot;;
               s ← cget;
               cput (s <|s_places := (<[n := PReg r]> $ s.(s_places))|>
                       <| s_saved_registers := (r, slot) :: s.(s_saved_registers)|> );;
               allocate_places ns regs
           end
  end.

Definition initialize_args (args : list string) : M unit :=
  cmap args 0 (λ n a,
    r ← cassert_opt TooManyArgs (args_registers !! n);
    write_var r a);;
  mret tt.

Definition initialize_locals (vars : list (string * Z)) : M unit :=
  cmap vars 0 (λ _ a,
    s ← cget;
    cassert (AssertionFailed "Not above") (s.(s_sp_above));;
    o ← alloc_stack (Z.to_N a.2);
    cappend [Aadd "R0" "SP" (ImmediateOp $ - (Z.of_N o + a.2))];;
    clear_mem "R0" a.2;;
    write_var "R0" a.1);;
  mret tt.

Definition restore_callee_save_registers : M unit :=
  s ← cget;
  cmap s.(s_saved_registers) 0 (λ _ '(r, slot), read_stack r slot);;
  mret tt.

Definition translate_val (v : static_val) : Z :=
  match v with
  | StaticValNum z => z
  | StaticValBool b => bool_to_Z b
  end.

Definition read_var_val (r : string) (e : var_val) : M unit :=
  match e with
  | VVal v =>
      cappend [Amov r (ImmediateOp (translate_val v))]
  | VVar v => read_var r v
  end.

Definition translate_args (n : nat) (vs : list var_val) : M unit :=
  cmap vs n (λ n a,
    r ← cassert_opt TooManyArgs (args_registers !! n);
    read_var_val r a);;
  mret tt.

Definition translate_lexpr_op (e : lexpr_op) : M unit :=
  match e with
  | LVarVal v => read_var_val "R0" v
  | LBinOp v1 op v2 =>
      read_var_val "R1" v1;;
      read_var_val "R2" v2;;
      match op with
      | AddOp | ShiftOp => cappend [Aadd "R0" "R1" (RegisterOp "R2")]
      | EqOp => cappend [Aseq "R0" "R1" (RegisterOp "R2")]
      | LeOp => cappend [Asle "R0" "R1" (RegisterOp "R2")]
      | LtOp => cappend [Aslt "R0" "R1" (RegisterOp "R2")]
      end
  | LLoad v1 =>
      read_var_val "R1" v1;;
      cappend [Aload "R0" "R1" 0]
  | LStore v1 v2 =>
      read_var_val "R1" v1;;
      read_var_val "R0" v2;;
      cappend [Astore "R0" "R1" 0]
  | LCall f vs =>
      s ← cget;
      a ← cassert_opt (UnknownFunction f) (s.(s_f2i) !! f);
      translate_args 0 vs;;
      cappend [Abranch_link true (ImmediateOp a)]
  | LUbE =>
      cappend [Abranch false (ImmediateOp 0)]
  end.

Fixpoint translate_lexpr (e : lexpr) : M unit :=
  match e with
  | LLetE v e1 e =>
      translate_lexpr_op e1;;
      write_var "R0" v;;
      translate_lexpr e
  (* We cannot handle [LetE v (If v1 e2 e3) e] because e2 and e3 could
  contain let bindings whose effect we would need to undo before
  executing e. Instead we rewrite LetE v (If v1 e2 e3) e to If v1
  (LetE v e2 e) (LetE v e3 e). *)
  | LIf e1 e2 e3 =>
      translate_lexpr_op e1;;
      s ← cget;
      '(_, a2) ← cscope (translate_lexpr e2);
      (* trick such that we don't need to prove that translate_lexpr
      does not modify the state *)
      cput s;;
      '(_, a3) ← cscope (translate_lexpr e3);
      cput s;;
      (* + 1 for the branch_eq at the start and + 1 for the branch at the end *)
      cappend [Abranch_eq false (ImmediateOp (2 + length a2)) "R0" (ImmediateOp 0)];;
      cappend a2;;
      cappend [Abranch false (ImmediateOp (1 + length a3))];;
      cappend a3
  | LEnd e => translate_lexpr_op e
  end.

Definition pass (args : list string) (vars : list (string * Z)) (e : lexpr) : M unit :=
  let ns := remove_dups (args ++ vars.*1 ++ assigned_vars (lexpr_to_expr e)) in
  save_r30;;
  allocate_places ns variable_registers;;
  initialize_args args;;
  initialize_locals vars;;
  move_sp false;;
  translate_lexpr e;;
  move_sp true;;
  restore_callee_save_registers;;
  cappend [Aret].

(** * examples *)
Definition test_fn_expr : lexpr :=
  LLetE "r" (LBinOp (VVar "a") AddOp (VVar "b")) $
  LLetE "r" (LBinOp (VVar "r") AddOp (VVar "c")) $
  LEnd $ LBinOp (VVar "a") AddOp (VVar "r").

Definition test_fn : fndef := {|
  fd_args := ["a"; "b"];
  fd_vars := [("c", 1)];
  fd_body := lexpr_to_expr test_fn_expr;
  fd_static := I
|}.

Compute let x := crun (initial_state ∅) (pass test_fn.(fd_args) test_fn.(fd_vars) test_fn_expr) in (x.(c_prog), x.(c_result)).

Definition test2_fn_expr : lexpr :=
  LIf (LVarVal (VVar "a"))
      (LIf (LVarVal (VVar "b")) (LEnd $ LVarVal (VVal $ StaticValNum 1)) (LEnd $ LVarVal (VVal $ StaticValNum 2)))
      (LIf (LVarVal (VVar "b")) (LEnd $ LVarVal (VVal $ StaticValNum 3)) (LEnd $ LVarVal (VVal $ StaticValNum 4))).

Definition test2_fn : fndef := {|
  fd_args := ["a"; "b"];
  fd_vars := [];
  fd_body := lexpr_to_expr test2_fn_expr;
  fd_static := I
|}.

Compute let x := crun (initial_state ∅) (pass test2_fn.(fd_args) test2_fn.(fd_vars) test2_fn_expr) in (x.(c_prog), x.(c_result)).

Definition test3_fn_expr : lexpr :=
  LLetE "r" (LCall "test3" [VVar "a"; VVal $ StaticValNum 1]) $
  LEnd (LVarVal (VVar "r")).

Definition test3_fn : fndef := {|
  fd_args := ["a"; "b"];
  fd_vars := [];
  fd_body := lexpr_to_expr test3_fn_expr;
  fd_static := I
|}.

Compute let x := crun (initial_state (<["test3" := 100]> $ ∅)) (pass test3_fn.(fd_args) test3_fn.(fd_vars) test3_fn_expr) in (x.(c_prog), x.(c_result)).

(** * proof *)
Class ProofFixedValues := {
  pf_sp : Z;
  pf_ins : gmap Z asm_instr;
  pf_fns : gmap string fndef;
  pf_cs : list imp_to_asm_stack_item;
  pf_rsold : gmap string Z;
  pf_f2i : gmap string Z;
}.

Section proof.
Context `{!ProofFixedValues}.

(** ** general invariants *)
Definition stack_slot (slot : N) (v : Z) : uPred _ :=
  i2a_mem_constant (pf_sp - Z.of_N slot - 1) v.

Definition ci2a_regs_inv (s : state) (lr rs : gmap string Z) : uPred imp_to_asmUR :=
  ⌜pf_rsold !! "SP" = Some pf_sp⌝ ∗
  ⌜rs !! "SP" = Some (if s.(s_sp_above) then pf_sp else pf_sp - Z.of_N s.(s_stacksize))⌝ ∗
  ⌜map_scramble touched_registers lr rs⌝ ∗
  ⌜map_list_included touched_registers rs⌝ ∗
  ⌜s.(s_f2i) = pf_f2i⌝.

Definition ci2a_inv (s : state) (lr rs : gmap string Z) (mem : gmap Z Z) (h : heap_state) : uPred _ :=
    i2a_mem_inv (pf_sp - Z.of_N s.(s_stacksize)) mem ∗
    i2a_heap_inv h ∗
    ci2a_regs_inv s lr rs.

(** *** lemmas for general invariants *)
Lemma stack_slot_lookup slot v mem sp:
  stack_slot slot v -∗
  i2a_mem_inv sp mem -∗
  ⌜mem !!! (pf_sp - Z.of_N slot - 1) = v⌝.
Proof. iIntros "? ?". iApply (i2a_mem_lookup with "[$] [$]"). Qed.

Lemma ci2a_regs_inv_mono_insert rs s r lr v :
  r ∈ touched_registers ∧ r ≠ "SP" →
  ci2a_regs_inv s lr rs -∗
  ci2a_regs_inv s lr (<[r := v]> rs).
Proof.
  iIntros ([??] (?&?&?&?&?)).
  iPureIntro. simplify_map_eq. split!.
  - by apply map_scramble_insert_r_in.
  - by apply map_list_included_insert.
Qed.

Lemma ci2a_regs_inv_mono_insert_l rs s r lr v :
  r ∈ touched_registers ∧ r ≠ "SP" →
  map_list_included touched_registers rs →
  ci2a_regs_inv s lr (<[r := v]> rs) -∗
  ci2a_regs_inv s lr rs.
Proof.
  iIntros ([??] ? (?&?&?&?&?)).
  iPureIntro. simplify_map_eq. split!.
  etrans; [done|]. by apply map_scramble_insert_l_in.
Qed.

(** ** ci2a_places_inv *)
(* sr : saved registers (regname, slot) *)
Definition ci2a_places_inv (ps : gmap string place) (sr : list (string*N)) (vs : gmap string val) (rs : gmap string Z)
  : uPred imp_to_asmUR :=
  ([∗ map] n↦p∈ps, ∃ av,
     (if vs !! n is Some v then i2a_val_rel v av else True) ∗
     match p with
     | PReg r => ⌜r ∈ variable_registers⌝ ∗ ⌜rs !! r = Some av⌝ ∗ ⌜r ∈ sr.*1⌝
     | PStack slot => stack_slot slot av
     end) ∗
   ([∗ list] r∈sr, ∃ v, ⌜pf_rsold !! r.1 = Some v⌝ ∗ stack_slot r.2 v) ∗
   ⌜sr.*1 ⊆ "R30"::variable_registers⌝ ∗
   ⌜Forall (λ v, v ∈ sr.*1 ∨ pf_rsold !! v = rs !! v) variable_registers⌝ ∗
   ⌜∀ v1 v2 r, ps !! v1 = Some (PReg r) → ps !! v2 = Some (PReg r) → v1 = v2⌝.

Lemma ci2a_places_inv_mono_rs rs ps sr vs rs' :
  map_preserved variable_registers rs rs' →
  ci2a_places_inv ps sr vs rs -∗
  ci2a_places_inv ps sr vs rs'.
Proof.
  iIntros (Hp) "(Hp&$&$&%Hv&$)".
  iSplitL "Hp".
  - iApply (big_sepM_impl with "[$]"). iIntros "!>" (???). iDestruct 1 as (?) "[? Hp]".
    iExists _. iFrame. case_match => //. iDestruct "Hp" as %(?&?&?). iPureIntro. split!.
    by etrans; [symmetry; apply: Hp|].
  - iPureIntro. apply Forall_forall => ??. rewrite <-Hp; [|done]. move: Hv => /Forall_forall. naive_solver.
Qed.

(** ** sim *)
Definition sim (n : trace_index) (b : bool) (dins : list deep_asm_instr) (e : expr)
           (s : state) (rs : gmap string Z) (h h' : heap_state) : uPred imp_to_asmUR :=
  ∀ mem lr rf,
  ⌜deep_to_asm_instrs (rs !!! "PC") dins ⊆ pf_ins⌝ -∗
  rf -∗
  ci2a_inv s lr rs mem h' -∗
  iSat_end (AsmState (Some []) rs mem pf_ins
             ⪯{asm_module, imp_to_asm (dom _ pf_ins) (dom _ pf_fns) s.(s_f2i) imp_module, n, b}
           (SMProg, Imp e h pf_fns, (PPInside, I2A pf_cs lr, rf))).

Lemma to_sim n b dins e s rs h h' :
  sim n b dins e s rs h h' -∗ sim n b dins e s rs h h'.
Proof. done. Qed.

Lemma sim_mono_s n b dins e s s' rs h h':
  (∀ lr mem,
      ci2a_inv s lr rs mem h' -∗
      ⌜s'.(s_f2i) = s.(s_f2i)⌝ ∗ ci2a_inv s' lr rs mem h' ∗ sim n b dins e s' rs h h') -∗
  sim n b dins e s rs h h'.
Proof.
  iIntros "Hcont" (????) "Hrf ?".
  iDestruct ("Hcont" with "[$]") as (<-) "[? Hcont]".
  iApply ("Hcont" with "[//] Hrf [$]").
Qed.

Lemma sim_mono_b n b dins e s rs h h':
  sim n b dins e s rs h h'-∗
  sim n true dins e s rs h h'.
Proof.
  iIntros "Hcont" (????) "Hrf ?".
  iSatStop. apply: tsim_mono_b. iSatStart.
  by iApply ("Hcont" with "[//] Hrf").
Qed.

Lemma sim_get_sp s p b n rs e h h':
  (⌜rs !! "SP" = Some (if s.(s_sp_above) then pf_sp else pf_sp - Z.of_N s.(s_stacksize))⌝ -∗ sim n b p e s rs h h') -∗
  sim n b p e s rs h h'.
Proof.
  iIntros "Hcont" (????) "Hrf (?&?&(?&%&?))".
  iApply ("Hcont" with "[//] [//] Hrf").
  by iFrame.
Qed.

Lemma sim_regs_included s p b n rs e h h':
  (⌜map_list_included touched_registers rs⌝ -∗ sim n b p e s rs h h') -∗
  sim n b p e s rs h h'.
Proof.
  iIntros "Hcont" (????) "Hrf (?&?&(?&?&%))".
  iApply ("Hcont" with "[] [//] Hrf"); [naive_solver..|].
  by iFrame.
Qed.


Lemma sim_alloc_shared n b p e s rs h h' sz l a:
  heap_is_fresh h' l →
  ([∗ list] a ∈ seqZ a sz, i2a_mem_constant a 0) -∗
  (i2a_heap_shared l.1 a -∗ sim n b p e s rs h (heap_alloc h' l sz)) -∗
  sim n b p e s rs h h'.
Proof.
  iIntros (?) "Ha Hcont". iIntros (????) "Hrf (?&?&?)". iSatStop. iSatStartBupd.
  iMod (i2a_heap_alloc_shared with "[$] [$]") as "[??]"; [done|]. iModIntro.
  iApply ("Hcont" with "[$] [//] Hrf"). iFrame.
Qed.

Lemma sim_Amov r o n b p' e rs s h h':
  r ∈ touched_registers ∧ r ≠ "SP" ∧ r ≠ "PC" →
  sim n true p' e s (<["PC" := rs !!! "PC" + 1]> $ <[r := op_lookup rs o]>rs) h h' -∗
  sim n b (Amov r o :: p') e s rs h h'.
Proof.
  iIntros ([?[??]]) "Hcont".
  iApply sim_regs_included. iIntros (?).
  iIntros (??? Hins) "Hrf Hinv". iSatStop.
  tstep_i => ??. simplify_map_eq'.
  move: Hins => /deep_to_asm_instrs_cons_inv[??]. simplify_map_eq.
  rewrite orb_true_r.
  tstep_i. split!. { apply: map_list_included_is_Some; [done|]. naive_solver. }
  tstep_i. simplify_map_eq'. split!.
  iSatStart. iApply ("Hcont" with "[] Hrf"). { by simplify_map_eq'. }
  iDestruct "Hinv" as "(?&?&?)". iFrame.
  iApply ci2a_regs_inv_mono_insert; [compute_done|].
  by iApply ci2a_regs_inv_mono_insert.
Qed.

Lemma sim_Aadd rd r1 o n b p' e rs s h h':
  rd ∈ touched_registers ∧ rd ≠ "SP" ∧ rd ≠ "PC" →
  sim n true p' e s (<["PC" := rs !!! "PC" + 1]> $ <[rd := rs !!! r1 + op_lookup rs o]>rs) h h' -∗
  sim n b (Aadd rd r1 o :: p') e s rs h h'.
Proof.
  iIntros ([?[??]]) "Hcont".
  iApply sim_regs_included. iIntros (?).
  iIntros (??? Hins) "Hrf Hinv". iSatStop.
  tstep_i => ??. simplify_map_eq'.
  move: Hins => /deep_to_asm_instrs_cons_inv[??]. simplify_map_eq.
  rewrite orb_true_r.
  tstep_i. split!. { apply: map_list_included_is_Some; [done|]. naive_solver. }
  tstep_i. simplify_map_eq'. split!.
  iSatStart. iApply ("Hcont" with "[] Hrf"). { by simplify_map_eq'. }
  iDestruct "Hinv" as "(?&?&?)". iFrame.
  iApply ci2a_regs_inv_mono_insert; [compute_done|].
  by iApply ci2a_regs_inv_mono_insert.
Qed.

Lemma sim_Astore r r1 o n b p' e rs s h h' a v v':
  rs !! r = Some v' →
  rs !! r1 = Some (a - o) →
  i2a_mem_constant a v -∗
  (i2a_mem_constant a v' -∗ sim n true p' e s (<["PC" := rs !!! "PC" + 1]> rs) h h') -∗
  sim n b (Astore r r1 o :: p') e s rs h h'.
Proof.
  iIntros (??) "Ha Hcont".
  iIntros (??? Hins) "Hrf Hinv". iSatStop.
  tstep_i => ??. simplify_map_eq'.
  move: Hins => /deep_to_asm_instrs_cons_inv[??]. simplify_map_eq.
  rewrite orb_true_r.
  tstep_i. split!.  rewrite Z.sub_simpl_r.
  tstep_i. simplify_map_eq'. split!.
  iSatStartBupd.
  iDestruct "Hinv" as "(?&?&?)".
  iMod (i2a_mem_update with "[$] [$]") as "[? ?]". iModIntro.
  iApply ("Hcont" with "[$] [] Hrf"). { by simplify_map_eq'. }
  iFrame. by iApply ci2a_regs_inv_mono_insert; [compute_done|].
Qed.

Lemma sim_Var s p b n rs h h' e K v `{!ImpExprFill e K (Var v)}:
  ⊢ sim n b p e s rs h h'.
Proof.
  destruct ImpExprFill0; subst.
  iIntros (????) "??". iSatStop. by tstep_s.
Qed.

(** rules for operations *)
Lemma move_sp_correct s s' p p' r n b e rs ab h h':
  crun s (move_sp ab) = CResult s' p (CSuccess r) →
  (∀ pc' sp',
      ⌜s' = s <|s_sp_above := ab |>⌝ -∗
      sim n true p' e s' (<["PC":=pc']> $ <["SP":=sp']>rs) h h') -∗
  sim n b (p ++ p') e s rs h h'.
Proof.
  unfold move_sp. move => ?. simplify_crun_eq. iIntros "Hcont".
  iApply sim_get_sp. iIntros (?).
  iIntros (??? Hins) "Hrf (Hmem&Hheap&Hregs)".
  iSatStop.
  tstep_i => ??. simplify_map_eq'.
  move: Hins => /deep_to_asm_instrs_cons_inv[??]. simplify_map_eq.
  rewrite orb_true_r.
  tstep_i. split!.
  tstep_i. split!; simplify_map_eq'; [done|].
  iSatStart.
  iApply ("Hcont" with "[//] [] Hrf"). { by simplify_map_eq'. }
  iFrame.
  iDestruct "Hregs" as %(?&?&?&?&?).
  iApply ci2a_regs_inv_mono_insert; [compute_done|].
  iPureIntro. simplify_map_eq. split!.
  - by repeat case_match; f_equal; lia.
  - apply map_scramble_insert_r_in; [compute_done|done].
  - by apply map_list_included_insert.
Qed.

Lemma alloc_stack_correct s s' p p' r n b e rs h h' sz:
  crun s (alloc_stack sz) = CResult s' p (CSuccess r) →
  (⌜s' = s <|s_stacksize := (s.(s_stacksize) + sz)%N |>⌝ -∗
   ⌜r = s.(s_stacksize)⌝ -∗
   ⌜p = []⌝ -∗
   ([∗ list] a ∈ seqZ (pf_sp - Z.of_N (s.(s_stacksize)) - Z.of_N sz) (Z.of_N sz), ∃ v, i2a_mem_constant a v) -∗
   sim n b p' e s' rs h h') -∗
  sim n b (p ++ p') e s rs h h'.
Proof.
  unfold alloc_stack. move => ?. simplify_crun_eq.
  iIntros "Hcont" (????) "Hrf (Hmem&Hheap&Hregs)".
  iSatStop. iSatStartBupd.
  iMod (i2a_mem_alloc_big (Z.of_N sz) with "[$]") as "[? Ha]"; [lia|]. iModIntro.
  iApply ("Hcont" with "[//] [//] [//] [Ha] [//] Hrf").
  - iApply (big_sepL_impl with "Ha"). iIntros "!>" (???) "?". iExists _. iFrame.
  - iFrame => /=.
    have -> : pf_sp - Z.of_N (s_stacksize s) - Z.of_N sz = (pf_sp - Z.of_N (s_stacksize s + sz)) by lia.
    iFrame. iDestruct "Hregs" as %(?&?&?&?&?).
    iPureIntro. split!. by case_match.
Qed.

Lemma alloc_stack_correct_slot s s' p p' r n b e rs h h':
  crun s (alloc_stack 1) = CResult s' p (CSuccess r) →
  (∀ v, ⌜s' = s <|s_stacksize := (s.(s_stacksize) + 1)%N |>⌝ -∗
        ⌜r = s.(s_stacksize)⌝ -∗
        ⌜p = []⌝ -∗
        stack_slot s.(s_stacksize) v -∗
        sim n b p' e s' rs h h') -∗
  sim n b (p ++ p') e s rs h h'.
Proof.
  iIntros (?) "Hcont".
  iApply alloc_stack_correct; [done|]. iIntros (???) "[[%v ?] _]".
  by iApply "Hcont".
Qed.

Lemma read_stack_correct s s' p p' r res b n slot rs v e h h':
  crun s (read_stack r slot) = CResult s' p (CSuccess res) →
  r ∈ touched_registers ∧ r ≠ "SP" ∧ r ≠ "PC" →
  stack_slot slot v -∗
  (⌜s' = s⌝ -∗ stack_slot slot v -∗ sim n true p' e s' (<["PC" := rs !!! "PC" + length p]> $ <[r := v]> rs) h h') -∗
  sim n b (p ++ p') e s rs h h'.
Proof.
  unfold read_stack, stack_offset.
  iIntros (?[?[??]]) "Hs Hcont". simplify_crun_eq.
  iApply sim_get_sp. iIntros (?).
  iApply sim_regs_included. iIntros (?).

  iIntros (??? Hins) "Hrf (Hmem&Hheap&Hregs)". iSatStop.
  tstep_i => ??. simplify_map_eq'.
  move: Hins => /deep_to_asm_instrs_cons_inv[??]. simplify_map_eq.
  rewrite orb_true_r.
  tstep_i. split!. { apply: map_list_included_is_Some; [done|]. naive_solver. }
  tstep_i. split!; simplify_map_eq'; [done|].
  iSatStart.
  iDestruct (stack_slot_lookup with "[$] [$]") as %?. simplify_eq.
  have -> : (if s_sp_above s then pf_sp else pf_sp - Z.of_N (s_stacksize s)) +
       ((if s_sp_above s then 0 else Z.of_N (s_stacksize s)) - Z.of_N slot - 1) = pf_sp - Z.of_N slot - 1 by case_match; lia.
  iApply ("Hcont" with "[//] [$] [%] Hrf"). { by simplify_map_eq'. } iFrame.
  iApply ci2a_regs_inv_mono_insert; [compute_done| ].
  by iApply ci2a_regs_inv_mono_insert.
Qed.

Lemma write_stack_correct s s' p p' r res b n slot rs v v' e h h':
  crun s (write_stack r slot) = CResult s' p (CSuccess res) →
  rs !! r = Some v' →
  stack_slot slot v -∗
  (⌜s' = s⌝ -∗ stack_slot slot v' -∗ sim n true p' e s' (<["PC" := rs !!! "PC" + length p]> rs) h h') -∗
  sim n b (p ++ p') e s rs h h'.
Proof.
  unfold write_stack, stack_offset.
  iIntros (??) "Hs Hcont". simplify_crun_eq.
  iApply sim_get_sp. iIntros (?).
  iApply (sim_Astore with "[$]"); [done| |].
  { simplify_map_eq. f_equal. case_match; lia. }
  iIntros "Hs". by iApply "Hcont".
Qed.

Lemma clear_mem_correct_inv s s' p p' r res n rs e h h' sz a:
  crun s (cmap (E:=error) (seqZ 0 sz) 0 (λ _ o, cappend [Astore "R1" r o])) = CResult s' p (CSuccess res) →
  rs !! r = Some a →
  rs !! "R1" = Some 0 →
  r ≠ "PC" ∧ r ≠ "R1" →
  ([∗ list] a ∈ seqZ a sz, ∃ v, i2a_mem_constant a v) -∗
  (∀ rs',
      ⌜s' = s⌝ -∗
      ⌜map_scramble ["PC"] rs rs'⌝ -∗
      ([∗ list] a ∈ seqZ a sz, i2a_mem_constant a 0) -∗
      sim n true p' e s' rs' h h') -∗
  sim n true (p ++ p') e s rs h h'.
Proof.
  have ->: a = a + 0 by lia. rewrite -(fmap_add_seqZ a 0).
  elim: (seqZ 0 sz) rs p res.
  { move => rs p res /= ????. iIntros "? Hcont". simplify_crun_eq. by iApply "Hcont". }
  move => a' al IH rs p res /= ??? [??].
  iIntros "[[%v ?] ?] Hcont". simplify_crun_eq.
  iApply (sim_Astore with "[$]"); [done|simplify_map_eq;f_equal;lia|].
  iIntros "Ha". rewrite -!app_assoc /=.
  iApply (IH with "[$]"); [by rewrite cmap_S|by simplify_map_eq|by simplify_map_eq|done|].
  iIntros (???) "?". iApply "Hcont"; [done| |by iFrame]. iPureIntro. etrans; [|done].
  apply map_scramble_insert_r_in; [|done]. compute_done.
Qed.

Lemma clear_mem_correct s s' p p' r res n rs e h h' sz a:
  crun s (clear_mem r sz) = CResult s' p (CSuccess res) →
  rs !! r = Some a →
  r ≠ "PC" ∧ r ≠ "R1" →
  ([∗ list] a ∈ seqZ a sz, ∃ v, i2a_mem_constant a v) -∗
  (∀ rs',
      ⌜s' = s⌝ -∗
      ⌜map_scramble ["PC"; "R1"] rs rs'⌝ -∗
      ([∗ list] a ∈ seqZ a sz, i2a_mem_constant a 0) -∗
      sim n true p' e s' rs' h h') -∗
  sim n true (p ++ p') e s rs h h'.
Proof.
  unfold clear_mem.
  iIntros (??[??]) "Ha Hcont". simplify_crun_eq.
  iApply sim_Amov; [compute_done|]. rewrite -!app_assoc/=.
  iApply (clear_mem_correct_inv with "[$]"); [done|by simplify_map_eq|by simplify_map_eq|done|..].
  iIntros (???) "?". iApply "Hcont"; [done| |done]. iPureIntro.
  etrans. 2: { apply: map_scramble_mono; [done|compute_done]. }
  apply map_scramble_insert_r_in; [compute_done|].
  apply map_scramble_insert_r_in; [compute_done|done].
Qed.

Lemma read_var_correct s s' p p' r res b n rs v v' e vs h h':
  crun s (read_var r v) = CResult s' p (CSuccess res) →
  r ∈ tmp_registers ∧ r ≠ "PC" →
  vs !! v = Some v' →
  ci2a_places_inv s.(s_places) s.(s_saved_registers) vs rs -∗
  (∀ pc' av,
   let rs' := (<["PC":=pc']> $ <[r := av]>rs) in
   ⌜s' = s⌝ -∗
   i2a_val_rel v' av -∗
   ci2a_places_inv s.(s_places) s.(s_saved_registers) vs rs' -∗
   sim n true p' e s' rs' h h') -∗
  sim n b (p ++ p') e s rs h h'.
Proof.
  unfold read_var.
  iIntros (?[Hin ?]?) "Hp Hcont". simplify_crun_eq.
  have ? : r ∈ touched_registers ∧ r ≠ "SP" ∧ r ≠ "PC". {
    split. 2: split => ?; subst; set_solver.
    apply: (list_elem_of_weaken tmp_registers); [done|compute_done].
  }
  iDestruct "Hp" as "[Hp ?]".
  iDestruct (big_sepM_lookup_acc with "Hp") as "[[% [Hv Hpl]] Hp]"; [done|]. simplify_map_eq.
  iDestruct "Hv" as "#Hv".
  case_match; simplify_crun_eq.
  - iDestruct "Hpl" as %(?&?&?).
    iApply sim_Amov; [done|].
    simplify_map_eq'.
    iApply ("Hcont" with "[//] Hv").
    iApply (ci2a_places_inv_mono_rs). {
      apply map_preserved_insert_r_not_in; [compute_done|].
      apply map_preserved_insert_r_not_in; [|done].
      clear -Hin. set_unfold. naive_solver.
    }
    iFrame. iApply "Hp". iSplit!.
  - iApply (read_stack_correct with "[$]"); [done..|]. iIntros (?) "?".
    iApply ("Hcont" with "[//] Hv").
    iApply (ci2a_places_inv_mono_rs rs). {
      apply map_preserved_insert_r_not_in; [compute_done|].
      apply map_preserved_insert_r_not_in; [|done].
      clear -Hin. set_unfold. naive_solver.
    }
    iFrame. iApply "Hp". iExists _. by iFrame.
Qed.

Lemma write_var_correct v' s s' p p' r res b n rs v av e vs h h':
  crun s (write_var r v) = CResult s' p (CSuccess res) →
  rs !! r = Some av →
  ci2a_places_inv s.(s_places) s.(s_saved_registers) vs rs -∗
  i2a_val_rel v' av -∗
  (∀ rs', ⌜s' = s⌝ -∗
          ⌜map_scramble ("PC"::variable_registers) rs rs'⌝ -∗
          ci2a_places_inv s.(s_places) s.(s_saved_registers) (<[v := v']>vs) rs' -∗
          sim n true p' e s' rs' h h') -∗
  sim n b (p ++ p') e s rs h h'.
Proof.
  unfold write_var.
  iIntros (??) "Hp Hv Hcont". simplify_crun_eq.
  iDestruct "Hp" as "[Hp [Hf [% [%Ha %Hbij]]]]".
  rewrite big_sepM_delete; [|done].
  iDestruct "Hp" as "[[% [_ Hpl]] Hp]".
  case_match; simplify_crun_eq.
  - iDestruct "Hpl" as %(?&?&?).
    iApply sim_Amov. {
      split. 2: split => ?; subst; set_solver.
      apply: (list_elem_of_weaken variable_registers); [done|compute_done].
    }
    simplify_map_eq'.
    iApply ("Hcont" with "[//] [%]"). {
      apply map_scramble_insert_r_in; [compute_done|].
      apply map_scramble_insert_r_in; [|done].
      apply: (list_elem_of_weaken variable_registers); [done|compute_done].
    }
    iApply (ci2a_places_inv_mono_rs). { apply map_preserved_insert_r_not_in; [compute_done|]. done. }
    iFrame. rewrite (big_sepM_delete _ (s_places _)); [|done].
    iSplit; [iSplitR "Hp"|iSplit!]; simplify_map_eq.
    + iExists _. by iFrame.
    + iApply (big_sepM_impl with "Hp").
      iIntros "!>" (??[??]%lookup_delete_Some) "[%a [? Hx]]". simplify_map_eq. iExists _. iFrame.
      case_match => //. simplify_map_eq. iDestruct "Hx" as %(?&?&?). iPureIntro. split!.
      rewrite lookup_insert_ne //. naive_solver.
    + apply Forall_forall => r' ?. destruct (decide (r0 = r')); [naive_solver|simplify_map_eq].
      move: Ha => /Forall_forall. naive_solver.
  - iApply (write_stack_correct with "[$]"); [done..|]. iIntros (?) "?".
    iApply ("Hcont" with "[//] [%]"). { by apply map_scramble_insert_r_in; [compute_done|]. }
    iApply (ci2a_places_inv_mono_rs rs). { apply map_preserved_insert_r_not_in; [compute_done|]. done. }
    iFrame. rewrite (big_sepM_delete _ (s_places _)); [|done].
    iSplit; [iSplitR "Hp"|done]; simplify_map_eq.
    + simplify_map_eq. iExists _. iFrame.
    + iApply (big_sepM_impl with "Hp").
      iIntros "!>" (??[??]%lookup_delete_Some) "?". by simplify_map_eq.
Qed.

Lemma read_var_val_correct e e' s s' p p' n r rs vs res h h' K `{!ImpExprFill e' K (subst_map vs (var_val_to_expr e))}:
  crun s (read_var_val r e) = CResult s' p (CSuccess res) →
  r ∈ tmp_registers ∧ r ≠ "PC" →
  ci2a_places_inv s.(s_places) s.(s_saved_registers) vs rs -∗
  (∀ pc' av v,
      let rs' := <["PC" := pc']> $ <[r := av]> rs in
      ⌜s' = s⌝ -∗
      i2a_val_rel v av -∗
      ci2a_places_inv s.(s_places) s.(s_saved_registers) vs rs' -∗
      sim n true p' (expr_fill K (Val v)) s' rs' h h') -∗
  sim n true (p ++ p') e' s rs h h'.
Proof.
  destruct ImpExprFill0; subst.
  iIntros (?[??]) "Hp Hcont".
  destruct e; simplify_crun_eq.
  - case_match; [|iApply sim_Var; typeclasses eauto with tstep].
    iApply (read_var_correct with "Hp"); [done..|].
    iIntros (???) "?". by iApply "Hcont".
  - iApply sim_Amov.
    { split!; [|set_unfold;naive_solver]. apply: list_elem_of_weaken; [done|]. compute_done. }
    iApply "Hcont"; [by simplify_map_eq|by destruct v; simplify_eq/=|].
    iApply ci2a_places_inv_mono_rs; [|done].
    apply map_preserved_insert_r_not_in; [compute_done|].
    apply map_preserved_insert_r_not_in; [|done].
    set_unfold. naive_solver.
Qed.

Lemma save_r30_correct s s' p p' r n b e rs h h':
  crun s save_r30 = CResult s' p (CSuccess r) →
  s.(s_places) = ∅ →
  s.(s_saved_registers) = [] →
  pf_rsold = rs →
  is_Some (rs !! "R30") →
  (∀ pc' slot,
     let rs' := (<["PC":=pc']>rs) in
     ⌜s' = s <| s_stacksize := (s_stacksize s + 1)%N |> <|s_saved_registers := [("R30", slot)] |>⌝ -∗
     ci2a_places_inv ∅ s'.(s_saved_registers) ∅ rs' -∗
     sim n true p' e s' rs' h h') -∗
  sim n b (p ++ p') e s rs h h'.
Proof.
  unfold save_r30.
  iIntros (? Hp Hs ? [??]) "Hcont". simplify_crun_eq. rewrite -!app_assoc/=.
  iApply alloc_stack_correct_slot; [done|]. iIntros (????) "Hs". simplify_eq/=.
  iApply (write_stack_correct with "[$]"); [done..|]. iIntros (?) "Hs". simplify_eq.
  iApply "Hcont"; [by rewrite Hs|] => /=.
  iApply ci2a_places_inv_mono_rs. { apply map_preserved_insert_r_not_in; [compute_done|]. done. }
  iSplit; [done|]. rewrite Hs. iSplit! => /=.
  - set_solver.
  - apply Forall_true. by right.
Qed.

Lemma allocate_places_correct s ns vars s' p p' r n b e rs h h':
  crun s (allocate_places ns vars) = CResult s' p (CSuccess r) →
  vars ⊆+ variable_registers →
  (∀ v, v ∈ vars → v ∉ s.(s_saved_registers).*1) →
  (∀ v n, s.(s_places) !! n = Some (PReg v) → v ∉ vars) →
  NoDup ns →
  (∀ n, n ∈ ns → s.(s_places) !! n = None) →
  s_stacksize s = N.of_nat (length (s.(s_saved_registers)) + length (s_stack_places s.(s_places))) →
  ci2a_places_inv s.(s_places) s.(s_saved_registers) ∅ rs -∗
  (∀ rs',
     ⌜s.(s_places) ⊆ s'.(s_places)⌝ -∗
     ⌜s.(s_saved_registers) ⊆ s'.(s_saved_registers)⌝ -∗
     ⌜map_list_included ns s'.(s_places)⌝ -∗
     ⌜s_stacksize s' = N.of_nat (length (s'.(s_saved_registers)) + length (s_stack_places s'.(s_places)))⌝ -∗
     ⌜map_scramble ["PC"] rs rs'⌝ -∗
     ci2a_places_inv s'.(s_places) s'.(s_saved_registers) ∅ rs' -∗
     sim n b p' e s' rs' h h') -∗
  sim n b (p ++ p') e s rs h h'.
Proof.
  elim: ns vars s s' p rs b h h' => /=. {
    iIntros (???????????????) "? Hcont". simplify_crun_eq.
    iApply ("Hcont" with "[//] [//] [%] [//] [//] [$]").
    1: by apply map_list_included_nil. }
  iIntros (?? IH [|v vars] ????????); iIntros (Hsub Hn ? [??]%NoDup_cons ?); iIntros (?) "Hp Hcont"; simplify_crun_eq.
  - rewrite -app_assoc. iApply alloc_stack_correct_slot; [done|]. iIntros (????) "Hs". simplify_eq/=.
    iApply sim_mono_s. iIntros (??) "Hinv".
    iSplitR; [|iSplitL "Hinv"]. 3: iApply (IH with "[Hs Hp]"); [done|done|done|set_solver|done|..] => /=.
    { done. }
    + iDestruct "Hinv" as "(?&?&?)". iFrame.
    + move => ??. apply lookup_insert_None. set_solver.
    + rewrite /= s_stack_places_insert; [|set_solver] => /=. lia.
    + iDestruct "Hp" as "[? [$ [$ [$ %]]]]". iSplit.
      * iApply big_sepM_insert; [set_solver|]. iFrame.
        simplify_map_eq. iExists _. iFrame.
      * iPureIntro. move => ??? /lookup_insert_Some? /lookup_insert_Some?. naive_solver.
    + iIntros (??????). iApply "Hcont"; iPureIntro.
      * etrans; [|done]. apply insert_subseteq. set_solver.
      * set_solver.
      * apply map_list_included_cons; [|done].
        apply: elem_of_weaken; [|by apply subseteq_dom].
        set_solver.
      * done.
      * done.
  - rewrite -!app_assoc. iApply alloc_stack_correct_slot; [done|]. iIntros (????) "Hs". simplify_eq/=.
    iApply sim_regs_included. iIntros (?).
    move: Hsub => /submseteq_cons_l [?[Hperm Hsub]].
    have [??]: is_Some (rs !! v). {
      apply: map_list_included_is_Some.
      { apply: (map_list_included_mono _ variable_registers); [done|compute_done]. }
      rewrite Hperm. set_solver. }
    iApply (write_stack_correct with "[$]"); [done..|]. iIntros (?) "Hs". simplify_eq.
    iApply sim_mono_s. iIntros (??) "Hinv".
    have ? : v ∉ vars. {
      move => /(elem_of_submseteq _ _ _)/(_ Hsub).
      apply: NoDup_cons_1_1. rewrite -Hperm. compute_done.
    }
    iSplitR; [|iSplitL "Hinv"]. 3: iApply (IH with "[Hp Hs]"); [done|..]. all: csimpl.
    + done.
    + iDestruct "Hinv" as "(?&?&?)". iFrame.
    + rewrite Hperm. by apply submseteq_cons.
    + set_unfold; naive_solver.
    + move => ?? /lookup_insert_Some[[??]|[??]]; set_solver.
    + done.
    + move => ??. apply lookup_insert_None. set_solver.
    + rewrite /= s_stack_places_insert; [|set_solver] => /=. lia.
    + iApply ci2a_places_inv_mono_rs. { apply map_preserved_insert_r_not_in; [compute_done|]. done. }
      iDestruct "Hp" as "(Hp&Hsr&%&%Hv&%)". iSplitL "Hp"; [|repeat iSplit]; csimpl.
      * iApply big_sepM_insert; [set_solver|]. iFrame. iSplitR.
        { iExists _. simplify_map_eq. iPureIntro. split!. { rewrite Hperm. set_solver. } set_solver. }
        iApply (big_sepM_impl with "[$]"). iIntros "!>" (???) "[% [? Hp]]". iExists _. iFrame.
        case_match => //. iDestruct "Hp" as %(?&?&Hin). iPureIntro. csimpl. split!.
        clear -Hin. set_unfold. naive_solver.
      * simpl. iFrame. iExists _. iFrame. iPureIntro.
        move: Hv => /Forall_forall/(_ v)[| |->//]. { rewrite Hperm. set_solver. }  set_unfold. naive_solver.
      * iPureIntro. apply list_subseteq_cons_l; [|done]. rewrite Hperm. set_solver.
      * iPureIntro. apply: Forall_impl; [done|]. set_unfold. naive_solver.
      * iPureIntro. move => ??? /lookup_insert_Some[[??]|[??]] /lookup_insert_Some[[??]|[??]]; set_solver.
    + iIntros (??????) "?". iApply sim_mono_b.
      iApply ("Hcont" with "[%] [%] [%] [//] [%] [$]").
      * etrans; [|done]. apply insert_subseteq. set_solver.
      * set_solver.
      * apply map_list_included_cons; [|done].
        apply: elem_of_weaken; [|by apply subseteq_dom].
        set_solver.
      * etrans; [|done]. rewrite map_scramble_insert_r_in; [done|compute_done].
Qed.

Lemma initialize_args_correct s xs s' p p' r n e rs vs vm h h':
  crun s (initialize_args xs) = CResult s' p (CSuccess r) →
  length xs = length vs →
  NoDup xs →
  i2a_args 0 vs rs -∗
  ci2a_places_inv s.(s_places) s.(s_saved_registers) vm rs -∗
  (∀ rs',
     ⌜s' = s⌝ -∗
     ⌜map_scramble ("PC"::variable_registers) rs rs'⌝ -∗
     ci2a_places_inv s'.(s_places) s'.(s_saved_registers) (list_to_map (zip xs vs) ∪ vm) rs' -∗
     sim n true p' e s' rs' h h') -∗
  sim n true (p ++ p') e s rs h h'.
Proof.
  unfold initialize_args.
  elim: xs vs vm s s' p rs 0%nat => /=. {
    move => [|//] ?????????. simplify_crun_eq.
    iIntros "_ Hp Hcont". iApply "Hcont"; [done..|]. by rewrite left_id_L.
  }
  move => ?? IH [//|??] ??????? /=[?] /NoDup_cons[??]. simplify_crun_eq.
  rewrite i2a_args_cons; [|done]. iIntros "[[% [% ?]] Hl] Hp Hcont".
  rewrite -!app_assoc /=.
  iApply (write_var_correct with "[$] [$]"); [done..|].
  iIntros (?? Hrs) "Hp". simplify_eq.
  iApply (IH with "[Hl] Hp"). { apply cbind_success. split!; [done..|]. by rewrite app_nil_r. }
  { done. } { done. }
  { iApply i2a_args_mono; [|done]. apply: map_scramble_preserved; [done|]. clear.
    set_unfold => ?? /(elem_of_drop _ _). set_unfold. naive_solver. }
  iIntros (???) "Hp".
  iApply "Hcont"; [done|iPureIntro;by etrans|].
  rewrite -insert_union_l -insert_union_r; [done|].
  apply not_elem_of_list_to_map_1. rewrite fst_zip //. lia.
Qed.

Lemma initialize_locals_correct_inv K s vars s' p p' r n e rs vm h h' ls e'
      `{!ImpExprFill e' K e}:
  crun s (initialize_locals vars) = CResult s' p (CSuccess r) →
  NoDup vars.*1 →
  heap_alloc_list vars.*2 ls h' h →
  Forall (λ z : Z, 0 < z) vars.*2 →
  ci2a_places_inv s.(s_places) s.(s_saved_registers) vm rs -∗
  (∀ rs' adrs,
     ⌜s' = s <| s_stacksize := (s.(s_stacksize) + N.of_nat (sum_list_with Z.to_nat vars.*2))%N |>⌝ -∗
     ⌜length ls = length vars⌝ -∗
     ⌜Forall (λ l, l.2 = 0) ls⌝ -∗
     ⌜Forall2 (λ a n, a + n ≤ pf_sp) adrs vars.*2⌝ -∗
     ([∗ list] l;a∈ls;adrs, i2a_heap_shared l.1 a) -∗
     ci2a_places_inv s'.(s_places) s'.(s_saved_registers) (list_to_map (zip vars.*1 (ValLoc <$> ls)) ∪ vm) rs' -∗
     sim n true p' (expr_fill K e) s' rs' h h) -∗
  sim n true (p ++ p') e' s rs h h'.
Proof.
  destruct ImpExprFill0; subst. destruct r.
  elim: vars ls s s' p h' rs vm. {
    unfold initialize_locals.
    move => ls s s' p h' rs vm /= ????. iIntros "? Hcont". destruct_all?. simplify_crun_eq.
    iApply "Hcont"; try iPureIntro; try done.
    - destruct s. rewrite /set/=. f_equal. lia.
    - by rewrite left_id_L.
  }
  move => [v sz] vars IH ls s s' p h' rs vm; csimpl.
  unfold initialize_locals => ? /NoDup_cons[??] ? /Forall_cons[??]. destruct_all?. simplify_crun_eq.
  iIntros "Hinv Hcont". rewrite -!app_assoc /=.
  iApply alloc_stack_correct; [done|].
  iIntros (???) "Hs". simplify_eq. rewrite Z2N.id; [|lia].
  iApply sim_get_sp. iIntros (Hsp). simplify_eq/=. case_match; [|done].
  iApply sim_Aadd; [compute_done|] => /=. rewrite -!app_assoc /=.
  iApply (clear_mem_correct with "[$]"); [done|simplify_map_eq';f_equal;lia|compute_done|].
  iIntros (?? Hrs) "?". simplify_map_eq.
  iApply (sim_alloc_shared with "[$]"); [done|]. iIntros "#?".
  iApply (write_var_correct (ValLoc _) with "[Hinv]");
    [done|rewrite <-Hrs;[|compute_done];by simplify_map_eq|..] => /=.
  { iApply ci2a_places_inv_mono_rs; [|done].
    etrans; [ |apply: map_scramble_preserved; [done|set_solver-]].
    eapply map_preserved_insert_r_not_in; [compute_done|].
    eapply map_preserved_insert_r_not_in; [compute_done|done]. }
  { iExists _. iFrame "#". iPureIntro. simplify_map_eq'. revert select (heap_is_fresh _ _) => -[??]. lia. }
  iIntros (???) "Hinv". simplify_eq/=.
  iApply (IH with "[Hinv]"); [|done|done|done|done|..].
  { unfold initialize_locals. apply cbind_success. split!; [| by apply cret_success|by rewrite app_nil_r].
    by rewrite cmap_S. }
  iIntros (??????) "#Hs ?". simplify_eq/=.
  iApply ("Hcont" $! _ (_::_) with "[%] [%] [%] [%] [$]").
  - destruct s. rewrite /set/=. f_equal. lia.
  - lia.
  - econs; [|done]. revert select (heap_is_fresh _ _) => -[??]. done.
  - econs; [|done]. lia.
  - rewrite -insert_union_r ?insert_union_l; [done|]. apply not_elem_of_list_to_map.
    move => /elem_of_list_fmap[[??][?/(elem_of_zip_l _ _ _)]]. naive_solver.
Qed.

Lemma initialize_locals_correct s vars s' p p' r n e rs vm h K:
  crun s (initialize_locals vars) = CResult s' p (CSuccess r) →
  NoDup vars.*1 →
  ci2a_places_inv s.(s_places) s.(s_saved_registers) vm rs -∗
  (∀ rs' (ls : list loc) adrs h',
     ⌜s' = s <| s_stacksize := (s.(s_stacksize) + N.of_nat (sum_list_with Z.to_nat vars.*2))%N |>⌝ -∗
     ⌜length ls = length vars⌝ -∗
     ⌜Forall (λ l, l.2 = 0) ls⌝ -∗
     ⌜Forall2 (λ a n, a + n ≤ pf_sp) adrs vars.*2⌝ -∗
     ([∗ list] l;a∈ls;adrs, i2a_heap_shared l.1 a) -∗
     ci2a_places_inv s'.(s_places) s'.(s_saved_registers) (list_to_map (zip vars.*1 (ValLoc <$> ls)) ∪ vm) rs' -∗
     sim n true p' (expr_fill K (FreeA (zip ls vars.*2) (subst_l vars.*1 (ValLoc <$> ls) e))) s' rs' h' h') -∗
  sim n true (p ++ p') (expr_fill K (AllocA vars e)) s rs h h.
Proof.
  iIntros (??) "Hp Hcont". iIntros (????) "Hrf ?". iSatStop. tstep_s.
  have [??]:= heap_alloc_list_fresh vars.*2 ∅ h. split!; [done|]. move => ?. iSatStart.
  iApply (initialize_locals_correct_inv with "Hp [Hcont] [//] [Hrf]");
    [typeclasses eauto with tstep|done|done|done|done| |done|done].
  iIntros (??????) "??" => /=. iApply ("Hcont" with "[//] [//] [//] [//] [$] [$]").
Qed.

Lemma translate_args_correct vs1 s s' p p' n rs vs vm res m K f h:
  crun s (translate_args m vs) = CResult s' p (CSuccess res) →
  ci2a_places_inv s.(s_places) s.(s_saved_registers) vm rs -∗
  (∀ rs' vs',
      ⌜s' = s⌝ -∗
      ⌜map_preserved (take m args_registers) rs rs'⌝ -∗
      i2a_args m vs' rs' -∗
      ci2a_places_inv s.(s_places) s.(s_saved_registers) vm rs' -∗
      sim n true p' (expr_fill K (Call f (Val <$> (vs1 ++ vs')))) s' rs' h h) -∗
  sim n true (p ++ p') (expr_fill K (Call f ((Val <$> vs1) ++ ((subst_map vm) <$> (var_val_to_expr <$> vs)))))  s rs h h.
Proof.
  elim: vs m s s' p p' res rs vs1; unfold translate_args; csimpl.
  - move => *. simplify_crun_eq. iIntros "? Hcont". setoid_rewrite fmap_app.
    iApply ("Hcont" $! _ []); [done|done| |done]. by rewrite i2a_args_nil.
  - move => v vs IH m s s' p p' res rs vs1 ?. simplify_crun_eq. rewrite -?app_assoc /=.
    iIntros "Hp Hcont".
    revert select (args_registers !! _ = Some _) => Hreg. move: (Hreg) => /(elem_of_list_lookup_2 _ _ _)?.
    iApply (read_var_val_correct with "Hp"); [|done| |]. {
      apply imp_expr_fill_expr_fill.
      constructor. by instantiate (1 := [CallCtx _ _ _]).
    } { set_unfold. naive_solver. }
    iIntros (?? v' ?) "Hv Hp" => /=. subst.
    rewrite cons_middle app_assoc. change ([Val v']) with (Val <$> [v']).
    rewrite -fmap_app.
    iApply (IH with "Hp").
    { apply cbind_success. split!; [done|by apply cret_success|by rewrite app_nil_r]. }
    iIntros (rs' ?? Hpre) "Hvs Hp". subst. rewrite -app_assoc.
    move: Hpre. erewrite take_S_r; [|done]. move => /map_preserved_app[Hpre1 Hpre2].
    iApply ("Hcont" with "[//] [%] [Hvs Hv] Hp"). {
      etrans; [|done].
      apply map_preserved_insert_r_not_in.
      { move => /elem_of_take[?[/(elem_of_list_lookup_2 _ _ _) ]]. set_solver. }
      apply map_preserved_insert_r_not_in; [|done].
      move => /elem_of_take[?[]].
      have /NoDup_alt: NoDup args_registers by compute_done.
      move => /[apply]. naive_solver lia.
    }
    rewrite i2a_args_cons; [|done]. iFrame. iSplit!; [|done].
    etrans; [symmetry; apply: Hpre2; set_solver|]. rewrite lookup_insert_ne; [by simplify_map_eq|set_solver].
Qed.

Definition call_correct (n : trace_index) (s : state) (K : list expr_ectx) : Prop :=
  (∀ rs vs vm p' a f K' h,
      s.(s_f2i) !! f = Some a →
  i2a_args 0 vs rs -∗
  ci2a_places_inv (s_places s) (s_saved_registers s) vm rs -∗
  (∀ rs' av v h',
     ⌜rs' !! "R0" = Some av⌝ -∗
     i2a_val_rel v av -∗
     ci2a_places_inv (s_places s) (s_saved_registers s) vm rs' -∗
     sim n true p' (expr_fill (K' ++ K) (Val v)) s rs' h' h') -∗
  sim n true (Abranch_link true (ImmediateOp a) :: p') (expr_fill (K' ++ K) (Call f (Val <$> vs))) s rs h h).

Lemma translate_lexpr_op_correct s s' p p' n e e' rs vs res h K K'
      `{!ImpExprFill e' K' (subst_map vs (lexpr_op_to_expr e))}:
  crun s (translate_lexpr_op e) = CResult s' p (CSuccess res) →
  call_correct n s K →
  K `suffix_of` K' →
  ci2a_places_inv s.(s_places) s.(s_saved_registers) vs rs -∗
  (∀ rs' av v h',
      ⌜rs' !! "R0" = Some av⌝ -∗
      ⌜s' = s⌝ -∗
      i2a_val_rel v av -∗
      ci2a_places_inv s.(s_places) s.(s_saved_registers) vs rs' -∗
      sim n true p' (expr_fill K' (Val v)) s' rs' h' h') -∗
  sim n true (p ++ p') e' s rs h h.
Proof.
  destruct ImpExprFill0; subst.
  iIntros (? Hcall [??]) "Hp Hcont".
  destruct e; simplify_crun_eq.
  - iApply (read_var_val_correct with "Hp"); [typeclasses eauto with tstep|done|compute_done|].
    iIntros (????) "? Hp".
    iApply ("Hcont" with "[] [//] [$] Hp"). by simplify_map_eq.
  - rewrite -!app_assoc.
    iApply sim_regs_included. iIntros (?).
    iApply (read_var_val_correct with "Hp"); [typeclasses eauto with tstep|done|compute_done|].
    iIntros (?? v1' ?) "? Hp". simplify_eq/=.
    iApply (read_var_val_correct with "Hp"); [typeclasses eauto with tstep|done|compute_done|].
    iIntros (?? v2' ?) "? Hp". simplify_eq/=.
    iIntros (??? Hins) "Hrf Hinv".
    iSatStop. tstep_s => ??.
    case_match; simplify_crun_eq; destruct v1' as [|b1|], v2' as [|b2|] => //; simplify_eq/=.
    all: iSatStart; iDestruct!; iSatStop.
    all: tstep_i => ??; simplify_map_eq'.
    all: move: Hins => /deep_to_asm_instrs_cons_inv[??]; simplify_map_eq.
    all: tstep_i; simplify_map_eq'; split!; [apply: map_list_included_is_Some; [done|compute_done]|].
    all: tstep_i; simplify_map_eq'; split!.
    all: iSatStart.
    all: try iDestruct select (i2a_heap_shared _ _) as "#Hs".
    all: iApply (to_sim with "[Hcont Hp] [] Hrf"); [|by simplify_map_eq'|
      iDestruct "Hinv" as "($&$&?)";
      iApply ci2a_regs_inv_mono_insert; [compute_done|];
      iApply ci2a_regs_inv_mono_insert; [compute_done|done]].
    all: iApply "Hcont"; [by simplify_map_eq|done|simpl|
      iApply ci2a_places_inv_mono_rs; [|done];
      apply map_preserved_insert_r_not_in; [compute_done|];
      by apply map_preserved_insert_r_not_in; [compute_done|]].
    + done.
    + iExists _ => /=. iFrame "#". iPureIntro. lia.
    + done.
    + iPureIntro. destruct b1, b2 => //.
    + done.
    + done.
  - rewrite -!app_assoc.
    iApply sim_regs_included. iIntros (?).
    iApply (read_var_val_correct with "Hp"); [typeclasses eauto with tstep|done|compute_done|].
    iIntros (?? v' ?) "Hv Hp". simplify_eq/=.
    iIntros (??? Hins) "Hrf Hinv". iSatStop.
    tstep_s => ????. subst.
    tstep_i => ??. simplify_map_eq'.
    move: Hins => /deep_to_asm_instrs_cons_inv[??]. simplify_map_eq.
    tstep_i. split!; simplify_map_eq'; [done| |]. { apply: map_list_included_is_Some; [done|compute_done]. }
    tstep_i; simplify_map_eq'. split!.
    iSatStart. iDestruct "Hv" as (??) "Hv". simplify_eq.
    iDestruct "Hinv" as "(?&?&?)". rewrite Z.add_0_r.
    iDestruct (i2a_heap_lookup_shared with "[$] [$] [$]") as "#?"; [done|].
    iApply ("Hcont" with "[] [] [//] [Hp] [%] Hrf"); [by simplify_map_eq|done| | |].
    + iApply ci2a_places_inv_mono_rs; [|done].
      apply map_preserved_insert_r_not_in; [compute_done|].
      by apply map_preserved_insert_r_not_in; [compute_done|].
    + by simplify_map_eq'.
    + iFrame.
      iApply ci2a_regs_inv_mono_insert; [compute_done|].
      by iApply ci2a_regs_inv_mono_insert; [compute_done|].
  - rewrite -!app_assoc.
    iApply sim_regs_included. iIntros (?).
    iApply (read_var_val_correct with "Hp"); [typeclasses eauto with tstep|done|compute_done|].
    iIntros (?? v1' ?) "Hv1 Hp". simplify_eq/=.
    iApply (read_var_val_correct with "Hp"); [typeclasses eauto with tstep|done|compute_done|].
    iIntros (?? v2' ?) "#Hv2 Hp". simplify_eq/=.
    iIntros (??? Hins) "Hrf Hinv". iSatStop.
    tstep_s => ???. subst.
    tstep_i => ??. simplify_map_eq'.
    move: Hins => /deep_to_asm_instrs_cons_inv[??]. simplify_map_eq.
    tstep_i. split!; simplify_map_eq'; [done..|].
    tstep_i; simplify_map_eq'. split!.
    iSatStartBupd. iDestruct "Hv1" as (??) "Hv1". simplify_eq.
    iDestruct "Hinv" as "(?&?&?)". rewrite Z.add_0_r.
    iMod (i2a_heap_update_shared with "[$] [$] [$] [$]") as "[??]"; [done|]. iModIntro.
    iApply ("Hcont" with "[] [] [//] [Hp] [%] Hrf"); [by simplify_map_eq|done| | |].
    + iApply ci2a_places_inv_mono_rs; [|done].
      apply map_preserved_insert_r_not_in; [compute_done|].
      by apply map_preserved_insert_l_not_in; [compute_done|].
    + by simplify_map_eq'.
    + iFrame.
      iApply ci2a_regs_inv_mono_insert; [compute_done|].
      iApply ci2a_regs_inv_mono_insert_l; [..|done]; [compute_done|].
      by repeat apply map_list_included_insert.
  - rewrite -!app_assoc.
    iApply (translate_args_correct [] with "Hp"); [done|].
    iIntros (????) "Hvs Hp" => /=. subst.
    iApply (Hcall with "Hvs Hp"); [done|].
    iIntros (?????). by iApply "Hcont".
  - iIntros (????) "??". iSatStop. by tstep_s.
Qed.

Lemma translate_lexpr_correct s s' p p' n e e' rs vs res K h
      `{!ImpExprFill e' K (subst_map vs (lexpr_to_expr e))}:
  crun s (translate_lexpr e) = CResult s' p (CSuccess res) →
  call_correct n s K →
  ci2a_places_inv s.(s_places) s.(s_saved_registers) vs rs -∗
  (∀ rs' vs' av v h',
      ⌜rs' !! "R0" = Some av⌝ -∗
      ⌜s' = s⌝ -∗
      i2a_val_rel v av -∗
      ci2a_places_inv s.(s_places) s.(s_saved_registers) vs' rs' -∗
      sim n true p' (expr_fill K (Val v)) s' rs' h' h') -∗
  sim n true (p ++ p') e' s rs h h.
Proof.
  destruct ImpExprFill0; subst.
  iIntros (Hrun ?) "Hp Hcont".
  iInduction e as [] "IH" forall (vs s' p p' rs h Hrun); simplify_crun_eq; rewrite -?app_assoc.
  - iApply (translate_lexpr_op_correct with "Hp"); [typeclasses eauto with tstep|done..|eauto using suffix_app_r|].
    iIntros (??????) "Hv Hp" => /=. subst.
    iIntros (????) "Hrf Hs". iSatStop. tstep_s. iSatStart. iRevert "Hrf Hs". iApply (to_sim with "[-]"); [|done].
    iApply (write_var_correct with "Hp Hv"); [done..|].
    iIntros (???) "Hp". subst.
    rewrite -subst_subst_map_delete.
    by iApply ("IH" with "[//] Hp").
  - iApply (translate_lexpr_op_correct with "Hp"); [typeclasses eauto with tstep|done..|eauto using suffix_app_r|].
    iIntros (??????) "Hv Hp" => /=. repeat (destruct_all?; simplify_crun_eq).
    rewrite -?app_assoc.

    destruct_all unit.
    iIntros (??? Hins) "Hrf Hinv". iSatStop.
    tstep_s => b ?. subst.
    tstep_i => ??. simplify_map_eq'.
    move: Hins => /deep_to_asm_instrs_cons_inv[??]. simplify_map_eq.
    tstep_i. split!. simplify_map_eq'.
    iSatStart. iDestruct "Hv" as %?. subst.
    destruct b; simplify_eq/=.
    + iApply (to_sim with "[Hcont Hp] [] Hrf"). 2: { by simplify_map_eq'. }
      2: { iDestruct "Hinv" as "($&$&?)". iApply ci2a_regs_inv_mono_insert; [compute_done|done]. }
      iApply ("IH" with "[//] [Hp]"). {
         iApply ci2a_places_inv_mono_rs; [|done].
         apply map_preserved_insert_r_not_in; [compute_done|done].
      }
      iIntros (???????) "Hv Hp". subst.
      iIntros (??? Hins) "Hrf Hinv". iSatStop.
      tstep_i => ??. simplify_map_eq'.
      move: Hins => /deep_to_asm_instrs_cons_inv[??]. simplify_map_eq.
      tstep_i. split!. simplify_map_eq'.
      iSatStart.
      iApply (to_sim with "[Hcont Hp Hv] [%] Hrf"). 2: {
        simplify_map_eq'. etrans; [|done].
        rewrite deep_to_asm_instrs_app Z.add_assoc.
        apply: map_union_subseteq_r. apply lookup_map_seqZ_disjoint. rewrite fmap_length. lia. }
      2: { iDestruct "Hinv" as "($&$&?)". iApply ci2a_regs_inv_mono_insert; [compute_done|done]. }

      iApply ("Hcont" with "[%] [//] [$]"); [by simplify_map_eq|].
      iApply ci2a_places_inv_mono_rs; [|done].
      apply map_preserved_insert_r_not_in; [compute_done|done].
    + iApply (to_sim with "[Hcont Hp] [%] Hrf"). 2: {
        simplify_map_eq'. etrans; [|done].
        rewrite deep_to_asm_instrs_app.
        apply: map_union_subseteq_r'. { apply lookup_map_seqZ_disjoint. rewrite fmap_length. lia. }
        rewrite deep_to_asm_instrs_cons.
        etrans; [|apply insert_subseteq; apply lookup_map_seqZ_None; lia].
        f_equiv; [lia|done].
      }
      2: { iDestruct "Hinv" as "($&$&?)". iApply ci2a_regs_inv_mono_insert; [compute_done|done]. }
      iApply ("IH1" with "[//] [Hp]"). {
         iApply ci2a_places_inv_mono_rs; [|done].
         apply map_preserved_insert_r_not_in; [compute_done|done].
      }
      iIntros (???????) "Hv Hp". subst.
      iApply ("Hcont" with "[//] [//] [$] Hp").
  - iApply (translate_lexpr_op_correct with "Hp"); [typeclasses eauto with tstep|done..|eauto using suffix_app_r|].
    iIntros (??????) "? ?" => /=. iApply ("Hcont" with "[//] [//] [$] [$]").
Qed.

Lemma restore_callee_save_registers_correct s s' p p' r n e rs h:
  crun s restore_callee_save_registers = CResult s' p (CSuccess r) →
  s.(s_saved_registers).*1 ⊆ "R30"::variable_registers →
  ([∗ list] r ∈ s.(s_saved_registers), ∃ v : Z, ⌜pf_rsold !! r.1 = Some v⌝ ∗ stack_slot r.2 v) -∗
  (∀ rs',
     ⌜s' = s⌝ -∗
     ⌜map_scramble ("PC"::s.(s_saved_registers).*1) rs rs'⌝ -∗
     ⌜Forall (λ r, rs' !! r.1 = Some (pf_rsold !!! r.1)) s.(s_saved_registers)⌝ -∗
     ([∗ list] r ∈ s.(s_saved_registers), ∃ v : Z, stack_slot r.2 v) -∗
     sim n true p' e s' rs' h h) -∗
  sim n true (p ++ p') e s rs h h.
Proof.
  unfold restore_callee_save_registers.
  move: 0%nat => n'.
  iIntros (? Hsub ) "Hsr Hcont". simplify_crun_eq.
  rewrite -!app_assoc/=.
  rename select (crun _ _ = _) into Hrun.
  match type of Hrun with | _ = CResult _ ?x (CSuccess ?r') => rename x into p; rename r' into res end.
  iInduction (s_saved_registers s) as [|[r ?] ?] "IH" forall (rs p res n' Hrun); simplify_crun_eq. 1: by iApply "Hcont".
  rewrite -!app_assoc/=.
  iDestruct "Hsr" as "[[% [% Hs]] Hsr]".
  iApply (read_stack_correct with "Hs"); [done| |]. { set_unfold; naive_solver. }
  iIntros (?) "Hs". simplify_eq.
  iApply ("IH" with "[%] [//] Hsr"); [set_solver|].
  iIntros (?? Hrs Hall) "?".
  iApply "Hcont"; try iPureIntro.
  - done.
  - etrans. 2: { apply: map_scramble_mono; [done|]. set_solver. }
    apply map_scramble_insert_r_in; [set_solver|].
    apply map_scramble_insert_r_in; [set_solver|]. done.
  - econs; [|done] => /=.
    destruct (decide (r ∈ l.*1)) as [[?[??]]%elem_of_list_fmap|].
    + move: Hall => /Forall_forall. naive_solver.
    + simplify_map_eq'. etrans; [symmetry; apply: Hrs; set_solver|].
      rewrite lookup_insert_ne; [| set_solver]. by simplify_map_eq.
  - iFrame. iExists _. iFrame.
Qed.

End proof.

Lemma sim_intro s dins rs mem ins ins_dom fns_dom f2i n b e h fns cs lr rf P:
  let H := Build_ProofFixedValues (rs !!! "SP") ins fns cs rs f2i in
  deep_to_asm_instrs (rs !!! "PC") dins = ins →
  ins_dom = dom _ ins →
  fns_dom = dom _ fns →
  f2i = s.(s_f2i) →
  satisfiable (rf ∗ ci2a_inv s lr rs mem h ∗ P) →
  (P -∗ sim n b dins e s rs h h) →
  AsmState (Some []) rs mem ins
     ⪯{asm_module, imp_to_asm ins_dom fns_dom f2i imp_module, n, b}
  (SMProg, Imp e h fns, (PPInside, I2A cs lr, rf))
.
Proof.
  move => ?????? Hcont. subst.
  iSatStart. iIntros "(Hrf&Hinv&HP)".
  iApply (Hcont with "[$] [//] Hrf Hinv").
Qed.

Lemma pass_correct a f2i f s' dins ins fn:
  crun (initial_state f2i) (pass fn.(lfd_args) fn.(lfd_vars) fn.(lfd_body)) = CResult s' dins (CSuccess tt) →
  ins = deep_to_asm_instrs a dins →
  f2i !! f = Some a →
  NoDup (fn.(lfd_args) ++ fn.(lfd_vars).*1) →
  (∀ f' i', f2i !! f' = Some i' → ins !! i' = None ↔ f' ≠ f) →
  trefines (MS asm_module (initial_asm_state ins))
           (MS (imp_to_asm (dom _ ins) {[f]} f2i imp_module) (initial_imp_to_asm_state imp_module
             (initial_imp_lstate (<[f := fn]> ∅)))).
Proof.
  move => Hrun ? Ha /NoDup_app[?[??]] Hf2i.
  apply imp_to_asm_proof; [done|set_solver|].
  move => n i rs mem K f' fn' vs h cs pc ret rf rc lr Hpc Hins Hf ? Hsat Hargs Hlen Hlr Hcall Hret.
  move: Hf. rewrite {1}fmap_insert {1}fmap_empty lookup_insert_Some lookup_empty => ?.
  destruct_all?; simplify_map_eq. move: Hargs => [??].

  apply: (sim_intro (initial_state f2i)).
  1: by simplify_map_eq'. 1: done. 1: set_solver. 1: done. {
    iSatMono. iIntros "(Hmem&Hheap&Hvals&?&?)". iFrame => /=. rewrite Z.sub_0_r. iFrame.
    iSplitR. 2: iAccu.
    iPureIntro => /=. rewrite lookup_lookup_total; [done|].
    apply: (map_list_included_is_Some touched_registers); [done|compute_done].
  }
  iSatClear.
  iIntros "(Hvals&Hrc)".
  unfold pass in Hrun. simplify_crun_eq.
  rename x3 into s.

  iApply save_r30_correct; [done..|]. iIntros (???) "Hp". simplify_eq/=.
  iApply (allocate_places_correct with "[Hp]").
  { done. } { done. } { set_solver. } { naive_solver. } { apply NoDup_remove_dups. }
  { set_solver. } { done. } { done. }
  iIntros (????? Hsc) "Hpl". simplify_eq/=. rewrite map_scramble_insert_l_in in Hsc; [|compute_done].

  iApply (initialize_args_correct with "[Hvals] Hpl").
  { done. } { done. } { done. } {
    iApply (i2a_args_mono with "Hvals").
    apply: map_scramble_preserved; [done|set_solver-].
  }
  iIntros (???) "Hpl". simplify_eq.

  iApply (initialize_locals_correct with "Hpl"); [done..|].
  iIntros (? ls las ???? Hsple) "Hlas Hpl". simplify_eq/=.

  iApply (move_sp_correct); [done|].
  iIntros (???). simplify_eq.
  rewrite subst_l_subst_map ?fmap_length // subst_l_subst_map // -subst_map_subst_map right_id_L.
  rewrite map_union_comm. 2: {
    apply map_disjoint_list_to_map_l, Forall_forall => -[??]. move => /(elem_of_zip_l _ _ _)?/=.
    apply not_elem_of_list_to_map. move => /elem_of_list_fmap[[??][?/(elem_of_zip_l _ _ _) ?]]. naive_solver.
  }
  iApply (translate_lexpr_correct with "[Hpl]"); [typeclasses eauto with tstep|done| | |]. {
    clear Hins.
    iIntros (?????????) "Hvs Hp Hcont".
    iIntros (??? Hins) "Hrf (Hmem&Hh&(%Hsp1&%Hsp2&%&%&%))".
    iSatStop.
    tstep_i => pc ?. simplify_map_eq.
    move: (Hins) => /deep_to_asm_instrs_subseteq_range?.
    move: Hins => /deep_to_asm_instrs_cons_inv[Hi ?]. simplify_map_eq'.
    tstep_i. split!. { apply: map_list_included_is_Some; [done|compute_done]. }
    tstep_i; simplify_map_eq'. split!.
    rewrite dom_fmap_L dom_insert_L dom_empty_L right_id_L (cons_middle (FreeACtx _)) (app_assoc K') expr_fill_app.
    eapply Hcall.
    - apply Forall2_fmap_l. apply: Forall_Forall2_diag. by apply Forall_true.
    - by simplify_map_eq.
    - rewrite Hf2i; [|done]. rewrite lookup_fmap fmap_None lookup_insert_None. naive_solver.
    - done.
    - iSatMono. simplify_map_eq'. iFrame. iSplitL "Hvs"; [|iAccu].
      iApply (i2a_args_mono with "Hvs").
      apply map_preserved_insert_r_not_in; [compute_done|].
      apply map_preserved_insert_r_not_in; [compute_done|done].
    - unfold i2a_regs_call. simplify_map_eq'. split; [done|].
      by repeat apply map_list_included_insert.
    - apply deep_to_asm_instrs_is_Some.
      match goal with | |- context [length ?l] => destruct (decide (pc = a + length l - 1)); [|lia] end.
      subst. exfalso. move: Hi. clear. rewrite lookup_map_seqZ. case_option_guard => //.
      rewrite list_lookup_fmap. rewrite !lookup_app_r ?app_length /=; [|lia..].
      move => /fmap_Some[?[]]. rewrite lookup_cons_Some. naive_solver lia.
    - apply map_scramble_insert_r_in; [compute_done|].
      apply map_scramble_insert_r_in; [compute_done|done].
    - iSatClear. move => ????????? [?[? Hpre]] ?. rewrite -expr_fill_app. subst.
      assert ({[f']} = dom (gset string) (lfndef_to_fndef <$> (<[f':=fn]> ∅ : gmap _ _))) as ->.
      { by rewrite dom_fmap_L dom_insert_L dom_empty_L right_id_L. }
      rewrite map_preserved_insert_l_not_in in Hpre; [|compute_done].
      rewrite map_preserved_insert_l_not_in in Hpre; [|compute_done].
      rewrite -(app_assoc K') /=.
      iSatStart.
      iIntros "(Hmem&Hh&Hv&Hrf&Hp&Hcont)".
      iApply ("Hcont" with "[%] Hv [Hp] [%] Hrf").
      + apply lookup_lookup_total. apply: map_list_included_is_Some; [done|compute_done].
      + iApply ci2a_places_inv_mono_rs; [|done].
        apply: map_preserved_mono; [by etrans;[|done]|].
        set_solver-.
      + by simplify_map_eq'.
      + iFrame => /=. iSplitL.
        * erewrite lookup_total_correct; [done|].
          rewrite -Hsp2. symmetry. apply: Hpre. compute_done.
        * iPureIntro. split_and! => /=; [done| |done..].
          rewrite -Hsp2. symmetry. apply: Hpre. compute_done.
  }
  { iApply ci2a_places_inv_mono_rs; [|done].
    apply map_preserved_insert_r_not_in; [compute_done|].
    apply map_preserved_insert_r_not_in; [compute_done|done]. }
  iIntros (???????) "Hv Hp". simplify_eq.
  iApply move_sp_correct; [done|].
  iIntros (???). simplify_eq/=.
  iDestruct "Hp" as "(Hpl&Hsr&%Hsub&%Hall&_)".
  iApply (restore_callee_save_registers_correct with "[Hsr]"); [done..|] => /=.
  iIntros (?? Hrs2 Hallsr) "Hsr".

  clear Hins.
  iIntros (??? Hins) "? (Hmem&Hh&(%Hsp1&%Hsp2&%&%&%))".
  iSatStop.
  tstep_s => ? Hfree.
  iSatStartBupd.
  iMod (i2a_heap_free_list_shared with "Hh [Hlas]") as "[Hlas Hh]"; [done|..];
    rewrite ?fst_zip ?snd_zip ?fmap_length //; try lia.
  iModIntro.

  iSatStop.
  tstep_i => ??. simplify_map_eq.
  move: Hins => /deep_to_asm_instrs_cons_inv[??]. simplify_map_eq'.
  tstep_i. split!.
  rewrite dom_fmap_L dom_insert_L dom_empty_L right_id_L.
  eapply Hret.
  - simplify_map_eq'. f_equal. eapply lookup_total_correct.
    move: Hallsr => /Forall_forall/(_ ("R30", slot)) ->. 2: set_unfold; naive_solver.
    by simplify_map_eq'.
  - iSatMonoBupd. simplify_map_eq'. iFrame.
    iApply (i2a_mem_delete_big (mjoin (zip_with (λ a n, seqZ a n) las (lfd_vars fn).*2)
                               ++ ((λ slot, rs !!! "SP" - Z.of_N slot - 1) <$>
                               ((s_saved_registers s).*2 ++ s_stack_places s.(s_places))))
             with "Hmem").
    + lia.
    + apply Forall_app. split.
      * apply Forall_forall => ? /elem_of_list_join[?[Hin/(elem_of_lookup_zip_with _ _ _ _)[?[?[?[?[??]]]]]]].
        subst. move: Hin => /elem_of_seqZ?.
        have := Forall2_lookup_lr _ _ _ _ _ _ Hsple ltac:(done) ltac:(done). lia.
      * apply Forall_forall => ? /elem_of_list_fmap[?[??]]. subst. lia.
    + rewrite app_length fmap_length app_length fmap_length.
      have ->: length (mjoin (zip_with (λ a n, seqZ a n) las (lfd_vars fn).*2)) =
               sum_list_with Z.to_nat (lfd_vars fn).*2;[ |lia].
      rewrite mjoin_length (sum_list_with_sum_list (Z.to_nat)). f_equal.
      apply list_eq => {}i. apply option_eq => ?.
      rewrite 2!list_lookup_fmap !fmap_Some.
      setoid_rewrite lookup_zip_with_Some.
      split => ?; destruct_all?; simplify_eq.
      * split!. by rewrite seqZ_length.
      * efeed pose proof @Forall2_lookup_r; [done..|]. destruct_all?.
        split!. by rewrite seqZ_length.
    + iFrame. rewrite big_sepL_fmap big_sepL_app big_sepL_fmap big_sepL_omap big_opM_map_to_list.
      iSplitL "Hsr".
      * iApply (big_sepL_impl with "[$]"). iIntros "!>" (???) "[% ?]". iExists _. iFrame.
      * iApply (big_sepL_impl with "[$]"). iIntros "!>" (?[? pl] ?) "[% [??]]" => /=.
        destruct pl => //=. iExists _. iFrame.
  - unfold i2a_regs_ret. simplify_map_eq'. split!.
    + apply lookup_total_correct. etrans; [symmetry; apply: Hrs2; set_unfold; naive_solver |].
      by simplify_map_eq.
    + apply map_list_included_insert. apply: map_list_included_mono; [done|]. compute_done.
    + apply map_preserved_insert_r_not_in; [compute_done|].
      have ->: saved_registers = variable_registers ++ ["SP"] by compute_done.
      apply map_preserved_app. split. 2: { move => ?. set_unfold => ?. naive_solver congruence. }
      move => r Hr.
      destruct (decide (r ∈ (s_saved_registers s).*1)) as [[?[? Hin]]%elem_of_list_fmap|?].
      * subst. move: Hallsr Hin => /Forall_forall/[apply]->.
        apply lookup_lookup_total. apply: map_list_included_is_Some; [done|].
        apply: list_elem_of_weaken; [done|]. clear. set_solver.
      * move: Hall (Hr) => /Forall_forall/[apply] -[//| ->].
        etrans; [|apply: Hrs2; set_unfold; naive_solver].
        rewrite !lookup_insert_ne //; set_unfold; naive_solver.
  - by apply map_scramble_insert_r_in; [compute_done|].
Qed.

Definition pass_fn (f2i : gmap string Z) (fn : lfndef) : compiler_success error (list deep_asm_instr) :=
  let res := crun (initial_state f2i) (pass fn.(lfd_args) fn.(lfd_vars) fn.(lfd_body)) in
  (λ _, res.(c_prog)) <$> res.(c_result).

Lemma pass_fn_correct a f2i f dins ins fn:
  pass_fn f2i fn = CSuccess dins →
  ins = deep_to_asm_instrs a dins →
  f2i !! f = Some a →
  NoDup (fn.(lfd_args) ++ fn.(lfd_vars).*1) →
  (∀ f' i', f2i !! f' = Some i' → ins !! i' = None ↔ f' ≠ f) →
  trefines (MS asm_module (initial_asm_state ins))
           (MS (imp_to_asm (dom _ ins) {[f]} f2i imp_module) (initial_imp_to_asm_state imp_module
             (initial_imp_lstate (<[f := fn]> ∅)))).
Proof.
  unfold pass_fn.
  destruct (crun (initial_state f2i) (pass (lfd_args fn) (lfd_vars fn) (lfd_body fn))) eqn: Hres => /=.
  move => /(compiler_success_fmap_success _ _ _ _ _ _)[[][??]]. simplify_eq.
  by apply: pass_correct.
Qed.

End ci2a_codegen.
