Require Export iris.algebra.lib.gmap_view.
Require Export refframe.module.
Require Export refframe.compiler.
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

Lemma list_elem_of_weaken {A} (xs ys : list A) x:
  x ∈ xs → xs ⊆ ys → x ∈ ys.
Proof. set_solver. Qed.

Lemma list_subseteq_cons_l {A} x (xs ys : list A):
  x ∈ ys → xs ⊆ ys → x :: xs ⊆ ys.
Proof. set_solver. Qed.

Transparent map_preserved.
Lemma map_preserved_app {K A} `{Countable K} ns1 ns2 (m m' : gmap K A) :
  map_preserved (ns1 ++ ns2) m m' ↔ map_preserved ns1 m' m ∧ map_preserved ns2 m' m.
Proof. unfold map_preserved. set_solver. Qed.
Opaque map_preserved.

Lemma deep_to_asm_instrs_nil pc :
  deep_to_asm_instrs pc [] = ∅.
Proof. done. Qed.
Lemma deep_to_asm_instrs_cons pc di dins :
  deep_to_asm_instrs pc (di :: dins) = <[pc := deep_to_asm_instr di]> $ deep_to_asm_instrs (pc + 1) dins.
Proof. done. Qed.

Lemma deep_to_asm_instrs_cons_inv pc di dins ins :
  deep_to_asm_instrs pc (di :: dins) ⊆ ins →
  ins !! pc = Some (deep_to_asm_instr di) ∧ deep_to_asm_instrs (pc + 1) dins ⊆ ins.
Proof.
  rewrite deep_to_asm_instrs_cons => Hsub.
  split.
  - eapply lookup_weaken; [|done]. apply lookup_insert.
  - etrans; [|done]. apply insert_subseteq. apply lookup_map_seqZ_None. lia.
Qed.

Inductive i2a_error :=
| UnsupportedExpr (e : expr)
| UnknownOperand (e : expr)
| UnknownFunction (f : string)
| UnboundVariable (v : string)
| LocInCode
| NotImplemented (s : string)
| AssertionFailed (s : string)
| TooManyArgs
.

Fixpoint imp_let_names (e : expr) : list string :=
  match e with
  | Var v => []
  | Val v => []
  | BinOp e1 o e2 => imp_let_names e1 ++ imp_let_names e2
  | Load e => imp_let_names e
  | Store e1 e2 => imp_let_names e1 ++ imp_let_names e2
  | Alloc e => imp_let_names e
  | Free e => imp_let_names e
  | If e e1 e2 => imp_let_names e ++ imp_let_names e1 ++ imp_let_names e2
  | LetE v e1 e2 => [v] ++ imp_let_names e1 ++ imp_let_names e2
  | Call f args => mjoin (imp_let_names <$> args)
  | UbE => []
  | ReturnExt can_return_further e => imp_let_names e
  | Waiting can_return => []
  end.

Module ci2a_codegen.

Definition variable_registers : list string :=
  ["R19"; "R20"; "R21"; "R22"; "R23"; "R24"; "R25"; "R26"; "R27"; "R28"; "R29"].

Inductive place :=
| PReg (r : string) | PStack (slot : N).

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

Definition M := compiler_monad state (list_compiler_monoid deep_asm_instr) i2a_error.

Definition alloc_stack : M N :=
  s ← cget;
  cassert (AssertionFailed "alloc_stack: s_sp_above is not true") (s.(s_sp_above) = true);;
  cput (s <| s_stacksize := (s.(s_stacksize) + 1)%N |>);;
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
  slot ← alloc_stack;
  write_stack "R30" slot;;
  s ← cget;
  cput (s <| s_saved_registers := ("R30", slot) :: s.(s_saved_registers)|> );;
  mret tt.

Fixpoint allocate_places (ns : list string) (regs : list string) : M unit :=
  match ns with
  | [] => mret tt
  | n::ns => match regs with
           | [] =>
               slot ← alloc_stack;
               s ← cget;
               cput (s <|s_places := (<[n := PStack slot]> $ s.(s_places))|> );;
               allocate_places ns regs
           | r::regs =>
               (* save callee save register *)
               slot ← alloc_stack;
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

Definition restore_callee_save_registers : M unit :=
  s ← cget;
  cmap s.(s_saved_registers) 0 (λ _ '(r, slot), read_stack r slot);;
  mret tt.

Definition translate_val (v : val) : option Z :=
  match v with
  | ValNum z => Some z
  | ValBool b => Some (bool_to_Z b)
  | ValLoc l => None (* should never occur since code does not contain source locations *)
  end.

Definition read_operand (r : string) (e : expr) : M unit :=
  match e with
  | Val v =>
      z ← cassert_opt LocInCode (translate_val v);
      cappend [Amov r (ImmediateOp z)]
  | Var v => read_var r v
  | _ => cerror (UnknownOperand e)
  end.

Definition translate_expr_op (e : expr) : M unit :=
  match e with
  | Val v => read_operand "R0" (Val v)
  | Var v => read_operand "R0" (Var v)
  | BinOp v1 op v2 =>
      read_operand "R1" v1;;
      read_operand "R2" v2;;
      match op with
      | AddOp | ShiftOp => cappend [Aadd "R0" "R1" (RegisterOp "R2")]
      | EqOp => cappend [Aseq "R0" "R1" (RegisterOp "R2")]
      | LeOp => cappend [Asle "R0" "R1" (RegisterOp "R2")]
      | LtOp => cappend [Aslt "R0" "R1" (RegisterOp "R2")]
      end
  | Load v1 =>
      read_operand "R1" v1;;
      cappend [Aload "R0" "R1" 0]
  | Store v1 v2 =>
      read_operand "R1" v1;;
      read_operand "R0" v2;;
      cappend [Astore "R0" "R1" 0]
  | Call f vs =>
      s ← cget;
      a ← cassert_opt (UnknownFunction f) (s.(s_f2i) !! f);
      cmap vs 0 (λ n a,
        r ← cassert_opt TooManyArgs (args_registers !! n);
        read_operand r a);;
      cappend [Abranch_link true (ImmediateOp a)]
  | _ => cerror (UnsupportedExpr e)
  end.

Fixpoint translate_expr (e : expr) : M unit :=
  match e with
  | LetE v e1 e =>
      translate_expr_op e1;;
      write_var "R0" v;;
      translate_expr e
  (* We cannot handle [LetE v (If v1 e2 e3) e] because e2 and e3 could
  contain let bindings whose effect we would need to undo before
  executing e. Instead we rewrite LetE v (If v1 e2 e3) e to If v1
  (LetE v e2 e) (LetE v e3 e). *)
  | If e1 e2 e3 =>
      translate_expr_op e1;;
      '(_, a2) ← cscope (translate_expr e2);
      '(_, a3) ← cscope (translate_expr e3);
      (* + 1 for the branch_eq at the start and + 1 for the branch at the end *)
      cappend [Abranch_eq false (ImmediateOp (2 + length a2)) "R0" (ImmediateOp 0)];;
      cappend a2;;
      cappend [Abranch false (ImmediateOp (1 + length a3))];;
      cappend a3
  | _ => translate_expr_op e
  end.

Definition pass (fn : fndef) : M unit :=
  let ns := remove_dups (fn.(fd_args) ++ imp_let_names fn.(fd_body)) in
  save_r30;;
  allocate_places ns variable_registers;;
  initialize_args fn.(fd_args);;
  move_sp false;;
  translate_expr fn.(fd_body);;
  move_sp true;;
  restore_callee_save_registers;;
  cappend [Aret].

Definition test_fn : fndef := {|
  fd_args := ["a"; "b"];
  fd_body := LetE "r" (BinOp (Var "a") AddOp (Var "b")) $
             BinOp (Var "a") AddOp (Var "r");
  fd_static := I
|}.

Compute let x := crun (initial_state ∅) (pass test_fn) in (x.(c_prog), x.(c_result)).

Definition test2_fn : fndef := {|
  fd_args := ["a"; "b"];
  fd_body := If (Var "a")
                (If (Var "b") (Val 1) (Val 2))
                (If (Var "b") (Val 3) (Val 4));
  fd_static := I
|}.

Compute let x := crun (initial_state ∅) (pass test2_fn) in (x.(c_prog), x.(c_result)).

Definition test3_fn : fndef := {|
  fd_args := ["a"; "b"];
  fd_body := LetE "r" (Call "test3" [Var "a"; Val 1]) $
             Var "r";
  fd_static := I
|}.

Compute let x := crun (initial_state (<["test3" := 100]> $ ∅)) (pass test3_fn) in (x.(c_prog), x.(c_result)).

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

(** general invariants *)
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

(** lemmas for general invariants *)
Lemma stack_slot_lookup slot v mem sp:
  stack_slot slot v -∗
  i2a_mem_inv sp mem -∗
  ⌜mem !!! (pf_sp - Z.of_N slot - 1) = v⌝.
Proof. iIntros "? ?". iApply (i2a_mem_lookup with "[$] [$]"). Qed.

Lemma stack_slot_update v' slot v mem sp:
  stack_slot slot v -∗
  i2a_mem_inv sp mem ==∗
  stack_slot slot v' ∗ i2a_mem_inv sp (<[pf_sp - Z.of_N slot - 1:=v']>mem).
Proof. iIntros "? ?". iMod (i2a_mem_update with "[$] [$]") as "[$ $]". by iModIntro. Qed.

Lemma stack_slot_alloc mem ss:
  i2a_mem_inv (pf_sp - Z.of_N ss) mem ==∗
  ∃ v, stack_slot ss v ∗ i2a_mem_inv (pf_sp - Z.of_N (ss + 1)) mem.
Proof.
  iIntros "?".
  iMod (i2a_mem_alloc with "[$]") as "[??]". iModIntro.
  iExists _. iFrame.
  by have -> : (pf_sp - Z.of_N ss - 1) = (pf_sp - Z.of_N (ss + 1)) by lia.
Qed.

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

(** ci2a_places_inv *)
Definition ci2a_places_inv (ps : gmap string place) (sr : list (string*N)) (vs : gmap string val) (rs : gmap string Z)
  : uPred imp_to_asmUR :=
  ([∗ map] n↦p∈ps, ∃ av,
     (if vs !! n is Some v then imp_val_to_asm_val v av else True) ∗
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

(** sim *)
Definition sim (n : trace_index) (b : bool) (dins : list deep_asm_instr) (e : expr)
           (s : state) (rs : gmap string Z) : uPred imp_to_asmUR :=
  ∀ mem lr h rf,
  ⌜deep_to_asm_instrs (rs !!! "PC") dins ⊆ pf_ins⌝ -∗
  rf -∗
  ci2a_inv s lr rs mem h -∗
  iSat_end (AsmState (Some []) rs mem pf_ins
             ⪯{asm_module, imp_to_asm (dom _ pf_ins) (dom _ pf_fns) s.(s_f2i) imp_module, n, b}
           (SMProg, Imp e h pf_fns, (PPInside, I2A pf_cs lr, rf))).

Lemma to_sim n b dins e s rs :
  sim n b dins e s rs -∗ sim n b dins e s rs.
Proof. done. Qed.

Lemma sim_mono_s n b dins e s s' rs:
  (∀ lr mem h,
      ci2a_inv s lr rs mem h -∗
      ⌜s'.(s_f2i) = s.(s_f2i)⌝ ∗ ci2a_inv s' lr rs mem h ∗ sim n b dins e s' rs) -∗
  sim n b dins e s rs.
Proof.
  iIntros "Hcont" (?????) "Hrf ?".
  iDestruct ("Hcont" with "[$]") as (<-) "[? Hcont]".
  iApply ("Hcont" with "[//] Hrf [$]").
Qed.

Lemma sim_mono_b n b dins e s rs:
  sim n b dins e s rs -∗
  sim n true dins e s rs.
Proof.
  iIntros "Hcont" (?????) "Hrf ?".
  iSatStop. apply: tsim_mono_b. iSatStart.
  by iApply ("Hcont" with "[//] Hrf").
Qed.

Lemma sim_get_sp s p b n rs e:
  (⌜rs !! "SP" = Some (if s.(s_sp_above) then pf_sp else pf_sp - Z.of_N s.(s_stacksize))⌝ -∗ sim n b p e s rs) -∗
  sim n b p e s rs.
Proof.
  iIntros "Hcont" (?????) "Hrf (?&?&(?&%&?))".
  iApply ("Hcont" with "[//] [//] Hrf").
  by iFrame.
Qed.

Lemma sim_regs_included s p b n rs e:
  (⌜map_list_included touched_registers rs⌝ -∗ sim n b p e s rs) -∗
  sim n b p e s rs.
Proof.
  iIntros "Hcont" (?????) "Hrf (?&?&(?&?&%))".
  iApply ("Hcont" with "[] [//] Hrf"); [naive_solver..|].
  by iFrame.
Qed.

Lemma sim_Amov r o n b p' e rs s :
  r ∈ touched_registers ∧ r ≠ "SP" ∧ r ≠ "PC" →
  sim n true p' e s (<["PC" := rs !!! "PC" + 1]> $ <[r := op_lookup rs o]>rs) -∗
  sim n b (Amov r o :: p') e s rs.
Proof.
  iIntros ([?[??]]) "Hcont".
  iApply sim_regs_included. iIntros (?).
  iIntros (???? Hins) "Hrf Hinv". iSatStop.
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

Lemma sim_Var s p b n rs e K v `{!ImpExprFill e K (Var v)}:
  ⊢ sim n b p e s rs.
Proof.
  destruct ImpExprFill0; subst.
  iIntros (?????) "??". iSatStop. by tstep_s.
Qed.

(** rules for operations *)
Lemma move_sp_correct s s' p p' r n b e rs ab:
  crun s (move_sp ab) = CResult s' p (CSuccess r) →
  (∀ pc' sp', ⌜s' = s <|s_sp_above := ab |>⌝ -∗
        sim n true p' e s' (<["PC":=pc']> $ <["SP":=sp']>rs)) -∗
  sim n b (p ++ p') e s rs.
Proof.
  unfold move_sp. move => ?. simplify_crun_eq. iIntros "Hcont".
  iApply sim_get_sp. iIntros (?).
  iIntros (???? Hins) "Hrf (Hmem&Hheap&Hregs)".
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

Lemma alloc_stack_correct s s' p p' r n b e rs:
  crun s alloc_stack = CResult s' p (CSuccess r) →
  (∀ v, ⌜s' = s <|s_stacksize := (s.(s_stacksize) + 1)%N |>⌝ -∗
        ⌜r = s.(s_stacksize)⌝ -∗
        ⌜p = []⌝ -∗
        stack_slot s.(s_stacksize) v -∗
        sim n b p' e s' rs) -∗
  sim n b (p ++ p') e s rs.
Proof.
  unfold alloc_stack. move => ?. simplify_crun_eq.
  iIntros "Hcont" (?????) "Hrf (Hmem&Hheap&Hregs)".
  iSatStop. iSatStartBupd.
  iMod (stack_slot_alloc with "[$]") as (?) "[??]". iModIntro.
  iApply ("Hcont" with "[//] [//] [//] [$] [//] Hrf"). iFrame.
  iDestruct "Hregs" as %(?&?&?&?&?).
  iPureIntro. split!. by case_match.
Qed.

Lemma read_stack_correct s s' p p' r res b n slot rs v e:
  crun s (read_stack r slot) = CResult s' p (CSuccess res) →
  r ∈ touched_registers ∧ r ≠ "SP" ∧ r ≠ "PC" →
  stack_slot slot v -∗
  (⌜s' = s⌝ -∗ stack_slot slot v -∗ sim n true p' e s' (<["PC" := rs !!! "PC" + length p]> $ <[r := v]> rs)) -∗
  sim n b (p ++ p') e s rs.
Proof.
  unfold read_stack, stack_offset.
  iIntros (?[?[??]]) "Hs Hcont". simplify_crun_eq.
  iApply sim_get_sp. iIntros (?).
  iApply sim_regs_included. iIntros (?).

  iIntros (???? Hins) "Hrf (Hmem&Hheap&Hregs)". iSatStop.
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

Lemma write_stack_correct s s' p p' r res b n slot rs v v' e:
  crun s (write_stack r slot) = CResult s' p (CSuccess res) →
  rs !! r = Some v' →
  stack_slot slot v -∗
  (⌜s' = s⌝ -∗ stack_slot slot v' -∗ sim n true p' e s' (<["PC" := rs !!! "PC" + length p]> rs)) -∗
  sim n b (p ++ p') e s rs.
Proof.
  unfold write_stack, stack_offset.
  iIntros (??) "Hs Hcont". simplify_crun_eq.
  iApply sim_get_sp. iIntros (?).

  iIntros (???? Hins) "Hrf (Hmem&Hheap&Hregs)". iSatStop.
  tstep_i => ??. simplify_map_eq'.
  move: Hins => /deep_to_asm_instrs_cons_inv[??]. simplify_map_eq.
  rewrite orb_true_r.
  tstep_i. split!.
  tstep_i. split!. simplify_map_eq'.
  iSatStartBupd.
  iMod (stack_slot_update with "[$] [$]") as "[??]". iModIntro.
  iApply ("Hcont" with "[//] [$] [%] Hrf"). { by simplify_map_eq'. }
  have -> : (if s_sp_above s then pf_sp else pf_sp - Z.of_N (s_stacksize s)) +
       ((if s_sp_above s then 0 else Z.of_N (s_stacksize s)) - Z.of_N slot - 1) = pf_sp - Z.of_N slot - 1 by case_match; lia.
  iFrame.
  iApply ci2a_regs_inv_mono_insert; [compute_done|done].
Qed.

Lemma read_var_correct s s' p p' r res b n rs v v' e vs:
  crun s (read_var r v) = CResult s' p (CSuccess res) →
  r ∈ tmp_registers ∧ r ≠ "PC" →
  vs !! v = Some v' →
  ci2a_places_inv s.(s_places) s.(s_saved_registers) vs rs -∗
  (∀ pc' av,
   let rs' := (<["PC":=pc']> $ <[r := av]>rs) in
   ⌜s' = s⌝ -∗
   imp_val_to_asm_val v' av -∗
   ci2a_places_inv s.(s_places) s.(s_saved_registers) vs rs' -∗
   sim n true p' e s' rs') -∗
  sim n b (p ++ p') e s rs.
Proof.
  unfold read_var.
  iIntros (?[Hin ?]?) "Hp Hcont". simplify_crun_eq.
  have ? : r ∈ touched_registers ∧ r ≠ "SP" ∧ r ≠ "PC". {
    split. 2: split => ?; subst; set_solver.
    apply: (list_elem_of_weaken tmp_registers); [done| ].
    clear. set_unfold. naive_solver.
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

Lemma write_var_correct s s' p p' r res b n rs v av v' e vs:
  crun s (write_var r v) = CResult s' p (CSuccess res) →
  rs !! r = Some av →
  ci2a_places_inv s.(s_places) s.(s_saved_registers) vs rs -∗
  imp_val_to_asm_val v' av -∗
  (∀ rs', ⌜s' = s⌝ -∗
          ⌜map_scramble ("PC"::variable_registers) rs rs'⌝ -∗
          ci2a_places_inv s.(s_places) s.(s_saved_registers) (<[v := v']>vs) rs' -∗
          sim n true p' e s' rs') -∗
  sim n b (p ++ p') e s rs.
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
      apply: (list_elem_of_weaken variable_registers); [done| ].
      clear. set_unfold. naive_solver.
    }
    simplify_map_eq'.
    iApply ("Hcont" with "[//] [%]"). {
      apply map_scramble_insert_r_in; [compute_done|].
      apply map_scramble_insert_r_in; [set_unfold; naive_solver|done].
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

Lemma read_operand_correct e e' s s' p p' n r rs vs res K `{!ImpExprFill e' K (subst_map vs e)}:
  crun s (read_operand r e) = CResult s' p (CSuccess res) →
  r ∈ tmp_registers ∧ r ≠ "PC" →
  ci2a_places_inv s.(s_places) s.(s_saved_registers) vs rs -∗
  (∀ pc' av v,
      let rs' := <["PC" := pc']> $ <[r := av]> rs in
      ⌜s' = s⌝ -∗
      imp_val_to_asm_val v av -∗
      ci2a_places_inv s.(s_places) s.(s_saved_registers) vs rs' -∗
      sim n true p' (expr_fill K (Val v)) s' rs') -∗
  sim n true (p ++ p') e' s rs.
Proof.
  destruct ImpExprFill0; subst.
  iIntros (??) "Hp Hcont".
  destruct e; simplify_crun_eq.
  - case_match; [|iApply sim_Var; typeclasses eauto with tstep].
    iApply (read_var_correct with "Hp"); [done..|].
    iIntros (???) "?". by iApply "Hcont".
  - iApply sim_Amov. { set_unfold. naive_solver. }
    iApply "Hcont"; [by simplify_map_eq|by destruct v; simplify_eq/=|].
    iApply ci2a_places_inv_mono_rs; [|done].
    apply map_preserved_insert_r_not_in; [compute_done|].
    apply map_preserved_insert_r_not_in; [|done].
    set_unfold. naive_solver.
Qed.
Opaque read_operand.

Lemma save_r30_correct s s' p p' r n b e rs:
  crun s save_r30 = CResult s' p (CSuccess r) →
  s.(s_places) = ∅ →
  s.(s_saved_registers) = [] →
  pf_rsold = rs →
  is_Some (rs !! "R30") →
  (∀ pc' slot,
     let rs' := (<["PC":=pc']>rs) in
     ⌜s' = s <| s_stacksize := (s_stacksize s + 1)%N |> <|s_saved_registers := [("R30", slot)] |>⌝ -∗
     ci2a_places_inv ∅ s'.(s_saved_registers) ∅ rs' -∗
     sim n true p' e s' rs') -∗
  sim n b (p ++ p') e s rs.
Proof.
  unfold save_r30.
  iIntros (? Hp Hs ? [??]) "Hcont". simplify_crun_eq. rewrite -!app_assoc/=.
  iApply alloc_stack_correct; [done|]. iIntros (????) "Hs". simplify_eq/=.
  iApply (write_stack_correct with "[$]"); [done..|]. iIntros (?) "Hs". simplify_eq.
  iApply "Hcont"; [by rewrite Hs|] => /=.
  iApply ci2a_places_inv_mono_rs. { apply map_preserved_insert_r_not_in; [compute_done|]. done. }
  iSplit; [done|]. rewrite Hs. iSplit! => /=.
  - set_solver.
  - apply Forall_true. by right.
Qed.

Lemma allocate_places_correct s ns vars s' p p' r n b e rs:
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
     ci2a_places_inv s'.(s_places) s'.(s_saved_registers) ∅ rs' -∗
     sim n b p' e s' rs') -∗
  sim n b (p ++ p') e s rs.
Proof.
  elim: ns vars s s' p rs b => /=. {
    iIntros (?????????????) "? Hcont". simplify_crun_eq.
    iApply ("Hcont" with "[//] [//] [%] [//] [$]").
    1: by apply map_list_included_nil. }
  iIntros (?? IH [|v vars] ?????? Hsub Hn ? [??]%NoDup_cons ?); iIntros (?) "Hp Hcont"; simplify_crun_eq.
  - rewrite -app_assoc. iApply alloc_stack_correct; [done|]. iIntros (????) "Hs". simplify_eq/=.
    iApply sim_mono_s. iIntros (???) "Hinv".
    iSplitR; [|iSplitL "Hinv"]. 3: iApply (IH with "[Hs Hp]"); [done|done|done|set_solver|done|..] => /=.
    { done. }
    + iDestruct "Hinv" as "(?&?&?)". iFrame.
    + move => ??. apply lookup_insert_None. set_solver.
    + rewrite /= s_stack_places_insert; [|set_solver] => /=. lia.
    + iDestruct "Hp" as "[? [$ [$ [$ %]]]]". iSplit.
      * iApply big_sepM_insert; [set_solver|]. iFrame.
        simplify_map_eq. iExists _. iFrame.
      * iPureIntro. move => ??? /lookup_insert_Some? /lookup_insert_Some?. naive_solver.
    + iIntros (?????). iApply "Hcont"; iPureIntro.
      * etrans; [|done]. apply insert_subseteq. set_solver.
      * set_solver.
      * apply map_list_included_cons; [|done].
        apply: elem_of_weaken; [|by apply subseteq_dom].
        set_solver.
      * done.
  - rewrite -!app_assoc. iApply alloc_stack_correct; [done|]. iIntros (????) "Hs". simplify_eq/=.
    iApply sim_regs_included. iIntros (?).
    move: Hsub => /submseteq_cons_l [?[Hperm Hsub]].
    have [??]: is_Some (rs !! v). {
      apply: map_list_included_is_Some.
      { apply: (map_list_included_mono _ variable_registers); [done|compute_done]. }
      rewrite Hperm. set_solver. }
    iApply (write_stack_correct with "[$]"); [done..|]. iIntros (?) "Hs". simplify_eq.
    iApply sim_mono_s. iIntros (???) "Hinv".
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
        case_match => //. iDestruct "Hp" as %(?&?&?). iPureIntro. csimpl. split!. set_unfold. naive_solver.
      * simpl. iFrame. iExists _. iFrame. iPureIntro.
        move: Hv => /Forall_forall/(_ v)[| |->//]. { rewrite Hperm. set_solver. }  set_unfold. naive_solver.
      * iPureIntro. apply list_subseteq_cons_l; [|done]. rewrite Hperm. set_solver.
      * iPureIntro. apply: Forall_impl; [done|]. set_unfold. naive_solver.
      * iPureIntro. move => ??? /lookup_insert_Some[[??]|[??]] /lookup_insert_Some[[??]|[??]]; set_solver.
    + iIntros (?????) "?". iApply sim_mono_b.
      iApply ("Hcont" with "[%] [%] [%] [//] [$]").
      * etrans; [|done]. apply insert_subseteq. set_solver.
      * set_solver.
      * apply map_list_included_cons; [|done].
        apply: elem_of_weaken; [|by apply subseteq_dom].
        set_solver.
Qed.

Lemma initialize_args_correct s xs s' p p' r n e rs vs vm:
  crun s (initialize_args xs) = CResult s' p (CSuccess r) →
  length xs = length vs →
  NoDup xs →
  ([∗ list] i↦v∈vs, ∃ r av, ⌜args_registers !! (0 + i)%nat = Some r⌝ ∗ ⌜rs !! r = Some av⌝ ∗ imp_val_to_asm_val v av) -∗
  ci2a_places_inv s.(s_places) s.(s_saved_registers) vm rs -∗
  (∀ rs',
     ⌜s' = s⌝ -∗
     ⌜map_scramble ("PC"::variable_registers) rs rs'⌝ -∗
     ci2a_places_inv s'.(s_places) s'.(s_saved_registers) (list_to_map (zip xs vs) ∪ vm) rs' -∗
     sim n true p' e s' rs') -∗
  sim n true (p ++ p') e s rs.
Proof.
  unfold initialize_args.
  elim: xs vs vm s s' p rs 0%nat => /=. {
    move => [|//] ?????????. simplify_crun_eq.
    iIntros "_ Hp Hcont". iApply "Hcont"; [done..|]. by rewrite left_id_L.
  }
  move => ?? IH [//|??] ??????? /=[?] /NoDup_cons[??]. simplify_crun_eq.
  rewrite Nat.add_0_r. iIntros "[[% [% [% [% ?]]]] Hl] Hp Hcont". simplify_eq.
  rewrite -!app_assoc /=.
  iApply (write_var_correct with "[$] [$]"); [done..|].
  iIntros (?? Hrs) "Hp". simplify_eq.
  iApply (IH with "[Hl] Hp"). { apply cbind_success. split!; [done..|]. by rewrite app_nil_r. }
  { done. } { done. }
  { setoid_rewrite Nat.add_succ_l. setoid_rewrite Nat.add_succ_r.
    iApply (big_sepL_impl with "[$]"). iIntros "!>" (???) "[% [% [%Hlookup [% ?]]]]".
    iSplit!; [done| |done].
    etrans; [symmetry; apply: Hrs|done]. move: Hlookup => /(elem_of_list_lookup_2 _ _ _).
    clear. set_unfold. naive_solver.
  }
  iIntros (???) "Hp".
  iApply "Hcont"; [done|iPureIntro;by etrans|].
  rewrite -insert_union_l -insert_union_r; [done|].
  apply not_elem_of_list_to_map_1. rewrite fst_zip //. lia.
Qed.

Lemma translate_expr_op_correct s s' p p' n e rs vs res K:
  crun s (translate_expr_op e) = CResult s' p (CSuccess res) →
  ci2a_places_inv s.(s_places) s.(s_saved_registers) vs rs -∗
  (∀ rs' vs' av v,
      ⌜rs' !! "R0" = Some av⌝ -∗
      ⌜s' = s⌝ -∗
      imp_val_to_asm_val v av -∗
      ci2a_places_inv s.(s_places) s.(s_saved_registers) vs' rs' -∗
      sim n true p' (expr_fill K (Val v)) s' rs') -∗
  sim n true (p ++ p') (expr_fill K (subst_map vs e)) s rs.
Proof.
  iIntros (?) "Hp Hcont".
  destruct e; simplify_crun_eq.
  - iApply (read_operand_correct (Var _) with "Hp"); [typeclasses eauto with tstep|done|compute_done|].
    iIntros (????) "? Hp".
    iApply ("Hcont" with "[] [//] [$] Hp"). by simplify_map_eq.
  - iApply (read_operand_correct (Val _) with "Hp"); [typeclasses eauto with tstep|done|compute_done|].
    iIntros (????) "? Hp".
    iApply ("Hcont" with "[] [//] [$] Hp"). by simplify_map_eq.
  - rewrite -!app_assoc.
    iApply sim_regs_included. iIntros (?).
    iApply (read_operand_correct with "Hp"); [typeclasses eauto with tstep|done|compute_done|].
    iIntros (?? v1 ?) "? Hp". simplify_eq/=.
    iApply (read_operand_correct with "Hp"); [typeclasses eauto with tstep|done|compute_done|].
    iIntros (?? v2 ?) "? Hp". simplify_eq/=.
    iIntros (???? Hins) "Hrf Hinv".
    iSatStop. tstep_s => ??.
    case_match; simplify_crun_eq; destruct v1 as [|b1|], v2 as [|b2|] => //; simplify_eq/=.
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
    iApply (read_operand_correct with "Hp"); [typeclasses eauto with tstep|done|compute_done|].
    iIntros (?? v ?) "? Hp". simplify_eq/=.
    admit.
  - rewrite -!app_assoc.
    iApply (read_operand_correct with "Hp"); [typeclasses eauto with tstep|done|compute_done|].
    iIntros (?? v1 ?) "? Hp". simplify_eq/=.
    iApply (read_operand_correct with "Hp"); [typeclasses eauto with tstep|done|compute_done|].
    iIntros (?? v2 ?) "? Hp". simplify_eq/=.
    admit.
  - rewrite -!app_assoc.
    admit.
Admitted.
Opaque translate_expr_op.

Lemma translate_expr_correct s s' p p' n e rs vs res K:
  crun s (translate_expr e) = CResult s' p (CSuccess res) →
  ci2a_places_inv s.(s_places) s.(s_saved_registers) vs rs -∗
  (∀ rs' vs' av v,
      ⌜rs' !! "R0" = Some av⌝ -∗
      ⌜s' = s⌝ -∗
      imp_val_to_asm_val v av -∗
      ci2a_places_inv s.(s_places) s.(s_saved_registers) vs' rs' -∗
      sim n true p' (expr_fill K (Val v)) s' rs') -∗
  sim n true (p ++ p') (expr_fill K (subst_map vs e)) s rs.
Proof.
  elim: e vs s s' p rs => *; simplify_crun_eq.
Admitted.

Lemma restore_callee_save_registers_correct s s' p p' r n e rs:
  crun s restore_callee_save_registers = CResult s' p (CSuccess r) →
  s.(s_saved_registers).*1 ⊆ "R30"::variable_registers →
  ([∗ list] r ∈ s.(s_saved_registers), ∃ v : Z, ⌜pf_rsold !! r.1 = Some v⌝ ∗ stack_slot r.2 v) -∗
  (∀ rs',
     ⌜s' = s⌝ -∗
     ⌜map_scramble ("PC"::s.(s_saved_registers).*1) rs rs'⌝ -∗
     ⌜Forall (λ r, rs' !! r.1 = Some (pf_rsold !!! r.1)) s.(s_saved_registers)⌝ -∗
     ([∗ list] r ∈ s.(s_saved_registers), ∃ v : Z, stack_slot r.2 v) -∗
     sim n true p' e s' rs') -∗
  sim n true (p ++ p') e s rs.
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
  (P -∗ sim n b dins e s rs) →
  AsmState (Some []) rs mem ins
     ⪯{asm_module, imp_to_asm ins_dom fns_dom f2i imp_module, n, b}
  (SMProg, Imp e h fns, (PPInside, I2A cs lr, rf))
.
Proof.
  move => ?????? Hcont. subst.
  iSatStart. iIntros "(Hrf&Hinv&HP)".
  iApply (Hcont with "[$] [//] Hrf Hinv").
Qed.

Lemma pass_correct a f2i f fn s' dins ins :
  crun (initial_state f2i) (pass fn) = CResult s' dins (CSuccess tt) →
  ins = deep_to_asm_instrs a dins →
  f2i !! f = Some a →
  NoDup (fn.(fd_args)) →
  trefines (MS asm_module (initial_asm_state ins))
           (MS (imp_to_asm (dom _ ins) {[f]} f2i imp_module) (initial_imp_to_asm_state imp_module
             (initial_imp_state (<[f := fn]> ∅)))).
Proof.
  move => Hrun ? Ha ?.
  apply imp_to_asm_proof; [done|set_solver|].
  move => n i rs mem K f' fn' avs vs h cs pc ret rf rc lr Hpc Hins Hf ? Hsat Hargs Hlen Hlr Hcall Hret.
  move: Hf. rewrite lookup_insert_Some lookup_empty => ?. destruct_all?; simplify_map_eq.
  move: Hargs => [?[?[??]]].

  apply: (sim_intro (initial_state f2i)).
  1: by simplify_map_eq'. 1: done. 1: set_solver. 1: done. {
    iSatMono. iIntros "(Hmem&Hheap&Hvals&?&?)". iFrame => /=. rewrite Z.sub_0_r. iFrame.
    iSplitR. 2: iAccu.
    iPureIntro => /=. rewrite /touched_registers map_list_included_app lookup_lookup_total; [done|].
    apply: (map_list_included_is_Some saved_registers); [done|compute_done].
  }
  iSatClear.
  iIntros "(Hvals&Hrc)".
  unfold pass in Hrun. simplify_crun_eq.
  rename x3 into s.

  iApply save_r30_correct; [done..|]. iIntros (???) "Hp". simplify_eq/=.
  iApply (allocate_places_correct with "[Hp]").
  { done. } { done. } { set_solver. } { naive_solver. } { apply NoDup_remove_dups. }
  { set_solver. } { done. } { done. }
  iIntros (?????) "Hpl". simplify_eq/=.
  iApply (initialize_args_correct with "[Hvals] Hpl").
  { done. } { done. } { done. }
  { admit. }
  iIntros (???) "Hpl". simplify_eq.
  iApply (move_sp_correct); [done|].
  iIntros (???). simplify_eq.
  rewrite subst_l_subst_map // right_id_L.
  iApply (translate_expr_correct with "[Hpl]"); [done| |].
  { iApply ci2a_places_inv_mono_rs; [|done].
    apply map_preserved_insert_r_not_in; [compute_done|].
    apply map_preserved_insert_r_not_in; [compute_done|done]. }
  iIntros (??????) "Hv Hp". simplify_eq.
  iApply move_sp_correct; [done|].
  iIntros (???). simplify_eq/=.
  iDestruct "Hp" as "(Hpl&Hsr&%Hsub&%Hall&_)".
  iApply (restore_callee_save_registers_correct with "[Hsr]"); [done..|] => /=.
  iIntros (?? Hrs2 Hallsr) "Hsr".

  clear Hins.
  iIntros (???? Hins) "? (Hmem&Hh&(%Hsp1&%Hsp2&%&%&%))".
  iSatStop.
  tstep_i => ??. simplify_map_eq.
  move: Hins => /deep_to_asm_instrs_cons_inv[??]. simplify_map_eq'.
  tstep_i. split!.
  rewrite dom_insert_L dom_empty_L right_id_L.
  eapply Hret.
  - simplify_map_eq'. f_equal. eapply lookup_total_correct.
    move: Hallsr => /Forall_forall/(_ ("R30", slot)) ->. 2: set_unfold; naive_solver.
    by simplify_map_eq'.
  - iSatMonoBupd. simplify_map_eq'. iFrame.
    iApply (i2a_mem_delete_big
              ((λ slot, rs !!! "SP" - Z.of_N slot - 1) <$> ((s_saved_registers s).*2 ++ s_stack_places s.(s_places)))
             with "Hmem").
    + lia.
    + apply Forall_forall => ? /elem_of_list_fmap[?[??]]. subst. lia.
    + rewrite fmap_length app_length fmap_length. lia.
    +

  - unfold imp_to_asm_ret. simplify_map_eq'. split!.
    + apply lookup_total_correct. etrans; [symmetry; apply: Hrs2; set_unfold; naive_solver |].
      by simplify_map_eq.
    + apply map_list_included_insert. apply: map_list_included_mono; [done|]. compute_done.
    + apply map_preserved_insert_r_not_in; [compute_done|].
      have ->: saved_registers = variable_registers ++ ["SP"] by compute_done.
      apply map_preserved_app. split. 2: { move => ?. set_unfold => ?. naive_solver congruence. }
      move => r Hr.
      destruct (decide (r ∈ (s_saved_registers s).*1)) as [[?[? Hin]]%elem_of_list_fmap|?].
      * move: Hallsr Hin => /Forall_forall/[apply]?. subst. etrans; [done|]. symmetry.
        apply lookup_lookup_total. apply: map_list_included_is_Some; [done|].
        apply: list_elem_of_weaken; [done|]. clear. set_solver.
      * move: Hall (Hr) => /Forall_forall/[apply] -[//| ->].
        symmetry. etrans; [|apply: Hrs2; set_unfold; naive_solver].
        rewrite !lookup_insert_ne //; set_unfold; naive_solver.
  - by apply map_scramble_insert_r_in; [compute_done|].



map_list_included_insert. apply: map_list_included_mono; [done|]. compute_done.

split
    admit.


  tstep_i. split!; simplify_map_eq'; [done|].
  iSatStart.

  (* move: (fd_args fn') => xs. *)
  (* move: (fd_body fn') Hrun => e. *)
  (* move: Hins. move: {1 2}(dins) => dins'. *)
  (* move: Hpc Hlr. *)
  (* move Hrs': (rs) => rs'. *)
  (* have : map_preserved saved_registers rs rs' by subst. clear Hrs'. *)
  (* clear Hinv Hargs. *)
  (* move: (a) => a'. *)
  (* move: a' rs' dins'. *)
  (* induction e => a' dins' ? ? ? ? Hdins' Hrun; simplify_crun_eq. *)

  (* apply cbind_success in Hrun. *)
  (* destruct Hrun as (?&?&?&?&?&?&?). *)
  (* simplify_eq/=. *)
Abort.

End ci2a_codegen.
