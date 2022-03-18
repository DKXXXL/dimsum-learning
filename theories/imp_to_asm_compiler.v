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

Section theorems.
Context `{FinMap K M}.
Lemma insert_subseteq_Some {A} (m1 m2 : M A) i x :
  <[i:=x]> m1 ⊆ m2 → m2 !! i = Some x.
Proof. intros Hsub. eapply lookup_weaken; [|done]. apply lookup_insert. Qed.
End theorems.

Set Default Proof Using "Type".

Lemma deep_to_asm_instrs_nil pc :
  deep_to_asm_instrs pc [] = ∅.
Proof. done. Qed.
Lemma deep_to_asm_instrs_cons pc di dins :
  deep_to_asm_instrs pc (di :: dins) = <[pc := deep_to_asm_instr di]> $ deep_to_asm_instrs (pc + 1) dins.
Proof. done. Qed.

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
| PReg (r : string) | PStack (slot : Z).

Record state := State {
  s_f2i : gmap string Z;
  s_stacksize : Z;
  s_places : gmap string place;
  s_saved_registers : list (string * Z);
  s_sp_above : bool; (* tracks whether sp currently points to above the stack or below *)
}.
Global Instance eta_state : Settable _ := settable! State <s_f2i; s_stacksize; s_places; s_saved_registers; s_sp_above>.
Add Printing Constructor state.

Definition initial_state (f2i : gmap string Z) : state := State f2i 0 ∅ [] true.

Definition M := compiler_monad state (list_compiler_monoid deep_asm_instr) i2a_error.

Definition alloc_stack : M Z :=
  s ← cget;
  cassert (AssertionFailed "alloc_stack: s_sp_above is not true") (s.(s_sp_above) = true);;
  cput (s <| s_stacksize := s.(s_stacksize) + 1 |>);;
  mret s.(s_stacksize).

Definition move_sp (above : bool) : M unit :=
  s ← cget;
  cassert (AssertionFailed "move_sp: already at the right place") (s.(s_sp_above) ≠ above);;
  cappend [Aadd "SP" "SP" (ImmediateOp $ if s.(s_sp_above) then - s.(s_stacksize) else s.(s_stacksize))];;
  cput (s <| s_sp_above := above |>);;
  mret tt.

(* for stack slot [slot] returns offset that one needs to add to SP to
reach the slot *)
Definition stack_offset (slot : Z) : M Z :=
  s ← cget;
  mret ((if s.(s_sp_above) then 0 else s.(s_stacksize)) - slot - 1).

Definition read_stack (r : string) (slot : Z) : M unit :=
  o ← stack_offset slot;
  cappend [Aload r "SP" o];;
  mret tt.

Definition write_stack (r : string) (slot : Z) : M unit :=
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
  s ← cget;
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

Fixpoint translate_expr (e : expr) : M unit :=
  match e with
  | Val v => read_operand "R0" (Val v)
  | Var v => read_operand "R0" (Var v)
  | LetE v (Val v1) e =>
      read_operand "R0" (Val v1);;
      write_var "R0" v;;
      translate_expr e
  | LetE v (Var v1) e =>
      read_operand "R0" (Var v1);;
      write_var "R0" v;;
      translate_expr e
  | LetE v (BinOp v1 op v2) e =>
      read_operand "R0" v1;;
      read_operand "R1" v2;;
      match op with
      | AddOp | ShiftOp => cappend [Aadd "R2" "R0" (RegisterOp "R1")]
      | EqOp => cappend [Aseq "R2" "R0" (RegisterOp "R1")]
      | LeOp => cappend [Asle "R2" "R0" (RegisterOp "R1")]
      | LtOp => cappend [Aslt "R2" "R0" (RegisterOp "R1")]
      end;;
      write_var "R2" v;;
      translate_expr e
  | LetE v (Load v1) e =>
      read_operand "R0" v1;;
      cappend [Aload "R1" "R0" 0];;
      write_var "R1" v;;
      translate_expr e
  | LetE v (Store v1 v2) e =>
      read_operand "R0" v1;;
      read_operand "R1" v2;;
      cappend [Astore "R1" "R0" 0];;
      write_var "R1" v;;
      translate_expr e
  (* We cannot handle [LetE v (If v1 e2 e3) e] because e2 and e3 could
  contain let bindings whose effect we would need to undo before
  executing e. Instead we rewrite LetE v (If v1 e2 e3) e to If v1
  (LetE v e2 e) (LetE v e3 e). *)
  | If v1 e2 e3 =>
      read_operand "R0" v1;;
      '(_, a1) ← cscope (translate_expr e2);
      '(_, a2) ← cscope (translate_expr e3);
      (* + 1 for the branch_eq at the start and + 1 for the branch at the end *)
      cappend [Abranch_eq false (ImmediateOp (2 + length a1)) "R0" (ImmediateOp 0)];;
      cappend a1;;
      cappend [Abranch false (ImmediateOp (1 + length a2))];;
      cappend a2
  | LetE v (Call f vs) e =>
      s ← cget;
      a ← cassert_opt (UnknownFunction f) (s.(s_f2i) !! f);
      cmap vs 0 (λ n a,
        r ← cassert_opt TooManyArgs (args_registers !! n);
        read_operand r a);;
      cappend [Abranch_link true (ImmediateOp a)];;
      write_var "R0" v;;
      translate_expr e
  | _ => cerror (UnsupportedExpr e)
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
             Var "r";
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
}.

Section proof.
Context `{!ProofFixedValues}.

(** general invariants *)
Definition stack_slot (slot : Z) (v : Z) : uPred _ :=
  ⌜0 ≤ slot⌝ ∗ i2a_mem_constant (pf_sp - slot - 1) v.

Definition ci2a_regs_inv (s : state) (lr rs : gmap string Z) : uPred imp_to_asmUR :=
  ⌜pf_rsold !! "SP" = Some pf_sp⌝ ∗
  ⌜rs !! "SP" = Some (if s.(s_sp_above) then pf_sp else pf_sp - s.(s_stacksize))⌝ ∗
  ⌜map_scramble touched_registers lr rs⌝ ∗
  ⌜map_list_included tmp_registers rs⌝ ∗
  ⌜map_list_included saved_registers rs⌝.

Definition ci2a_mem_inv (stacksize : Z) (mem : gmap Z Z) : uPred imp_to_asmUR :=
  ∃ amem, ⌜0 ≤ stacksize⌝ ∗ ⌜i2a_mem_agree mem amem⌝ ∗ ⌜i2a_mem_sp (pf_sp - stacksize) amem⌝ ∗ i2a_mem_auth amem.

Definition ci2a_heap_inv (h : heap_state) : uPred imp_to_asmUR :=
  ∃ ih, ⌜i2a_heap_agree h ih⌝ ∗ i2a_heap_shared_agree (h_heap h) ih ∗ i2a_heap_auth ih.

Definition ci2a_inv (s : state) (lr rs : gmap string Z) (mem : gmap Z Z) (h : heap_state) : uPred _ :=
    ci2a_mem_inv s.(s_stacksize) mem ∗
    ci2a_heap_inv h ∗
    ci2a_regs_inv s lr rs.

(** lemmas for general invariants *)
Lemma mem_constant_update v' a v mem ss:
  i2a_mem_constant a v -∗
  ci2a_mem_inv ss mem ==∗
  i2a_mem_constant a v' ∗ ci2a_mem_inv ss (<[a := v']>mem).
Proof.
  iIntros "Hconst".
  iDestruct 1 as (?? Hag Hsp) "Hauth".
  iDestruct (i2a_mem_lookup with "[$] [$]") as %?.
  iMod (i2a_mem_update with "[$]") as "[? $]". iModIntro.
  iExists _. iFrame. iPureIntro. split!.
  - move => ?? /lookup_insert_Some[[??]|[??]]; simplify_map_eq'; [done|]. by apply Hag.
  - move => ??. apply lookup_insert_None. unfold i2a_mem_sp in *. naive_solver lia.
Qed.

Lemma stack_slot_update v' slot v mem ss:
  stack_slot slot v -∗
  ci2a_mem_inv ss mem ==∗
  stack_slot slot v' ∗ ci2a_mem_inv ss (<[pf_sp - slot - 1:=v']>mem).
Proof. iIntros "(%&?) ?". iMod (mem_constant_update with "[$] [$]") as "[$ $]". by iModIntro. Qed.

Lemma stack_slot_alloc mem ss:
  ci2a_mem_inv ss mem ==∗
  ∃ v, stack_slot ss v ∗ ci2a_mem_inv (ss + 1) mem.
Proof.
  iDestruct 1 as (? ? Hag Hsp) "Hauth".
  iMod (i2a_mem_alloc (pf_sp - ss - 1) with "[$]") as "[? ?]". { apply Hsp. lia. } iModIntro.
  iExists _. iFrame. iSplit; [done|]. iExists _. iFrame. iPureIntro. split!.
  - lia.
  - move => ?? /lookup_insert_Some[[??]|[??]]; simplify_map_eq => //. by apply Hag.
  - move => ??. apply lookup_insert_None. split; [|lia]. apply Hsp. lia.
Qed.

(** ci2a_places_inv *)
Definition ci2a_places_inv (ps : gmap string place) (sr : list (string*Z)) (vs : gmap string val) (rs : gmap string Z)
  : uPred imp_to_asmUR :=
  ([∗ map] n↦p∈ps, ∃ av,
     (if vs !! n is Some v then imp_val_to_asm_val v av else True) ∗
     match p with
     | PReg r => ⌜r ∈ variable_registers⌝ ∗ ⌜rs !! r = Some av⌝ ∗ ⌜r ∈ sr.*1⌝
     | PStack slot => stack_slot slot av
     end) ∗
   ([∗ list] r∈sr, ∃ v, ⌜pf_rsold !! r.1 = Some v⌝ ∗ stack_slot r.2 v) ∗
   ⌜Forall (λ v, v ∈ sr.*1 ∨ pf_rsold !! v = rs !! v) variable_registers⌝.

Lemma ci2a_places_inv_mono_rs rs ps sr vs rs' :
  map_preserved variable_registers rs rs' →
  ci2a_places_inv ps sr vs rs -∗
  ci2a_places_inv ps sr vs rs'.
Proof.
  iIntros (Hp) "(Hp&$&%Hv)".
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
  (⌜rs !! "SP" = Some (if s.(s_sp_above) then pf_sp else pf_sp - s.(s_stacksize))⌝ -∗ sim n b p e s rs) -∗
  sim n b p e s rs.
Proof.
  iIntros "Hcont" (?????) "Hrf (?&?&(?&%&?))".
  iApply ("Hcont" with "[//] [//] Hrf").
  by iFrame.
Qed.

Lemma sim_regs_included s p b n rs e:
  (⌜map_list_included tmp_registers rs⌝ -∗ ⌜map_list_included saved_registers rs⌝ -∗ sim n b p e s rs) -∗
  sim n b p e s rs.
Proof.
  iIntros "Hcont" (?????) "Hrf (?&?&(?&?&%))".
  iApply ("Hcont" with "[] [] [//] Hrf"); [naive_solver..|].
  by iFrame.
Qed.

(** rules for operations *)
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

  iIntros (?????) "Hrf (Hmem&Hheap&Hregs)". iSatStop.
  tstep_i => ??. simplify_map_eq'.
  rewrite deep_to_asm_instrs_cons in H2.
  move: (H2) => Hsub.
  apply insert_subseteq_Some in Hsub. simplify_option_eq.
  rewrite orb_true_r.

  tstep_i. split!.
  tstep_i. split!. simplify_map_eq'.
  iSatStartBupd.
  iMod (stack_slot_update with "[$] [$]") as "[??]". iModIntro.
  iApply ("Hcont" with "[//] [$] [%] Hrf").
  - simplify_map_eq'. admit.
  - iFrame.
    admit.
Admitted.

Lemma alloc_stack_correct s s' p p' r n b e rs:
  crun s alloc_stack = CResult s' p (CSuccess r) →
  (∀ v, ⌜s' = s <|s_stacksize := (s.(s_stacksize) + 1)%Z |>⌝ -∗
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

Lemma save_r30_correct s s' p p' r n b e rs:
  crun s save_r30 = CResult s' p (CSuccess r) →
  s.(s_places) = ∅ →
  s.(s_saved_registers) = [] →
  pf_rsold = rs →
  is_Some (rs !! "R30") →
  (∀ pc' slot,
     let rs' := (<["PC":=pc']>rs) in
     ⌜s' = s <| s_stacksize := (s_stacksize s + 1)%Z |> <|s_saved_registers := [("R30", slot)] |>⌝ -∗
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
  iSplit; [done|]. rewrite Hs. iSplit => /=.
  - iSplit!.
  - iPureIntro. apply Forall_true. by right.
Qed.

Lemma allocate_places_correct s ns vars s' p p' r n b e rs:
  crun s (allocate_places ns vars) = CResult s' p (CSuccess r) →
  vars ⊆+ variable_registers →
  (∀ v, v ∈ vars → v ∉ s.(s_saved_registers).*1) →
  NoDup ns →
  (∀ n, n ∈ ns → s.(s_places) !! n = None) →
  ci2a_places_inv s.(s_places) s.(s_saved_registers) ∅ rs -∗
  (∀ rs',
     ⌜s.(s_places) ⊆ s'.(s_places)⌝ -∗
     ⌜s.(s_saved_registers) ⊆ s'.(s_saved_registers)⌝ -∗
     ⌜map_list_included ns s'.(s_places)⌝ -∗
     ci2a_places_inv s'.(s_places) s'.(s_saved_registers) ∅ rs' -∗
     sim n b p' e s' rs') -∗
  sim n b (p ++ p') e s rs.
Proof.
  elim: ns vars s s' p rs b => /=. {
    iIntros (???????????) "? Hcont". simplify_crun_eq.
    iApply ("Hcont" with "[//] [//] [%] [$]").
    1: by apply map_list_included_nil. }
  iIntros (?? IH [|v vars] ?????? Hsub Hn [??]%NoDup_cons ?) "Hp Hcont"; simplify_crun_eq.
  - rewrite -app_assoc. iApply alloc_stack_correct; [done|]. iIntros (????) "Hs". simplify_eq/=.
    iApply sim_mono_s. iIntros (???) "Hinv".
    iSplitR; [|iSplitL "Hinv"]. 3: iApply (IH with "[Hs Hp]"); [done|done|done|done|..] => /=.
    { done. }
    + iDestruct "Hinv" as "(?&?&?)". iFrame.
    + move => ??. apply lookup_insert_None. set_solver.
    + iDestruct "Hp" as "[? $]". iApply big_sepM_insert; [set_solver|]. iFrame.
      simplify_map_eq. iExists _. iFrame.
    + iIntros (????). iApply "Hcont"; iPureIntro.
      * etrans; [|done]. apply insert_subseteq. set_solver.
      * set_solver.
      * apply map_list_included_cons; [|done].
        apply: elem_of_weaken; [|by apply subseteq_dom].
        set_solver.
  - rewrite -!app_assoc. iApply alloc_stack_correct; [done|]. iIntros (????) "Hs". simplify_eq/=.
    iApply sim_regs_included. iIntros (??).
    move: Hsub => /submseteq_cons_l [?[Hperm Hsub]].
    have [??]: is_Some (rs !! v). {
      apply: map_list_included_is_Some.
      { apply: (map_list_included_mono _ variable_registers); [done|compute_done]. }
      rewrite Hperm. set_solver. }
    iApply (write_stack_correct with "[$]"); [done..|]. iIntros (?) "Hs". simplify_eq.
    iApply sim_mono_s. iIntros (???) "Hinv".
    iSplitR; [|iSplitL "Hinv"]. 3: iApply (IH with "[Hp Hs]"); [done|..]. all: csimpl.
    + done.
    + iDestruct "Hinv" as "(?&?&?)". iFrame.
    + rewrite Hperm. by apply submseteq_cons.
    + move => ? Hin /=. apply not_elem_of_cons. split; [|set_unfold;naive_solver]. move => ?. subst.
      move: Hin => /(elem_of_submseteq _ _ _)/(_ Hsub).
      apply: NoDup_cons_1_1. rewrite -Hperm. compute_done.
    + done.
    + move => ??. apply lookup_insert_None. set_solver.
    + iApply ci2a_places_inv_mono_rs. { apply map_preserved_insert_r_not_in; [compute_done|]. done. }
      iDestruct "Hp" as "(Hp&Hsr&%Hv)". iSplitL "Hp"; [|iSplit].
      * iApply big_sepM_insert; [set_solver|]. iFrame. iSplitR.
        { iExists _. simplify_map_eq. iPureIntro. split!. { rewrite Hperm. set_solver. } set_solver. }
        iApply (big_sepM_impl with "[$]"). iIntros "!>" (???) "[% [? Hp]]". iExists _. iFrame.
        case_match => //. iDestruct "Hp" as %(?&?&?). iPureIntro. csimpl. split!. set_solver.
      * simpl. iFrame. iExists _. iFrame. iPureIntro.
        move: Hv => /Forall_forall/(_ v)[| |->//]. { rewrite Hperm. set_solver. } set_solver.
      * iPureIntro. apply: Forall_impl; [done|]. set_solver.
    + iIntros (????) "?". iApply sim_mono_b.
      iApply ("Hcont" with "[%] [%] [%] [$]").
      * etrans; [|done]. apply insert_subseteq. set_solver.
      * set_solver.
      * apply map_list_included_cons; [|done].
        apply: elem_of_weaken; [|by apply subseteq_dom].
        set_solver.
Qed.
End proof.

Lemma sim_intro s dins rs mem ins ins_dom fns_dom f2i n b e h fns cs lr rf P:
  let H := Build_ProofFixedValues (rs !!! "SP") ins fns cs rs in
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
  trefines (MS asm_module (initial_asm_state ins))
           (MS (imp_to_asm (dom _ ins) {[f]} f2i imp_module) (initial_imp_to_asm_state imp_module
             (initial_imp_state (<[f := fn]> ∅)))).
Proof.
  move => Hrun ? Ha.
  apply imp_to_asm_proof; [done|set_solver|].
  move => n i rs mem K f' fn' avs vs h cs pc ret rf rc amem ih lr Hpc Hins Hf ? Hsat Hinv Hargs Hlen Hlr Hcall Hret.
  move: Hf. rewrite lookup_insert_Some lookup_empty => ?. destruct_all?; simplify_map_eq.
  move: Hinv => [?[??]].
  move: Hargs => [?[?[??]]].

  apply: (sim_intro (initial_state f2i)).
  1: by simplify_map_eq'. 1: done. 1: set_solver. 1: done. {
    iSatMono. iIntros "(Hmem&Hheap&Hshare&Hvals&?&?)". iFrame.
    iSplitL "Hmem Hheap Hshare". 2: iAccu.
    iSplitL "Hmem" => /=; [|iSplitL].
    - iExists _. iFrame. iPureIntro. by rewrite Z.sub_0_r.
    - iExists _. by iFrame.
    - iPureIntro => /=. rewrite lookup_lookup_total; [done|].
      apply: (map_list_included_is_Some saved_registers); [done|compute_done].
  }
  iSatClear.
  iIntros "(Hvals&Hrc)".
  unfold pass in Hrun. simplify_crun_eq.

  iApply save_r30_correct; [done..|]. iIntros (???) "Hp". simplify_eq/=.
  iApply (allocate_places_correct with "[Hp]").
  { done. } { done. } { set_solver. } { apply NoDup_remove_dups. }
  { set_solver. } { done. }
  iIntros (????) "Hpl". simplify_eq/=.

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

*)
