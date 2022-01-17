Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.filter.
Require Import refframe.product.
Require Import refframe.seq_product.
Require Import refframe.proof_techniques.
Require Import refframe.imp.
Require Import refframe.asm.
Require Import refframe.itree.


(** * imp_to_asm *)
Definition imp_to_asm_args (ret : Z) (rs : gmap string Z) (vs : list val) : Prop.
(* args correspond to registers *)
(* R30 contain ret *)
Admitted.

Definition imp_to_asm_ret (rs rsold : gmap string Z) (v : val) : Prop.
(* registers stay the same / get clobbered *)
(* R0 contain representation of v *)
Admitted.

Definition imp_to_asm_itree_from_env (ins : gset Z) (fns : gset string) (f2i : gmap string Z) : itree (moduleE (imp_event + asm_event) (list (bool * Z * gmap string Z))) () :=
  pc ← TExist Z;;;
  rs ← TExist _;;;
  TVis (inr (EARecvJump pc rs));;;;
  (* env chooses if this is a function call or return *)
  b ← TAll bool;;;
  if b then
    (* env chooses return address *)
    ret ← TAll _;;;
    (* env chooses function name *)
    f ← TAll _;;;
    (* env chooses arguments *)
    vs ← TAll _;;;
    (* env proves that function name is valid *)
    TAssume (f ∈ fns);;;;
    (* env proves it calls the right address *)
    TAssume (f2i !! f = Some pc);;;;
    (* env proves that ret is not in invs *)
    TAssume (ret ∉ ins);;;;
    (* env proves that rs corresponds to vs and ret  *)
    TAssume (imp_to_asm_args ret rs vs);;;;
    (* track the registers and return address (false means ret belongs to env) *)
    cs ← TGet;;; TPut ((false, ret, rs)::cs);;;;
    TVis (inl (EIRecvCall f vs))
  else
    (* env chooses return value *)
    v ← TAll _;;;
    (* env chooses old registers *)
    rsold ← TAll _;;;
    (* env chooses rest of cs *)
    cs' ← TAll _;;;
    (* get registers from stack (true means pc belongs to the program) *)
    cs ← TGet;;;
    TAssume (cs = (true, pc, rsold)::cs');;;;
    TPut cs';;;;
    (* env proves that rs is updated correctly *)
    TAssume (imp_to_asm_ret rs rsold v);;;;
    TVis (inl (EIRecvReturn v))
.

Definition imp_to_asm_itree_to_env (ins : gset Z) (fns : gset string) (f2i : gmap string Z) : itree (moduleE (imp_event + asm_event) (list (bool * Z * gmap string Z))) () :=
  pc ← TExist Z;;;
  rs ← TExist _;;;
  (* program chooses whether it returns or makes a function call *)
  b ← TExist bool;;;
  if b then
    (* program chooses return address *)
    ret ← TExist Z;;;
    (* program chooses which function it calls *)
    f ← TExist _;;;
    (* program chooses the arguments of the function *)
    vs ← TExist _;;;
    (* program proves that this function is external *)
    TAssert (f ∉ fns);;;;
    (* program proves that the address is correct *)
    TAssert (f2i !! f = Some pc);;;;
    (* program proves that ret is in invs *)
    TAssert (ret ∈ ins);;;;
    (* program proves that rs corresponds to vs and ret  *)
    TAssert (imp_to_asm_args ret rs vs);;;;
    (* track the registers and return address (true means ret belongs to program) *)
    cs ← TGet;;; TPut ((true, ret, rs)::cs);;;;
    TVis (inl (EICall f vs));;;;
    TVis (inr (EAJump pc rs))
  else
    (* program chooses return value *)
    v ← TExist _;;;
    (* program chooses old registers *)
    rsold ← TExist _;;;
    (* program chooses rest of cs *)
    cs' ← TExist _;;;
    (* get registers from stack (false means pc belongs to the env) *)
    cs ← TGet;;;
    TAssert (cs = (false, pc, rsold)::cs');;;;
    TPut cs';;;;
    (* env proves that rs is updated correctly *)
    TAssert (imp_to_asm_ret rs rsold v);;;;
    TVis (inl (EIReturn v));;;;
    TVis (inr (EAJump pc rs)).

Definition imp_to_asm_itree (ins : gset Z) (fns : gset string) (f2i : gmap string Z) : itree (moduleE (imp_event + asm_event) (list (bool * Z * gmap string Z))) () :=
  ITree.forever (imp_to_asm_itree_from_env ins fns f2i;;;; imp_to_asm_itree_to_env ins fns f2i).

Definition imp_to_asm (m : module imp_event) : module asm_event :=
  mod_seq_map m (mod_itree (imp_event + asm_event) (list (bool * Z * gmap string Z))).

Definition initial_imp_to_asm_state (m : module imp_event) (σ : m.(m_state)) (ins : gset Z) (fns : gset string) (f2i : gmap string Z) : (imp_to_asm m).(m_state) :=
  (SPRight, σ, (imp_to_asm_itree ins fns f2i, []), SMFilter).

Inductive imp_to_asm_combine_stacks (ins1 ins2 : gset Z) :
  imp_prod_filter_enum → list imp_prod_filter_enum →
  list (bool * Z * gmap string Z) → list (bool * Z * gmap string Z) → list (bool * Z * gmap string Z) →
 Prop :=
| IAC_nil :
  imp_to_asm_combine_stacks ins1 ins2 IPFNone [] [] [] []
| IAC_NoneLeft ret rs ics cs cs1 cs2:
  ret ∉ ins1 →
  ret ∉ ins2 →
  imp_to_asm_combine_stacks ins1 ins2 IPFNone ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 IPFLeft (IPFNone :: ics) ((false, ret, rs) :: cs) ((false, ret, rs) :: cs1) cs2
| IAC_NoneRight ret rs ics cs cs1 cs2:
  ret ∉ ins1 →
  ret ∉ ins2 →
  imp_to_asm_combine_stacks ins1 ins2 IPFNone ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 IPFRight (IPFNone :: ics) ((false, ret, rs) :: cs) cs1 ((false, ret, rs) :: cs2)
| IAC_LeftRight ret rs ics cs cs1 cs2:
  ret ∈ ins1 →
  imp_to_asm_combine_stacks ins1 ins2 IPFLeft ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 IPFRight (IPFLeft :: ics) cs ((true, ret, rs) :: cs1) ((false, ret, rs) :: cs2)
| IAC_LeftNone ret rs ics cs cs1 cs2:
  ret ∈ ins1 →
  imp_to_asm_combine_stacks ins1 ins2 IPFLeft ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2  IPFNone (IPFLeft :: ics) ((true, ret, rs) :: cs) ((true, ret, rs) :: cs1) cs2
| IAC_RightLeft ret rs ics cs cs1 cs2:
  ret ∈ ins2 →
  imp_to_asm_combine_stacks ins1 ins2 IPFRight ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 IPFLeft (IPFRight :: ics) cs ((false, ret, rs) :: cs1) ((true, ret, rs) :: cs2)
| IAC_RightNone ret rs ics cs cs1 cs2:
  ret ∈ ins2 →
  imp_to_asm_combine_stacks ins1 ins2 IPFRight ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 IPFNone (IPFRight :: ics) ((true, ret, rs) :: cs) cs1 ((true, ret, rs) :: cs2)
.

Definition imp_to_asm_combine_inv (m1 m2 : module imp_event)
           (ins1 ins2 : gset Z) (fns1 fns2 : gset string) (f2i1 f2i2 : gmap string Z)
  (σ1 : (asm_prod ins1 ins2 (imp_to_asm m1) (imp_to_asm m2)).(m_state))
  (σ2 : (imp_to_asm (imp_prod fns1 fns2 m1 m2)).(m_state)) : Prop :=
  let '(σpa, (σpi1, σi1, (t1, cs1), σf1), (σpi2, σi2, (t2, cs2), σf2), σfa) := σ1 in
  let '(σps, (σpi, σs1, σs2, σf), (t, cs), σfs) := σ2 in
  let ins := (ins1 ∪ ins2) in
  let fns := (fns1 ∪ fns2) in
  let f2i := (f2i1 ∪ f2i2) in
  ∃ ics ips,
  σi1 = σs1 ∧
  σi2 = σs2 ∧
  imp_to_asm_combine_stacks ins1 ins2 ips ics cs cs1 cs2 ∧
  (( σfa = APFNone ∧ σpa = SPNone ∧ σfs = SMFilter ∧ σps = SPRight ∧ t = imp_to_asm_itree ins fns f2i
      ∧ t1 = imp_to_asm_itree ins1 fns1 f2i1 ∧ t2 = imp_to_asm_itree ins2 fns2 f2i2
      ∧ σf1 = SMFilter ∧ σf2 = SMFilter ∧ σpi1 = SPRight ∧ σpi2 = SPRight
      ∧ σpi = SPNone ∧ σf = IPFState IPFNone ics
      ∧ ips = IPFNone
    ) ∨
  (( (∃ f vs, σf = IPFState (IPFLeftRecvCall f vs) ics ∧ σf1 = SMProgRecv (EIRecvCall f vs))
      ∨ (∃ v, σf = IPFState (IPFLeftRecvReturn v) ics ∧ σf1 = SMProgRecv (EIRecvReturn v))
      ∨ σf = IPFState IPFLeft ics ∧ σf1 = SMProg)
      ∧ σfa = APFLeft ∧ σpa = SPLeft ∧ σfs = SMProg ∧ σps = SPLeft
      ∧ t = (imp_to_asm_itree_to_env ins fns f2i;;;; imp_to_asm_itree ins fns f2i)
      ∧ t1 = (imp_to_asm_itree_to_env ins1 fns1 f2i1;;;; (imp_to_asm_itree ins1 fns1 f2i1))
      ∧ t2 = imp_to_asm_itree ins2 fns2 f2i2
      ∧ σf2 = SMFilter ∧ σpi1 = SPLeft ∧ σpi2 = SPRight
      ∧ σpi = SPLeft
      ∧ ips = IPFLeft) ∨
  (((∃ f vs, σf = IPFState (IPFRightRecvCall f vs) ics ∧ σf2 = SMProgRecv (EIRecvCall f vs))
      ∨ (∃ v, σf = IPFState (IPFRightRecvReturn v) ics ∧ σf2 = SMProgRecv (EIRecvReturn v))
      ∨ σf = IPFState IPFRight ics ∧ σf2 = SMProg)
      ∧ σfa = APFRight ∧ σpa = SPRight ∧ σfs = SMProg ∧ σps = SPLeft
      ∧ t = (imp_to_asm_itree_to_env ins fns f2i;;;; imp_to_asm_itree ins fns f2i)
      ∧ t1 = imp_to_asm_itree ins1 fns1 f2i1
      ∧ t2 = (imp_to_asm_itree_to_env ins2 fns2 f2i2;;;; (imp_to_asm_itree ins2 fns2 f2i2))
      ∧ σf1 = SMFilter ∧ σpi1 = SPRight ∧ σpi2 = SPLeft
      ∧ σpi = SPRight
      ∧ ips = IPFRight)).
Ltac solve_imp_to_asm_combine_inv :=
  eexists _, _; split_and!; [naive_solver..| try done; try by econs | naive_solver].

Program Definition itree_step_forever_s EV S R (t : itree (moduleE EV S) R) s :=
  @eq_it_to_tstep_s EV S s (ITree.forever t) (t;;;;ITree.forever t) _.
Next Obligation. move => *. setoid_rewrite unfold_forever at 1. by setoid_rewrite tau_eutt. Qed.
Global Hint Resolve itree_step_forever_s : tstep.

Program Definition itree_step_forever_i EV S R (t : itree (moduleE EV S) R) s :=
  @eq_it_to_tstep_i EV S s (ITree.forever t) (t;;;; (ITree.forever t)) _.
Next Obligation. move => *. setoid_rewrite unfold_forever at 1. by setoid_rewrite tau_eutt. Qed.
Global Hint Resolve itree_step_forever_i : tstep.

Axiom ELIM_EUTT : ∀ EV R (t1 t2 : itree EV R), t1 ≈ t2 -> t1 = t2.
Local Hint Constants Transparent : tstep.
Local Ltac go :=
      unfold itree_rel; intros; destruct_all?; simplify_eq/=; repeat lazymatch goal with | H : _ ≈ _ |- _ => apply ELIM_EUTT in H; subst end.
Local Ltac go_i := tstep_i; go.
Local Ltac go_s := tstep_s; go.

Lemma imp_to_asm_combine ins1 ins2 fns1 fns2 f2i1 f2i2 m1 m2 σ1 σ2 `{!VisNoAll m1} `{!VisNoAll m2}:
  ins1 ## ins2 →
  fns1 ## fns2 →
  (∀ f, f ∈ fns1 → ∃ i, i ∈ ins1 ∧ f2i1 !! f = Some i) →
  (∀ f, f ∈ fns2 → ∃ i, i ∈ ins2 ∧ f2i2 !! f = Some i) →
  (∀ f i1 i2, f2i1 !! f = Some i1 → f2i2 !! f = Some i2 → i1 = i2) →
  (∀ f i, f2i1 !! f = Some i → i ∈ ins2 → f ∈ fns2) →
  (∀ f i, f2i2 !! f = Some i → i ∈ ins1 → f ∈ fns1) →
  trefines (MS (asm_prod ins1 ins2 (imp_to_asm m1) (imp_to_asm m2))
               (SPNone, initial_imp_to_asm_state m1 σ1 ins1 fns1 f2i1,
                 initial_imp_to_asm_state m2 σ2 ins2 fns2 f2i2, APFNone))
           (MS (imp_to_asm (imp_prod fns1 fns2 m1 m2))
               (initial_imp_to_asm_state (imp_prod _ _ _ _)
                  (SPNone, σ1, σ2, (IPFState IPFNone [])) (ins1 ∪ ins2) (fns1 ∪ fns2) (f2i1 ∪ f2i2))
).
Proof.
  move => Hdisji Hdisjf Hin1 Hin2 Hagree Ho1 Ho2.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { exact (λ _, imp_to_asm_combine_inv _ _ _ _ _ _ f2i1 f2i2). }
  { solve_imp_to_asm_combine_inv. } { done. }
  move => /= {σ1 σ2} {}n Hloop [[[σpa [[[σpi1 σi1] [t1 cs1]] σf1]] [[[σpi2 σi2] [t2 cs2]] σf2]] σfa].
  move => [[[σps [[[σpi σs1] σs2] σf]] [t cs]] σfs] /= ?.
  destruct_all?; simplify_eq.
  - go_s. rewrite -/(imp_to_asm_itree _ _).
    go_s. go_s. go_i. invert_all asm_prod_filter.
    + go_s. eexists _. go.
      go_s. go_s. eexists _. go. go_s. go_s. split; [done|]. go.
      go_s. go_s. rename x into b.
      go_i. rewrite -/(imp_to_asm_itree _ _). go_i. go_i. go_i.
      go_i. go_i. go_i. go_i.
      invert_all asm_prod_filter.
      go_i. go_i. eexists b. go. destruct b.
      * go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s.
        go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s.
        revert select (_ ∉ (_ ∪ _)) => /not_elem_of_union[??].
        revert select (_ ∈ (_ ∪ _)) => Hin. revert select ((_ ∪ _) !! _ = Some _) => Hf2i.
        move: Hin => /elem_of_union [Hf|Hf]. 2: {
          move: (Hf) => /Hin2[?[??]]. move: Hf2i => /lookup_union_Some_raw[?|[??]]; simplify_eq => //. naive_solver.
        }
        move: (Hf) => /Hin1[f[??]].
        have ?: x = f. { move: Hf2i => /lookup_union_Some_raw[?|[??]]; simplify_eq => //. } subst.
        eexists _, _, _. split; [apply IPFCallExtToLeft|]. { done. } { by apply: Hdisjf. } simpl.
        split; [done|].
        go_i. go_i. eexists _. go. go_i. go_i. eexists _. go. go_i. go_i. eexists _. go.
        go_i. go_i. split; [done|]. go. go_i. go_i. split; [done|]. go.
        go_i. go_i. split; [done|]. go. go_i. go_i. split; [done|]. go. go_i. go_i.
        go_i. go_i.
        go_i. apply Hloop. solve_imp_to_asm_combine_inv.
        (* split_and! => //. right.  naive_solver. *)
      * go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s.
        revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
        inversion Hstack; simplify_eq/= => //.
        eexists _, _, _. split; [apply IPFReturnExtToLeft|]. simpl. split; [done|].
        go_i. go_i. eexists _. go. go_i. go_i. eexists _. go.
        go_i. go_i. eexists _. go. go_i. go_i. go_i. go_i. split; [done|]. go. go_i. go_i.
        go_i. go_i. split; [done|]. go.
        go_i. apply Hloop. solve_imp_to_asm_combine_inv.
    + go_s. eexists _. go.
      go_s. go_s. eexists _. go. go_s. go_s. split; [done|]. go.
      go_s. go_s. rename x into b.
      go_i. rewrite -/(imp_to_asm_itree _ _). go_i. go_i. go_i.
      go_i. go_i. go_i. go_i.
      invert_all asm_prod_filter.
      go_i. go_i. eexists b. go. destruct b.
      * go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s.
        go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s.
        revert select (_ ∉ (_ ∪ _)) => /not_elem_of_union[??].
        revert select (_ ∈ (_ ∪ _)) => Hin. revert select ((_ ∪ _) !! _ = Some _) => Hf2i.
        move: Hin => /elem_of_union [Hf|Hf]. 1: {
          move: (Hf) => /Hin1[?[??]]. move: Hf2i => /lookup_union_Some_raw[?|[??]]; simplify_eq => //.
        }
        move: (Hf) => /Hin2[f[??]].
        have ?: x = f. { move: Hf2i => /lookup_union_Some_raw[?|[??]]; simplify_eq => //. naive_solver. } subst.
        eexists _, _, _. split; [apply IPFCallExtToRight|]. { move => ?. by apply: Hdisjf. } { done. } simpl.
        split; [done|].
        go_i. go_i. eexists _. go. go_i. go_i. eexists _. go. go_i. go_i. eexists _.  go.
        go_i. go_i. split; [done|]. go. go_i. go_i. split; [done|]. go.
        go_i. go_i. split; [done|]. go. go_i. go_i. split; [done|]. go. go_i. go_i. go_i. go_i.
        go_i. apply Hloop. solve_imp_to_asm_combine_inv.
      * go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s.
        revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
        inversion Hstack; simplify_eq/= => //.
        eexists _, _, _. split; [apply IPFReturnExtToRight|]. simpl. split; [done|].
        go_i. go_i. eexists _. go. go_i. go_i. eexists _. go.
        go_i. go_i. eexists _. go. go_i. go_i. go_i. go_i. split; [done|]. go. go_i. go_i.
        go_i. go_i. split; [done|]. go.
        go_i. apply Hloop. solve_imp_to_asm_combine_inv.
  - tstep_both.
    apply steps_impl_step_end => κ Pσ2. go. case_match; go.
    + tstep_s. eexists (Some (EIRecvCall f vs)), _. split; [done|]. eexists _, _. split; [econs|].
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. solve_imp_to_asm_combine_inv.
    + tstep_s. eexists None, _. split; [done|]. eexists _, _. split; [done|].
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. solve_imp_to_asm_combine_inv.
  - tstep_both.
    apply steps_impl_step_end => κ Pσ2. go. case_match; go.
    + tstep_s. eexists (Some (EIRecvReturn v)), _. split; [done|]. eexists _, _. split; [econs|].
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. solve_imp_to_asm_combine_inv.
    + tstep_s. eexists None, _. split; [done|]. eexists _, _. split; [done|].
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. solve_imp_to_asm_combine_inv.
  - tstep_both.
    apply steps_impl_step_end => κ Pσ2. go. destruct κ as [e|]; go.
    + tend. have [σ' Hσ'] := vis_no_all _ _ _ ltac:(done). eexists σ'. split; [naive_solver|].
      go_i. go_i. go_i. go_i. go_i. go_i. destruct x1.
      * go_i. go_i. go_i. go_i. go_i. go_i.
        go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i.
        go_i. go_i. go_i. go_i. go_i. go_i.
        invert_all asm_prod_filter.
        -- go_i. go_i. go_i. go_i. go_i. go_i.
           go_i. go_i. invert_all asm_prod_filter.
           go_i. go_i. eexists true. go. go_i. go_i. eexists _. go.
           go_i. go_i. eexists _. go. go_i. go_i. eexists _. go.
           go_i. go_i. split; [ naive_solver|]. go. go_i. go_i. split; [naive_solver|]. go.
           go_i. go_i. split; [by apply: Hdisji|]. go. go_i. go_i. split; [done|]. go. go_i. go_i. go_i.
           go_i. go_i.
           go_s. eexists (Some _), _. split; [done|]. eexists _, _ => /=.
           split; [econs|]. { naive_solver. } { naive_solver. }
           apply: steps_spec_step_end; [done|] => ??.
           apply: Hloop. solve_imp_to_asm_combine_inv.
        -- go_s. eexists (Some _), _. split; [done|]. eexists _, _ => /=. split; [apply IPFCallLeftToExt|].
           { naive_solver. } { naive_solver. }
           apply: steps_spec_step_end; [done|] => ??.
           go_s. go_s. eexists _. go. go_s. go_s. eexists _. go.
           go_s. go_s. eexists true. go. go_s. go_s. eexists _. go.
           go_s. go_s. eexists _. go. go_s. go_s. eexists _. go.
           go_s. go_s. split. { apply not_elem_of_union. naive_solver. }
           go. go_s. go_s. split. { apply lookup_union_Some_raw. naive_solver. }
           go. go_s. go_s. split; [apply elem_of_union; by left|]. go.
           go_s. go_s. split; [done|]. go. go_s. go_s. go_s. go_s. go_s.
           go_s. split; [done|]. go. go_s. split; [done|]. go.
           apply: Hloop. solve_imp_to_asm_combine_inv.
      * go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i.
        invert_all asm_prod_filter.
        -- go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i.
           invert_all asm_prod_filter.
           revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
           inversion Hstack; simplify_eq/= => //.
           go_i. go_i. eexists false. go. go_i. go_i. eexists _. go.
           go_i. go_i. eexists _. go. go_i. go_i. eexists _. go. go_i. go_i. go_i. go_i. split;[done|]. go.
           go_i. go_i. go_i. go_i. split; [done|]. go. go_i.
           go_s. eexists (Some _), _. split; [done|]. eexists _, _ => /=.
           split; [apply IPFReturnLeftToRight|].
           apply: steps_spec_step_end; [done|] => ??.
           apply: Hloop. solve_imp_to_asm_combine_inv.
        -- revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
           inversion Hstack; simplify_eq/= => //.
           go_s. eexists (Some _), _. split; [done|]. eexists _, _ => /=.
           split; [apply IPFReturnLeftToExt|].
           apply: steps_spec_step_end; [done|] => ??.
           go_s. go_s. eexists _. go. go_s. go_s. eexists _. go.
           go_s. go_s. eexists false. go. go_s. go_s. eexists _. go.
           go_s. go_s. eexists _. go. go_s. go_s. eexists _. go. go_s. go_s. go_s. go_s.
           split; [done|]. go. go_s. go_s. go_s. go_s. split; [done|]. go.
           go_s. go_s. split; [done|]. go. go_s. split; [done|]. go.
           apply: Hloop. solve_imp_to_asm_combine_inv.
    + tstep_s. eexists None, _. split; [done|]. eexists _, _. split; [done|].
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. solve_imp_to_asm_combine_inv.
  - tstep_both.
    apply steps_impl_step_end => κ Pσ2. go. case_match; go.
    + tstep_s. eexists (Some (EIRecvCall f vs)), _. split; [done|]. eexists _, _. split; [econs|].
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. solve_imp_to_asm_combine_inv.
    + tstep_s. eexists None, _. split; [done|]. eexists _, _. split; [done|].
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. solve_imp_to_asm_combine_inv.
  - tstep_both.
    apply steps_impl_step_end => κ Pσ2. go. case_match; go.
    + tstep_s. eexists (Some (EIRecvReturn v)), _. split; [done|]. eexists _, _. split; [econs|].
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. solve_imp_to_asm_combine_inv.
    + tstep_s. eexists None, _. split; [done|]. eexists _, _. split; [done|].
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. solve_imp_to_asm_combine_inv.
  - tstep_both.
    apply steps_impl_step_end => κ Pσ2. go. destruct κ as [e|]; go.
    + tend. have [σ' Hσ'] := vis_no_all _ _ _ ltac:(done). eexists σ'. split; [naive_solver|].
      go_i. go_i. go_i. go_i. go_i. go_i. destruct x1.
      * go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i.
        go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i.
        invert_all asm_prod_filter.
        -- go_i. go_i. go_i. go_i. go_i. go_i.
           go_i. go_i. invert_all asm_prod_filter.
           go_i. go_i. eexists true. go. go_i. go_i. eexists _. go.
           go_i. go_i. eexists _. go. go_i. go_i. eexists _. go.
           go_i. go_i. split; [ naive_solver|]. go. go_i. go_i. split; [naive_solver|]. go.
           go_i. go_i. split. { move => ?. by apply: Hdisji. } go. go_i. go_i. split; [done|]. go.
           go_i. go_i. go_i. go_i. go_i.
           go_s. eexists (Some _), _. split; [done|]. eexists _, _ => /=.
           split; [econs|]. { naive_solver. } { naive_solver. }
           apply: steps_spec_step_end; [done|] => ??.
           apply: Hloop. solve_imp_to_asm_combine_inv.
        -- go_s. eexists (Some _), _. split; [done|]. eexists _, _ => /=. split; [apply IPFCallRightToExt|].
           { naive_solver. } { naive_solver. }
           apply: steps_spec_step_end; [done|] => ??.
           go_s. go_s. eexists _. go. go_s. go_s. eexists _. go.
           go_s. go_s. eexists true. go. go_s. go_s. eexists _. go.
           go_s. go_s. eexists _. go. go_s. go_s. eexists _. go.
           go_s. go_s. split. { apply not_elem_of_union. naive_solver. }
           go. go_s. go_s. split. { apply lookup_union_Some_raw. destruct (f2i1 !! x2) eqn:?; naive_solver. }
           go. go_s. go_s. split; [apply elem_of_union; by right|]. go. go_s. go_s. split; [done|]. go.
           go_s. go_s. go_s. go_s. go_s.
           go_s. split; [done|]. go. go_s. split; [done|]. go.
           apply: Hloop. solve_imp_to_asm_combine_inv.
      * go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i.
        invert_all asm_prod_filter.
        -- go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i.
           invert_all asm_prod_filter.
           revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
           inversion Hstack; simplify_eq/= => //.
           go_i. go_i. eexists false. go. go_i. go_i. eexists _. go.
           go_i. go_i. eexists _. go. go_i. go_i. eexists _. go. go_i. go_i.
           go_i. go_i. split;[done|]. go. go_i. go_i.
           go_i. go_i. split; [done|]. go. go_i.
           go_s. eexists (Some _), _. split; [done|]. eexists _, _ => /=.
           split; [apply IPFReturnRightToLeft|].
           apply: steps_spec_step_end; [done|] => ??.
           apply: Hloop. solve_imp_to_asm_combine_inv.
        -- revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
           inversion Hstack; simplify_eq/= => //.
           go_s. eexists (Some _), _. split; [done|]. eexists _, _ => /=.
           split; [apply IPFReturnRightToExt|].
           apply: steps_spec_step_end; [done|] => ??.
           go_s. go_s. eexists _. go. go_s. go_s. eexists _. go.
           go_s. go_s. eexists false. go. go_s. go_s. eexists _. go.
           go_s. go_s. eexists _. go. go_s. go_s. eexists _. go.
           go_s. go_s. go_s. go_s. split; [done|]. go.
           go_s. go_s. go_s. go_s. split; [done|]. go.
           go_s. go_s. split; [done|]. go. go_s. split; [done|]. go.
           apply: Hloop. solve_imp_to_asm_combine_inv.
    + tstep_s. eexists None, _. split; [done|]. eexists _, _. split; [done|].
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. solve_imp_to_asm_combine_inv.
Qed.
