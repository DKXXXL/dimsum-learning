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
Definition imp_val_to_asm_val (v : val) : Z :=
  match v with
  | ValNum z => z
  | ValBool b => bool_to_Z b
  end.

Definition args_registers : list string :=
  ["R0"; "R1"; "R2"; "R3"; "R4"; "R5"; "R6"; "R7" ; "R8"].

Definition tmp_registers : list string :=
  ["R9"; "R10"; "R11"; "R12"; "R13"; "R14"; "R15"; "R16"; "R17"].

Definition saved_registers : list string :=
  ["R19"; "R20"; "R21"; "R22"; "R23"; "R24"; "R25"; "R26"; "R27"; "R28"; "R29"].

Definition imp_to_asm_args (ret : Z) (rs : gmap string Z) (vs : list val) : Prop :=
  rs !! "R30" = Some ret ∧
  Forall2 (λ v r, rs !! r = Some (imp_val_to_asm_val v)) vs
          (take (length vs) args_registers) ∧
  Forall (λ r, is_Some (rs !! r)) (args_registers ++ tmp_registers ++ saved_registers)
.

Definition imp_to_asm_ret (rs rsold : gmap string Z) (v : val) : Prop :=
  rs !! "R0" = Some (imp_val_to_asm_val v) ∧
  Forall (λ r, is_Some (rs !! r)) (args_registers ++ tmp_registers) ∧
  Forall (λ r, rs !! r = Some (rsold !!! r)) (saved_registers).

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

Definition imp_to_asm_itree' (ins : gset Z) (fns : gset string) (f2i : gmap string Z) : itree (moduleE (imp_event + asm_event) (list (bool * Z * gmap string Z))) () :=
  (ITree.forever (imp_to_asm_itree_from_env ins fns f2i;;;; imp_to_asm_itree_to_env ins fns f2i)).
Definition imp_to_asm_itree :=
(* This is sadly necessary as assumption goes crazy in some cases without it. *)
  locked imp_to_asm_itree'.

Definition imp_to_asm (m : module imp_event) : module asm_event :=
  mod_seq_map m (mod_itree (imp_event + asm_event) (list (bool * Z * gmap string Z))).

Definition initial_imp_to_asm_state (m : module imp_event) (σ : m.(m_state)) (ins : gset Z) (fns : gset string) (f2i : gmap string Z) : (imp_to_asm m).(m_state) :=
  (SPRight, σ, (imp_to_asm_itree ins fns f2i, []), SMFilter).

Lemma imp_to_asm_trefines m m' σ σ' ins fns f2i `{!VisNoAll m}:
  trefines (MS m σ) (MS m' σ') →
  trefines (MS (imp_to_asm m) (initial_imp_to_asm_state m σ ins fns f2i))
           (MS (imp_to_asm m') (initial_imp_to_asm_state m' σ' ins fns f2i)).
Proof. move => ?. apply: mod_map_trefines. by apply: mod_seq_product_trefines. Qed.

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
  (( σfa = APFNone ∧ σpa = SPNone ∧ σfs = SMFilter ∧ σps = SPRight
     ∧ t ≈ (imp_to_asm_itree ins fns f2i)
      ∧ t1 ≳ (imp_to_asm_itree ins1 fns1 f2i1)
      ∧ t2 ≳ imp_to_asm_itree ins2 fns2 f2i2
      ∧ σf1 = SMFilter ∧ σf2 = SMFilter ∧ σpi1 = SPRight ∧ σpi2 = SPRight
      ∧ σpi = SPNone ∧ σf = IPFState IPFNone ics
      ∧ ips = IPFNone
    ) ∨
  (( (∃ f vs, σf = IPFState (IPFLeftRecvCall f vs) ics ∧ σf1 = SMProgRecv (EIRecvCall f vs))
      ∨ (∃ v, σf = IPFState (IPFLeftRecvReturn v) ics ∧ σf1 = SMProgRecv (EIRecvReturn v))
      ∨ σf = IPFState IPFLeft ics ∧ σf1 = SMProg)
      ∧ σfa = APFLeft ∧ σpa = SPLeft ∧ σfs = SMProg ∧ σps = SPLeft
      ∧ t ≈ (imp_to_asm_itree_to_env ins fns f2i;;;; (imp_to_asm_itree ins fns f2i))
      ∧ t1 ≳ (imp_to_asm_itree_to_env ins1 fns1 f2i1;;;; (imp_to_asm_itree ins1 fns1 f2i1))
      ∧ t2 ≳ imp_to_asm_itree ins2 fns2 f2i2
      ∧ σf2 = SMFilter ∧ σpi1 = SPLeft ∧ σpi2 = SPRight
      ∧ σpi = SPLeft
      ∧ ips = IPFLeft) ∨
  (((∃ f vs, σf = IPFState (IPFRightRecvCall f vs) ics ∧ σf2 = SMProgRecv (EIRecvCall f vs))
      ∨ (∃ v, σf = IPFState (IPFRightRecvReturn v) ics ∧ σf2 = SMProgRecv (EIRecvReturn v))
      ∨ σf = IPFState IPFRight ics ∧ σf2 = SMProg)
      ∧ σfa = APFRight ∧ σpa = SPRight ∧ σfs = SMProg ∧ σps = SPLeft
      ∧ t ≈ (imp_to_asm_itree_to_env ins fns f2i;;;; (imp_to_asm_itree ins fns f2i))
      ∧ t1 ≳ (imp_to_asm_itree ins1 fns1 f2i1)
      ∧ t2 ≳ (imp_to_asm_itree_to_env ins2 fns2 f2i2;;;; (imp_to_asm_itree ins2 fns2 f2i2))
      ∧ σf1 = SMFilter ∧ σpi1 = SPRight ∧ σpi2 = SPLeft
      ∧ σpi = SPRight
      ∧ ips = IPFRight)).

Lemma itree_tstep_imp_to_asm_itree ins fns f2i b:
  ITreeTStep false b (imp_to_asm_itree ins fns f2i) (imp_to_asm_itree_from_env ins fns f2i;;;; imp_to_asm_itree_to_env ins fns f2i;;;; imp_to_asm_itree ins fns f2i).
Proof. rewrite /imp_to_asm_itree. unlock. constructor. rewrite -bind_bind. eapply itree_tstep_forever. Qed.
Global Hint Resolve itree_tstep_imp_to_asm_itree : tstep.

Local Hint Constants Transparent : tstep.
Local Ltac go := clear_itree; destruct_all?; simplify_eq/=.
Local Ltac go_i := tstep_i; intros; go.
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
  { split!; [econs|done]. } { done. }
  move => /= {σ1 σ2} {}n _ Hloop [[[σpa [[[σpi1 σi1] [t1 cs1]] σf1]] [[[σpi2 σi2] [t2 cs2]] σf2]] σfa].
  move => [[[σps [[[σpi σs1] σs2] σf]] [t cs]] σfs] /= ?.
  destruct_all?; simplify_eq.
  - go_s.
    go_i. invert_all asm_prod_filter.
    + go_s. eexists _; go. go_s. eexists _; go.
      go_s. split; [done|]; go.
      go_s => b; go.
      go_i. go_i. go_i. go_i.
      invert_all asm_prod_filter.
      go_i. eexists b; go. destruct b.
      * go_s => ?; go.
        go_s => ?; go.
        go_s => ?; go.
        go_s => Hin; go.
        go_s => Hf2i; go.
        go_s => /not_elem_of_union[??]; go.
        go_s => ?; go.
        go_s. go_s. go_s. go_s.
        move: Hin => /elem_of_union [Hf|Hf]. 2: {
          move: (Hf) => /Hin2[?[??]]. move: Hf2i => /lookup_union_Some_raw[?|[??]]; simplify_eq => //.
          exfalso. naive_solver.
        }
        move: (Hf) => /Hin1[f[??]].
        have ?: x = f. { move: Hf2i => /lookup_union_Some_raw[?|[??]]; simplify_eq => //. } subst.
        split!; [apply IPFCallExtToLeft|]. { done. } { by apply: Hdisjf. } simpl.
        split; [done|].
        go_i. eexists _; go.
        go_i. eexists _; go.
        go_i. eexists _; go.
        go_i. split; [done|]; go.
        go_i. split; [done|]; go.
        go_i. split; [done|]; go.
        go_i. split; [done|]; go.
        go_i. go_i. go_i.
        apply Hloop. split!; [by econs|done|done].
      * go_s => ?; go.
        go_s => ?; go.
        go_s => ?; go.
        go_s.
        go_s => ?; go.
        go_s.
        go_s => ?; go.
        go_s.
        go_s.
        revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
        inversion Hstack; simplify_eq/= => //.
        eexists _, _, _. split; [apply IPFReturnExtToLeft|]. simpl. split; [done|].
        go_i. eexists _; go. go_i. eexists _; go.
        go_i. eexists _; go. go_i. go_i. split; [done|]. go.
        go_i. go_i. split; [done|]. go.
        go_i. apply Hloop. by split!.
    + go_s. eexists _; go.
      go_s. eexists _; go.
      go_s. split; [done|]. go.
      go_s => b; go.
      go_i. go_i. go_i. go_i.
      invert_all asm_prod_filter.
      go_i. eexists b. go. destruct b.
      * go_s => ?; go.
        go_s => ?; go.
        go_s => ?; go.
        go_s => Hin; go.
        go_s => Hf2i; go.
        go_s => /not_elem_of_union[??]; go.
        go_s => ?; go.
        go_s. go_s. go_s. go_s.
        move: Hin => /elem_of_union [Hf|Hf]. 1: {
          move: (Hf) => /Hin1[?[??]]. move: Hf2i => /lookup_union_Some_raw[?|[??]]; simplify_eq => //.
        }
        move: (Hf) => /Hin2[f[??]].
        have ?: x = f. { move: Hf2i => /lookup_union_Some_raw[?|[??]]; simplify_eq => //. naive_solver. } subst.
        eexists _, _, _. split; [apply IPFCallExtToRight|]. { move => ?. by apply: Hdisjf. } { done. } simpl.
        split; [done|].
        go_i. eexists _; go.
        go_i. eexists _; go.
        go_i. eexists _; go.
        go_i. split; [done|]; go.
        go_i. split; [done|]; go.
        go_i. split; [done|]; go.
        go_i. split; [done|]; go.
        go_i. go_i. go_i.
        apply Hloop. split!; [by econs|done|done].
      * go_s => ?; go.
        go_s => ?; go.
        go_s => ?; go.
        go_s.
        go_s => ?; go.
        go_s.
        go_s => ?; go.
        go_s.
        go_s.
        revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
        inversion Hstack; simplify_eq/= => //.
        eexists _, _, _. split; [apply IPFReturnExtToRight|]. simpl. split; [done|].
        go_i. eexists _; go.
        go_i. eexists _; go.
        go_i. eexists _; go.
        go_i.
        go_i. split; [done|]; go.
        go_i.
        go_i. split; [done|]; go.
        go_i.
        apply Hloop. by split!.
  - tstep_both.
    apply steps_impl_step_end => κ Pσ2 ?. case_match; intros; go.
    + tstep_s. eexists (Some (EIRecvCall f vs)), _. split!; [econs|].
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop. by split!.
    + tstep_s. eexists None, _. split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop. by split!.
  - tstep_both.
    apply steps_impl_step_end => κ Pσ2 ?. case_match; intros; go.
    + tstep_s. eexists (Some (EIRecvReturn v)), _. split!; [econs|].
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop. by split!.
    + tstep_s. eexists None, _. split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop. by split!.
  - tstep_both.
    apply steps_impl_step_end => κ Pσ2 ? *. go. destruct κ as [e|]; go.
    + tend. have [σ' Hσ'] := vis_no_all _ _ _ ltac:(done). eexists σ'. split; [naive_solver|].
      go_i. go_i. go_i. destruct x1.
      * go_i. go_i. go_i. go_i. go_i. go_i.
        go_i. go_i. go_i. go_i. go_i.
        invert_all asm_prod_filter.
        -- go_i. go_i. go_i. go_i. invert_all asm_prod_filter.
           go_i. eexists true; go. go_i. eexists _; go.
           go_i. eexists _; go. go_i. eexists _; go.
           go_i. split; [ naive_solver|]. go. go_i. split; [naive_solver|]. go.
           go_i. split; [by apply: Hdisji|]. go. go_i. split; [done|]. go. go_i. go_i. go_i.
           go_s. eexists (Some _), _. split!; [econs; naive_solver|].
           apply: steps_spec_step_end; [done|] => ??.
           apply: Hloop. split!; [ naive_solver| by econs| done| done].
        -- go_s. eexists (Some _), _. split!; [apply IPFCallLeftToExt; naive_solver|].
           apply: steps_spec_step_end; [done|] => ??.
           go_s. eexists _; go. go_s. eexists _; go.
           go_s. eexists true; go. go_s. eexists _; go.
           go_s. eexists _; go. go_s. eexists _; go.
           go_s. split. { apply not_elem_of_union. naive_solver. } go.
           go_s. split. { apply lookup_union_Some_raw. naive_solver. } go.
           go_s. split; [apply elem_of_union; by left|]. go.
           go_s. split; [done|]. go. go_s. go_s. go_s. split; [done|]; go.
           go_s. split; [done|]. go.
           apply: Hloop. split!; [naive_solver|by econs|done].
      * go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i.
        invert_all asm_prod_filter.
        -- go_i. go_i. go_i. go_i.
           invert_all asm_prod_filter.
           revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
           inversion Hstack; simplify_eq/= => //.
           go_i. eexists false; go. go_i. eexists _; go.
           go_i. eexists _; go. go_i. eexists _; go. go_i. go_i. split;[done|]; go.
           go_i. go_i. split; [done|]; go. go_i.
           go_s. eexists (Some _), _. split!; [apply IPFReturnLeftToRight|].
           apply: steps_spec_step_end; [done|] => ??.
           apply: Hloop. split!; [naive_solver|done|done|done].
        -- revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
           inversion Hstack; simplify_eq/= => //.
           go_s. eexists (Some _), _. split!; [apply IPFReturnLeftToExt|].
           apply: steps_spec_step_end; [done|] => ??.
           go_s. eexists _; go. go_s. eexists _; go.
           go_s. eexists false; go. go_s. eexists _; go.
           go_s. eexists _; go. go_s. eexists _; go.
           go_s. go_s. split; [done|]. go. go_s. go_s. split; [done|]. go.
           go_s. split; [done|]. go. go_s. split; [done|]. go.
           apply: Hloop. split!; [naive_solver|done|done].
    + tstep_s. eexists None, _. split!.
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. by split!.
  - tstep_both.
    apply steps_impl_step_end => κ Pσ2 ?. case_match; intros; go.
    + tstep_s. eexists (Some (EIRecvCall f vs)), _. split!; [econs|].
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop. by split!.
    + tstep_s. eexists None, _. split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop. by split!.
  - tstep_both.
    apply steps_impl_step_end => κ Pσ2 ?. case_match; intros; go.
    + tstep_s. eexists (Some (EIRecvReturn v)), _. split!; [econs|].
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop. by split!.
    + tstep_s. eexists None, _. split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop. by split!.
  - tstep_both.
    apply steps_impl_step_end => κ Pσ2 ? *. go. destruct κ as [e|]; go.
    + tend. have [σ' Hσ'] := vis_no_all _ _ _ ltac:(done). eexists σ'. split; [naive_solver|].
      go_i. go_i. go_i. destruct x1.
      * go_i. go_i. go_i. go_i. go_i. go_i.
        go_i. go_i. go_i. go_i. go_i.
        invert_all asm_prod_filter.
        -- go_i. go_i. go_i. go_i. invert_all asm_prod_filter.
           go_i. eexists true; go. go_i. eexists _; go.
           go_i. eexists _; go. go_i. eexists _; go.
           go_i. split; [ naive_solver|]. go. go_i. split; [naive_solver|]. go.
           go_i. split. { move => ?. by apply: Hdisji. } go. go_i. split; [done|]. go. go_i. go_i. go_i.
           go_s. eexists (Some _), _. split!; [econs; naive_solver|].
           apply: steps_spec_step_end; [done|] => ??.
           apply: Hloop. split!; [ naive_solver| by econs| done| done].
        -- go_s. eexists (Some _), _. split!; [apply IPFCallRightToExt; naive_solver|].
           apply: steps_spec_step_end; [done|] => ??.
           go_s. eexists _; go. go_s. eexists _; go.
           go_s. eexists true; go. go_s. eexists _; go.
           go_s. eexists _; go. go_s. eexists _; go.
           go_s. split. { apply not_elem_of_union. naive_solver. } go.
           go_s. split. { apply lookup_union_Some_raw. destruct (f2i1 !! x2) eqn:?; naive_solver. } go.
           go_s. split; [apply elem_of_union; by right|]. go.
           go_s. split; [done|]. go. go_s. go_s. go_s. split; [done|]; go.
           go_s. split; [done|]. go.
           apply: Hloop. split!; [naive_solver|by econs|done].
      * go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i.
        invert_all asm_prod_filter.
        -- go_i. go_i. go_i. go_i.
           invert_all asm_prod_filter.
           revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
           inversion Hstack; simplify_eq/= => //.
           go_i. eexists false; go. go_i. eexists _; go.
           go_i. eexists _; go. go_i. eexists _; go. go_i. go_i. split;[done|]; go.
           go_i. go_i. split; [done|]; go. go_i.
           go_s. eexists (Some _), _. split!; [apply IPFReturnRightToLeft|].
           apply: steps_spec_step_end; [done|] => ??.
           apply: Hloop. split!; [naive_solver|done|done|done].
        -- revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
           inversion Hstack; simplify_eq/= => //.
           go_s. eexists (Some _), _. split!; [apply IPFReturnRightToExt|].
           apply: steps_spec_step_end; [done|] => ??.
           go_s. eexists _; go. go_s. eexists _; go.
           go_s. eexists false; go. go_s. eexists _; go.
           go_s. eexists _; go. go_s. eexists _; go.
           go_s. go_s. split; [done|]. go. go_s. go_s. split; [done|]. go.
           go_s. split; [done|]. go. go_s. split; [done|]. go.
           apply: Hloop. split!; [naive_solver|done|done].
    + tstep_s. eexists None, _. split!.
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. by split!.
Qed.

Inductive imp_to_asm_proof_stack (n : trace_index) (ins : gmap Z asm_instr) (fns : gmap string fndef) (f2i : gmap string Z) :
  bool → list expr_ectx → list (bool * Z * gmap string Z) → Prop :=
|IAPSNil :
  imp_to_asm_proof_stack n ins fns f2i false [] []
|IAPSStep c cs K' K'' rs ret K b:
  imp_to_asm_proof_stack n ins fns f2i b K cs →
  (∀ i rs' v t,
      rs' !! "PC" = Some ret →
      ins !! ret = Some i →
      imp_to_asm_ret rs' rs v →
      t ≈ (imp_to_asm_itree_to_env (dom (gset Z) ins) (dom (gset string) fns) f2i;;;;
              imp_to_asm_itree (dom (gset Z) ins) (dom (gset string) fns) f2i) →
      AsmState (Some i) rs' ins ⪯{asm_module, imp_to_asm imp_module, n, true}
               (SPLeft, Imp (expr_fill ((K' ++ K'') ++ K) v) fns, (t, c :: cs), SMProg)) →
  imp_to_asm_proof_stack n ins fns f2i true ((K' ++ K'') ++ K) ((true, ret, rs) :: c :: cs)
.


Lemma imp_to_asm_proof ins fns ins_dom fns_dom f2i :
  ins_dom = dom _ ins →
  fns_dom = dom _ fns →
  (∀ n i rs K f fn vs cs t pc ret,
      rs !! "PC" = Some pc →
      ins !! pc = Some i →
      fns !! f = Some fn →
      f2i !! f = Some pc →
      imp_to_asm_args ret rs vs →
      length vs = length (fd_args fn) →
      (* Call *)
      (∀ K' rs' f' es vs pc' i' ret' b t',
          Forall2 (λ e v, e = Val v) es vs →
          rs' !! "PC" = Some pc' →
          ins !! pc' = None →
          fns !! f' = None →
          f2i !! f' = Some pc' →
          imp_to_asm_args ret' rs' vs →
          ins !! ret' = Some i' →
          t' ≈ t →
          (∀ rs'' v t'',
              rs'' !! "PC" = Some ret' →
              imp_to_asm_ret rs'' rs' v →
              t'' ≈ t' →
              AsmState (Some i') rs'' ins ⪯{asm_module, imp_to_asm imp_module, n, false}
               (SPLeft, Imp (expr_fill K (expr_fill K' v)) fns, (t'', cs), SMProg)) →
          AsmState (Some []) rs' ins ⪯{asm_module, imp_to_asm imp_module, n, b}
               (SPLeft, Imp (expr_fill K (expr_fill K' (imp.Call f' es))) fns, (t', cs), SMProg)) →
      (* Return *)
      (∀ rs' v b t',
          rs' !! "PC" = Some ret →
          imp_to_asm_ret rs' rs v  →
          t' ≈ t →
          AsmState (Some []) rs' ins ⪯{asm_module, imp_to_asm imp_module, n, b}
               (SPLeft, Imp (expr_fill K v) fns, (t', cs), SMProg)) →
      AsmState (Some i) rs ins ⪯{asm_module, imp_to_asm imp_module, n, false}
               (SPLeft, Imp (expr_fill K (subst_l fn.(fd_args) vs fn.(fd_body))) fns, (t, cs), SMProg)
) →
  trefines (MS asm_module (initial_asm_state ins))
           (MS (imp_to_asm imp_module) (initial_imp_to_asm_state imp_module
             (initial_imp_state fns) ins_dom fns_dom f2i)).
Proof.
  move => -> -> Hf.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { simpl. exact: (λ n' '(AsmState i rs ins') '(σps, Imp e fns', (t, cs), σfs),
     ∃ K b, i = None ∧ ins = ins' ∧ σps = SPRight ∧ e = expr_fill K (Waiting b) ∧ fns = fns' ∧
              t ≈ imp_to_asm_itree (dom _ ins) (dom _ fns) f2i ∧ σfs = SMFilter ∧
              imp_to_asm_proof_stack n' ins fns f2i b K cs
). }
  { eexists []. split!; [done|]. econs. } {
    clear => /= n n' [???] [[[?[??]][??]]?] Hsub ?. destruct_all?; simplify_eq. split!; [done|].
    elim: H7 n' Hsub; [by econs|].
    move => *. econs; [ naive_solver..|]. move => *. apply: tsim_mono; [|done]. naive_solver.
  }
  move => {}n _ /= IH [i rs ins'] [[[?[??]][??]]?] ?. destruct_all?; simplify_eq/=.
  tstep_i => ?????.
  go_s.
  go_s. eexists _; go.
  go_s. eexists _; go.
  go_s. split; [done|]; go.
  go_s => -[]; go.
  - go_s => ?; go.
    go_s => ?; go.
    go_s => ?; go.
    go_s => /elem_of_dom[??]; go.
    go_s => ?; go.
    go_s => /not_elem_of_dom ?; go.
    go_s => ?; go.
    go_s. go_s. go_s. go_s. split!; [done|done|]. case_bool_decide; [|by go_s].
    match goal with | |- context [ReturnExt b ?e] => change (ReturnExt b e) with (expr_fill [ReturnExtCtx b] e) end.
    rewrite -expr_fill_app.
    apply: tsim_mono_b.
    apply: Hf; [done..| |].
    + move => K' rs' f' es vs pc i' ret' ? ? Hall ??????? Hret. go.
      have ?: es = Val <$> vs. { clear -Hall. elim: Hall; naive_solver. } subst.
      tstep_i => ??. simplify_map_eq. rewrite orb_true_r.
      go_s. right. split!.
      go_s. eexists _; go.
      go_s. eexists _; go.
      go_s. eexists true; go.
      go_s. eexists _; go.
      go_s. eexists _; go.
      go_s. eexists _; go.
      go_s. split; [by apply not_elem_of_dom|]; go.
      go_s. split; [done|]; go.
      go_s. split; [by apply elem_of_dom|]; go.
      go_s. split; [done|]; go.
      go_s. go_s.
      go_s. split; [done|]; go.
      go_s. split; [done|]; go.
      apply IH.
      split!; [done|].
      econs; [done|]. move => ????????. simplify_map_eq.
      rewrite !expr_fill_app /=.
      apply: tsim_mono_b.
      apply Hret; [done..|]. by etrans; [|done].
    + move => ???????. go.
      tstep_i => ??. simplify_map_eq. rewrite orb_true_r.
      go_s.
      go_s. eexists _; go.
      go_s. eexists _; go.
      go_s. eexists false; go.
      go_s. eexists _; go.
      go_s. eexists _; go.
      go_s. eexists _; go.
      go_s.
      go_s. split; [done|]; go.
      go_s.
      go_s. split; [done|]; go.
      go_s. split; [done|]; go.
      go_s. split; [done|]; go.
      apply IH. by split!.
  - go_s => ?; go.
    go_s => ?; go.
    go_s => ?; go.
    go_s.
    go_s => ?; go.
    go_s.
    go_s => ?; go.
    revert select (imp_to_asm_proof_stack _ _ _ _ _ _ _) => HK.
    inversion HK; clear HK; simplify_eq.
    go_s.
    go_s.
    split!; [done|].
    by apply: H6.
Qed.
