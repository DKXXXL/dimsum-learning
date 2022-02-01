Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.link.
Require Import refframe.seq_product.
Require Import refframe.state_transform.
Require Import refframe.proof_techniques.

Set Default Proof Using "Type".

(** * prepost *)
Inductive prepost {R : Type} : Type :=
| pp_end (r : R)
| pp_prop (P : Prop) (pp : prepost)
| pp_quant {T} (pp : T → prepost)
.
Arguments prepost : clear implicits.

Fixpoint pp_to_ex {R} (pp : prepost R) (Q : R → Prop) : Prop :=
  match pp with
  | pp_end r => Q r
  | pp_prop P pp' => P ∧ pp_to_ex pp' Q
  | pp_quant pp' => ∃ x, pp_to_ex (pp' x) Q
  end.

Fixpoint pp_to_all {R} (pp : prepost R) (Q : R → Prop) : Prop :=
  match pp with
  | pp_end r => Q r
  | pp_prop P pp' => P → pp_to_all pp' Q
  | pp_quant pp' => ∀ x, pp_to_all (pp' x) Q
  end.

Lemma pp_to_ex_exists {R} pp Q:
  @pp_to_ex R pp Q ↔ ∃ r, Q r ∧ pp_to_ex pp (r =.).
Proof. elim: pp => /=; naive_solver. Qed.

Lemma pp_to_all_ex {R} pp Q1 Q2:
  @pp_to_all R pp Q1 →
  pp_to_ex pp Q2 →
  ∃ r, Q1 r ∧ Q2 r.
Proof. elim: pp => /=; naive_solver. Qed.

(** * mod_prepost *)
Section prepost.
  Context {EV1 EV2 S : Type}.
  Implicit Types (i : EV2 → S → prepost (EV1 * S)) (o : EV1 → S → prepost (EV2 * S)).
  Implicit Types (m : module EV1).

  Inductive pp_state : Type :=
  | PPOutside
  | PPRecv1 (e : EV2)
  | PPRecv2 (e : EV1)
  | PPInside
  | PPSend1 (e : EV1)
  | PPSend2 (e : EV2)
  .

  Inductive pp_filter_step i o :
    (pp_state * S) → option (EV1 + EV2) → ((pp_state * S) → Prop) → Prop :=
  | PPOutsideS s e:
    pp_filter_step i o (PPOutside, s) (Some (inr e)) (λ σ, σ = (PPRecv1 e, s))
  | PPRecv1S s e:
    pp_filter_step i o (PPRecv1 e, s) None (λ σ, pp_to_ex (i e s) (λ r, σ = (PPRecv2 r.1, r.2)))
  | PPRecv2S s e:
    pp_filter_step i o (PPRecv2 e, s) (Some (inl e)) (λ σ, σ = (PPInside, s))
  | PPInsideS s e:
    pp_filter_step i o (PPInside, s) (Some (inl e)) (λ σ, σ = (PPSend1 e, s))
  | PPSend1S s e r:
    pp_to_ex (o e s) (r=.) →
    pp_filter_step i o (PPSend1 e, s) None (λ σ, σ = (PPSend2 r.1, r.2))
  | PPSend2S s e:
    pp_filter_step i o (PPSend2 e, s) (Some (inr e)) (λ σ, σ = (PPOutside, s))
  .

  Definition mod_prepost_filter i o :=
    Mod (pp_filter_step i o).

  Global Instance mod_prepost_filter_vis_no_all i o : VisNoAll (mod_prepost_filter i o).
  Proof. move => ????. invert_all @m_step; naive_solver. Qed.

  Definition mod_prepost i o m : module EV2 :=
    mod_seq_map m (mod_prepost_filter i o).

  Global Instance mod_prepost_vis_no_all i o m `{!VisNoAll m}: VisNoAll (mod_prepost i o m).
  Proof. apply _. Qed.

  Lemma mod_prepost_trefines i o m m' σ σ' σm s `{!VisNoAll m}:
    trefines (MS m σ) (MS m' σ') →
    trefines (MS (mod_prepost i o m) (σm, σ, s)) (MS (mod_prepost i o m') (σm, σ', s)).
  Proof.
    move => ?. apply mod_seq_map_trefines => //. apply _.
  Qed.

  Lemma mod_prepost_step_Outside_i i o m σ s:
    TStepI (mod_prepost i o m) (SMFilter, σ, (PPOutside, s)) (λ G,
        ∀ e, G true (Some e) (λ G', G' (SMFilter, σ, (PPRecv1 e, s)))).
  Proof.
    constructor => G /= ?. tstep_i.
    apply steps_impl_step_end => ???. invert_all @m_step => ???. split! => ?. split!; [naive_solver|done|].
    naive_solver.
  Qed.

  Lemma mod_prepost_step_Recv1_i i o m σ s e:
    TStepI (mod_prepost i o m) (SMFilter, σ, (PPRecv1 e, s)) (λ G,
        pp_to_ex (i e s) (λ r, G true None (λ G', G' (SMProgRecv r.1, σ, (PPInside, r.2))))).
  Proof.
    constructor => G /= /pp_to_ex_exists[r [HG Hex]]. tstep_i.
    apply steps_impl_step_next => ???. invert_all @m_step.
    eexists (_, _). split!. { apply pp_to_ex_exists. naive_solver. }
    apply steps_impl_step_end => ???. invert_all @m_step => ???. naive_solver.
  Qed.

  Lemma mod_prepost_step_Inside_i i o m σ s e:
    TStepI (mod_prepost i o m) (SMFilterRecv e, σ, (PPInside, s)) (λ G,
        pp_to_all (o e s) (λ r, G true (Some (r.1)) (λ G', G' (SMFilter, σ, (PPOutside, r.2))))).
  Proof.
    constructor => G /= ?. apply steps_impl_step_trans. tstep_i.
    apply steps_impl_step_end => ???. invert_all @m_step => ? b *; simplify_eq. split! => ?. split!; [done|].
    tstep_i.
    apply steps_impl_step_next => ???. invert_all @m_step => *; simplify_eq. split!.
    apply steps_impl_step_end => ???. invert_all @m_step => *; simplify_eq. split! => ?.
    have [?[??]]:= pp_to_all_ex _ _ _ ltac:(done) ltac:(done); subst.
    split!; [done|by destruct b|]. naive_solver.
  Qed.

  Lemma mod_prepost_step_Outside_s i o m σ s:
    TStepS (mod_prepost i o m) (SMFilter, σ, (PPOutside, s)) (λ G,
        ∃ e, G (Some e) (λ G', G' (SMFilter, σ, (PPRecv1 e, s)))).
  Proof.
    constructor => G /= [??]. split!; [done|] => /= ??. tstep_s. eexists (Some (inr _)). split!; [done|].
    apply: steps_spec_step_end; [by econs|]. naive_solver.
  Qed.


  Lemma mod_prepost_step_Recv1_s i o m σ s e:
    TStepS (mod_prepost i o m) (SMFilter, σ, (PPRecv1 e, s)) (λ G,
        G None (λ G', pp_to_all (i e s) (λ r, G' (SMProgRecv r.1, σ, (PPInside, r.2))))).
  Proof.
    constructor => G /= ?. split!; [done|] => /= ??. apply steps_spec_step_trans.
    tstep_s. eexists None. split!.
    apply: steps_spec_step_end; [by econs|] => ? /=?.
    have [?[??]]:= pp_to_all_ex _ _ _ ltac:(done) ltac:(done); subst.
    tstep_s. eexists (Some (inl _)). split!.
    apply: steps_spec_step_end; [by econs|]. naive_solver.
  Qed.

  Lemma mod_prepost_step_Inside_s i o m σ s e:
    TStepS (mod_prepost i o m) (SMFilterRecv e, σ, (PPInside, s)) (λ G,
        pp_to_ex (o e s) (λ r, G (Some (r.1)) (λ G', G' (SMFilter, σ, (PPOutside, r.2))))).
  Proof.
    constructor => G /= /pp_to_ex_exists[?[??]]. split!; [done|] => /= ??.
    apply steps_spec_step_trans. tstep_s. eexists (Some _). split!.
    apply: steps_spec_step_end; [by econs|] => /= ? ->. tstep_s. eexists (Some (inr _)). split!; [done|].
    apply: steps_spec_step; [by econs|] => /= ? ->.
    apply: steps_spec_step_end; [by econs|] => /= ? ->.
    done.
  Qed.
End prepost.

Global Hint Resolve
       mod_prepost_step_Outside_i
       mod_prepost_step_Recv1_i
       mod_prepost_step_Inside_i
       mod_prepost_step_Outside_s
       mod_prepost_step_Recv1_s
       mod_prepost_step_Inside_s
 | 3 : tstep.
