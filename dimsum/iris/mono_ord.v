From iris.algebra Require Export cmra local_updates proofmode_classes auth.
From iris.algebra Require Import updates.
From iris.prelude Require Import options.
From dimsum.core Require Export ordinal.

(** This file is based min_nat in iris/algebra/numbers.v and mono_nat in iris/algebra/lib/mono_nat.v . *)

(** ** Ordinals with [min] as the operation. *)
Record min_ord := MinOrd { min_ord_car : ordinal }.
Add Printing Constructor min_ord.

Global Instance min_ord_equiv : Equiv min_ord := λ x y, min_ord_car x ≡ min_ord_car y.
Global Instance min_ord_equivalence : Equivalence (≡@{min_ord}).
Proof. constructor => ? *; unfold equiv, min_ord_equiv in *; [done| done | by etrans ]. Qed.
Global Instance MinOrd_proper : Proper ((≡) ==> (≡)) MinOrd.
Proof. move => ???. done. Qed.

Canonical Structure min_ordO := discreteO min_ord.

Section min_ord.
  Local Instance min_ord_unit_instance : Unit min_ord := MinOrd (oChoice Empty_set (λ x, match x with end)) .
  Local Instance min_ord_valid_instance : Valid min_ord := λ x, True.
  Local Instance min_ord_validN_instance : ValidN min_ord := λ n x, True.
  Local Instance min_ord_pcore_instance : PCore min_ord := Some.
  Local Instance min_ord_op_instance : Op min_ord := λ n m, MinOrd (o_min (min_ord_car n) (min_ord_car m)).
  Definition min_ord_op_min x y : MinOrd x ⋅ MinOrd y = MinOrd (o_min x y) := eq_refl.

  Lemma min_ord_included (x y : min_ord) : x ≼ y ↔ min_ord_car y ⊆ min_ord_car x.
  Proof.
    split.
    - intros [z [-> ?]]. simpl. apply o_min_le_l.
    - exists y. rewrite /op /min_ord_op_instance. symmetry. by apply o_min_r.
  Qed.
  Lemma min_ord_ra_mixin : RAMixin min_ord.
  Proof.
    apply ra_total_mixin; apply _ || eauto.
    - intros [x] [?] [?] Heq. rewrite !min_ord_op_min. rewrite /equiv/min_ord_equiv/= in Heq. by rewrite Heq.
    - intros [x] [y] [z]. repeat rewrite min_ord_op_min. by apply o_min_assoc.
    - intros [x] [y]. rewrite !min_ord_op_min. apply o_min_comm.
    - intros [x]. rewrite min_ord_op_min. apply o_min_id.
  Qed.
  Canonical Structure min_ordR : cmra := discreteR min_ord min_ord_ra_mixin.

  Global Instance min_ord_cmra_discrete : CmraDiscrete min_ordR.
  Proof. apply discrete_cmra_discrete. Qed.

  Global Instance min_ord_cmra_total : CmraTotal min_ordR.
  Proof. move => ?. done. Qed.

  Global Instance min_ord_core_id (x : min_ord) : CoreId x.
  Proof. by constructor. Qed.

  Lemma min_ord_local_update (x y x' : min_ord) :
    min_ord_car x' ⊆ min_ord_car x → (x,y) ~l~> (x',x').
  Proof.
    move: x y x' => [x] [y] [x'] /= Hle.
    rewrite local_update_discrete. move=> [[z]|] _ /=; last done.
    rewrite 2!min_ord_op_min. intros [Heq1 Heq2]; simpl in *.
    split; first done. rewrite ->Heq1 in Hle.
    split => /=.
    - apply o_min_l_2. rewrite Hle. apply o_min_le_r.
    - apply o_min_le_l.
  Qed.

  Global Instance : LeftAbsorb (≡) (MinOrd oO) (⋅).
  Proof. move => [x]. rewrite min_ord_op_min. apply o_min_l. constructor. Qed.

  Global Instance : RightAbsorb (≡) (MinOrd oO) (⋅).
  Proof. move => [x]. rewrite min_ord_op_min. apply o_min_r. constructor. Qed.

  Global Instance : IdemP (≡@{min_ord}) (⋅).
  Proof. intros [x]. rewrite min_ord_op_min. apply o_min_id. Qed.

  Global Instance min_ord_is_op x y :
    IsOp (MinOrd (o_min x y)) (MinOrd x) (MinOrd y).
  Proof. done. Qed.
End min_ord.

(** Authoritative CMRA over [min_ord]. The authoritative element is a
monotonically decreasing ord, while a fragment is a upper bound. *)

Definition mono_ord   := auth (optionUR min_ordR).
Definition mono_ordR  := authR (optionUR min_ordR).
Definition mono_ordUR := authUR (optionUR min_ordR).

(** [mono_ord_auth] is the authoritative element. The definition includes the
fragment at the same value so that lemma [mono_ord_included], which states that
[mono_ord_ub n ≼ mono_ord_auth q n], does not require a frame-preserving
update. *)
Definition mono_ord_auth (q : Qp) (n : ordinal) : mono_ord :=
  ●{#q} Some (MinOrd n) ⋅ ◯ Some (MinOrd n).
Definition mono_ord_ub (n : ordinal) : mono_ord := ◯ Some (MinOrd n).

Section mono_ord.
  Implicit Types (n : ordinal).

  Global Instance mono_ord_ub_core_id n : CoreId (mono_ord_ub n).
  Proof. apply _. Qed.

  Lemma mono_ord_auth_frac_op q1 q2 n :
    mono_ord_auth q1 n ⋅ mono_ord_auth q2 n ≡ mono_ord_auth (q1 + q2) n.
  Proof.
    rewrite /mono_ord_auth -dfrac_op_own auth_auth_dfrac_op.
    rewrite (comm _ (●{#q2} _)) -!assoc (assoc _ (◯ _)).
    by rewrite -core_id_dup (comm _ (◯ _)).
  Qed.

  Lemma mono_ord_ub_op n1 n2 :
    mono_ord_ub n1 ⋅ mono_ord_ub n2 = mono_ord_ub (o_min n1 n2).
  Proof. rewrite -auth_frag_op -Some_op min_ord_op_min //. Qed.

  Lemma mono_ord_auth_ub_op q n :
    mono_ord_auth q n ≡ mono_ord_auth q n ⋅ mono_ord_ub n.
  Proof.
    rewrite /mono_ord_auth /mono_ord_ub.
    rewrite -!assoc -auth_frag_op -Some_op min_ord_op_min.
    do 3 f_equiv. symmetry. apply o_min_id.
  Qed.

  (** rephrasing of [mono_ord_ub_op] useful for weakening a fragment to a
  larger upper-bound *)
  Lemma mono_ord_ub_op_le_l n n' :
    n ⊆ n' →
    mono_ord_ub n ≡ mono_ord_ub n' ⋅ mono_ord_ub n.
  Proof. intros. rewrite mono_ord_ub_op /mono_ord_ub. do 2 f_equiv. symmetry. by apply o_min_r. Qed.

  Lemma mono_ord_auth_frac_valid q n : ✓ mono_ord_auth q n ↔ (q ≤ 1)%Qp.
  Proof.
    rewrite /mono_ord_auth auth_both_dfrac_valid_discrete /=. naive_solver.
  Qed.
  Lemma mono_ord_auth_valid n : ✓ mono_ord_auth 1 n.
  Proof. by apply auth_both_valid. Qed.

  Lemma mono_ord_auth_frac_op_valid q1 q2 n1 n2 :
    ✓ (mono_ord_auth q1 n1 ⋅ mono_ord_auth q2 n2) ↔ (q1 + q2 ≤ 1)%Qp ∧ n1 ≡ n2.
  Proof.
    rewrite /mono_ord_auth (comm _ (●{#q2} _)) -!assoc (assoc _ (◯ _)).
    rewrite -auth_frag_op (comm _ (◯ _)) assoc -Some_op. split.
    - move=> /cmra_valid_op_l /auth_auth_dfrac_op_valid => -[? [/(inj _ _ _) ??]]. naive_solver.
    - intros [? ->]. rewrite -core_id_dup -auth_auth_dfrac_op.
      by apply auth_both_dfrac_valid_discrete.
  Qed.
  Lemma mono_ord_auth_op_valid n1 n2 :
    ✓ (mono_ord_auth 1 n1 ⋅ mono_ord_auth 1 n2) ↔ False.
  Proof. rewrite mono_ord_auth_frac_op_valid. naive_solver. Qed.

  Lemma mono_ord_both_frac_valid q n m :
    ✓ (mono_ord_auth q n ⋅ mono_ord_ub m) ↔ (q ≤ 1)%Qp ∧ n ⊆ m.
  Proof.
    rewrite /mono_ord_auth /mono_ord_ub -assoc -auth_frag_op -Some_op.
    rewrite auth_both_dfrac_valid_discrete Some_included_total min_ord_included /=.
    split.
    - move => [?[??]]. split; [done|]. etrans; [done|]. apply o_min_le_r.
    - move => [??]. split; [done|]. split; [|done]. by apply o_min_l_2.
  Qed.
  Lemma mono_ord_both_valid n m :
    ✓ (mono_ord_auth 1 n ⋅ mono_ord_ub m) ↔ n ⊆ m.
  Proof. rewrite mono_ord_both_frac_valid. naive_solver. Qed.

  Lemma mono_ord_ub_mono n1 n2 : n2 ⊆ n1 → mono_ord_ub n1 ≼ mono_ord_ub n2.
  Proof. intros. by apply auth_frag_mono, Some_included_2, min_ord_included. Qed.

  Lemma mono_ord_included q n : mono_ord_ub n ≼ mono_ord_auth q n.
  Proof. apply cmra_included_r. Qed.

  Lemma mono_ord_update {n} n' :
    n' ⊆ n →
    mono_ord_auth 1 n ~~> mono_ord_auth 1 n'.
  Proof.
    intros. rewrite /mono_ord_auth /mono_ord_ub.
    by apply auth_update, option_local_update, min_ord_local_update.
  Qed.
End mono_ord.

Global Typeclasses Opaque mono_ord_auth mono_ord_ub.
