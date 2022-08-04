From dimsum.core Require Import base axioms.

(** * [ordinal] *)
(** This file defines the [ordinal] type, which is a form of
ordinal and used as a step index. *)

Inductive ordinal : Type :=
| oO | oS (n : ordinal) | oChoice (T : Type) (f : T → ordinal).

Inductive o_le : ordinal → ordinal → Prop :=
| o_le_O n : o_le oO n
| o_le_S_S n1 n2 : o_le n1 n2 → o_le (oS n1) (oS n2)
| o_le_choice_l T f n : (∀ x, o_le (f x) n) → o_le (oChoice T f) n
| o_le_choice_r T f n x : o_le n (f x) → o_le n (oChoice T f)
.
Global Instance o_le_subseteq : SubsetEq ordinal := o_le.
Global Instance o_le_rewrite : RewriteRelation (o_le) := {}.
Global Instance o_le_equiv : Equiv ordinal := λ n1 n2, n1 ⊆ n2 ∧ n2 ⊆ n1.

Global Instance o_le_preorder : PreOrder (⊆@{ordinal}).
Proof.
  constructor.
  - move => n. elim: n.
    + constructor.
    + by constructor.
    + econs => ?. econs. naive_solver.
  - move => x y z Hx. elim: Hx z.
    + constructor.
    + move => ????. elim.
      * inversion 1.
      * move => ? IH Hs. inversion_clear Hs; simplify_eq. constructor. naive_solver.
      * move => ?? IH Hs. inversion Hs; simplify_K. econs. naive_solver.
    + move => ???????. econs. naive_solver.
    + move => ??????. elim.
      * inversion 1; simplify_K. naive_solver.
      * move => ? IH Hs. inversion Hs; simplify_K. naive_solver.
      * move => ?? IH Hs. inversion Hs; simplify_K.
        -- naive_solver.
        -- econs. naive_solver.
Qed.
Global Instance o_equiv_equiv : Equivalence (≡@{ordinal}).
Proof.
  constructor.
  - done.
  - move => ?? [??]. done.
  - move => ??? [??] [??]. by split; etrans.
Qed.

Lemma oChoice_mono T f1 f2:
  (∀ x, f1 x ⊆ f2 x) →
  oChoice T f1 ⊆ oChoice T f2.
Proof. move => ?. econs. econs. naive_solver. Qed.

Lemma o_le_choice_inv n T f:
  oS n ⊆ oChoice T f → ∃ x: T, oS n ⊆ (f x).
Proof.
  inversion 1; subst. eexists. done.
Qed.

Definition oS_maybe (b : bool) (n : ordinal) :=
  if b then oS n else n.
Notation "'oS?' b n" := (oS_maybe b n)
  (at level 20, b at level 9, n at level 20, right associativity, format "'oS?' b  n").

Fixpoint o_min (n1 : ordinal) : ordinal → ordinal :=
  fix go n2 :=
  match n1, n2 with
  | oChoice T f, _ => oChoice T (λ x, o_min (f x) n2)
  | _, oChoice T f => oChoice T (λ x, go (f x))
  | oO, _ => oO
  | _, oO => oO
  | oS n1', oS n2' => oS (o_min n1' n2')
  end.

Lemma o_min_choice_l_1 T f n :
  oChoice T (λ x, o_min (f x) n) ⊆ o_min (oChoice T f) n.
Proof. by destruct n. Qed.
Lemma o_min_choice_l_2 T f n :
  o_min (oChoice T f) n ⊆ oChoice T (λ x, o_min (f x) n).
Proof. by destruct n. Qed.

Lemma o_min_choice_r_1 T f n :
  oChoice T (λ x, o_min n (f x)) ⊆ o_min n (oChoice T f).
Proof.
  elim: n => //=.
  move => T' f' IH. econs => x.
  destruct (f x) eqn: Hx => //=; econs => ?; rewrite -Hx.
  all: econs; (etrans; [|by apply: IH]); by econs.
Qed.

Lemma o_min_choice_r_2 T f n :
  o_min n (oChoice T f) ⊆ oChoice T (λ x, o_min n (f x)).
Proof.
  elim: n => //=.
  move => T' f' IH. econs => x'. etrans; [apply: IH|].
  apply oChoice_mono => x.
  by destruct (f x) eqn: Hx => //=; rewrite -Hx; econs.
Qed.

Lemma o_min_mono n m n' m':
  n ⊆ n' →
  m ⊆ m' →
  o_min n m ⊆ o_min n' m'.
Proof.
  move => Hn. elim: Hn m m' => /=; clear.
  - move => n m m' Hm. elim: Hm n => //=; clear.
    + econs.
    + econs.
    + move => ???? IH ?. econs => ?. apply: IH.
    + move => ????? IH ?. rewrite -o_min_choice_r_1. econs. apply: IH.
  - move => n1 n2 _ IH m m' Hm. elim: Hm.
    + econs.
    + econs. by apply: IH.
    + move => ???? IH2. econs => ?. apply: IH2.
    + move => ????? IH2. econs. apply: IH2.
  - move => T f n ? IH m m' Hm. destruct m; econs => ?; by apply: IH.
  - move => T f n x ? IH m m' Hm. destruct m'; econs; by apply: IH.
Qed.

Global Instance o_mono_proper :
  Proper ((⊆) ==> (⊆) ==> (⊆)) o_min.
Proof. move => ??????. by apply: o_min_mono. Qed.
Global Instance o_mono_flip_proper :
  Proper (flip (⊆) ==> flip (⊆) ==> flip (⊆)) o_min.
Proof. move => ??????. by apply: o_min_mono. Qed.
Global Instance o_mono_equiv_proper :
  Proper ((≡) ==> (≡) ==> (≡)) o_min.
Proof. move => ?? [Hn1 Hn2] ?? [Hm1 Hm2]. split; by apply: o_min_mono. Qed.

Lemma o_min_comm_1 n m:
  o_min n m ⊆ o_min m n.
Proof.
  elim: n m => /=.
  - elim => //= ?? IH. apply oChoice_mono => ?. apply: IH.
  - move => n IH m.
    elim: m.
    + econs.
    + move => ??. econs. apply: IH.
    + move => ?? IH2. apply oChoice_mono => ?. apply: IH2.
  - move => ?? IH m. rewrite -o_min_choice_r_1.
    destruct m; apply oChoice_mono => ?; apply: IH.
Qed.

Lemma o_min_comm n m:
  o_min n m ≡ o_min m n.
Proof. split; apply o_min_comm_1. Qed.

Lemma o_min_assoc_1 n m p:
  o_min n (o_min m p) ⊆ o_min (o_min n m) p.
Proof.
  elim: n m p.
  - simpl. elim => //=.
    + elim => // ?? IH. apply oChoice_mono => ?. apply: IH.
    + move => n IH. elim => // ?? IH2. apply oChoice_mono => ?. apply: IH2.
    + move => T f IH. case => *; apply oChoice_mono => ?; apply: IH.
  - move => n IH m /=.
    elim: m.
    + elim => //= ?? IH2. apply oChoice_mono => ?; apply: IH2.
    + move => m IH2.
      elim => //= *.
      * econs. apply: IH.
      * apply oChoice_mono => ?; naive_solver.
    + move => T f IH2 /= p. destruct p; apply oChoice_mono => ?; apply: IH2.
  - move => T f IH m p. rewrite !o_min_choice_l_2. rewrite -!o_min_choice_l_1.
    by apply oChoice_mono => ?.
Qed.

Lemma o_min_assoc_2 n m p:
  o_min (o_min n m) p ⊆ o_min n (o_min m p).
Proof. by rewrite (o_min_comm_1 n m) o_min_comm_1 o_min_assoc_1 (o_min_comm_1 p m) o_min_comm_1. Qed.

Lemma o_min_assoc n m p:
  o_min n (o_min m p) ≡ o_min (o_min n m) p.
Proof. split; [apply o_min_assoc_1 | apply o_min_assoc_2 ]. Qed.

Lemma o_min_le_l n m:
  o_min n m ⊆ n.
Proof.
  elim: n m => /=.
  - elim => // ?? IH. econs => ?. apply: IH.
  - move => n IH m.
    elim: m.
    + econs.
    + move => ??. econs. apply: IH.
    + move => ?? IH2. econs => ?. apply: IH2.
  - move => ?? IH m. destruct m; econs => ?; econs; apply: IH.
Qed.

Lemma o_min_le_r n m:
  o_min n m ⊆ m.
Proof. etrans; [apply o_min_comm_1|]. apply o_min_le_l. Qed.

Lemma o_min_l_2 n m:
  n ⊆ m → n ⊆ o_min n m.
Proof.
  elim => /=; clear.
  - econs.
  - move => ????. by econs.
  - move => ?? m ? IH. econs => ?. destruct m; econs; apply: IH.
  - move => ?? n ?? IH. rewrite -o_min_choice_r_1. by econs.
Qed.

Lemma o_min_l n m:
  n ⊆ m → o_min n m ≡ n.
Proof. move => Hn. split; [apply o_min_le_l | by apply o_min_l_2]. Qed.

Lemma o_min_r_2 n m:
  m ⊆ n → m ⊆ o_min n m.
Proof. move => ?. etrans; [by apply o_min_l_2|]. apply o_min_comm. Qed.

Lemma o_min_r n m:
  m ⊆ n → o_min n m ≡ m.
Proof. move => Hn. split; [apply o_min_le_r | by apply o_min_r_2]. Qed.

Lemma o_min_id n:
  o_min n n ≡ n.
Proof. by apply o_min_l. Qed.

Lemma o_le_S n:
  n ⊆ oS n.
Proof.
  elim: n.
  - econs.
  - by econs.
  - move => ?? IH. constructor => ?. etrans; [apply: IH|]. econs. by econs.
Qed.

Lemma o_le_S_maybe n b:
  n ⊆ oS?b n.
Proof. destruct b => //. apply o_le_S. Qed.

Lemma oS_maybe_orb n b1 b2:
  oS?(b1 || b2) n ⊆ oS?b1 (oS?b2 n).
Proof. destruct b1, b2 => //=. apply o_le_S. Qed.

Lemma oS_maybe_mono n1 n2 (b1 b2 : bool):
  (b1 → b2) →
  n1 ⊆ n2 →
  oS?b1 n1 ⊆ oS?b2 n2.
Proof.
  destruct b1,b2 => /= ??. { by econs. } { naive_solver. } { etrans; [apply o_le_S|] => /=. by econs. } { done. }
Qed.

Lemma o_lt_impl_le (n1 n2 : ordinal):
  oS n1 ⊆ n2 →
  n1 ⊆ n2.
Proof. move => <-. apply o_le_S. Qed.

Lemma o_not_le_S n:
  oS n ⊈ n.
Proof.
  elim: n.
  - inversion 1.
  - move => ??. inversion 1; simplify_eq. naive_solver.
  - move => ?? IH. inversion 1; simplify_K.
    apply: IH. etrans; [|done]. econs. by econs.
Qed.

Lemma o_lt_S n:
  n ⊂ oS n.
Proof. split; [apply: o_le_S | apply: o_not_le_S]. Qed.

Lemma o_lt_ind (P : ordinal → Prop):
  (∀ x : ordinal, (∀ y : ordinal, oS y ⊆ x → P y) → P x) → ∀ a, P a.
Proof.
  move => HP.
  have : ∀ a n : ordinal, oS n ⊆ a → P n; last first.
  { move => Ha a. apply: HP => ??. by apply: Ha. }
  elim.
  - move => ?. inversion 1.
  - move => n IH n'. inversion 1; simplify_eq. apply: HP. move => ??. apply: IH. etrans; [done|]. done.
  - move => ?? IH n. inversion 1; simplify_eq; simplify_K. apply: HP => ??. apply: IH.
    etrans; [|done]. etrans; [done|]. apply o_le_S.
Qed.
