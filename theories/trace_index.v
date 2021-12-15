Require Import refframe.base.
Require Import refframe.axioms.

Inductive trace_index : Type :=
| tiO | tiS (n : trace_index) | tiChoice (T : Type) (f : T → trace_index).

Inductive ti_le : trace_index → trace_index → Prop :=
| ti_le_O n : ti_le tiO n
| ti_le_S_S n1 n2 : ti_le n1 n2 → ti_le (tiS n1) (tiS n2)
| ti_le_choice_l T f n : (∀ x, ti_le (f x) n) → ti_le (tiChoice T f) n
| ti_le_choice_r T f n x : ti_le n (f x) → ti_le n (tiChoice T f)
.
Global Instance ti_le_subseteq : SubsetEq trace_index := ti_le.
Global Instance ti_le_rewrite : RewriteRelation (ti_le) := {}.
Global Instance ti_le_equiv : Equiv trace_index := λ n1 n2, n1 ⊆ n2 ∧ n2 ⊆ n1.

Global Instance ti_le_preorder : PreOrder (⊆@{trace_index}).
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
Global Instance ti_equiv_equiv : Equivalence (≡@{trace_index}).
Proof.
  constructor.
  - done.
  - move => ?? [??]. done.
  - move => ??? [??] [??]. by split; etrans.
Qed.

Inductive ti_lt_alt : trace_index → trace_index → Prop :=
| ti_lt_O_S n : ti_lt_alt tiO (tiS n)
| ti_lt_S_S n1 n2 : ti_lt_alt n1 n2 → ti_lt_alt (tiS n1) (tiS n2)
| ti_lt_choice_l T f n : (∀ x, ti_lt_alt (f x) n) → ti_lt_alt (tiChoice T f) n
| ti_lt_choice_r T f n x : ti_lt_alt n (f x) → ti_lt_alt n (tiChoice T f)
.

Lemma ti_lt_alt_equiv n1 n2:
  n1 ⊂ n2 ↔ ti_lt_alt n1 n2.
Proof.
  split.
  - move => [Hle Hnle]. elim: Hle Hnle.
    + elim.
      * done.
      * econs.
      * move => ?? IH Hnle. admit.
    + move => ??? IH Hnle. econstructor. apply: IH. contradict Hnle. by constructor.
    + move => ???? IH Hnle. econs => ?. apply: IH. contradict Hnle. by econs.
    + move => ????? IH Hnle.
      (* TODO: the negation causes problems *)
  (* econs. apply: IH. contradict Hnle. econs. *)
      admit.
  - elim.
    + move => ?. split; [by econs| ] => Ht. inversion Ht.
    + move => ??? [IHle IHnle]. split; [by econs|] => Hs. inversion Hs; simplify_eq. naive_solver.
    + move => ???? IH. split. { econs. admit. } move => ?. admit.
    +
Admitted.

Lemma tiChoice_mono T f1 f2:
  (∀ x, f1 x ⊆ f2 x) →
  tiChoice T f1 ⊆ tiChoice T f2.
Proof. move => ?. econs. econs. naive_solver. Qed.

Fixpoint ti_min (n1 : trace_index) : trace_index → trace_index :=
  fix go n2 :=
  match n1, n2 with
  | tiChoice T f, _ => tiChoice T (λ x, ti_min (f x) n2)
  | _, tiChoice T f => tiChoice T (λ x, go (f x))
  | tiO, _ => tiO
  | _, tiO => tiO
  | tiS n1', tiS n2' => tiS (ti_min n1' n2')
  end.

Lemma ti_min_choice_l_1 T f n :
  tiChoice T (λ x, ti_min (f x) n) ⊆ ti_min (tiChoice T f) n.
Proof. by destruct n. Qed.
Lemma ti_min_choice_l_2 T f n :
  ti_min (tiChoice T f) n ⊆ tiChoice T (λ x, ti_min (f x) n).
Proof. by destruct n. Qed.

Lemma ti_min_choice_r_1 T f n :
  tiChoice T (λ x, ti_min n (f x)) ⊆ ti_min n (tiChoice T f).
Proof.
  elim: n => //=.
  move => T' f' IH. econs => x.
  destruct (f x) eqn: Hx => //=; econs => ?; rewrite -Hx.
  all: econs; (etrans; [|by apply: IH]); by econs.
Qed.

Lemma ti_min_choice_r_2 T f n :
  ti_min n (tiChoice T f) ⊆ tiChoice T (λ x, ti_min n (f x)).
Proof.
  elim: n => //=.
  move => T' f' IH. econs => x'. etrans; [apply: IH|].
  apply tiChoice_mono => x.
  by destruct (f x) eqn: Hx => //=; rewrite -Hx; econs.
Qed.

Lemma ti_min_mono n m n' m':
  n ⊆ n' →
  m ⊆ m' →
  ti_min n m ⊆ ti_min n' m'.
Proof.
  move => Hn. elim: Hn m m' => /=; clear.
  - move => n m m' Hm. elim: Hm n => //=; clear.
    + econs.
    + econs.
    + move => ???? IH ?. econs => ?. apply: IH.
    + move => ????? IH ?. rewrite -ti_min_choice_r_1. econs. apply: IH.
  - move => n1 n2 _ IH m m' Hm. elim: Hm.
    + econs.
    + econs. by apply: IH.
    + move => ???? IH2. econs => ?. apply: IH2.
    + move => ????? IH2. econs. apply: IH2.
  - move => T f n ? IH m m' Hm. destruct m; econs => ?; by apply: IH.
  - move => T f n x ? IH m m' Hm. destruct m'; econs; by apply: IH.
Qed.

Global Instance ti_mono_proper :
  Proper ((⊆) ==> (⊆) ==> (⊆)) ti_min.
Proof. move => ??????. by apply: ti_min_mono. Qed.
Global Instance ti_mono_flip_proper :
  Proper (flip (⊆) ==> flip (⊆) ==> flip (⊆)) ti_min.
Proof. move => ??????. by apply: ti_min_mono. Qed.
Global Instance ti_mono_equiv_proper :
  Proper ((≡) ==> (≡) ==> (≡)) ti_min.
Proof. move => ?? [Hn1 Hn2] ?? [Hm1 Hm2]. split; by apply: ti_min_mono. Qed.

Lemma ti_min_comm_1 n m:
  ti_min n m ⊆ ti_min m n.
Proof.
  elim: n m => /=.
  - elim => //= ?? IH. apply tiChoice_mono => ?. apply: IH.
  - move => n IH m.
    elim: m.
    + econs.
    + move => ??. econs. apply: IH.
    + move => ?? IH2. apply tiChoice_mono => ?. apply: IH2.
  - move => ?? IH m. rewrite -ti_min_choice_r_1.
    destruct m; apply tiChoice_mono => ?; apply: IH.
Qed.

Lemma ti_min_comm n m:
  ti_min n m ≡ ti_min m n.
Proof. split; apply ti_min_comm_1. Qed.

Lemma ti_min_assoc_1 n m p:
  ti_min n (ti_min m p) ⊆ ti_min (ti_min n m) p.
Proof.
  elim: n m p.
  - simpl. elim => //=.
    + elim => // ?? IH. apply tiChoice_mono => ?. apply: IH.
    + move => n IH. elim => // ?? IH2. apply tiChoice_mono => ?. apply: IH2.
    + move => T f IH. case => *; apply tiChoice_mono => ?; apply: IH.
  - move => n IH m /=.
    elim: m.
    + elim => //= ?? IH2. apply tiChoice_mono => ?; apply: IH2.
    + move => m IH2.
      elim => //= *.
      * econs. apply: IH.
      * apply tiChoice_mono => ?; naive_solver.
    + move => T f IH2 /= p. destruct p; apply tiChoice_mono => ?; apply: IH2.
  - move => T f IH m p. rewrite !ti_min_choice_l_2. rewrite -!ti_min_choice_l_1.
    by apply tiChoice_mono => ?.
Qed.

Lemma ti_min_assoc_2 n m p:
  ti_min (ti_min n m) p ⊆ ti_min n (ti_min m p).
Proof. by rewrite (ti_min_comm_1 n m) ti_min_comm_1 ti_min_assoc_1 (ti_min_comm_1 p m) ti_min_comm_1. Qed.

Lemma ti_min_assoc n m p:
  ti_min n (ti_min m p) ≡ ti_min (ti_min n m) p.
Proof. split; [apply ti_min_assoc_1 | apply ti_min_assoc_2 ]. Qed.

Lemma ti_min_le_l n m:
  ti_min n m ⊆ n.
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

Lemma ti_min_le_r n m:
  ti_min n m ⊆ m.
Proof. etrans; [apply ti_min_comm_1|]. apply ti_min_le_l. Qed.

Lemma ti_min_l_2 n m:
  n ⊆ m → n ⊆ ti_min n m.
Proof.
  elim => /=; clear.
  - econs.
  - move => ????. by econs.
  - move => ?? m ? IH. econs => ?. destruct m; econs; apply: IH.
  - move => ?? n ?? IH. rewrite -ti_min_choice_r_1. by econs.
Qed.

Lemma ti_min_l n m:
  n ⊆ m → ti_min n m ≡ n.
Proof. move => Hn. split; [apply ti_min_le_l | by apply ti_min_l_2]. Qed.

Lemma ti_min_r_2 n m:
  m ⊆ n → m ⊆ ti_min n m.
Proof. move => ?. etrans; [by apply ti_min_l_2|]. apply ti_min_comm. Qed.

Lemma ti_min_r n m:
  m ⊆ n → ti_min n m ≡ m.
Proof. move => Hn. split; [apply ti_min_le_r | by apply ti_min_r_2]. Qed.

Lemma ti_min_id n:
  ti_min n n ≡ n.
Proof. by apply ti_min_l. Qed.

Lemma ti_lt_impl_le (n1 n2 : trace_index):
  n1 ⊂ n2 →
  n1 ⊆ n2.
Proof. move => [??]. done. Qed.

Lemma ti_le_S n:
  n ⊆ tiS n.
Proof.
  elim: n.
  - econs.
  - by econs.
  - move => ?? IH. constructor => ?. etrans; [apply: IH|]. econs. by econs.
Qed.

Lemma ti_not_le_S n:
  tiS n ⊈ n.
Proof.
  elim: n.
  - inversion 1.
  - move => ??. inversion 1; simplify_eq. naive_solver.
  - move => ?? IH. inversion 1; simplify_K.
    apply: IH. etrans; [|done]. econs. by econs.
Qed.

Lemma ti_lt_S n:
  n ⊂ tiS n.
Proof. split; [apply: ti_le_S | apply: ti_not_le_S]. Qed.

Lemma ti_le_lt_S n1 n2:
  n1 ⊂ tiS n2 →
  n1 ⊆ n2.
Proof.
  elim: n1 n2.
  - move => ??. econs.
  - move => ? IH ? [Hle ?]. inversion Hle; simplify_eq. admit.
  - move => ?? IH ? [Hle Hnle]. inversion Hle; simplify_K. constructor => ?.
    apply: IH. split; [naive_solver|]. move => ?. apply: Hnle. by econs.
Admitted.

Lemma ti_le_lt_S' n1 n2:
  ti_lt_alt n1 n2 →
  tiS n1 ⊆ n2.
Proof.
  elim.
  - move => ?. econs. econs.
  - move => ????. by econs.
  - move => ?? n _. elim: n.
    (* This is not provable! *)
Admitted.

Lemma ti_lt_le (n1 n2 n3 : trace_index):
  n1 ⊂ n2 → n2 ⊆ n3 → n1 ⊂ n3.
Proof. move => [Hle1 Hnle] Hle. split; [by etrans|]. move => ?. apply: Hnle. by etrans. Qed.

Lemma ti_lt_wf : wf (⊂@{trace_index}).
Proof.
  have H : forall n a : trace_index, a ⊂ n -> Acc (⊂) a; last first.
  { move => n. apply: (H (tiS n)). apply ti_lt_S. }
  elim.
  - move => a [? Hnot]. contradict Hnot. econs.
  - move => n IH a Hs. constructor => ??. apply: IH. apply: ti_lt_le; [done|]. by apply ti_le_lt_S.
  - move => T f IH a [Hle Hnle].
    (* inversion Hle; simplify_K. *)
    (* + admit. *)
    (* + admit. *)
    (* + apply: IH. split; [done|]. contradict Hnle. constructor => ?. *)
Admitted.
