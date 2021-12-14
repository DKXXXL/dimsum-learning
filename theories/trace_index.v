Require Import refframe.base.
Require Import refframe.axioms.

Inductive trace_index : Type :=
| tiO | tiS (n : trace_index) | tiChoice (T : Type) (f : T → trace_index).

Inductive ti_le : trace_index → trace_index → Prop :=
| ti_le_O n : ti_le tiO n
| ti_le_S_S n1 n2 : ti_le n1 n2 → ti_le (tiS n1) (tiS n2)
(* | ti_le_choice_r T f n : (∀ x, ti_le n (f x)) → ti_le n (tiChoice T f) *)
(* | ti_le_choice_l T f n x : ti_le (f x) n → ti_le (tiChoice T f) n *)
| ti_le_choice_l T f n : (∀ x, ti_le (f x) n) → ti_le (tiChoice T f) n
| ti_le_choice_r T f n x : ti_le n (f x) → ti_le n (tiChoice T f)
.
Global Instance ti_le_subseteq : SubsetEq trace_index := ti_le.
Global Instance ti_le_rewrite : RewriteRelation (ti_le) := {}.
Global Instance ti_le_equiv : Equiv trace_index := λ n1 n2, ti_le n1 n2 ∧ ti_le n2 n1.

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
