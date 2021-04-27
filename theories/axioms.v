Require Import Coq.Logic.ChoiceFacts.
Require Import Coq.Logic.EqdepFacts.
Require Export Coq.Logic.FunctionalExtensionality.
Require Import refframe.base.

Module Ax : EqdepElimination.

Axiom eq_rect_eq :
    forall (U:Type) (p:U) (Q:U -> Type) (x:Q p) (h:p = p),
      x = eq_rect p Q x p h.

End Ax.

Module UIPM := EqdepTheory Ax.

Ltac simplify_K :=
  repeat match goal with
  | H : existT _ _ = existT _ _ |- _ =>
     apply UIPM.inj_pair2 in H
  end; simplify_eq.


Axiom AxCHOICE : ∀ A B, FunctionalChoice_on A B.

Axiom EM : ∀ P : Prop, LEM P.

Lemma CHOICE {A B} {P : _ → Prop} {R}:
  (∀ x : A, P x → ∃ y : B, R x y) → ∃ f : {x : A | P x} → B, ∀ x (H : P x), R x (f (exist _ x H)).
Proof.
  move => HP.
  have [f Hf]:= AxCHOICE {x | P x} _ (λ '(exist _ x _) t, R x t ) (λ '(exist _ x p), HP x p).
  eexists f => x H. by have := Hf (exist _ x H).
Qed.

Lemma CHOICE2 {A1 A2 B} {P1 P2 : _ → Prop} {R}:
  (∀ (x1 : A1) (x2 : A2), P1 x1 → P2 x2 → ∃ y : B, R x1 x2 y) →
  ∃ f : {x : A1 | P1 x} → {x : A2 | P2 x} → B, ∀ x1 x2 (H1 : P1 x1) H2, R x1 x2 (f (exist _ x1 H1) (exist _ x2 H2)).
Proof.
  move => HP.
  have [|f Hf]:= @CHOICE (A1 * A2) B (λ x, P1 x.1 ∧ P2 x.2) (λ x y, R x.1 x.2 y). naive_solver.
  eexists (λ '(exist _ x1 H1) '(exist _ x2 H2), f (exist _ (x1, x2) _)).
  Unshelve. 2: { simpl in *.  split. done. done. }
  move => ????. apply: (Hf (_, _)).
Qed.
