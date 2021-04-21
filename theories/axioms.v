Require Import Coq.Logic.EqdepFacts.
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
