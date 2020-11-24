Require Import Coq.Logic.EqdepFacts.

Module Ax : EqdepElimination.

Axiom eq_rect_eq :
    forall (U:Type) (p:U) (Q:U -> Type) (x:Q p) (h:p = p),
      x = eq_rect p Q x p h.

End Ax.

Module Export UIPM := EqdepTheory Ax.
