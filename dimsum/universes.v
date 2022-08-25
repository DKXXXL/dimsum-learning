From iris.algebra Require Import ofe.
From dimsum Require Import base.

Module Import universes.
  (** The universe of the state of modules. *)
  Universe State.
  (** The universe of events. *)
  Universe Event.
  (** The universe of ordinals. *)
  Universe Ordinal.
End universes.

Notation TypeState := Type@{State} (only parsing).
Notation TypeEvent := Type@{Event} (only parsing).
Notation TypeOrdinal := Type@{Ordinal} (only parsing).
Notation TypeOfe := Type@{ofe.u0} (only parsing).

Constraint State < Ordinal.
Constraint Ordinal <= ofe.u0.
