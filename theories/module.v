Require Export refframe.base.
Require Export refframe.axioms.

Inductive event (EV : Type) : Type :=
| Nb | Ub | Vis (e : EV).
Arguments Ub {_}.
Arguments Nb {_}.
Arguments Vis {_}.

Record module (EV : Type) : Type := Mod {
  m_state : Type;
  m_step : m_state → option EV → (m_state → Prop) → Prop;
}.
Arguments m_state {_}.
Arguments m_step {_}.
Arguments Mod {_ _}.
Add Printing Constructor module.

Record mod_state EV := MS {
  ms_module : module EV;
  ms_state : ms_module.(m_state);
}.
Arguments MS {_}.
Arguments ms_module {_}.
Arguments ms_state {_}.
Add Printing Constructor mod_state.

Coercion ms_module : mod_state >-> module.

Class VisNoAll {EV} (m : module EV) : Prop :=
  vis_no_all σ κ Pσ : m.(m_step) σ (Some κ) Pσ → ∃ σ', ∀ σ'', Pσ σ'' ↔ σ'' = σ'.

Inductive io_type : Set :=
| Incoming | Outgoing.

Definition io_event (EV : Type) : Type := io_type * EV.

Inductive player :=
| Prog | Env.
Global Instance player_eq_dec : EqDecision player.
Proof. solve_decision. Qed.

Definition opponent (p : player) : player :=
  match p with
  | Prog => Env
  | Env => Prog
  end.
