Require Export refframe.base.
Require Export refframe.axioms.

Inductive event (EV : Type) : Type :=
| Nb | Ub | Vis (e : EV).
Arguments Ub {_}.
Arguments Nb {_}.
Arguments Vis {_}.

Record module (EV : Type) : Type := {
  m_state : Type;
  m_step : m_state → option EV → (m_state → Prop) → Prop;
}.
Arguments m_state {_}.
Arguments m_step {_}.

Record mod_state EV := MS {
  ms_module : module EV;
  ms_state : ms_module.(m_state);
}.
Arguments MS {_}.
Arguments ms_module {_}.
Arguments ms_state {_}.
Coercion ms_module : mod_state >-> module.
