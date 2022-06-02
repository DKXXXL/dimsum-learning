Require Export refframe.module.
Require Export refframe.axioms.

(*
Compare this to
https://swt.informatik.uni-freiburg.de/teaching/SS2013/AutomataTheory/Resources/Slides/alternatingfiniteautomata-seminarslides-matthiashengel.pdf

The transition function g : Q × Σ × 2^Q → 2 is extended to a
function g : Q × Σ∗ × 2^Q → 2 as follows:
g(s, ε, u) = u_s , and
g(s, aw, u) = g(s, a, g (s, w , u)).

g(s, ε, u) = u_s corresponds to

      σ ∈ Pσ
-------------------
σ ~{ m , [] }~>ₗ Pσ

g(s, aw, u) = g(s, a, g (s, w, u)). corresponds to

σ -{a}-> (σ ~{ m , w }~>ₗ Pσ)
-------------------
σ ~{ m , a::w }~>ₗ Pσ

(σ -{a}-> Pσ is m.(m_step) σ (Some a) Pσ)

σ -{a}-> (σ ~{ m , w }~>ₗ Pσ)
is equivalent to
∃ Pσ', σ -{a}-> Pσ' ∧ (Pσ' ⊆ σ ~{ m , w }~>ₗ Pσ)

assuming that σ -{a}-> Pσ is covariant in Pσ.
Our formulation makes σ ~{ m , w }~>ₗ Pσ covariant when σ -{a}-> Pσ which is nice for technical reasons,
but should not really matter.

*)

Inductive lhas_trace {EV} (m : module EV) :
  m.(m_state) → list EV → (m.(m_state) → Prop) → Prop :=
| LTraceEnd σ (Pσ : _ → Prop):
    Pσ σ →
    lhas_trace m σ [] Pσ
| LTraceStep σ1 Pσ2 Pσ3 κ κs κs':
    m.(m_step) σ1 κ Pσ2 →
    (∀ σ2, Pσ2 σ2 → lhas_trace m σ2 κs Pσ3) →
    κs' = option_list κ ++ κs →
    lhas_trace m σ1 κs' Pσ3
.
Notation " σ '~{' m , κs '}~>ₗ' P " := (lhas_trace m σ κs P) (at level 40).
Notation " σ '~{' m , κs '}~>ₗ' - " := (lhas_trace m σ κs (λ _, True)) (at level 40).

Record lrefines {EV} (mimpl mspec : mod_state EV) : Prop := {
  lref_subset:
    ∀ κs, mimpl.(ms_state) ~{ mimpl, κs }~>ₗ - →
          mspec.(ms_state) ~{ mspec, κs }~>ₗ -
}.

Global Instance lrefines_preorder EV : PreOrder (@lrefines EV).
Proof.
  constructor.
  - constructor => // κ Hi; naive_solver.
  - move => ??? [Hr1] [Hr2]. constructor => /=. naive_solver.
Qed.
