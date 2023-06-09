From dimsum.core Require Import module.

(** * [lrefines] *)
(** [lrefines] is a notion of refinement that models behaviors as sets
of lists and correponds (roughly) to trace refinement on alternating automata. *)

(**
Compare the definition below to
https://swt.informatik.uni-freiburg.de/teaching/SS2013/AutomataTheory/Resources/Slides/alternatingfiniteautomata-seminarslides-pascalraiola.pdf

The transition function g : Q × Σ × 2^Q → 2 is extended to a
function g : Q × Σ∗ × 2^Q → 2 as follows:
g(s, ε, u) = u_s , and
g(s, aw, u) = g(s, a, λ s', g (s', w , u)).

g(s, ε, u) = u_s corresponds to

      σ ∈ Pσ
-------------------
σ ~{ m , [] }~>ₗ Pσ

g(s, aw, u) = g(s, a, λ s', g (s', w, u)). corresponds to

σ -{a}-> (λ σ', σ' ~{ m , w }~>ₗ Pσ)
-------------------
σ ~{ m , a::w }~>ₗ Pσ

(σ -{a}-> Pσ is m.(m_step) σ (Some a) Pσ)

σ -{a}-> (λ σ', σ' ~{ m , w }~>ₗ Pσ)
is equivalent to the following that the definition of [σ ~{m, w}~>ₗ Pσ] below is using
∃ Pσ', σ -{a}-> Pσ' ∧ (Pσ' ⊆ σ ~{ m , w }~>ₗ Pσ)
assuming that σ -{a}-> Pσ is covariant in Pσ.

Our formulation makes σ ~{ m , w }~>ₗ Pσ covariant even when σ -{a}-> Pσ is not which is nice for technical reasons.
It is unclear how much this difference matters.
Modulo this difference and the fact that we have silent steps whereas the reference has not, the two seems the same.
Or compare to the definition in Section 2.3 of Alternating Automata and Program Verification.
[σ ~{m, w}~>ₗ Pσ] could correspond to the notion of "run", i.e. labeled tree.
(There are some difference, like all states in our setting are accepting and we only look at finite words.
But they don't seems essential.)

*)

Inductive lhas_trace {EV} (m : mod_trans EV) :
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

Record lrefines {EV} (mimpl mspec : module EV) : Prop := {
  lref_subset:
    ∀ κs, mimpl.(m_init) ~{ mimpl.(m_trans), κs }~>ₗ - →
          mspec.(m_init) ~{ mspec.(m_trans), κs }~>ₗ -
}.

Global Instance lrefines_preorder EV : PreOrder (@lrefines EV).
Proof.
  constructor.
  - constructor => // κ Hi; naive_solver.
  - move => ??? [Hr1] [Hr2]. constructor => /=. naive_solver.
Qed.
