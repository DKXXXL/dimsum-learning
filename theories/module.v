Require Import refframe.base.

Inductive steps {A B} (R : A → list B → A → Prop) : A → list B → A → Prop :=
| steps_refl ρ :
    steps R ρ [] ρ
| steps_l ρ1 ρ2 ρ3 κ κs :
    R ρ1 κ ρ2 →
    steps R ρ2 κs ρ3 →
    steps R ρ1 (κ ++ κs) ρ3.

Record module := {
  m_state : Type;
  m_event : Type;
  m_initial : m_state → Prop;
  m_step : m_state → list m_event → m_state → Prop;
  (* This cannot be defined based on m_step since m_state might e.g. contain a threadpool
     and a state should be bad if any thread is stuck. *)
  m_good : m_state → Prop;
}.

Definition safe (m : module) : Prop :=
  ∀ σ κ σ', m.(m_initial) σ → steps m.(m_step) σ κ σ' → m.(m_good) σ'.

Record refines (mimpl mspec : module) (trans_initial : mimpl.(m_state) → mspec.(m_state)) (trans_event : mimpl.(m_event) → mspec.(m_event)) := {
  ref_initial σ : mimpl.(m_initial) σ → mspec.(m_initial) (trans_initial σ);
  ref_step σ κ σi:
    safe mspec →
    mimpl.(m_initial) σ →
    steps mimpl.(m_step) σ κ σi →
    mimpl.(m_good) σi ∧ ∃ σs, steps mspec.(m_step) (trans_initial σ) (trans_event <$> κ) σs;
}.

Lemma refines_preserves_safe mspec mimpl ti te:
  safe mspec →
  refines mimpl mspec ti te →
  safe mimpl.
Proof. move => Hs Hr σ κ σ' Hinit Hstep. by move: (ref_step _ _ _ _ Hr _ _ _ Hs Hinit Hstep) => [?[??]]. Qed.

Lemma refines_vertical m1 m2 m3 ti1 te1 ti2 te2:
  refines m1 m2 ti1 te1 →
  refines m2 m3 ti2 te2 →
  refines m1 m3 (ti2 ∘ ti1) (te2 ∘ te1).
Proof.
  move => Hr1 Hr2.
  constructor; first by destruct Hr1, Hr2; eauto.
  move => σ κ σi Hsafe3 Hinit1 Hstep1 /=. rewrite list_fmap_compose.
  have Hsafe2 := refines_preserves_safe _ _ _ _ Hsafe3 Hr2.
  have [Hgood [σ2 Hstep2]] := (ref_step _ _ _ _ Hr1 _ _ _ Hsafe2 Hinit1 Hstep1). split => //.
  have [|_ [σ3 Hstep3]] := (ref_step _ _ _ _ Hr2 _ _ _ Hsafe3 _ Hstep2); eauto using ref_initial.
Qed.
