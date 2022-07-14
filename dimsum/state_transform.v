From dimsum.core Require Export proof_techniques.

(*** state transform *)
Inductive state_transform_step {EV S} (m : module EV) (R : S → m.(m_state) → Prop) :
  S → option EV → (S → Prop) → Prop :=
| StateTransformStep σ σ' e Pσ:
  m.(m_step) σ' e Pσ →
  R σ σ' →
  state_transform_step m R σ e (λ σ'', ∃ σ''', R σ'' σ''' ∧ Pσ σ''').

Definition mod_state_transform {EV S} (m : module EV) (R : S → m.(m_state) → Prop) :=
  Mod (state_transform_step m R).

Lemma mod_state_transform_vis_no_all {EV S} (m : module EV) (R : S → m.(m_state) → Prop) `{!VisNoAll m}:
  (∀ σ e Pσ σ'', m_step m σ (Some e) Pσ → Pσ σ'' → ∃ σs, ∀ σs', R σs' σ'' ↔ σs = σs') →
  VisNoAll (mod_state_transform m R).
Proof.
  move => Hs ????. inv_all @m_step.
  have [σ'' Hσ'']:= vis_no_all _ _ _ ltac:(done).
  have [σs Hσs]:= Hs _ _ _ _ ltac:(done) ltac:(naive_solver).
  eexists σs. naive_solver.
Qed.

Lemma mod_state_transform_nil {EV S} (m : module EV) (R : S → m.(m_state) → Prop) σ σ' (Pσ Pσ' : _ → Prop):
  σ' ~{ m, tnil }~>ₜ Pσ' →
  R σ σ' →
  (∀ σ σ', Pσ' σ' → R σ σ' → Pσ σ) →
  σ ~{ mod_state_transform m R, tnil }~>ₜ Pσ.
Proof.
  move => /thas_trace_nil_inv. have : @tnil EV ⊆ tnil by done. move: {1 3}(tnil) => κs Hnil Ht.
  elim: Ht σ Pσ Hnil; clear. { tend. naive_solver. }
  move => σ' Pσ' Pσ'' κ κs κs' Hstep ? IH Hsub σ Pσ Hnil HR Hend. rewrite -Hsub in Hnil.
  destruct κ; [by inversion Hnil|]; simplify_eq/=.
  tstep_None; [by econs|] => ?/=[?[??]].
  apply: IH; naive_solver.
Qed.

Lemma mod_state_transform_trefines {EV S1 S2} (m1 m2 : module EV) (R1 : S1 → m1.(m_state) → Prop) (R2 : S2 → m2.(m_state) → Prop) σ1' σ1 σ2 σ2':
  (∀ σ1 σ σ', R1 σ1 σ → R1 σ1 σ' → σ = σ') →
  (∀ σ1 σ σ' κ Pσ, m_step m1 σ κ Pσ → Pσ σ' → R1 σ1 σ → ∃ σ'', R1 σ'' σ') →
  trefines (MS m1 σ1') (MS m2 σ2') →
  R1 σ1 σ1' →
  R2 σ2 σ2' →
  trefines (MS (mod_state_transform m1 R1) σ1) (MS (mod_state_transform m2 R2) σ2).
Proof.
  move => Heq Hstep Href HR1 HR2.
  apply wp_implies_refines => n.
  move: Href => /wp_complete/(_ n)/=.
  elim/ti_lt_ind: n σ1 σ2 σ1' σ2' HR1 HR2 => n IH σ1 σ2 σ1' σ2' HR1 HRc2 Hwp.
  apply Wp_step => Pσ n' κ ??. inv_all @m_step.
  inversion Hwp as [??? Hwp']; simplify_eq.
  have ?: σ' = σ1' by naive_solver. subst σ'.
  have [Pσ' [Ht HPσ]]:= Hwp' _ _ _ ltac:(done) ltac:(done).
  destruct κ; simplify_eq/=.
  - move: Ht => /(thas_trace_cons_inv _ _ _)?.
    apply: (thas_trace_trans tnil); [apply: mod_state_transform_nil; [done..|]|move => ? H'; apply H'].
    move => ?? [? [? HP']] ?.
    tstep_Some; [by econs|] => /= ? [?[? /HP'?]].
    apply: mod_state_transform_nil; [done..|] => ??/HPσ[?[??]]?.
    have [??]:= Hstep _ _ _ _ _ ltac:(done) ltac:(done) ltac:(done).
    eexists _. split; [naive_solver|].
    by apply: IH.
  - apply: mod_state_transform_nil; [done..|] => ??/HPσ[?[??]]?.
    have [??]:= Hstep _ _ _ _ _ ltac:(done) ltac:(done) ltac:(done).
    eexists _. split; [naive_solver|].
    by apply: IH.
Qed.

Lemma mod_state_transform_tstep_s {EV S} (m : module EV) (f : S → m.(m_state)) σ P `{!TStepS m (f σ) P} :
  TStepS (mod_state_transform m (λ σ σ', σ' = f σ)) σ (λ G, P (λ κ P', G κ (λ G', P' (λ σ', ∀ σ, σ' = f σ → G' σ)))).
Proof.
  move: TStepS0 => [HStep].
  constructor => G /HStep [κ [? [? HG']]]. split!; [done|] => ? /= /HG'/steps_spec_has_trace_1 Ht.
  apply steps_spec_has_trace_elim. apply: mod_state_transform_nil; [done..|].
  move => ?? /= ??; subst. case_match; destruct!.
  - apply: steps_spec_step_end; [by econs|] => /= ? [?[??]]. naive_solver.
  - apply: steps_spec_end. naive_solver.
Qed.
Global Hint Resolve mod_state_transform_tstep_s | 20 : typeclass_instances.
