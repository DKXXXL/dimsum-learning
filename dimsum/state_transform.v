From dimsum.core Require Export proof_techniques.

(** * state transform *)
Inductive state_transform_step {EV S} (m : mod_trans EV) (R : S → m.(m_state) → Prop) :
  S → option EV → (S → Prop) → Prop :=
| StateTransformStep σ σ' e Pσ:
  m.(m_step) σ' e Pσ →
  R σ σ' →
  state_transform_step m R σ e (λ σ'', ∃ σ''', R σ'' σ''' ∧ Pσ σ''').

Definition state_transform_trans {EV S} (m : mod_trans EV) (R : S → m.(m_state) → Prop) :=
  ModTrans (state_transform_step m R).

Lemma mod_state_transform_vis_no_all {EV S} (m : mod_trans EV) (R : S → m.(m_state) → Prop) `{!VisNoAng m}:
  (∀ σ e Pσ σ'', m_step m σ (Some e) Pσ → Pσ σ'' → ∃ σs, ∀ σs', R σs' σ'' ↔ σs = σs') →
  VisNoAng (state_transform_trans m R).
Proof.
  move => Hs ????. inv_all @m_step.
  have [σ'' Hσ'']:= vis_no_all _ _ _ ltac:(done).
  have [σs Hσs]:= Hs _ _ _ _ ltac:(done) ltac:(naive_solver).
  eexists σs. naive_solver.
Qed.

Definition state_transform_mod {EV S} (m : module EV) (R : S → m.(m_trans).(m_state) → Prop) σ :=
  Mod (state_transform_trans m.(m_trans) R) σ.

Lemma mod_state_transform_nil {EV S} (m : mod_trans EV) (R : S → m.(m_state) → Prop) σ σ' (Pσ Pσ' : _ → Prop):
  σ' ~{ m, tnil }~>ₜ Pσ' →
  R σ σ' →
  (∀ σ σ', Pσ' σ' → R σ σ' → Pσ σ) →
  σ ~{ state_transform_trans m R, tnil }~>ₜ Pσ.
Proof.
  move => /thas_trace_nil_inv. have : @tnil EV ⊆ tnil by done. move: {1 3}(tnil) => κs Hnil Ht.
  elim: Ht σ Pσ Hnil; clear. { tend. naive_solver. }
  move => σ' Pσ' Pσ'' κ κs κs' Hstep ? IH Hsub σ Pσ Hnil HR Hend. rewrite -Hsub in Hnil.
  destruct κ; [by inversion Hnil|]; simplify_eq/=.
  tstep_None; [by econs|] => ?/=[?[??]].
  apply: IH; naive_solver.
Qed.

Lemma state_transform_mod_trefines {EV S1 S2} (m1 m2 : module EV) (R1 : S1 → m1.(m_trans).(m_state) → Prop) (R2 : S2 → m2.(m_trans).(m_state) → Prop) σ1 σ2:
  (∀ σ1 σ σ', R1 σ1 σ → R1 σ1 σ' → σ = σ') →
  (∀ σ1 σ σ' κ Pσ, m_step m1.(m_trans) σ κ Pσ → Pσ σ' → R1 σ1 σ → ∃ σ'', R1 σ'' σ') →
  trefines m1 m2 →
  R1 σ1 m1.(m_init) →
  R2 σ2 m2.(m_init) →
  trefines (state_transform_mod m1 R1 σ1) (state_transform_mod m2 R2 σ2).
Proof.
  destruct m1 as [m1 σ1'], m2 as [m2 σ2']. simplify_eq/=.
  move => Heq Hstep Href HR1 HR2.
  apply wp_implies_refines => n.
  move: Href => /wp_complete/(_ n)/=.
  elim/o_lt_ind: n σ1 σ2 σ1' σ2' HR1 HR2 => n IH σ1 σ2 σ1' σ2' HR1 HRc2 Hwp.
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

Lemma state_transform_tstep_s {EV S} (m : mod_trans EV) (f : S → m.(m_state)) σ P `{!TStepS m (f σ) P} :
  TStepS (state_transform_trans m (λ σ σ', σ' = f σ)) σ (λ G, P (λ κ P', G κ (λ G', P' (λ σ', ∀ σ, σ' = f σ → G' σ)))).
Proof.
  move: TStepS0 => [HStep].
  constructor => G /HStep [κ [? [? HG']]]. split!; [done|] => ? /= /HG'/steps_spec_has_trace_1 Ht.
  apply steps_spec_has_trace_elim. apply: mod_state_transform_nil; [done..|].
  move => ?? /= ??; subst. case_match; destruct!.
  - apply: steps_spec_step_end; [by econs|] => /= ? [?[??]]. naive_solver.
  - apply: steps_spec_end. naive_solver.
Qed.
Global Hint Resolve state_transform_tstep_s | 20 : typeclass_instances.
