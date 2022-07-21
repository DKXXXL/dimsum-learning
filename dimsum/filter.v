From dimsum.core Require Export proof_techniques.
From dimsum.core Require Import srefines.
From dimsum.core Require Import axioms.

(** * filter *)

Inductive filter_step {EV1 EV2} (m : mod_trans EV1) (R : EV1 → option EV2 → Prop) :
  m.(m_state) → option EV2 → (m.(m_state) → Prop) → Prop :=
| FilterStep σ e e' Pσ:
    m.(m_step) σ e Pσ →
    (* TODO: is there a better way to formulate this? E.g. assume
    that there is no R None None Some in the theorem? *)
    (if e is Some κ then R κ e' else e' = None) →
    filter_step m R σ e' Pσ.

Definition filter_trans {EV1 EV2} (m : mod_trans EV1) (R : EV1 → option EV2 → Prop) : mod_trans EV2 :=
  ModTrans (filter_step m R).

Global Instance filter_vis_no_all {EV1 EV2} (m : mod_trans EV1) (R : EV1 → option EV2 → Prop) `{!VisNoAll m}:
  VisNoAll (filter_trans m R).
Proof. move => *. inv_all/= @m_step; case_match; simplify_eq. by apply: vis_no_all. Qed.

Definition filter_mod {EV1 EV2} (m : module EV1) (R : EV1 → option EV2 → Prop) :=
  Mod (filter_trans m.(m_trans) R) m.(m_init).

(** ** trefines for [mod_filter] *)
Fixpoint trace_bind {EV1 EV2} (f : EV1 → trace EV2) (κs : trace EV1) : trace EV2 :=
  match κs with
  | tnil => tnil
  | tcons κ κs => tapp (f κ) (trace_bind f κs)
  | tex T f' => tex T (λ x, trace_bind f (f' x))
  | tall T f' => tall T (λ x, trace_bind f (f' x))
  end.

Lemma trace_bind_mono {EV1 EV2} (f : EV1 → trace EV2) κs1 κs2 :
  κs1 ⊆ κs2 →
  trace_bind f κs1 ⊆ trace_bind f κs2.
Proof.
  elim => //=.
  - move => ?????. by apply: tapp_mono.
  - move => ?????. constructor. naive_solver.
  - move => ?????. econstructor. naive_solver.
  - move => ??????. econstructor. naive_solver.
  - move => ??????. econstructor. naive_solver.
Qed.


Definition filtered_trace {EV1 EV2} (R : EV1 → option EV2 → Prop)
  : trace EV1 → trace EV2 :=
  trace_bind (λ κ, tall ({ κ' | R κ κ'}) (λ x, option_trace (`x))).

Lemma filtered_trace_mono {EV1 EV2} (R : EV1 → option EV2 → Prop) κs1 κs2 :
  κs1 ⊆ κs2 →
  filtered_trace R κs1 ⊆ filtered_trace R κs2.
Proof. apply trace_bind_mono. Qed.

Lemma tmod_filter_to_mod {EV1 EV2} (m : mod_trans EV1) (R : EV1 → option EV2 → Prop) σi Pσ κs:
  σi ~{ filter_trans m R, κs }~>ₜ Pσ →
  ∃ κs', filtered_trace R κs' ⊆ κs ∧ σi ~{ m, κs' }~>ₜ Pσ.
Proof.
  elim.
  - move => ?????. eexists tnil => /=. split; [done|]. by constructor.
  - move => ??? κ ?? Hstep ? IH Hs.
    inversion Hstep; simplify_eq.
    have [f Hf]:= AxChoice1 IH.
    eexists (tapp (option_trace e) (tex _ f)). split.
    + etrans; [|done].
      destruct e => /=; simplify_option_eq.
      * rewrite /filtered_trace/=-/(filtered_trace _).
        apply: (subtrace_all_l (exist _ _ _)); [done|] => ?.
        apply: tapp_mono; [done|].
        constructor => -[??]. naive_solver.
      * rewrite /filtered_trace/=-/(filtered_trace _).
        constructor => -[??]. naive_solver.
    + apply: TTraceStep; [done | |done].
      move => ??/=. eapply thas_trace_ex. naive_solver.
      Unshelve. done.
  - move => T f ???? IH ?.
    have [fx Hfx]:= AxChoice _ _ _ IH.
    eexists (tall T (λ x, fx x)) => /=.
    rewrite /filtered_trace/=-/(filtered_trace _).
    split.
    + etrans; [|done]. constructor => ?. econstructor. naive_solver.
    + apply: thas_trace_all. naive_solver.
Qed.

Lemma tmod_to_mod_filter {EV1 EV2} (m : mod_trans EV1) (R : EV1 → option EV2 → Prop) σi Pσ κs:
  σi ~{ m, κs }~>ₜ Pσ →
  σi ~{ filter_trans m R, filtered_trace R κs }~>ₜ Pσ.
Proof.
  elim.
  - move => ?????. constructor. done. by apply: (filtered_trace_mono _ tnil).
  - move => ??? κ ?? Hstep ? IH Hs.
    apply: thas_trace_mono; [| by apply: filtered_trace_mono |done].
    destruct κ => /=.
    + rewrite /filtered_trace/=-/(filtered_trace _).
      apply thas_trace_all => -[??].
      apply: TTraceStep; [econstructor;[done| simpl;done] |done |done].
    + apply: TTraceStep; [by econstructor | done | simpl;done].
  - move => ????????.
    apply: thas_trace_mono; [| by apply: filtered_trace_mono |done].
    rewrite /filtered_trace/=-/(filtered_trace _).
    apply: thas_trace_all. naive_solver.
Qed.

Lemma filter_mod_trefines {EV1 EV2} (R : EV1 → option EV2 → Prop) mi ms:
  trefines mi ms →
  trefines (filter_mod mi R) (filter_mod ms R).
Proof.
  move => [/=Hr]. constructor => /=? /tmod_filter_to_mod[?[? /Hr/tmod_to_mod_filter?]].
  by apply: thas_trace_mono.
Qed.

(** A significantly simpler proof using [trefines1_implies_trefines2] *)
Lemma mod_filter_trefines' {EV1 EV2} (R : EV1 → option EV2 → Prop) mi ms:
  trefines mi ms →
  trefines (filter_mod mi R) (filter_mod ms R).
Proof.
  move => Hr. eapply (trefines1_implies_trefines2 mi ms (filter_mod mi R) (filter_mod ms R) (λ σ1 σ2, σ1 = σ2) (λ σ1 σ2, σ1 = σ2)); [done.. | |] => /=.
  - move => ???? -> Hstep. inversion Hstep; simplify_eq. eexists e.
    split.
    + case_match; simplify_eq => //.
      move => ??? -> ?. apply: TTraceStep; [| |by erewrite tapp_tnil_r].
      { econstructor; [done| simpl; done]. }
      move => ??. apply: TTraceEnd; naive_solver.
    + apply: TTraceStep; [done| |by erewrite tapp_tnil_r].
      move => ??. apply: TTraceEnd; [|done]. naive_solver.
  - move => ??? -> ?.
    apply: TTraceStep; [by econstructor| |simpl; done].
    move => ??. apply: TTraceEnd; [|done]. naive_solver.
Qed.
