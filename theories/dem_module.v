Require Export refframe.module.
Require Export refframe.refines.

(*** Demonic module **)
Inductive dem_event (EV : Type) : Type :=
| DUb | DVis (e : EV).
Arguments DUb {_}.
Arguments DVis {_}.

Record dem_module (EV : Type) : Type := {
  dem_state : Type;
  dem_step : dem_state → option EV → dem_state → Prop;
  dem_is_ub : dem_state → Prop;
}.
Arguments dem_state {_}.
Arguments dem_step {_}.
Arguments dem_is_ub {_}.

Inductive dem_has_trace {EV} (m : dem_module EV) : m.(dem_state) → list (dem_event EV) → (m.(dem_state) → Prop) → Prop :=
| DTraceEnd σ (Pσ : _ → Prop):
    Pσ σ →
    dem_has_trace m σ [] Pσ
| DTraceStep σ1 σ2 Pσ3 κ κs:
    m.(dem_step) σ1 κ σ2 →
    dem_has_trace m σ2 κs Pσ3 →
    dem_has_trace m σ1 (option_list (DVis <$> κ) ++ κs) Pσ3
| DTraceUb σ1 κs Pσ2:
    m.(dem_is_ub) σ1 →
    dem_has_trace m σ1 κs Pσ2
.
Notation " σ '~{' m , κ '}~>ₘ' P " := (dem_has_trace m σ κ P) (at level 40).

Global Instance dem_has_trace_proper {EV} (m : dem_module EV) :
  Proper ((=) ==> (=) ==> (pointwise_relation m.(dem_state) impl) ==> impl) (dem_has_trace m).
Proof.
  move => ?? -> ?? -> Pσ1 Pσ2 HP Ht.
  elim: Ht Pσ2 HP.
  - move => ???? HP. apply: DTraceEnd. by apply: HP.
  - move => ??????????. apply: DTraceStep; naive_solver.
  - move => ??????. by apply: DTraceUb.
Qed.

Lemma dem_has_trace_mono {EV} (m : dem_module EV) σ1 (Pσ2 Pσ2' : _ → Prop) κs:
  σ1 ~{ m, κs }~>ₘ Pσ2' →
  (∀ σ, Pσ2' σ → Pσ2 σ) →
  σ1 ~{ m, κs }~>ₘ Pσ2.
Proof. move => ??. by apply: dem_has_trace_proper. Qed.

Lemma DTraceEnd' {EV} (m : dem_module EV) σ :
  σ ~{ m, [] }~>ₘ (σ =.).
Proof. by apply: DTraceEnd. Qed.

Lemma DTraceStepNone {EV} κs (m : dem_module EV) σ2 σ1 Pσ3 :
  m.(dem_step) σ1 None σ2 →
  σ2 ~{ m, κs }~>ₘ Pσ3 →
  σ1 ~{ m, κs }~>ₘ Pσ3.
Proof. move => ??. by apply: (DTraceStep _ _ _ _ None). Qed.

Lemma DTraceStepSome {EV} κs (m : dem_module EV) σ2 σ1 Pσ3 κ :
  m.(dem_step) σ1 (Some κ) σ2 →
  σ2 ~{ m, κs }~>ₘ Pσ3 →
  σ1 ~{ m, DVis κ :: κs }~>ₘ Pσ3.
Proof. move => ??. by apply: (DTraceStep _ _ _ _ (Some _)). Qed.

Lemma DTraceStep' {EV} κs κs' (m : dem_module EV) σ2 σ1 Pσ3 κ :
  m.(dem_step) σ1 κ σ2 →
  κs = option_list (DVis <$> κ) ++ κs' →
  σ2 ~{ m, κs' }~>ₘ Pσ3 →
  σ1 ~{ m, κs }~>ₘ Pσ3.
Proof. move => ? -> ?. by apply: DTraceStep. Qed.

Lemma dem_has_trace_trans {EV} κs1 κs2 (m : dem_module EV) σ1 Pσ2 Pσ3 :
  σ1 ~{ m, κs1 }~>ₘ Pσ2 →
  (∀ σ2, Pσ2 σ2 → σ2 ~{ m, κs2 }~>ₘ Pσ3) →
  σ1 ~{ m, κs1 ++ κs2 }~>ₘ Pσ3.
Proof.
  elim.
  - naive_solver.
  - move => ?????????. rewrite -app_assoc. econstructor; eauto.
  - move => ?????. by apply: DTraceUb.
Qed.

Lemma dem_has_trace_trans' {EV} κs1 κs2 (m : dem_module EV) σ1 Pσ3 :
  σ1 ~{ m, κs1 }~>ₘ (λ σ2, σ2 ~{ m, κs2 }~>ₘ Pσ3) →
  σ1 ~{ m, κs1 ++ κs2 }~>ₘ Pσ3.
Proof. move => ?. by apply: dem_has_trace_trans. Qed.

Lemma dem_has_trace_add_empty {EV} κs1 (m : dem_module EV) σ1 σ2 :
  σ1 ~{ m, κs1 ++ [] }~>ₘ σ2 →
  σ1 ~{ m, κs1 }~>ₘ σ2.
Proof. by rewrite -{2}[κs1](right_id_L [] (++)). Qed.

Lemma dem_has_trace_inv {EV} κs (m : dem_module EV) σ1 Pσ2:
  σ1 ~{ m, κs }~>ₘ Pσ2 →
  ∃ σ2, σ1 ~{ m, κs }~>ₘ (σ2 =.) ∧ (m.(dem_is_ub) σ2 ∨ Pσ2 σ2).
Proof.
  elim.
  - move => ???. eexists _. split; [by apply: DTraceEnd| by right].
  - move => ??????? [?[? Hor]].
    eexists _. split; [ by apply: DTraceStep | done].
  - move => ????. eexists _. split; [by apply: DTraceUb| by left].
Qed.

Lemma dem_has_trace_ub_inv {EV} κs (m : dem_module EV) σ1 Pσ2:
  σ1 ~{m, DUb :: κs }~>ₘ Pσ2 →
  σ1 ~{m, [] }~>ₘ (λ _, False).
Proof.
  move Hκ: (DUb :: κs) => κ Hκs.
  elim: Hκs Hκ => //.
  - move => ??? [] //= ??? IH ?. apply: DTraceStepNone; [done|].
    naive_solver.
  - move => ?????. by apply: DTraceUb.
Qed.

Lemma dem_has_trace_cons_inv {EV} κs κ (m : dem_module EV) σ1 Pσ3:
  σ1 ~{ m, DVis κ :: κs }~>ₘ Pσ3 →
  σ1 ~{ m, [] }~>ₘ (λ σ2, ∃ σ2', m.(dem_step) σ2 (Some κ) σ2' ∧ σ2' ~{ m, κs }~>ₘ Pσ3).
Proof.
  move Hs: (DVis κ :: κs) => s Hκs.
  elim: Hκs Hs => //.
  - move => ??? [] //=.
    + move => ???? IH [] ??. subst. apply: DTraceEnd. eexists _. split; [done|]. naive_solver.
    + move => ??? IH ?. apply: DTraceStepNone; [done|]. naive_solver.
  - move => ?????. by apply: DTraceUb.
Qed.

Lemma dem_has_trace_app_inv {EV} κs1 κs2 (m : dem_module EV) σ1 Pσ3:
  σ1 ~{ m, κs1 ++ κs2 }~>ₘ Pσ3 →
  σ1 ~{ m, κs1 }~>ₘ (λ σ2, σ2 ~{ m, κs2 }~>ₘ Pσ3).
Proof.
  elim: κs1 σ1 => /=. { move => ??. by apply: DTraceEnd. }
  move => [|?] ? IH ?.
  - move => /dem_has_trace_ub_inv?. by apply: (dem_has_trace_trans []).
  - move => /(dem_has_trace_cons_inv _ _)?.
    apply: (dem_has_trace_trans []); [done|] => ? [?[??]].
    apply: DTraceStepSome; [done|]. naive_solver.
Qed.

Lemma dem_has_trace_ub_app_inv {EV} κs (m : dem_module EV) σ1 Pσ2:
  σ1 ~{ m, κs ++ [DUb] }~>ₘ Pσ2 →
  σ1 ~{ m, κs }~>ₘ (λ _, False).
Proof.
  move => /dem_has_trace_app_inv ?.
  apply: dem_has_trace_add_empty.
  apply: dem_has_trace_trans; [done|] => ?.
  apply: dem_has_trace_ub_inv.
Qed.

Inductive dem_ub_step {EV} (m : dem_module EV) : m.(dem_state) → option EV → (m.(dem_state) → Prop) → Prop :=
| MStepStep σ1 κ σ2:
    m.(dem_step) σ1 κ σ2 →
    dem_ub_step m σ1 κ (λ σ2', σ2' = σ2)
| MStepUb σ1:
    m.(dem_is_ub) σ1 →
    dem_ub_step m σ1 None (λ _, False).

Definition dem_module_to_module {EV} (m : dem_module EV) : module EV := {|
  m_step := dem_ub_step m
|}.
Coercion dem_module_to_module : dem_module >-> module.

Record dem_mod_state EV := DMS {
  dms_module : dem_module EV;
  dms_state : dms_module.(dem_state);
}.
Arguments DMS {_}.
Arguments dms_module {_}.
Arguments dms_state {_}.
Coercion dms_module : dem_mod_state >-> dem_module.

Definition dms_to_ms {EV} (m : dem_mod_state EV) : mod_state EV := {|
  ms_module := m;
  ms_state := m.(dms_state)
|}.
Coercion dms_to_ms : dem_mod_state >-> mod_state.

Record dem_refines {EV} (mimpl mspec : dem_mod_state EV) : Prop := {
  dem_ref_subset:
    ∀ κs, mimpl.(dms_state) ~{ mimpl, κs }~>ₘ (λ _, True) → mspec.(dms_state) ~{ mspec, κs }~>ₘ (λ _, True)
}.

Global Instance sqsubseteq_dem_refines EV : SqSubsetEq (dem_mod_state EV) := dem_refines.

Definition dem_refines_equiv {EV} (m1 m2 : dem_mod_state EV) : Prop := m1 ⊑ m2 ∧ m2 ⊑ m1.

Definition dem_safe {EV} (m : dem_mod_state EV) (P : list (dem_event EV) → Prop) :=
  ∀ κs, m.(dms_state) ~{ m, κs }~>ₘ (λ _, True) → P κs.

Lemma dem_refines_preserves_safe EV (mspec mimpl : dem_mod_state EV) P:
  dem_safe mspec P →
  mimpl ⊑ mspec →
  dem_safe mimpl P.
Proof. move => Hs [Hr] κs Hκs. apply: Hs. by apply: Hr. Qed.

Global Instance dem_refines_preorder EV : PreOrder (@dem_refines EV).
Proof.
  constructor.
  - constructor => // κ Hi; naive_solver.
  - move => ??? [Hr1] [Hr2]. constructor => /=. naive_solver.
Qed.

(*** Equivalence between refines and dem_refines *)

Inductive dem_trace_to_set {EV} : list (dem_event EV) → (list (event EV) → Prop) → Prop :=
| DT2S_nil (Pκs : _ → Prop):
    Pκs [] →
    Pκs [Nb] →
    dem_trace_to_set [] Pκs
| DT2S_vis κ κs (Pκs : _ → Prop):
    Pκs [] →
    dem_trace_to_set κs (λ κs, Pκs (Vis κ::κs)) →
    dem_trace_to_set (DVis κ :: κs) Pκs
| DT2S_ub κs (Pκs : _ → Prop):
    Pκs [] →
    dem_trace_to_set (DUb :: κs) Pκs
.

Lemma dem_trace_to_set_nil {EV} (κs : list (dem_event EV)) Pκs:
  dem_trace_to_set κs Pκs → Pκs [].
Proof. inversion 1 => //; simplify_eq; naive_solver.  Qed.

Lemma dem_trace_to_set_mono {EV} (κs : list (dem_event EV)) (Pκs Pκs' : _ → Prop):
  dem_trace_to_set κs Pκs →
  (∀ x, Pκs x → Pκs' x) →
  dem_trace_to_set κs Pκs'.
Proof.
  move => Ht. elim: Ht Pκs'.
  - move => ???? Hsub. constructor; by apply: Hsub.
  - move => ????? IH ? Hsub. constructor. { by apply: Hsub. }
    apply: IH => ??. by apply: Hsub.
  - move => ???? Hsub. constructor. by apply: Hsub.
Qed.

Lemma has_trace_dem_has_trace {EV} (m : dem_module EV) σ Pσ Pκs:
  σ ~{ m, Pκs }~> Pσ ↔ ∃ κs, dem_trace_to_set κs Pκs ∧ σ ~{ m, κs }~>ₘ Pσ.
Proof.
  split.
  - elim.
    + move => ???? [??]. eexists [] => /=. split;[by constructor|]. by constructor.
    + move => ???? κ Hstep _ IH ?.
      inversion Hstep; simplify_eq.
      * have [κs [Hsub ?]]:= IH _ ltac:(done).
        eexists (option_list (DVis <$> _) ++ κs).
        split. 2: by apply: DTraceStep.
        destruct κ => //=. constructor => //. naive_solver.
      * eexists [DUb]. split; [constructor| by apply: DTraceUb]. naive_solver.
  - move => [κs [HP Ht]].
    elim: Ht Pκs HP.
    + move => ???? Ht. inversion Ht; simplify_eq. by constructor.
    + move => σ1 σ2 Pσ3 κ κs' Hstep _ IH Pκs Ht.
      apply: TraceStep. { by constructor. } 2: {
        move: (Ht) => /dem_trace_to_set_nil ?.
        destruct κ => //. inversion Ht; simplify_eq/=.
        split; [done|]. move: H3 => /dem_trace_to_set_nil. done.
       }
      move => ? ->. apply: IH.
      destruct κ => //; simplify_eq/=. by inversion Ht; simplify_eq.
    + move => ????? Ht. apply: TraceStep; [ by constructor | done | ].
      split; by apply: dem_trace_to_set_nil.
Qed.


Fixpoint events_to_set {EV} (κs : list (dem_event EV)) : list (event EV) → Prop :=
  match κs with
  | [] => λ κs'', κs'' = []  ∨ κs'' = [Nb]
  | DUb::_ => λ κs'', κs'' = []  ∨ κs'' = [Ub]
  | DVis κ::κs' => λ κs'', (κs'' = [])
      ∨ ∃ κs''', κs'' = Vis κ::κs''' ∧ events_to_set κs' κs'''
  end.

(* Compute events_to_set [Vis 1]. *)
(* Compute events_to_set [Vis 1; Ub]. *)
(* Compute events_to_set [Ub]. *)

Lemma events_to_set_nil {EV} (κs : list (dem_event EV)) :
  events_to_set κs [].
Proof. destruct κs as [|[|]] => //; naive_solver. Qed.

Lemma dem_trace_to_set_events {EV} (κs : list (dem_event EV)) :
  dem_trace_to_set κs (events_to_set κs).
Proof.
  elim: κs. 1: constructor; naive_solver.
  move => [|κ] κs IH /=. 1: constructor; by left.
  constructor.
  - by left.
  - apply: dem_trace_to_set_mono; [done|] => ??. naive_solver.
Qed.

Lemma dem_trace_to_set_inj {EV} (κs1 κs2 : list (dem_event EV)):
  dem_trace_to_set κs2 (events_to_set κs1) →
  κs1 = κs2 ∨ ∃ κs, κs ++ [DUb] `prefix_of` κs2 ∧ κs `prefix_of` κs1.
Proof.
  elim: κs2 κs1 => [|[|κ2] κs2] /=.
  - move => [|[|κ] κs] Hdem.
    + naive_solver.
    + inversion Hdem; simplify_eq/=. naive_solver.
    + inversion Hdem; simplify_eq/=.
      have := events_to_set_nil κs. naive_solver.
  - move => IH κs1 /= Hdem. right. eexists [].
    split; [apply: prefix_cons|]; apply: prefix_nil.
  - move => IH [|[|κ] κs] /=; inversion 1; simplify_eq/=.
    + move: H4 => /dem_trace_to_set_nil. naive_solver.
    + move: H4 => /dem_trace_to_set_nil. naive_solver.
    + move: (H4) => /dem_trace_to_set_nil [//|[?[??]]]; simplify_eq.
      have [| |]:= IH κs.
      -- apply: dem_trace_to_set_mono; [done|] => ??. naive_solver.
      -- naive_solver.
      -- move => [κs1 [??]]. right.
         eexists (_:: _) => /=. split; by apply: prefix_cons.
Qed.

Lemma dem_has_trace_has_trace {EV} (m : dem_module EV) σ Pσ κs:
  σ ~{ m, κs }~>ₘ Pσ ↔ σ ~{ m, events_to_set κs}~> Pσ.
Proof.
  rewrite has_trace_dem_has_trace.
  split.
  - move => ?. eexists _. split; [|done]. apply: dem_trace_to_set_events.
  - move => [κs2[/dem_trace_to_set_inj[->//|[?[[?->][?->]]]]]].
    move => /dem_has_trace_app_inv/dem_has_trace_ub_app_inv ?.
    by apply: dem_has_trace_trans.
Qed.

Lemma dem_refines_refines {EV} (m1 m2 : dem_mod_state EV):
  dem_refines m1 m2 → refines m1 m2.
Proof.
  move => [?]. constructor => ? /has_trace_dem_has_trace?.
  apply/has_trace_dem_has_trace. naive_solver.
Qed.

Lemma refines_dem_refines {EV} (m1 m2 : dem_mod_state EV):
  refines m1 m2 → dem_refines m1 m2.
Proof.
  move => [?]. constructor => ?.
  move => /dem_has_trace_has_trace?.
  apply/dem_has_trace_has_trace. naive_solver.
Qed.
