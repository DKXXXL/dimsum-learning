From dimsum.core Require Export module.

(** * Demonic module **)
(** A demonic module is a module that allows only demonic choice and
UB, but not more interesting angelic choices. *)
Inductive dem_event (EV : Type) : Type :=
| DUb | DVis (e : EV).
Arguments DUb {_}.
Arguments DVis {_}.

Record dem_mod_trans (EV : Type) : Type := {
  dem_state : Type;
  dem_step : dem_state → option EV → dem_state → Prop;
  dem_is_ub : dem_state → Prop;
}.
Arguments dem_state {_}.
Arguments dem_step {_}.
Arguments dem_is_ub {_}.

Inductive dem_has_trace {EV} (m : dem_mod_trans EV) : m.(dem_state) → list (dem_event EV) → (m.(dem_state) → Prop) → Prop :=
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

Global Instance dem_has_trace_proper {EV} (m : dem_mod_trans EV) :
  Proper ((=) ==> (=) ==> (pointwise_relation m.(dem_state) impl) ==> impl) (dem_has_trace m).
Proof.
  move => ?? -> ?? -> Pσ1 Pσ2 HP Ht.
  elim: Ht Pσ2 HP.
  - move => ???? HP. apply: DTraceEnd. by apply: HP.
  - move => ??????????. apply: DTraceStep; naive_solver.
  - move => ??????. by apply: DTraceUb.
Qed.

Lemma dem_has_trace_mono {EV} (m : dem_mod_trans EV) σ1 (Pσ2 Pσ2' : _ → Prop) κs:
  σ1 ~{ m, κs }~>ₘ Pσ2' →
  (∀ σ, Pσ2' σ → Pσ2 σ) →
  σ1 ~{ m, κs }~>ₘ Pσ2.
Proof. move => ??. by apply: dem_has_trace_proper. Qed.

Lemma DTraceEnd' {EV} (m : dem_mod_trans EV) σ :
  σ ~{ m, [] }~>ₘ (σ =.).
Proof. by apply: DTraceEnd. Qed.

Lemma DTraceStepNone {EV} κs (m : dem_mod_trans EV) σ2 σ1 Pσ3 :
  m.(dem_step) σ1 None σ2 →
  σ2 ~{ m, κs }~>ₘ Pσ3 →
  σ1 ~{ m, κs }~>ₘ Pσ3.
Proof. move => ??. by apply: (DTraceStep _ _ _ _ None). Qed.

Lemma DTraceStepSome {EV} κs (m : dem_mod_trans EV) σ2 σ1 Pσ3 κ :
  m.(dem_step) σ1 (Some κ) σ2 →
  σ2 ~{ m, κs }~>ₘ Pσ3 →
  σ1 ~{ m, DVis κ :: κs }~>ₘ Pσ3.
Proof. move => ??. by apply: (DTraceStep _ _ _ _ (Some _)). Qed.

Lemma DTraceStep' {EV} κs κs' (m : dem_mod_trans EV) σ2 σ1 Pσ3 κ :
  m.(dem_step) σ1 κ σ2 →
  κs = option_list (DVis <$> κ) ++ κs' →
  σ2 ~{ m, κs' }~>ₘ Pσ3 →
  σ1 ~{ m, κs }~>ₘ Pσ3.
Proof. move => ? -> ?. by apply: DTraceStep. Qed.

Lemma dem_has_trace_trans {EV} κs1 κs2 (m : dem_mod_trans EV) σ1 Pσ2 Pσ3 :
  σ1 ~{ m, κs1 }~>ₘ Pσ2 →
  (∀ σ2, Pσ2 σ2 → σ2 ~{ m, κs2 }~>ₘ Pσ3) →
  σ1 ~{ m, κs1 ++ κs2 }~>ₘ Pσ3.
Proof.
  elim.
  - naive_solver.
  - move => ?????????. rewrite -app_assoc. econstructor; eauto.
  - move => ?????. by apply: DTraceUb.
Qed.

Lemma dem_has_trace_trans' {EV} κs1 κs2 (m : dem_mod_trans EV) σ1 Pσ3 :
  σ1 ~{ m, κs1 }~>ₘ (λ σ2, σ2 ~{ m, κs2 }~>ₘ Pσ3) →
  σ1 ~{ m, κs1 ++ κs2 }~>ₘ Pσ3.
Proof. move => ?. by apply: dem_has_trace_trans. Qed.

Lemma dem_has_trace_add_empty {EV} κs1 (m : dem_mod_trans EV) σ1 σ2 :
  σ1 ~{ m, κs1 ++ [] }~>ₘ σ2 →
  σ1 ~{ m, κs1 }~>ₘ σ2.
Proof. by rewrite -{2}[κs1](right_id_L [] (++)). Qed.

Lemma dem_has_trace_inv {EV} κs (m : dem_mod_trans EV) σ1 Pσ2:
  σ1 ~{ m, κs }~>ₘ Pσ2 →
  ∃ σ2, σ1 ~{ m, κs }~>ₘ (σ2 =.) ∧ (m.(dem_is_ub) σ2 ∨ Pσ2 σ2).
Proof.
  elim.
  - move => ???. eexists _. split; [by apply: DTraceEnd| by right].
  - move => ??????? [?[? Hor]].
    eexists _. split; [ by apply: DTraceStep | done].
  - move => ????. eexists _. split; [by apply: DTraceUb| by left].
Qed.

Lemma dem_has_trace_ub_inv {EV} κs (m : dem_mod_trans EV) σ1 Pσ2:
  σ1 ~{m, DUb :: κs }~>ₘ Pσ2 →
  σ1 ~{m, [] }~>ₘ (λ _, False).
Proof.
  move Hκ: (DUb :: κs) => κ Hκs.
  elim: Hκs Hκ => //.
  - move => ??? [] //= ??? IH ?. apply: DTraceStepNone; [done|].
    naive_solver.
  - move => ?????. by apply: DTraceUb.
Qed.

Lemma dem_has_trace_cons_inv {EV} κs κ (m : dem_mod_trans EV) σ1 Pσ3:
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

Lemma dem_has_trace_app_inv {EV} κs1 κs2 (m : dem_mod_trans EV) σ1 Pσ3:
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

Lemma dem_has_trace_ub_app_inv {EV} κs (m : dem_mod_trans EV) σ1 Pσ2:
  σ1 ~{ m, κs ++ [DUb] }~>ₘ Pσ2 →
  σ1 ~{ m, κs }~>ₘ (λ _, False).
Proof.
  move => /dem_has_trace_app_inv ?.
  apply: dem_has_trace_add_empty.
  apply: dem_has_trace_trans; [done|] => ?.
  apply: dem_has_trace_ub_inv.
Qed.

Inductive dem_ub_step {EV} (m : dem_mod_trans EV) : m.(dem_state) → option EV → (m.(dem_state) → Prop) → Prop :=
| MStepStep σ1 κ σ2:
    m.(dem_step) σ1 κ σ2 →
    dem_ub_step m σ1 κ (λ σ2', σ2' = σ2)
| MStepUb σ1:
    m.(dem_is_ub) σ1 →
    dem_ub_step m σ1 None (λ _, False).

Definition dem_mod_trans_to_mod_trans {EV} (m : dem_mod_trans EV) : mod_trans EV := ModTrans (dem_ub_step m).
Coercion dem_mod_trans_to_mod_trans : dem_mod_trans >-> mod_trans.

Record dem_module EV := DMod {
  dem_trans : dem_mod_trans EV;
  dem_init : dem_trans.(dem_state);
}.
Arguments DMod {_}.
Arguments dem_trans {_}.
Arguments dem_init {_}.
(* Coercion dms_module : dem_mod_state >-> dem_mod_trans. *)
Add Printing Constructor dem_module.

Definition dmod_to_mod {EV} (m : dem_module EV) : module EV :=
  Mod m.(dem_trans) m.(dem_init).
Coercion dmod_to_mod : dem_module >-> module.

Record dem_refines {EV} (mimpl mspec : dem_module EV) : Prop := {
  dem_ref_subset:
    ∀ κs, mimpl.(dem_init) ~{ mimpl.(dem_trans), κs }~>ₘ (λ _, True) →
          mspec.(dem_init) ~{ mspec.(dem_trans), κs }~>ₘ (λ _, True)
}.

Global Instance sqsubseteq_dem_refines EV : SqSubsetEq (dem_module EV) := dem_refines.

Definition dem_refines_equiv {EV} (m1 m2 : dem_module EV) : Prop := m1 ⊑ m2 ∧ m2 ⊑ m1.

Definition dem_safe {EV} (m : dem_module EV) (P : list (dem_event EV) → Prop) :=
  ∀ κs, m.(dem_init) ~{ m.(dem_trans), κs }~>ₘ (λ _, True) → P κs.

Lemma dem_refines_preserves_safe EV (mspec mimpl : dem_module EV) P:
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
