Require Export refframe.module.
Require Export refframe.axioms.

(* It is important to use (list (event EV) → Prop) instead of (list EV
→ Prop) since we want to distinguish the program that
non-deterministically generates all events and the program that has
UB. In particular, the NB program would be equivalent to the UB
program if EV is not inhabited if we don't use [event EV] *)
Inductive has_trace {EV} (m : module EV) :
  m.(m_state) → (list (event EV) → Prop) → (m.(m_state) → Prop) → Prop :=
| TraceEnd σ (Pκs Pσ : _ → Prop):
    Pσ σ →
    Pκs [] ∧ Pκs [Nb] →
    has_trace m σ Pκs Pσ
| TraceStep σ1 Pκs Pσ2 Pσ3 κ:
    m.(m_step) σ1 κ Pσ2 →
    (∀ σ2, Pσ2 σ2 → has_trace m σ2 (λ κs, Pκs (option_list (Vis <$> κ) ++ κs)) Pσ3) →
    (* Or should the following be:
     (if κ is Some e then Pκs [] ∧ Pκs [e] else True) → *)
    (Pκs [] ∧ Pκs (option_list (Vis <$> κ))) →
    has_trace m σ1 Pκs Pσ3
.
Notation " σ '~{' m , Pκs '}~>' P " := (has_trace m σ Pκs P) (at level 40).

Global Instance has_trace_proper {EV} (m : module EV) :
  Proper ((=) ==> (pointwise_relation _ impl) ==> (pointwise_relation m.(m_state) impl) ==> impl) (has_trace m).
Proof.
  move => ?? -> Pκs1 Pκs2 Hκs Pσ1 Pσ2 HP Ht.
  elim: Ht Pκs2 Pσ2 Hκs HP.
  - move => ????[??] ?? Hκs HP. apply: TraceEnd. by apply: HP. split; by apply: Hκs.
  - move => ??????? IH ??? Hκs HP. apply: TraceStep; [done| | split; apply: Hκs; naive_solver].
    move => ??. apply: IH => // ??. by apply: Hκs.
Qed.

Lemma has_trace_mono {EV} {m : module EV} (Pκs' Pσ2' Pκs Pσ2 : _ → Prop)  σ1 :
  σ1 ~{ m, Pκs' }~> Pσ2' →
  (∀ κs, Pκs' κs → Pκs κs) →
  (∀ σ, Pσ2' σ → Pσ2 σ) →
  σ1 ~{ m, Pκs }~> Pσ2.
Proof. move => ???. by apply: has_trace_proper. Qed.

Lemma has_trace_exists {EV} {A} {m : module EV} Pκs Pσ σ1 :
  (∃ x, σ1 ~{ m, Pκs x}~> Pσ) →
  σ1 ~{ m, λ κs, ∃ x : A, Pκs x κs }~> Pσ.
Proof. move => [??]. apply: has_trace_mono; [done| |done]. naive_solver. Qed.

Lemma has_trace_or {EV} {m : module EV} Pκs1 Pκs2 Pσ σ1 :
  (σ1 ~{ m, Pκs1 }~> Pσ ∨ σ1 ~{ m, Pκs2 }~> Pσ) →
  σ1 ~{ m, λ κs, Pκs1 κs ∨ Pκs2 κs}~> Pσ.
Proof. move => [?|?]; (apply: has_trace_mono; [done| |done]); naive_solver. Qed.

Lemma has_trace_forall_inv {EV} {A} {m : module EV} (Pκs : A → _ → Prop) Pσ σ1 :
  (σ1 ~{ m, λ κs, ∀ x : A, Pκs x κs}~> Pσ) →
  ∀ x, σ1 ~{ m, Pκs x }~> Pσ.
Proof. move => ??. apply: has_trace_mono; [done| |done]. naive_solver. Qed.

(*
Lemma has_trace_trans {EV} κs1 κs2 (m : module EV) σ1 Pσ2 Pσ3 :
  σ1 ~{ m, κs1 }~> Pσ2 →
  (∀ σ2, Pσ2 σ2 → σ2 ~{ m, κs2 }~> Pσ3) →
  σ1 ~{ m, κs1 ++ κs2 }~> Pσ3.
Proof.
  elim.
  - naive_solver.
  - move => ?????????. rewrite -app_assoc. econstructor; eauto.
  - move => ?????. by apply: TraceUb.
Qed.

Lemma has_trace_trans' {EV} κs1 κs2 (m : module EV) σ1 Pσ3 :
  σ1 ~{ m, κs1 }~> (λ σ2, σ2 ~{ m, κs2 }~> Pσ3) →
  σ1 ~{ m, κs1 ++ κs2 }~> Pσ3.
Proof. move => ?. by apply: has_trace_trans. Qed.

Lemma has_trace_add_empty {EV} κs1 (m : module EV) σ1 σ2 :
  σ1 ~{ m, κs1 ++ [] }~> σ2 →
  σ1 ~{ m, κs1 }~> σ2.
Proof. by rewrite -{2}[κs1](right_id_L [] (++)). Qed.

Lemma has_trace_inv {EV} κs (m : module EV) σ1 Pσ2:
  σ1 ~{ m, κs }~> Pσ2 →
  ∃ σ2, σ1 ~{ m, κs }~> (σ2 =.) ∧ (m.(m_is_ub) σ2 ∨ Pσ2 σ2).
Proof.
  elim.
  - move => ???. eexists _. split; [by apply: TraceEnd| by right].
  - move => ??????? [?[? Hor]].
    eexists _. split; [ by apply: TraceStep | done].
  - move => ????. eexists _. split; [by apply: TraceUb| by left].
Qed.

Lemma has_trace_ub_inv {EV} κs (m : module EV) σ1 Pσ2:
  σ1 ~{m, Ub :: κs }~> Pσ2 →
  σ1 ~{m, [] }~> (λ _, False).
Proof.
  move Hκ: (Ub :: κs) => κ Hκs.
  elim: Hκs Hκ => //.
  - move => ??? [] //= ??? IH ?. apply: TraceStepNone; [done|].
    naive_solver.
  - move => ?????. by apply: TraceUb.
Qed.

Lemma has_trace_cons_inv {EV} κs κ (m : module EV) σ1 Pσ3:
  σ1 ~{ m, Vis κ :: κs }~> Pσ3 →
  σ1 ~{ m, [] }~> (λ σ2, ∃ σ2', m.(m_step) σ2 (Some κ) σ2' ∧ σ2' ~{ m, κs }~> Pσ3).
Proof.
  move Hs: (Vis κ :: κs) => s Hκs.
  elim: Hκs Hs => //.
  - move => ??? [] //=.
    + move => ???? IH [] ??. subst. apply: TraceEnd. eexists _. split; [done|]. naive_solver.
    + move => ??? IH ?. apply: TraceStepNone; [done|]. naive_solver.
  - move => ?????. by apply: TraceUb.
Qed.

Lemma has_trace_app_inv {EV} κs1 κs2 (m : module EV) σ1 Pσ3:
  σ1 ~{ m, κs1 ++ κs2 }~> Pσ3 →
  σ1 ~{ m, κs1 }~> (λ σ2, σ2 ~{ m, κs2 }~> Pσ3).
Proof.
  elim: κs1 σ1 => /=. { move => ??. by apply: TraceEnd. }
  move => [|?] ? IH ?.
  - move => /has_trace_ub_inv?. by apply: (has_trace_trans []).
  - move => /(has_trace_cons_inv _ _)?.
    apply: (has_trace_trans []); [done|] => ? [?[??]].
    apply: TraceStepSome; [done|]. naive_solver.
Qed.

Lemma has_trace_ub_app_inv {EV} κs (m : module EV) σ1 Pσ2:
  σ1 ~{ m, κs ++ [Ub] }~> Pσ2 →
  σ1 ~{ m, κs }~> (λ _, False).
Proof.
  move => /has_trace_app_inv ?.
  apply: has_trace_add_empty.
  apply: has_trace_trans; [done|] => ?.
  apply: has_trace_ub_inv.
Qed.


Inductive m_ub_step {EV} (m : module EV) : m.(m_state) → option (event EV) → m.(m_state) → Prop :=
| MStepStep σ1 κ σ2:
    m.(m_step) σ1 κ σ2 →
    m_ub_step m σ1 (Vis <$> κ) σ2
| MStepUb σ1:
    m.(m_is_ub) σ1 →
    m_ub_step m σ1 (Some Ub) σ1.
*)


Record refines {EV} (mimpl mspec : mod_state EV) : Prop := {
  ref_subset:
    ∀ Pκs, mimpl.(ms_state) ~{ mimpl, Pκs }~> (λ _, True) → mspec.(ms_state) ~{ mspec, Pκs }~> (λ _, True)
}.

Global Instance sqsubseteq_refines EV : SqSubsetEq (mod_state EV) := refines.

Definition refines_equiv {EV} (m1 m2 : mod_state EV) : Prop := m1 ⊑ m2 ∧ m2 ⊑ m1.

Global Instance equiv_refines EV : Equiv (mod_state EV) := refines_equiv.

Lemma refines_equiv_equiv {EV} (m1 m2 : mod_state EV) :
  (∀ Pκs, m1.(ms_state) ~{ m1, Pκs }~> (λ _, True) ↔ m2.(ms_state) ~{ m2, Pκs }~> (λ _, True)) →
  m1 ≡ m2.
Proof. move => ?. split; constructor => ?; naive_solver. Qed.

Definition safe {EV} (m : mod_state EV) (P : (list (event EV) → Prop) → Prop) :=
  ∀ Pκs, m.(ms_state) ~{ m, Pκs }~> (λ _, True) → P Pκs.

Lemma refines_preserves_safe EV (mspec mimpl : mod_state EV) P:
  safe mspec P →
  mimpl ⊑ mspec →
  safe mimpl P.
Proof. move => Hs [Hr] κs Hκs. apply: Hs. by apply: Hr. Qed.

Global Instance refines_preorder EV : PreOrder (@refines EV).
Proof.
  constructor.
  - constructor => // κ Hi; naive_solver.
  - move => ??? [Hr1] [Hr2]. constructor => /=. naive_solver.
Qed.
