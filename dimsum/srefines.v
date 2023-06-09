From dimsum.core Require Export module.

(** * [srefines] *)
(** [srefines] is a notion of refinement that models behaviors as sets
of sets of lists. It allows commuting choices and visible events. *)

Inductive event (EV : Type) : Type :=
| Nb | Ub | Vis (e : EV).
Arguments Ub {_}.
Arguments Nb {_}.
Arguments Vis {_}.

(* It is important to use (list (event EV) → Prop) instead of (list EV
→ Prop) since we want to distinguish the program that
non-deterministically generates all events and the program that has
UB. In particular, the NB program would be equivalent to the UB
program if EV is not inhabited if we don't use [event EV] *)
Inductive shas_trace {EV} (m : mod_trans EV) :
  m.(m_state) → (list (event EV) → Prop) → (m.(m_state) → Prop) → Prop :=
| STraceEnd σ (Pκs Pσ : _ → Prop):
    Pσ σ →
    Pκs [] ∧ Pκs [Nb] →
    shas_trace m σ Pκs Pσ
| STraceStep σ1 Pκs Pσ2 Pσ3 κ:
    m.(m_step) σ1 κ Pσ2 →
    (∀ σ2, Pσ2 σ2 → shas_trace m σ2 (λ κs, Pκs (option_list (Vis <$> κ) ++ κs)) Pσ3) →
    (* Or should the following be:
     (if κ is Some e then Pκs [] ∧ Pκs [e] else True) → *)
    (Pκs [] ∧ Pκs (option_list (Vis <$> κ))) →
    shas_trace m σ1 Pκs Pσ3
.
Notation " σ '~{' m , Pκs '}~>ₛ' P " := (shas_trace m σ Pκs P) (at level 40).

Global Instance shas_trace_proper {EV} (m : mod_trans EV) :
  Proper ((=) ==> (pointwise_relation _ impl) ==> (pointwise_relation m.(m_state) impl) ==> impl) (shas_trace m).
Proof.
  move => ?? -> Pκs1 Pκs2 Hκs Pσ1 Pσ2 HP Ht.
  elim: Ht Pκs2 Pσ2 Hκs HP.
  - move => ????[??] ?? Hκs HP. apply: STraceEnd. by apply: HP. split; by apply: Hκs.
  - move => ??????? IH ??? Hκs HP. apply: STraceStep; [done| | split; apply: Hκs; naive_solver].
    move => ??. apply: IH => // ??. by apply: Hκs.
Qed.

Lemma shas_trace_mono {EV} {m : mod_trans EV} (Pκs' Pσ2' Pκs Pσ2 : _ → Prop)  σ1 :
  σ1 ~{ m, Pκs' }~>ₛ Pσ2' →
  (∀ κs, Pκs' κs → Pκs κs) →
  (∀ σ, Pσ2' σ → Pσ2 σ) →
  σ1 ~{ m, Pκs }~>ₛ Pσ2.
Proof. move => ???. by apply: shas_trace_proper. Qed.

Lemma shas_trace_exists {EV} {A} {m : mod_trans EV} Pκs Pσ σ1 :
  (∃ x, σ1 ~{ m, Pκs x}~>ₛ Pσ) →
  σ1 ~{ m, λ κs, ∃ x : A, Pκs x κs }~>ₛ Pσ.
Proof. move => [??]. apply: shas_trace_mono; [done| |done]. naive_solver. Qed.

Lemma shas_trace_or {EV} {m : mod_trans EV} Pκs1 Pκs2 Pσ σ1 :
  (σ1 ~{ m, Pκs1 }~>ₛ Pσ ∨ σ1 ~{ m, Pκs2 }~>ₛ Pσ) →
  σ1 ~{ m, λ κs, Pκs1 κs ∨ Pκs2 κs}~>ₛ Pσ.
Proof. move => [?|?]; (apply: shas_trace_mono; [done| |done]); naive_solver. Qed.

Lemma shas_trace_forall_inv {EV} {A} {m : mod_trans EV} (Pκs : A → _ → Prop) Pσ σ1 :
  (σ1 ~{ m, λ κs, ∀ x : A, Pκs x κs}~>ₛ Pσ) →
  ∀ x, σ1 ~{ m, Pκs x }~>ₛ Pσ.
Proof. move => ??. apply: shas_trace_mono; [done| |done]. naive_solver. Qed.

Record srefines {EV} (mimpl mspec : module EV) : Prop := {
  sref_subset:
    ∀ Pκs, mimpl.(m_init) ~{ mimpl.(m_trans), Pκs }~>ₛ (λ _, True) →
           mspec.(m_init) ~{ mspec.(m_trans), Pκs }~>ₛ (λ _, True)
}.

Definition srefines_equiv {EV} (m1 m2 : module EV) : Prop := srefines m1 m2 ∧ srefines m2 m1.

Lemma srefines_equiv_equiv {EV} (m1 m2 : module EV) :
  (∀ Pκs, m1.(m_init) ~{ m1.(m_trans), Pκs }~>ₛ (λ _, True) ↔ m2.(m_init) ~{ m2.(m_trans), Pκs }~>ₛ (λ _, True)) →
  srefines_equiv m1 m2.
Proof. move => ?. split; constructor => ?; naive_solver. Qed.

Definition ssafe {EV} (m : module EV) (P : (list (event EV) → Prop) → Prop) :=
  ∀ Pκs, m.(m_init) ~{ m.(m_trans), Pκs }~>ₛ (λ _, True) → P Pκs.

Lemma srefines_preserves_safe EV (mspec mimpl : module EV) P:
  ssafe mspec P →
  srefines mimpl mspec →
  ssafe mimpl P.
Proof. move => Hs [Hr] κs Hκs. apply: Hs. by apply: Hr. Qed.

Global Instance srefines_preorder EV : PreOrder (@srefines EV).
Proof.
  constructor.
  - constructor => // κ Hi; naive_solver.
  - move => ??? [Hr1] [Hr2]. constructor => /=. naive_solver.
Qed.
