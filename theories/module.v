Require Import refframe.base.
Require Import stdpp.namespaces.
Require Import stdpp.strings.
Require Import stdpp.gmap.
Require Import stdpp.binders.
Require Import stdpp.propset.
Require Import refframe.axioms.

Module version1.
Inductive steps {A B C} (R : A → option C → option B → A → Prop) : A → list (option C * option B) → A → Prop :=
| steps_refl ρ :
    steps R ρ [] ρ
| steps_l ρ1 ρ2 ρ3 ι κ κs :
    R ρ1 ι κ ρ2 →
    steps R ρ2 κs ρ3 →
    steps R ρ1 ((ι, κ) :: κs) ρ3.

Record module := {
  m_state : Type;
  m_in_event : Type;
  m_out_event : Type;
  m_initial : m_state → Prop;
  m_step : m_state → option m_in_event → option m_out_event → m_state → Prop;
  (* This cannot be defined based on m_step since m_state might e.g. contain a threadpool
     and a state should be bad if any thread is stuck. *)
  m_good : m_state → Prop;
}.

Definition safe (m : module) : Prop :=
  ∀ σ κ σ', m.(m_initial) σ → steps m.(m_step) σ κ σ' → m.(m_good) σ'.

Record refines (mimpl mspec : module) (ti : mimpl.(m_state) → mspec.(m_state)) (tin : mimpl.(m_in_event) → mspec.(m_in_event)) (tout : mimpl.(m_out_event) → mspec.(m_out_event)) := {
  ref_initial σ : mimpl.(m_initial) σ → mspec.(m_initial) (ti σ);
  ref_step σ κ σi:
    mimpl.(m_initial) σ →
    steps mimpl.(m_step) σ κ σi →
    (∀ σs, steps mspec.(m_step) (ti σ) (prod_map (fmap tin) (fmap tout) <$> κ) σs → mspec.(m_good) σs) →
    mimpl.(m_good) σi ∧ ∃ σs, steps mspec.(m_step) (ti σ) (prod_map (fmap tin) (fmap tout) <$> κ) σs;
}.

Lemma refines_preserves_safe mspec mimpl ti tin tout:
  safe mspec →
  refines mimpl mspec ti tin tout →
  safe mimpl.
Proof.
  move => Hs Hr σ κ σ' Hinit Hstep.
  have [|]:= (ref_step _ _ _ _ _ Hr _ _ _ Hinit Hstep) => //.
  move => σs Hsteps. apply: Hs => //.
  by apply: ref_initial.
Qed.

Lemma prod_map_fmap_id {A B} (l : list (option A * option B)):
  (prod_map (fmap id) (fmap id) <$> l) = l.
Proof. rewrite -{2}(list_fmap_id l). apply list_fmap_ext => // -[[?|] [?|]] //. Qed.

Lemma refines_reflexive m:
  refines m m id id id.
Proof. constructor => // σ κ σi Hi Hs. rewrite prod_map_fmap_id. naive_solver. Qed.

Lemma prod_map_fmap_compose {A B C D E F} (f1 : A → B) (f2 : B → C) (g1 : D → E) (g2 : E → F) (l : list (option _ * option _)):
  (prod_map (fmap (f2 ∘ f1)) (fmap (g2 ∘ g1)) <$> l) =
  (prod_map (fmap f2) (fmap g2) <$> (prod_map (fmap f1) (fmap g1) <$> l)).
Proof. rewrite -list_fmap_compose. apply list_fmap_ext => // -[[?|] [?|]] //. Qed.

Lemma refines_vertical m1 m2 m3 ti1 tin1 tout1 ti2 tin2 tout2:
  refines m1 m2 ti1 tin1 tout1 →
  refines m2 m3 ti2 tin2 tout2 →
  refines m1 m3 (ti2 ∘ ti1) (tin2 ∘ tin1) (tout2 ∘ tout1).
Proof.
  move => Hr1 Hr2.
  constructor; first by destruct Hr1, Hr2; eauto.
  move => σ κ σi Hinit1 Hstep1 /=. rewrite prod_map_fmap_compose => Hsafe3.
  have [|Hgood [σ2 Hstep2]] := (ref_step _ _ _ _ _ Hr1 _ _ _ Hinit1 Hstep1). {
    move => σs2 Hstep2.
    by have [||? _] := (ref_step _ _ _ _ _ Hr2 _ _ _ _ Hstep2); eauto using ref_initial.
  }
  split => //.
  have [||_ [σ3 Hstep3]] := (ref_step _ _ _ _ _ Hr2 _ _ _ _ Hstep2); eauto using ref_initial.
Qed.

Definition handles_call {A B} (in_event : option A) (out_event : option B) (r : A → B → Prop) : Prop :=
  ∃ eo ei, in_event = Some ei ∧ out_event = Some eo ∧ r ei eo.

Inductive module_product_step (m1 m2 : module) (r1 : m1.(m_in_event) → m2.(m_out_event) → Prop) (r2 : m2.(m_in_event) → m1.(m_out_event) → Prop) : m1.(m_state) * m2.(m_state) → option (m1.(m_in_event) + m2.(m_in_event)) → option (m1.(m_out_event) + m2.(m_out_event)) → m1.(m_state) * m2.(m_state) → Prop :=
| ModuleStepBoth σ1 σ2 κs1 κs2 ι1 ι2 σ1' σ2' :
    m1.(m_step) σ1 ι1 κs1 σ1' →
    m2.(m_step) σ2 ι2 κs2 σ2' →
    (* This means either m1 must be calling m2 or the other way around. *)
       (ι2 = None ∧ handles_call ι1 κs2 r1)
    ∨ (ι1 = None ∧ handles_call ι2 κs1 r2) →
    module_product_step m1 m2 r1 r2 (σ1, σ2) None None (σ1', σ2)
| ModuleStepLeft σ1 σ2 ι κs σ1' :
    m1.(m_step) σ1 ι κs σ1' →
    (* TODO: Should this step be possible if κs is a call which could be handled by m2?*)
    module_product_step m1 m2 r1 r2 (σ1, σ2) (inl <$> ι) (inl <$> κs) (σ1', σ2)
| ModuleStepRight σ1 σ2 ι κs σ2' :
    m2.(m_step) σ2 ι κs σ2' →
    module_product_step m1 m2 r1 r2 (σ1, σ2) (inr <$> ι) (inr <$> κs) (σ1, σ2')
.

Definition module_product (m1 m2 : module) (r1 : m1.(m_in_event) → m2.(m_out_event) → Prop) (r2 : m2.(m_in_event) → m1.(m_out_event) → Prop) : module := {|
  m_state := m1.(m_state) * m2.(m_state);
  m_in_event := m1.(m_in_event) + m2.(m_in_event);
  m_out_event := m1.(m_out_event) + m2.(m_out_event);
  m_initial σ := m1.(m_initial) σ.1 ∧ m2.(m_initial) σ.2;
  m_step := module_product_step m1 m2 r1 r2;
  m_good σ := m1.(m_good) σ.1 ∧ m2.(m_good) σ.2;
|}.

Lemma refines_horizontal m1 m2 m1' m2' ti1 tin1 tout1 ti2 tin2 tout2 r1 r2 r1' r2':
  refines m1 m1' ti1 tin1 tout1 →
  refines m2 m2' ti2 tin2 tout2 →
  refines (module_product m1 m2 r1 r2) (module_product m1' m2' r1' r2') (prod_map ti1 ti2) (sum_map tin1 tin2) (sum_map tout1 tout2).
Proof.
  move => Hr1 Hr2. constructor; first by move => [??]/= [??]; eauto using ref_initial.
  move => /= [σ1 σ2] κ [σi1 σi2] /= [Hinit1 Hinit2].
  have := (ref_step _ _ _ _ _ Hr1 _ _ _ Hinit1).
Abort.
(*
  I am not sure if this will work out and how to best define the semantics of linking.
  Maybe it is better to do something more closely based on RUSC where you have explicit call and
  return states?
  One would need to add something for atomic calls (necessary for calling the memory) but this could
  maybe be handled by adding a special case for it.
  Also in RUSC the notion of event seems to be shared by all modules, which we maybe do not want?
 *)
End version1.

Module version2.
Inductive steps {A B} (R : A → option B → A → Prop) : A → list B → A → Prop :=
| steps_refl ρ :
    steps R ρ [] ρ
| steps_l ρ1 ρ2 ρ3 κ κs :
    R ρ1 κ ρ2 →
    steps R ρ2 κs ρ3 →
    steps R ρ1 (option_list κ ++ κs) ρ3.

Lemma steps_None {A B} ρ2 (R : A → option B → A → Prop) ρ1 ρ3 κs2:
  R ρ1 None ρ2 →
  steps R ρ2 κs2 ρ3 →
  steps R ρ1 (κs2) ρ3.
Proof. move => ??. by apply: (steps_l _ _ _ _ None). Qed.

Lemma steps_Some {A B} ρ2 (R : A → option B → A → Prop) ρ1 ρ3 κ κs2:
  R ρ1 (Some κ) ρ2 →
  steps R ρ2 κs2 ρ3 →
  steps R ρ1 (κ :: κs2) ρ3.
Proof. move => ??. by apply: (steps_l _ _ _ _ (Some κ)). Qed.

Lemma steps_trans {A B} (R : A → option B → A → Prop) ρ1 ρ2 ρ3 κs1 κs2:
  steps R ρ1 κs1 ρ2 →
  steps R ρ2 κs2 ρ3 →
  steps R ρ1 (κs1 ++ κs2) ρ3.
Proof. elim => // ?????????. rewrite -app_assoc. econstructor; eauto. Qed.




(*

            id
A --------------------> B2
     id       5     id
A1 ------> G --> G' --> B2
|
|    id          5
A1 ------> G ---------> B1
|          |
|----------|
|
|          5
A2 -------------------> B1



A2 refines (A1 + G)       -> value: 5
B1 refines (G' + B2)      -> value: 5
(G + G') refines identity -> value: id
A1 refines A              -> value: id

example: Would this abstraction also work for abstraction of linked list to mathematical list?
Simple case: B2 calls functions on A1 to access data
Complex case: B2 accesses data (e.g. pointer to singly linked list) from A1 directly

*)





Record event := {
  e_name: positive;
  e_type: Type;
  e_data: e_type;
}.

Definition thread_id := positive.

Record module := {
  m_state : Type;
  (* multiple initial states can be modeled by non-deterministically
  branching from the initial state *)
  m_initial : m_state;
  m_interface : coPset;
  m_in : m_state → thread_id → event → m_state → Prop;
  m_step : m_state → thread_id → option event → m_state → Prop;
  m_is_good : m_state → Prop;
}.

Inductive module_step (m : module) : m.(m_state) → option (thread_id * (event + event)) → m.(m_state) → Prop :=
| MSStep e σ1 tid σ2:
    m.(m_step) σ1 tid e σ2 →
    module_step m σ1 ((λ e, (tid, inr e)) <$> e) σ2
| MSIn σ1 tid e σ2:
    m.(m_in) σ1 tid e σ2 →
    e.(e_name) ∈ m.(m_interface) →
    (* TODO should we have the following here?
    m.(m_is_blocked) σ1 tid →
     *)
    module_step m σ1 (Some (tid, inl e)) σ2.


(* Definition can_step (m : module) (σ : m.(m_state)) (tid : thread_id) : Prop := *)
(*   ∃ e σ2, m.(m_step) σ tid e σ2. *)

(* Definition safe_state (m : module) (σ : m.(m_state)) : Prop := *)
(*   ∀ tid, m.(m_is_blocked) σ tid ∨ can_step m σ tid. *)

Definition safe_trace (m : module) (σ : m.(m_state)) (κ : list (thread_id * (event + event))) :=
  (∀ σs κ', κ' `prefix_of` κ → steps (module_step m) σ κ' σs → m.(m_is_good) σs).

Definition safe (m : module) : Prop :=
  ∀ κ, safe_trace m m.(m_initial) κ.


Record refines (mimpl mspec : module) := {
  (* ref_interface : *)
  (*   mimpl.(m_interface) = mspec.(m_interface); *)
  (* ref_in σ tid e σs: *)
    (* mspec.(m_in) (ti σ) tid e σs → *)
    (* ∃ σi, mimpl.(m_in) σ tid e σi; *)
  ref_step κ σi:
    steps (module_step mimpl) mimpl.(m_initial) κ σi →
    safe_trace mspec mspec.(m_initial) κ →
    mimpl.(m_is_good) σi ∧ ∃ σs, steps (module_step mspec) mspec.(m_initial) κ σs;
}.

(* Suggestion by Youngju: forall target trace, exists source trace, such that traces are equal up to the point where source gives ub or target gives NB event *)

Lemma refines_preserves_safe mspec mimpl:
  safe mspec →
  refines mimpl mspec →
  safe mimpl.
Proof.
  move => Hs Hr κ σ' κ' Hpre Hstep.
  have [|]:= (ref_step _ _ Hr _ _ Hstep); by eauto.
Qed.

Lemma refines_reflexive m:
  refines m m.
Proof. constructor => // κ σi Hi Hs; naive_solver. Qed.

Lemma refines_vertical m1 m2 m3:
  refines m1 m2 →
  refines m2 m3 →
  refines m1 m3.
Proof.
  move => Hr1 Hr2.
  constructor => /=.
  (* - move => σ tid e σs Hin3. *)
  (*   have [//|? Hin2]:= (ref_in _ _ _ _ _ _ _ _ Hin3). *)
  (*   have [//|? ?]:= (ref_in _ _ _ _ _ _ _ _ Hin2). *)
  (*   naive_solver. *)
  - move => κ σi Hstep1 Hsafe3.
    have [|Hgood [σ2 Hstep2]] := (ref_step _ _ Hr1 _ _ Hstep1). {
      move => σs2 κ' Hprefix Hstep2.
      have [|? _] := (ref_step _ _ Hr2 _ _ Hstep2); eauto.
      move => σs3 κ'2 Hprefix2 Hstep3.
      apply: Hsafe3;[|done]. by etrans.
    }
    split => //.
    by have [|_ [σ3 Hstep3]] := (ref_step _ _ Hr2 _ _ Hstep2); eauto.
Qed.

Definition module_without (m : module) (rem : coPset) : module := {|
  m_state := m.(m_state);
  m_interface := m.(m_interface) ∖ rem;
  m_in := m.(m_in);
  m_initial := m.(m_initial);
  m_step := m.(m_step);
  m_is_good := m.(m_is_good);
|}.


Inductive module_product_in (m1 m2 : module) : m1.(m_state) * m2.(m_state) → thread_id → event → m1.(m_state) * m2.(m_state) → Prop :=
| MpInL σ1 σ2 tid e σ1' : module_product_in m1 m2 (σ1, σ2) tid e (σ1', σ2)
| MpInR σ1 σ2 tid e σ2' : module_product_in m1 m2 (σ1, σ2) tid e (σ1, σ2').
Inductive module_product_step (m1 m2 : module) : m1.(m_state) * m2.(m_state) → thread_id → option event → m1.(m_state) * m2.(m_state) → Prop :=
| MpStepL σ1 σ2 tid e e' σ1' σ2':
    m1.(m_step) σ1 tid e σ1' →
    (if (λ ev, (bool_decide (ev.(e_name) ∈ m2.(m_interface)), ev)) <$> e is Some (true, ev) then
      m2.(m_in) σ2 tid ev σ2' ∧ e' = None else σ2' = σ2 ∧ e' = e) →
    module_product_step m1 m2 (σ1, σ2) tid e' (σ1', σ2')
| MpStepR σ1 σ2 tid e e' σ1' σ2':
    m2.(m_step) σ2 tid e σ2' →
    (if (λ ev, (bool_decide (ev.(e_name) ∈ m1.(m_interface)), ev)) <$> e is Some (true, ev) then
      m1.(m_in) σ1 tid ev σ1' ∧ e' = None else σ1' = σ1 ∧ e' = e) →
    module_product_step m1 m2 (σ1, σ2) tid e' (σ1', σ2')
.

Definition module_product (m1 m2 : module) : module := {|
  m_state := m1.(m_state) * m2.(m_state);
  m_interface := m1.(m_interface) ∪ m2.(m_interface);
  m_in := module_product_in m1 m2;
  m_initial := (m1.(m_initial), m2.(m_initial));
  m_step := (module_product_step m1 m2);
(* TODO: we probably need some "always enabled" condition: If m1 can make a call, m2 can always receive it. *)
  m_is_good σ := m1.(m_is_good) σ.1 ∧ m2.(m_is_good) σ.2;
|}.

(* Lemma product_safe_state_l m1 m2 σ1 σ2: *)
(*   (* TODO: Not sure if this the the correct formulation because the reason that the produce is safe might be *)
(*   because m2 can do steps. However, eventually *) *)
(*   (∀ σ1' σ2', steps (module_step (module_product m1 m2)) (σ1, σ2) [] (σ1', σ2') → safe_state (module_product m1 m2) (σ1', σ2')) → *)
(*   safe_state m1 σ1. *)
(* Proof. *)

(* Admitted. *)
(* Lemma product_safe_trace_l m1 m2 σ1 σ2 \: *)
(*       safe_trace m1' σs1 [] *)
(*       safe_trace (module_product m1' m2') (σs1, σs2) [] *)


(* TODO: to make this proof go through, we probably need to ensure
that safe_state (product m1 m2) implies stafe_state m1 and safe_state
m2. The problem is that safe_state (product m1 m2) might hold because
m2 is able to do a step but m1 is already stuck. To fix this, we
probably need to make the notion of safe_state defined by the
module. *)
Lemma refines_horizontal m1 m2 m1' m2' :
  refines m1 m1' →
  refines m2 m2' →
  refines (module_product m1 m2) (module_product m1' m2').
Proof.
  move => Hr1 Hr2. constructor => κ σi /= Hsteps Hsafe.
  (* have : (∀ κ' σi1, steps (module_step m1) (m_initial m1) κ' σi1 → *)
  (*          safe_state m1 σi1 ∧ (∃ σs, steps (module_step m1') (m_initial m1') κ' σs)). { *)
  (*   move => κ' σi1 {}Hsteps. apply ref_step => // σs κ'' Hpref Hsteps2. admit. *)
  (* } *)

  (* TODO: turn the all quantifiers into existentials, similar to the soundness of wp? *)

  have := (ref_step _ _ Hr2). have := (ref_step _ _ Hr1). move: Hsteps.
  move: (m_initial m1) (m_initial m1') (m_initial m2) (m_initial m2') => σi1 σs1 σi2 σs2.
  move Heq: (σi1, σi2) => σi0.
  replace σi1 with (σi0.1). 2: by rewrite -Heq. replace σi2 with (σi0.2). 2: by rewrite -Heq.
  clear Heq => Hsteps.
  elim: Hsteps σs1 σs2; clear.
  -
    admit.
    (* move => [σi1 σi2] /= σs1 σs2 Hr1 Hr2 Hsafe. *)
    (* have [|?[σs1' ?]] := Hr1 _ _ (steps_refl _ _). { admit. } *)
    (* have [|?[σs2' ?]] := Hr2 _ _ (steps_refl _ _). { admit. } *)
    (* split => //. exists (σs1', σs2'). *)
  (* admit. *)
  - admit.
  (* - move => [σi1 σi2] [σi1' σi2'] [σi1'' σi2''] κ κs/= Hstep Hsteps IH σs1 σs2 Hm1 Hm2 Hsafe. *)
  (*   inversion Hstep; simplify_eq. *)
  (*   + revert select (m_step _ _ _ _ _). inversion 1; simplify_eq. *)
  (*     * *)
  (*     * admit. *)
  (*   + admit. *)
Abort.

(*** Proving refinement *)
Lemma inv_implies_refines m1 m2 (inv : m1.(m_state) → m2.(m_state) → Prop):
  (* (∀ σ tid e σs, m_in m2 (ti σ) tid e σs → ∃ σi : m_state m1, m_in m1 σ tid e σi) → *)
  inv m1.(m_initial) m2.(m_initial) →
  (∀ σi σs, inv σi σs → m1.(m_is_good) σi) →
  (∀ σi1 σs1 σi2 e,
      inv σi1 σs1 → module_step m1 σi1 e σi2 →
      safe_trace m2 σs1 (option_list e) →
      ∃ σs2, inv σi2 σs2 ∧ steps (module_step m2) σs1 (option_list e) σs2) →
  refines m1 m2.
Proof.
  move => Hinvinit Hinvsafe Hinvstep.
  constructor => // κ σi2. move: m1.(m_initial) m2.(m_initial) Hinvinit => σi1 σs1 Hinv Hsteps Hspec.
  elim: Hsteps σs1 Hinv Hspec => {σi1 κ σi2}.
  - by eauto using steps_refl.
  - move => σi1 σi2 σi3 κ κs Hstep Hsteps IH σs1 Hinv Hspec.
    case: (Hinvstep _ _ _ _ Hinv Hstep).
    { move => ???. apply: Hspec. etrans; first done. destruct κ; [apply prefix_cons|]; apply prefix_nil. }
    move => σs2 [Hinv2 Hssteps]. case: (IH _ Hinv2) => //.
    + move => σs κ' Hprefix Hs. apply: Hspec. 2: by apply: steps_trans. by apply prefix_app.
    + move => Hsafe [σs3 Hs]. split => //. eexists. by apply: steps_trans.
Qed.

Inductive wp (m1 m2 : module) : nat → m1.(m_state) -> m2.(m_state) -> list (thread_id * (event + event)) -> Prop :=
| Wp_step σi1 σs1 κs n:
    (∀ κ, safe_trace m2 σs1 (option_list κ) → m1.(m_is_good) σi1 ∧
    (∀ σi2 κs' n', κs = option_list κ ++ κs' -> n = S n' → module_step m1 σi1 κ σi2 ->
       ∃ σs2, steps (module_step m2) σs1 (option_list κ) σs2 ∧ wp m1 m2 n' σi2 σs2 κs')) ->
    wp m1 m2 n σi1 σs1 κs
.

Lemma forall_to_ex A B (P : A → B → Prop) (Q : B → Prop):
 (∃ n : A, ∀ y : B, P n y → Q y) -> ∀ y : B, ((∀ n : A, P n y) → Q y).
Proof. naive_solver. Qed.

Lemma wp_implies_refines m1 m2:
  (∀ κ n, wp m1 m2 n m1.(m_initial) m2.(m_initial) κ) →
  refines m1 m2.
Proof.
  move => Hwp. constructor => κ σi. move: m1.(m_initial) m2.(m_initial) {Hwp}(Hwp κ) => σi1 σs1 Hwp Hsteps Hsafe.
  move: σs1 Hwp Hsafe. apply: forall_to_ex.
  elim: Hsteps => {σi1 κ σi}.
  - move => σi1. exists 0 => σs1 Hwp Hsafe. split; eauto using steps_refl.
    destruct Hwp as [???? Hwp].
    move : (Hwp None) => [|] //= ?? Hprefix.
    apply Hsafe. etrans => //. apply prefix_nil.
  - move => σi1 σi2 σi3 κ κs Hstep Hsteps [n IH]. exists (S n) =>  σs1 Hwp Hsafe.
    inversion Hwp as [???? Hwp2]; subst.
    move : (Hwp2 κ) => [|] //=. { move => ???. apply Hsafe. by apply: prefix_app_r. }
    move => ? {Hwp2}Hwp.
    have [||σs2 [Hsteps2 {}Hwp]]:= (Hwp _ κs n _ _ Hstep) => //.
    have [|?[??]]:= (IH _ Hwp).
    + move => σs κ' Hprefix Hs. apply: Hsafe. 2: by apply: steps_trans. by apply prefix_app.
    + split => //. eexists. by apply: steps_trans.
Qed.

Ltac inv_step :=
  lazymatch goal with
  | H : module_step ?m _ _ _ |- _ => inversion H; clear H; subst;
    repeat lazymatch goal with
    | H : m_step _ _ _ _ _  |- _ => inversion H; clear H
    | H : m_in _ _ _ _ _  |- _ => inversion H; clear H
    end; simplify_eq/=
  end.

(*** Tests *)
Module test.
Definition nat_event (n : nat) : event := {|
  e_name := encode (nroot.@"test");
  e_type := nat;
  e_data := n;
|}.

(*   2
  1 --- 2 (done)
 *)
Inductive mod1_step : bool → thread_id → option event → bool → Prop :=
| T1False tid: mod1_step false tid (Some (nat_event 2)) true.


Definition mod1 : module := {|
  m_state := bool;
  m_initial := false;
  m_interface := ∅;
  m_in _ _ _ _:= False;
  m_step := mod1_step;
  m_is_good s:= True;
|}.

(*         2
  1 --- 2 --- 3 (done)
 *)
Inductive mod2_state := | S1 | S2 | S3.
Inductive mod2_step : mod2_state → thread_id → option event → mod2_state → Prop :=
| T2S1 tid: mod2_step S1 tid None S2
| T2S2 tid: mod2_step S2 tid (Some (nat_event 2)) S3.
Definition mod2 : module := {|
  m_state := mod2_state;
  m_initial := S1;
  m_interface := ∅;
  m_in _ _ _ _:= False;
  m_step := mod2_step;
  m_is_good s:= True;
|}.

Definition t2_to_t1_inv (σ1 : mod2_state) (σ2 : bool) : Prop :=
  σ2 = match σ1 with
  | S1 | S2 => false
  | _ => true
  end.
Lemma test_refines1 :
  refines mod2 mod1.
Proof.
  apply: (inv_implies_refines mod2 mod1 t2_to_t1_inv).
  - done.
  - done.
  - move => σi1 σs1 σi2 e -> ? Hsafe. inv_step; eexists _; split => //.
    + by left.
    + apply: steps_Some; last by left. apply (MSStep _ (Some _)). constructor.
Qed.

Definition mod_loop : module := {|
  m_state := unit;
  m_initial := tt;
  m_interface := ∅;
  m_in _ _ _ _ := False;
  m_step _ _ e _ := e = None;
  m_is_good s:= True;
|}.
Lemma test_refines2 m :
  refines mod_loop m.
Proof.
  apply: (inv_implies_refines mod_loop m (λ _ _, True)).
  - done.
  - done.
  - move => ???????. inv_step. eexists. split => //. left.
Qed.

Lemma test_refines2_wp m :
  refines mod_loop m.
Proof.
  apply: wp_implies_refines => /=.
  move => κ n. elim/lt_wf_ind: n => n Hloop.
  constructor => κ' Hsafe. split => // [[]] κs' ????.
  inv_step. eexists. split; [left|]. apply Hloop.
  lia.
Qed.


(*   1
      /- 2 (done)
  1 --
      \- 3 (stuck)
     2
 *)

Inductive stuck1_state := | S1S1 | S1S2 | S1S3.
Inductive stuck1_step : stuck1_state → thread_id → option event → stuck1_state → Prop :=
| S1_1To2 tid: stuck1_step S1S1 tid (Some (nat_event 1)) S1S2
| S1_1To3 tid: stuck1_step S1S1 tid (Some (nat_event 2)) S1S3.
Definition mod_stuck1 : module := {|
  m_state := stuck1_state;
  m_interface := ∅;
  m_initial := S1S1;
  m_in _ _ _ _:= False;
  m_step := stuck1_step;
  m_is_good s:= s ≠ S1S3;
|}.

Lemma test_refines_stuck1 :
  refines mod_stuck1 mod_stuck1.
Proof.
  apply: (inv_implies_refines mod_stuck1 mod_stuck1 (λ σ1 σ2, σ1 = σ2 ∧ σ1 ≠ S1S3)).
  - done.
  - move => [] ?[??] => //.
  - move => σi1 σs1 σi2 e [-> ?] ? Hsafe. inv_step.
    + (* 1 -> 2 *) eexists _. split => //. apply: steps_Some; last by left. apply: (MSStep _ (Some _)). constructor.
    + (* 1 -> 3 *) exfalso.
      have [||]:= (Hsafe S1S3 [(tid, inr (nat_event 2))]) => //.
      apply: steps_Some; last by left. apply: (MSStep _ (Some _)). econstructor.
Qed.

(*   1
      /- 2 (done)
  1 --
      \- 3 ---- 4 (stuck)
     2      3
 *)

Inductive stuck2_state := | S2S1 | S2S2 | S2S3 | S2S4.
Inductive stuck2_step : stuck2_state → thread_id → option event → stuck2_state → Prop :=
| S2_1To2 tid: stuck2_step S2S1 tid (Some (nat_event 1)) S2S2
| S2_1To3 tid: stuck2_step S2S1 tid (Some (nat_event 2)) S2S3
| S2_3To4 tid: stuck2_step S2S3 tid (Some (nat_event 3)) S2S4.
Definition mod_stuck2 : module := {|
  m_state := stuck2_state;
  m_interface := ∅;
  m_initial := S2S1;
  m_in _ _ _ _:= False;
  m_step := stuck2_step;
  m_is_good s:= s ≠ S2S4;
|}.

Definition stuck2_inv (σ1 : stuck2_state) (σ2 : stuck1_state) :=
  (* We could prove an even stronger invariant with also σ1 ≠ S2S3
  since we don't need to reestablish it for a stuck source state. *)
  σ1 ≠ S2S4 ∧
  σ2 = match σ1 with | S2S1 => S1S1 | S2S2 => S1S2 | S2S3 => S1S3 | S2S4 => S1S1 end.

Lemma test_refines_stuck2 :
  refines mod_stuck2 mod_stuck1.
Proof.
  apply: (inv_implies_refines mod_stuck2 mod_stuck1 stuck2_inv).
  - done.
  - move => [] ?[??] => //.
  - move => σi1 σs1 σi2 e [? ->] ? Hsafe. inv_step.
    + (* 1 -> 2 *) eexists _. split => //. apply: steps_Some; last by left. apply: (MSStep _ (Some _)). constructor.
    + (* 1 -> 3 *) eexists _. split => //. apply: steps_Some; last by left. apply: (MSStep _ (Some _)). constructor.
    + (* 3 -> 4 *) exfalso.
      have [||]:= (Hsafe S1S3 []) => //.
      * apply prefix_nil.
      * econstructor.
Qed.

Lemma test_refines_stuck2_wp :
  refines mod_stuck2 mod_stuck1.
Proof.
  apply: wp_implies_refines => κ n.
  (* S2S1 *)
  constructor => e1 Hsafe.
  split => // σ2 κs' ????. inv_step.
  - (* S2S2 *)
    eexists _. split. {
      apply: steps_Some; last by left. apply: (MSStep _ (Some _)). constructor.
    }
    constructor => {}e1 {}Hsafe.
    split => // {}σ2 κs'' ????; inv_step.
  - (* S2S3 *)
    eexists _. split. {
      apply: steps_Some; last by left. apply: (MSStep _ (Some _)). constructor.
    }
    constructor => {}e1 {}Hsafe.
    split => // {}σ2 κs'' ????. inv_step.
    have []:= Hsafe S1S3 [] => //.
    * apply prefix_nil.
    * apply steps_refl.
Qed.

(*   1       3
      /- 2 ---- 4 (done)
  1 --
      \- 3 (stuck)
     2
 *)

Inductive stuck3_state := | S3S1 | S3S2 | S3S3 | S3S4.
Inductive stuck3_step : stuck3_state → thread_id → option event → stuck3_state → Prop :=
| S3_1To2 tid: stuck3_step S3S1 tid (Some (nat_event 1)) S3S2
| S3_1To3 tid: stuck3_step S3S1 tid (Some (nat_event 2)) S3S3
| S3_2To4 tid: stuck3_step S3S2 tid (Some (nat_event 3)) S3S4.
Definition mod_stuck3 : module := {|
  m_state := stuck3_state;
  m_interface := ∅;
  m_initial := S3S1;
  m_in _ _ _ _:= False;
  m_step := stuck3_step;
  m_is_good s:= s ≠ S3S3;
|}.

Definition stuck3_inv (σ1 : stuck3_state) (σ2 : stuck1_state) :=
  σ1 ≠ S3S3 ∧
  σ2 = match σ1 with | S3S1 => S1S1 | S3S2 => S1S2 | S3S3 => S1S3 | S3S4 => S1S2 end.

(* The following is not provable: *)
Lemma test_refines_stuck3 :
  refines mod_stuck3 mod_stuck1.
Proof.
  apply: (inv_implies_refines mod_stuck3 mod_stuck1 stuck3_inv).
  - done.
  - move => [] ?[??] => //.
  - move => σi1 σs1 σi2 e [? ->] ? Hsafe. inv_step.
    + (* 1 -> 2 *) eexists _. split => //. apply: steps_Some; last by left. apply: (MSStep _ (Some _)). constructor.
    + (* 1 -> 3 *) exfalso.
      have [||]:= (Hsafe S1S3 [(tid, inr (nat_event 2))]) => //.
      apply: steps_Some; last by left. apply: (MSStep _ (Some _)). econstructor.
    + (* 2 -> 4 *) eexists _. split => //. apply: steps_Some; last by left. apply: (MSStep _ (Some _)).
      (* Not provable! *)
Abort.


Definition call_event (n : nat) : event := {|
  e_name := encode (nroot.@"call");
  e_type := nat;
  e_data := n;
|}.

(*
     Call 1
  1 -------- 2
 *)

Inductive call1_step : bool → thread_id → option event → bool → Prop :=
| C1_1To2 tid: call1_step false tid (Some (call_event 1)) true.
Definition mod_call1 : module := {|
  m_state := bool;
  m_interface := ∅;
  m_initial := false;
  m_in _ _ _ _:= False;
  m_step := call1_step;
  m_is_good s := True;
|}.

(*
            -> Call n     1 + n
  1 (done) ---------- 2 -------- 3
 *)

Inductive call2_state := | C2S1 | C2S2 (n : nat) | C2S3.
Inductive call2_in : call2_state → thread_id → event → call2_state → Prop :=
| C2In tid n: call2_in C2S1 tid (call_event n) (C2S2 n).
Inductive call2_step : call2_state → thread_id → option event → call2_state → Prop :=
| C2_2To3 tid n: call2_step (C2S2 n) tid (Some (nat_event (1 + n))) C2S3.
Definition mod_call2 : module := {|
  m_state := call2_state;
  m_interface := {[ encode (nroot.@"call") ]};
  m_initial := C2S1;
  m_in := call2_in;
  m_step := call2_step;
  m_is_good s := True;
|}.

Definition call_merge_inv (σ1 : bool * call2_state) (σ2 : bool) :=
  match σ1.1, σ1.2 with
  | false, C2S3 => False
  | false, C2S2 _ => False
  | _, C2S2 n => n = 1
  | _, _ => True
  end ∧ σ2 = if σ1.2 is C2S3 then true else false.
Lemma test_refines_call_merge :
  refines (module_without (module_product mod_call1 mod_call2) {[(call_event 0).(e_name)]}) mod1.
Proof.
  apply: (inv_implies_refines (module_without (module_product mod_call1 mod_call2) {[(call_event 0).(e_name)]}) mod1 call_merge_inv).
  - done.
  - done.
  - move => σi1 σs1 σi2 e [??] ? Hsafe. inv_step; try set_solver.
    + (* mod_call1 *)
      destruct σ2 => //. case_bool_decide; [|set_solver]. destruct_and!; subst.
      revert select (call2_in _ _ _ _) => /=.
      inversion 1; subst.
      revert select (existT _ _ = _) => /(UIPM.inj_pair2 _ _ _ _ _) ->.
      exists false. split => //. apply steps_refl.
    + (* mod_call2 *)
      destruct σ1 => //. destruct_and!; simplify_eq/=.
      exists true. split => //.
      apply: steps_Some; last by left. apply: (MSStep _ (Some _)). constructor.
Qed.

Definition call_split_inv (σ1 : bool) (σ2 : bool * call2_state) :=
  if σ1 then True else σ2 = (false, C2S1).
Lemma test_refines_call_split :
  refines mod1 (module_without (module_product mod_call1 mod_call2) {[(call_event 0).(e_name)]}).
Proof.
  apply: (inv_implies_refines mod1 (module_without (module_product mod_call1 mod_call2) {[(call_event 0).(e_name)]}) call_split_inv).
  - done.
  - done.
  - move => σi1 [σs1 σs2] σi2 e Hinv ? Hsafe. inv_step.
    exists (true, C2S3). split => //=.
    apply: (steps_None (true, C2S2 1)). 2: apply: steps_Some. 3: by left.
    + apply: (MSStep _ None). apply: MpStepL. constructor. simpl. case_bool_decide => //. set_solver.
    + apply: (MSStep _ (Some _)). apply: MpStepR. constructor => //. simpl. done.
      Unshelve. done.
Qed.
End test.
End version2.

Module version3.
Inductive steps {A B} (R : A → option B → A → Prop) : A → list B → A → Prop :=
| steps_refl ρ :
    steps R ρ [] ρ
| steps_l ρ1 ρ2 ρ3 κ κs :
    R ρ1 κ ρ2 →
    steps R ρ2 κs ρ3 →
    steps R ρ1 (option_list κ ++ κs) ρ3.

Inductive nsteps {A B} (R : A → option B → A → Prop) : nat → A → list B → A → Prop :=
| nsteps_refl ρ :
    nsteps R 0 ρ [] ρ
| nsteps_l ρ1 ρ2 ρ3 κ κs n:
    R ρ1 κ ρ2 →
    nsteps R n ρ2 κs ρ3 →
    nsteps R (S n) ρ1 (option_list κ ++ κs) ρ3.

Lemma steps_to_nsteps {A B} (R : A → option B → A → Prop) ρ1 κs ρ2:
  steps R ρ1 κs ρ2 → ∃ n, nsteps R n ρ1 κs ρ2.
Proof.
  elim. { move => ?. eexists _. by left. }
  move => ??????? [n ?]. exists (S n). by econstructor.
Qed.

Lemma nsteps_to_steps {A B} (R : A → option B → A → Prop) ρ1 κs ρ2 n:
  nsteps R n ρ1 κs ρ2 → steps R ρ1 κs ρ2.
Proof.
  elim. { move => ?. by left. }
  move => ?????????. by econstructor.
Qed.

Lemma nsteps_inv_end {A B} (R : A → option B → A → Prop) σ1 κ κs σ2 σ3 n:
  R σ1 κ σ2 → nsteps R n σ2 κs σ3 → ∃ κ' κs' σ2',
      option_list κ ++ κs = κs' ++ option_list κ' ∧ nsteps R n σ1 κs' σ2' ∧ R σ2' κ' σ3.
Proof.
  move => HR Hsteps. elim: Hsteps σ1 κ HR.
  - move => σ σ1 κ HR. exists κ, [], σ1. rewrite right_id_L /=. split_and! => //. by left.
  - move => σ1' σ2' σ3' κ' κs' n' HR Hsteps IH σ1 κ HR2.
    have [κ2 [κs2 [σs2 [-> [Hsteps2 HR3]]]]]:= (IH _ _ HR).
    eexists κ2, _, _. rewrite (assoc (++)). split_and! => //.
    by apply: nsteps_l.
Qed.

Lemma steps_rev_ind A B (R : A → option B → A → Prop) (P : A → list B → A → Prop):
  (∀ ρ : A, P ρ [] ρ) →
  (∀ (ρ1 ρ2 ρ3 : A) (κ : option B) (κs : list B),
        steps R ρ1 κs ρ2 → P ρ1 κs ρ2 → R ρ2 κ ρ3 → P ρ1 (κs ++ option_list κ) ρ3)
  → ∀ (y : A) (l : list B) (y0 : A), steps R y l y0 → P y l y0.
Proof.
  move => Hbase Hstep σ1 κs σ2 /(steps_to_nsteps _ _ _ _)[n ]. elim/lt_wf_ind: n σ1 κs σ2 => n IH σ1 κs σ2.
  inversion 1; simplify_eq. { by eauto. }
  have [?[?[?[-> [??]]]]]:= nsteps_inv_end _ _ _ _ _ _ _ H H0.
  apply: Hstep => //. by apply: nsteps_to_steps.
  apply: IH => //. lia.
Qed.

Lemma steps_option_list {A B} ρ2 (R : A → option B → A → Prop) ρ1 κ:
  R ρ1 κ ρ2 →
  steps R ρ1 (option_list κ) ρ2.
Proof.
  move => ?.
  rewrite -(right_id_L [] (++) (option_list _)).
    apply: steps_l => //. by left.
Qed.

Lemma steps_None {A B} ρ2 (R : A → option B → A → Prop) ρ1 ρ3 κs2:
  R ρ1 None ρ2 →
  steps R ρ2 κs2 ρ3 →
  steps R ρ1 (κs2) ρ3.
Proof. move => ??. by apply: (steps_l _ _ _ _ None). Qed.

Lemma steps_Some {A B} ρ2 (R : A → option B → A → Prop) ρ1 ρ3 κ κs2:
  R ρ1 (Some κ) ρ2 →
  steps R ρ2 κs2 ρ3 →
  steps R ρ1 (κ :: κs2) ρ3.
Proof. move => ??. by apply: (steps_l _ _ _ _ (Some κ)). Qed.

Lemma steps_trans {A B} (R : A → option B → A → Prop) ρ1 ρ2 ρ3 κs1 κs2:
  steps R ρ1 κs1 ρ2 →
  steps R ρ2 κs2 ρ3 →
  steps R ρ1 (κs1 ++ κs2) ρ3.
Proof. elim => // ?????????. rewrite -app_assoc. econstructor; eauto. Qed.

Lemma steps_trans_cons {A B} (R : A → option B → A → Prop) ρ1 ρ2 ρ3 κ1 κs2:
  steps R ρ1 [κ1] ρ2 →
  steps R ρ2 κs2 ρ3 →
  steps R ρ1 (κ1 :: κs2) ρ3.
Proof. move => ??. by apply: (steps_trans _ _ _ _ [κ1]). Qed.

Lemma steps_cons_inv {A B} (R : A → option B → A → Prop) ρ1 ρ3 κ1 κs2:
  steps R ρ1 (κ1 :: κs2) ρ3 → ∃ ρ2 ρ2', steps R ρ1 [] ρ2 ∧ R ρ2 (Some κ1) ρ2' ∧ steps R ρ2' κs2 ρ3.
Proof.
  move => /(steps_to_nsteps _ _ _ _)[n ]. elim/lt_wf_ind: n ρ1.
  move => n IH. inversion 1; simplify_eq. destruct κ; simplify_eq/=.
  - eexists _, _. split_and! => //; apply: nsteps_to_steps => //.
    by left.
  - have [|ρ [?[?[??]]]]:= IH _ _ _ H3. lia.
    eexists _, _. split_and! => //. by apply: steps_None.
Qed.

Lemma steps_cons_inv' {A B} (R : A → option B → A → Prop) ρ1 ρ3 κ1 κs2:
  steps R ρ1 (κ1 :: κs2) ρ3 → ∃ ρ2, steps R ρ1 [κ1] ρ2 ∧ steps R ρ2 κs2 ρ3.
Proof.
  move => /(steps_cons_inv _ _ _ _)[ρ2 [ρ2' [?[??]]]]. eexists _.
  split => //. apply: (steps_trans _ _ _ _ []) => //. apply: steps_Some => //. by left.
Qed.

Lemma steps_app_inv {A B} (R : A → option B → A → Prop) ρ1 ρ3 κs1 κs2:
  steps R ρ1 (κs1 ++ κs2) ρ3 → ∃ ρ2, steps R ρ1 κs1 ρ2 ∧ steps R ρ2 κs2 ρ3.
Proof.
  elim: κs1 ρ1 => /=. { move => ρ1 ?. exists ρ1. split => //. by left. }
  move => κ κs1 IH ρ1 /(steps_cons_inv' _ _ _ _)[ρ2 [? /IH[ρ2' [??]]]].
  eexists. split => //. by apply: steps_trans_cons.
Qed.

Definition thread_id := positive.

Record module (EV : Type) : Type := {
  m_state : Type;
  (* multiple initial states can be modeled by non-deterministically
  branching from the initial state *)
  m_initial : m_state;
  (* m_interface : coPset; *)
  m_step : m_state → option EV → m_state → Prop;
  (* making the following properties on events is tricky because then events are
  used for different purposes (should be the same in spec and target and for signaling UB) *)
  m_is_good : m_state → Prop;
  (* m_non_nb_state : m_state → Prop; *)
}.
Arguments m_state {_}.
Arguments m_initial {_}.
Arguments m_step {_}.
Arguments m_is_good {_}.

Definition safe_trace {EV} (m : module EV) (σ : m.(m_state)) (κ : list EV) : Prop :=
  (∀ σ' κ', κ' `prefix_of` κ → steps m.(m_step) σ κ' σ' → m.(m_is_good) σ').

Definition safe {EV} (m : module EV) : Prop :=
  (∀ κ, safe_trace m m.(m_initial) κ).

Record refines {EV} (mimpl mspec : module EV) := {
  ref_step κ σi:
    steps mimpl.(m_step) mimpl.(m_initial) κ σi →
    safe_trace mspec mspec.(m_initial) κ →
    mimpl.(m_is_good) σi ∧
    ∃ σs, steps (mspec.(m_step)) mspec.(m_initial) κ σs;
}.

(* Suggestion by Youngju: forall target trace, exists source trace, such that traces are equal up to the point where source gives ub or target gives NB event.
  Only works if language is deterministic?! (cannot exploit UB in other paths) *)

(*** wp': equivalent definition of refines *)
Inductive wp' {EV} (m1 m2 : module EV) : nat → m1.(m_state) -> list EV -> Prop :=
| Wp_step' σi1 κs n:
    (∀ κ, safe_trace m2 m2.(m_initial) (κs ++ option_list κ)
             → m1.(m_is_good) σi1 ∧
     (∀ σi2 n', n = S n' → m1.(m_step) σi1 κ σi2 ->
        ∃ σs2, steps (m2.(m_step)) m2.(m_initial) (κs ++ option_list κ) σs2 ∧
               wp' m1 m2 n' σi2 (κs ++ option_list κ))) ->
    wp' m1 m2 n σi1 κs
.

Lemma wp'_weaken {EV} (m1 m2 : module EV) κs σ n n':
  n' ≤ n →
  wp' m1 m2 n σ κs →
  wp' m1 m2 n' σ κs.
Proof.
  elim: n' n σ κs.
  - move => ???? Hwp. constructor => κ Hsafe. split; [ | lia].
    inversion Hwp as [??? Hwp']; simplify_eq.
      by have []:= Hwp' κ Hsafe.
  - move => n' IH [|n] σ κs ? Hwp. lia.
    inversion Hwp as [??? Hwp']; simplify_eq.
    constructor => κ Hsafe.
    have [? {}Hwp]:= Hwp' κ Hsafe.
    split => // σi2 ? [?] Hstep. subst.
    have [||?[??]]:= Hwp σi2 n => //.
    eexists _. split => //. apply: IH; [|done]. lia.
Qed.

Lemma forall_to_ex A B (P : A → B → Prop) (Q : B → Prop):
 (∃ n : A, ∀ y : B, P n y → Q y) -> ∀ y : B, ((∀ n : A, P n y) → Q y).
Proof. naive_solver. Qed.

Lemma wp'_implies_refines {EV} (m1 m2 : module EV):
  (∀ n, wp' m1 m2 n m1.(m_initial) []) →
  refines m1 m2.
Proof.
  move => Hwp.
  constructor => κs σi.
  move: m1.(m_initial) Hwp => σi1.
  have : (steps m2.(m_step) m2.(m_initial) [] m2.(m_initial)). { by left. }
  move: {2}m2.(m_initial) => σs1.
  have : κs = [] ++ κs by [].
  move: ([]) => κstart. move: {2 3}(κs) => κend.
  move => Hκ Hs Hwp Hsteps Hsafe.
  move: κstart Hwp σs1 Hs Hsafe Hκ. apply: forall_to_ex.
  elim: Hsteps => {σi1 κend σi}.
  - move => σi1. exists 0 => κstart Hwp σs Hsteps Hsafe Hκ.
    rewrite right_id in Hκ; subst. split; eauto.
    destruct Hwp as [??? Hwp].
    move: (Hwp None) => [|] //=.
    by rewrite right_id.
  - move => σi1 σi2 σi3 κ κend Hstep Hsteps [n IH]. exists (S n) => κstart Hwp σs1 Hstepsi Hsafe Hκs.
    inversion_clear Hwp as [??? Hwp2]; subst.
    move : (Hwp2 κ) => [|? Hwp] //=. { move => ???. apply Hsafe. etrans => //. rewrite assoc. by eexists. }
    have [|σs2 [Hsteps2 {}Hwp]]:= (Hwp _ n _ Hstep) => //.
    have [||?[??]]:= (IH _ Hwp _ Hsteps2) => //. by rewrite assoc.
    split => //. naive_solver.
Qed.

Lemma refines_implies_wp' {EV} (m1 m2 : module EV):
  refines m1 m2 →
  (∀ n, wp' m1 m2 n m1.(m_initial) []).
Proof.
  move => Hr n.
  have : (steps m1.(m_step) m1.(m_initial) [] m1.(m_initial)). { by left. }
  move: {2 3}(m1.(m_initial)) => σi.
  move: ([]) => κstart.
  elim/lt_wf_ind: n κstart σi.
  move => n IH κstart σi Hstepi.
  constructor => κ Hsafe.
  have [|??]:= (ref_step _ _ Hr _ _ Hstepi). { move => ???. apply Hsafe. etrans => //. by eexists. }
  split => // σi2 n' ? Hstep; subst.
  have Hs1' : steps (m_step m1) (m_initial m1) (κstart ++ option_list κ) σi2. {
    apply: steps_trans => //.
    rewrite -(right_id_L [] (++) (option_list _)).
    apply: steps_l => //. by left.
  }
  have [|?[? Hs]]:= (ref_step _ _ Hr _ _ Hs1') => //.
  eexists _. split => //.
  apply: IH => //. lia.
Qed.

(*** properties of refines *)
Lemma refines_preserves_safe EV (mspec mimpl : module EV):
  safe mspec →
  refines mimpl mspec →
  safe mimpl.
Proof.
  move => Hs Hr κ σ' κ' Hpre Hstep.
  have [|]:= (ref_step _ _ Hr _ _ Hstep); by eauto.
Qed.

Lemma refines_reflexive EV (m : module EV):
  refines m m.
Proof. constructor => // κ σi Hi Hs; naive_solver. Qed.

Lemma refines_vertical EV (m1 m2 m3 : module EV):
  refines m1 m2 →
  refines m2 m3 →
  refines m1 m3.
Proof.
  move => Hr1 Hr2.
  constructor => /=.
  - move => κ σi Hstep1 Hsafe3.
    have [|Hgood [σ2 Hstep2]] := (ref_step _ _ Hr1 _ _ Hstep1) => //. {
      move => σs2 κ' Hprefix Hstep2.
      have [|? _] := (ref_step _ _ Hr2 _ _ Hstep2); eauto.
      move => σs3 κ'2 Hprefix2 Hstep3.
      apply: Hsafe3;[ |done]. by etrans.
    }
    split => //.
    by have [|_ [σ3 Hstep3]] := (ref_step _ _ Hr2 _ _ Hstep2); eauto.
Qed.

(*** link *)
Inductive link_step {EV1 EV2 EV3} (m1 : module EV1) (m2 : module EV2) (R : option EV1 → option EV2 → option EV3 → Prop) :
  m1.(m_state) * m2.(m_state) → option EV3 → m1.(m_state) * m2.(m_state) → Prop :=
| LinkStepL σ1 σ2 e1 e' σ1':
    m1.(m_step) σ1 e1 σ1' →
    (* TODO: is there a better way to formulate this? E.g. assume
    that there is no R None None Some in the theorem? *)
    (if e1 is Some es1 then R e1 None e' else e' = None) →
    link_step m1 m2 R (σ1, σ2) e' (σ1', σ2)
| LinkStepR σ1 σ2 e2 e' σ2':
    m2.(m_step) σ2 e2 σ2' →
    (if e2 is Some es2 then R None e2 e' else e' = None) →
    link_step m1 m2 R (σ1, σ2) e' (σ1, σ2')
| LinkStepBoth σ1 σ2 e1 e2 e' σ1' σ2':
    m1.(m_step) σ1 (Some e1) σ1' →
    m2.(m_step) σ2 (Some e2) σ2' →
    R (Some e1) (Some e2) e' →
    link_step m1 m2 R (σ1, σ2) e' (σ1', σ2').


(*

  mod1 EV1 := nat + Z

  mod2 EV2 := nat + bool

  -> mod3 := Z + bool

  R (Some (inl n)) (Some (inl n)) None
  R (Some (inr z)) None           (Some (inl z))
  R None           (Some (inr b)) (Some (inr b))



  mem_mod EV := Alloc (l : loc) | Read (l : loc) (v : val) | ReadNA (l : loc) (v : val) | Store (l : loc) (v : val)

  c_mod EV := Alloc (l : loc) | Read (l : loc) (v : val) | Store (l : loc) (v : val) | Syscall


   mem_mod:
              h !! l = Some vold
   h -------CAS(l, vold, vnew, true)------> <[l := vnew]> h
            h !! l = Some v ∧ v ≠ vold
   h -------CAS(l, vold, vnew, false)------> h


   c_mod:

   E[CAS(l, vold, vnew)] -------CAS(l, vold, vnew, b)------> E[b]


   yield()
   b = Call CAS(l, vold, new);
   yield()


       h !! l = Some v      h !! l = Some v'
   h -------FAA(l)------> h ---------------> <[l := v' + 1]>h

       h !! l = Some v
   h -------FAA(l)------> <[l := v + 1]>h


      h !! l = Some v
   h ---READ(l, v)---> h -STORE(l, v + 1)-> <[l]h

 *)



Definition link {EV1 EV2 EV3} (m1 : module EV1) (m2 : module EV2) (R : option EV1 → option EV2 → option EV3 → Prop) : module EV3 := {|
  m_state := m1.(m_state) * m2.(m_state);
  m_initial := (m1.(m_initial), m2.(m_initial));
  m_step := (link_step m1 m2 R);
  m_is_good σ := m1.(m_is_good) σ.1 ∧ m2.(m_is_good) σ.2;
|}.


Lemma link_empty_steps_l {EV1 EV2 EV3} m1 m2 σ1 σ1' σ2 (R : option EV1 → option EV2 → option EV3 → Prop) :
  steps (m_step m1) σ1 [] σ1' →
  steps (link_step m1 m2 R) (σ1, σ2) [] (σ1', σ2).
Proof.
  move Hκ: ([]) => κ Hsteps.
  elim: Hsteps Hκ. by left.
  move => ??? [] //= ?????.
  apply: (steps_l _ _ _ _ None); [ | naive_solver].
    by econstructor.
Qed.

Lemma link_empty_steps_r {EV1 EV2 EV3} m1 m2 σ1 σ2' σ2 (R : option EV1 → option EV2 → option EV3 → Prop) :
  steps (m_step m2) σ2 [] σ2' →
  steps (link_step m1 m2 R) (σ1, σ2) [] (σ1, σ2').
Proof.
  move Hκ: ([]) => κ Hsteps.
  elim: Hsteps Hκ. by left.
  move => ??? [] //= ?????.
  apply: (steps_l _ _ _ _ None); [ | naive_solver].
    by econstructor.
Qed.

Inductive link_trace_related {EV1 EV2 EV3} (R : option EV1 → option EV2 → option EV3 → Prop) : list EV1 → list EV2 → list EV3 → Prop :=
| LinkTraceRelNil:
    link_trace_related R [] [] []
| LinkTraceRelL κ1 κ1' κs1 κs2 κs3:
    link_trace_related R κs1 κs2 κs3 →
    R (Some κ1) None κ1' →
    link_trace_related R (κs1 ++ [κ1]) κs2 (κs3 ++ option_list κ1')
| LinkTraceRelR κ2 κ2' κs1 κs2 κs3:
    link_trace_related R κs1 κs2 κs3 →
    R None (Some κ2) κ2' →
    link_trace_related R κs1 (κs2 ++ [κ2]) (κs3 ++ option_list κ2')
| LinkTraceRelBoth κ1 κ2 κ3 κs1 κs2 κs3:
    link_trace_related R κs1 κs2 κs3 →
    R (Some κ1) (Some κ2) κ3 →
    link_trace_related R (κs1 ++ [κ1]) (κs2 ++ [κ2]) (κs3 ++ option_list κ3)
.

Lemma link_trace_related_create {EV1 EV2 EV3} (R : option EV1 → option EV2 → option EV3 → Prop) m1 m2 κs3 σ1 σ1':
  steps (link m1 m2 R).(m_step) σ1 κs3 σ1' →
  ∃ κs1 κs2, link_trace_related R κs1 κs2 κs3 ∧
  steps m1.(m_step) σ1.1 κs1 σ1'.1 ∧
  steps m2.(m_step) σ1.2 κs2 σ1'.2.
Proof.
  elim/steps_rev_ind; clear. { move => ?. exists [], []. split_and!; constructor. }
  move => σ1 σ2 σ3 κ κs Hsteps [κs1 [κs2 [Hlink [Hκ1 Hκ2]]]] Hstep.
  inversion Hstep; clear Hstep; simplify_eq.
  - exists (κs1 ++ option_list e1), κs2.
    split_and! => //; destruct e1; simplify_eq/= => //; rewrite ?right_id //. by constructor.
    + apply: steps_trans => //. apply: steps_Some => //. left.
    + rewrite -(right_id_L [] (++) κs1).
      apply: steps_trans => //. apply: steps_None => //. left.
  - exists κs1, (κs2 ++ option_list e2).
    split_and! => //; destruct e2; simplify_eq/= => //; rewrite ?right_id //. by constructor.
    + apply: steps_trans => //. apply: steps_Some => //. left.
    + rewrite -(right_id_L [] (++) κs2).
      apply: steps_trans => //. apply: steps_None => //. left.
  - exists (κs1 ++ [e1]), (κs2 ++ [e2]).
    split_and!.
    + by apply LinkTraceRelBoth.
    + apply: steps_trans => //. apply: steps_Some => //. left.
    + apply: steps_trans => //. apply: steps_Some => //. left.
Qed.

Lemma link_trace_related_step {EV1 EV2 EV3} (R : option EV1 → option EV2 → option EV3 → Prop) m1 m2 κs1 κs2 κs3 σ1 σ1' σ2 σ2':
  link_trace_related R κs1 κs2 κs3 →
  steps m1.(m_step) σ1 κs1 σ1' →
  steps m2.(m_step) σ2 κs2 σ2' →
  steps (link m1 m2 R).(m_step) (σ1, σ2) κs3 (σ1', σ2').
Proof.
  move => Hrel.
  elim: Hrel σ1' σ2'; clear.
  - move => σ1' σ2' Hstep1 Hstep2.
    apply: (steps_trans  _ _ _ _ [] []). by apply: link_empty_steps_l.
      by apply: link_empty_steps_r.
  - move => κ1 κ1' κs1 κs2 κs3 ? IH HR σ1' σ2' /(steps_app_inv _ _ _)[σ' [? /(steps_cons_inv _ _ _ _)[?[?[?[??]]]]]] ?.
    apply: steps_trans. by apply IH.
    apply: (steps_trans _ _ _ _ []). by apply: link_empty_steps_l.
    rewrite -/option_list.
    rewrite -(right_id_L [] (++) (option_list _)).
    apply: steps_trans. { apply: steps_option_list. by apply: LinkStepL. }
    by apply: link_empty_steps_l.
  - move => κ2 κ2' κs1 κs2 κs3 ? IH HR σ1' σ2' ? /(steps_app_inv _ _ _)[σ' [? /(steps_cons_inv _ _ _ _)[?[?[?[??]]]]]].
    apply: steps_trans. by apply IH.
    apply: (steps_trans _ _ _ _ []). by apply: link_empty_steps_r.
    rewrite -/option_list.
    rewrite -(right_id_L [] (++) (option_list _)).
    apply: steps_trans. { apply: steps_option_list. by apply: LinkStepR. }
    by apply: link_empty_steps_r.
  - move => κ1 κ2 κ3 κs1 κs2 κs3 ? IH HR σ1' σ2' /(steps_app_inv _ _ _)[σ' [? /(steps_cons_inv _ _ _ _)[?[?[?[??]]]]]] /(steps_app_inv _ _ _)[? [? /(steps_cons_inv _ _ _ _)[?[?[?[??]]]]]].
    apply: steps_trans. by apply IH.
    apply: (steps_trans _ _ _ _ []). by apply: link_empty_steps_r.
    apply: (steps_trans _ _ _ _ []). by apply: link_empty_steps_l.
    rewrite -/option_list.
    rewrite -(right_id_L [] (++) (option_list _)).
    apply: steps_trans. { apply: steps_option_list. by apply: LinkStepBoth. }
    apply: (steps_trans _ _ _ _ []). by apply: link_empty_steps_l.
    by apply: link_empty_steps_r.
Qed.

Lemma link_trace_related_inv_l {EV1 EV2 EV3} (R : option EV1 → option EV2 → option EV3 → Prop) κs1 κs2 κs3 κs1':
  κs1' `prefix_of` κs1 →
  link_trace_related R κs1 κs2 κs3 →
  ∃ κs2' κs3', κs2' `prefix_of` κs2 ∧ κs3' `prefix_of` κs3 ∧
               link_trace_related R κs1' κs2' κs3'.
Proof.
  move => Hpre Hprod. elim: Hprod Hpre; clear.
  - destruct κs1'; [ | by move => /(prefix_nil_not _ _)] => ?.
    exists [], []. split_and! => //. constructor.
  - move => κ1 κ1' κs1 κs2 κs3 Hprod IH HR [κend Hpre].
    have [?|[κ [κend' ?]]]:= snoc_inv κend; subst.
    + rewrite right_id in Hpre. subst.
      eexists _, _. split_and! => //. by constructor.
    + rewrite assoc in Hpre. move: Hpre => /(app_inj_tail _ _ _ _)[??]. subst.
      have [|?[?[?[??]]]]:= IH. by apply prefix_app_r.
      eexists _, _. split_and!; [done | |done..].
      etrans => //. by apply prefix_app_r.
  - move => κ1 κ1' κs1 κs2 κs3 Hprod IH HR ?.
    have [|?[?[?[??]]]]:= IH => //.
    eexists _, _. split_and!; [| |done..].
    all: etrans => //.
    all: by apply prefix_app_r.
  - move => κ1 κ2 κ3 κs1 κs2 κs3 Hprod IH HR [κend Hpre].
    have [?|[κ [κend' ?]]]:= snoc_inv κend; subst.
    + rewrite right_id in Hpre. subst.
      eexists _, _. split_and! => //. by constructor.
    + rewrite assoc in Hpre. move: Hpre => /(app_inj_tail _ _ _ _)[??]. subst.
      have [|?[?[?[??]]]]:= IH. by apply prefix_app_r.
      eexists _, _. split_and!; [| |done..].
      all: etrans => //.
      all: by apply prefix_app_r.
Qed.

Lemma link_trace_related_inv_r {EV1 EV2 EV3} (R : option EV1 → option EV2 → option EV3 → Prop) κs1 κs2 κs3 κs2':
  κs2' `prefix_of` κs2 →
  link_trace_related R κs1 κs2 κs3 →
  ∃ κs1' κs3', κs1' `prefix_of` κs1 ∧ κs3' `prefix_of` κs3 ∧
               link_trace_related R κs1' κs2' κs3'.
Proof.
  move => Hpre Hprod. elim: Hprod Hpre; clear.
  - destruct κs2'; [ | by move => /(prefix_nil_not _ _)] => ?.
    exists [], []. split_and! => //. constructor.
  - move => κ1 κ1' κs1 κs2 κs3 Hprod IH HR ?.
    have [|?[?[?[??]]]]:= IH => //.
    eexists _, _. split_and!; [| |done..].
    all: etrans => //.
    all: by apply prefix_app_r.
  - move => κ1 κ1' κs1 κs2 κs3 Hprod IH HR [κend Hpre].
    have [?|[κ [κend' ?]]]:= snoc_inv κend; subst.
    + rewrite right_id in Hpre. subst.
      eexists _, _. split_and! => //. by constructor.
    + rewrite assoc in Hpre. move: Hpre => /(app_inj_tail _ _ _ _)[??]. subst.
      have [|?[?[?[??]]]]:= IH. by apply prefix_app_r.
      eexists _, _. split_and!; [done | |done..].
      etrans => //. by apply prefix_app_r.
  - move => κ1 κ2 κ3 κs1 κs2 κs3 Hprod IH HR [κend Hpre].
    have [?|[κ [κend' ?]]]:= snoc_inv κend; subst.
    + rewrite right_id in Hpre. subst.
      eexists _, _. split_and! => //. by constructor.
    + rewrite assoc in Hpre. move: Hpre => /(app_inj_tail _ _ _ _)[??]. subst.
      have [|?[?[?[??]]]]:= IH. by apply prefix_app_r.
      eexists _, _. split_and!; [| |done..].
      all: etrans => //.
      all: by apply prefix_app_r.
Qed.

Lemma refines_horizontal {EV1 EV2 EV3} m1 m2 m1' m2' (R : option EV1 → option EV2 → option EV3 → Prop) :
  (* TODO: it is also ok to get this for m1' *)
  (∀ κs, LEM (∃ σf2, steps (m_step m2') (m_initial m2') κs σf2))  →
  refines m1 m1' →
  refines m2 m2' →
  refines (link m1 m2 R) (link m1' m2' R).
Proof.
  move => HLEM /refines_implies_wp' Hr1 /refines_implies_wp' Hr2.
  apply: wp'_implies_refines => n /=.
  move: (Hr1 n) (Hr2 n).
  have : (∃ σ, steps m1'.(m_step) m1'.(m_initial) [] σ). { eexists. by left. }
  have : (∃ σ, steps m2'.(m_step) m2'.(m_initial) [] σ). { eexists. by left. }
  move: (m1.(m_initial)) => σi1. move: (m2.(m_initial)) => σi2.
  have := (LinkTraceRelNil R).
  move: [] => κs1. move: [] => κs2. move: [] => κs3.
  move: σi1 σi2 κs1 κs2 κs3.
  elim/lt_wf_ind: n => n IH σi1 σi2 κs1 κs2 κs3 Hrel [σs2 Hs2] [σs1 Hs1] {}Hr1 {}Hr2.
  constructor => κ Hsafe.
  inversion Hr1 as [??? Hwp1]; simplify_eq.
  inversion Hr2 as [??? Hwp2]; simplify_eq.
  split.
  - have [|? _] := Hwp1 None => /=. {
      rewrite right_id.
      move => σs κ' Hpre Hsteps.
      have [? [κs3' [[??] [[??]?]]]]:= link_trace_related_inv_l _ _ _ _ _ Hpre Hrel; subst.
      move: Hs2 => /(steps_app_inv _ _ _)[σ2 [??]].
      have []:= Hsafe (σs, σ2) κs3' => //.
      - apply prefix_app_r. by apply prefix_app_r.
      - by apply: link_trace_related_step.
    }
    have [|? _] := Hwp2 None => /=. {
      rewrite right_id.
      move => σs κ' Hpre Hsteps.
      have [? [κs3' [[??] [[??]?]]]]:= link_trace_related_inv_r _ _ _ _ _ Hpre Hrel; subst.
      move: Hs1 => /(steps_app_inv _ _ _)[σ2 [??]].
      have []:= Hsafe (σ2, σs) κs3' => //.
      - apply prefix_app_r. by apply prefix_app_r.
      - by apply: link_trace_related_step.
    }
    done.
  - move => [σi1' σi2'] n' ? Hstep. subst.
    inversion Hstep; clear Hstep; simplify_eq/=.
    + have {}Hrel : link_trace_related R (κs1 ++ option_list e1) κs2 (κs3 ++ option_list κ). {
        destruct e1; simplify_eq/=; [| by rewrite !right_id].
        by apply LinkTraceRelL.
      }
      have {Hwp1 Hwp2}[|_ Hwp1] := Hwp1 e1. {
        move => σs κ' Hpre Hsteps.
        have [? [κs3' [[??] [[? Heq]?]]]]:= link_trace_related_inv_l _ _ _ _ _ Hpre Hrel; subst.
        move: Hs2 => /(steps_app_inv _ _ _)[σ2 [??]].
        have []:= Hsafe (σs, σ2) κs3' => //.
        - rewrite Heq. by apply prefix_app_r.
        - by apply: link_trace_related_step.
      }
      have [|σs1' [Hsteps {}Hwp1]]:= Hwp1 _ n' _ H3 => //.
      exists (σs1', σs2).
      split.
      * by apply: link_trace_related_step.
      * apply: IH => //; try by eexists. lia. apply: wp'_weaken; [| done]. lia.
    + have {}Hrel : link_trace_related R κs1 (κs2 ++ option_list e2) (κs3 ++ option_list κ). {
        destruct e2; simplify_eq/=; [| by rewrite !right_id].
        by apply LinkTraceRelR.
      }
      have {Hwp1 Hwp2}[|_ Hwp] := Hwp2 e2. {
        move => σs κ' Hpre Hsteps.
        have [? [κs3' [[??] [[? Heq]?]]]]:= link_trace_related_inv_r _ _ _ _ _ Hpre Hrel; subst.
        move: Hs1 => /(steps_app_inv _ _ _)[σ2 [??]].
        have []:= Hsafe (σ2, σs) κs3' => //.
        - rewrite Heq. by apply prefix_app_r.
        - by apply: link_trace_related_step.
      }
      have [|σs' [Hsteps {}Hwp]]:= Hwp _ n' _ H3 => //.
      exists (σs1, σs').
      split.
      * by apply: link_trace_related_step.
      * apply: IH => //; try by eexists. lia. apply: wp'_weaken; [| done]. lia.
    + move: Hrel => Hrelold.
      have Hrel : link_trace_related R (κs1 ++ [e1]) (κs2 ++ [e2]) (κs3 ++ option_list κ). {
        by apply LinkTraceRelBoth.
      }
      have [[of2 Hfsteps]|Hnof2]:= HLEM (κs2 ++ [e2]).
      * have {Hwp1}[|_ Hwp1] := Hwp1 (Some e1). {
          move => σs κ' Hpre Hsteps.
          have [? [κs3' [[? Heq1] [[? Heq]?]]]]:= link_trace_related_inv_l _ _ _ _ _ Hpre Hrel; subst.
          rewrite Heq1 in Hfsteps.
          move: Hfsteps => /(steps_app_inv _ _ _)[σ2 [??]].
          have []:= Hsafe (σs, σ2) κs3' => //.
          - rewrite Heq. by apply prefix_app_r.
          - by apply: link_trace_related_step.
        }
        have [|/=σs1' [Hsteps1 {}Hwp1]]:= Hwp1 _ n' _ H4 => //.
        have {Hwp2}[|_ Hwp2] := Hwp2 (Some e2). {
          move => σs κ' Hpre Hsteps.
          have [? [κs3' [[? Heq1] [[? Heq]?]]]]:= link_trace_related_inv_r _ _ _ _ _ Hpre Hrel; subst.
          rewrite Heq1 in Hsteps1.
          move: Hsteps1 => /(steps_app_inv _ _ _)[σ2 [??]].
          have []:= Hsafe (σ2,σs) κs3' => //.
          - rewrite Heq. by apply prefix_app_r.
          - by apply: link_trace_related_step.
        }
        have [|σs2' [Hsteps2 {}Hwp2]]:= Hwp2 _ n' _ H5 => //.
        exists (σs1', σs2').
        split.
        -- by apply: link_trace_related_step.
        -- apply: IH => //; try by eexists. lia.
      * have {Hwp2}[|_ Hwp2] := Hwp2 (Some e2). {
          move => σs κ' [κend Hpre] Hsteps.
          have [?|[κ'' [κend' ?] ]]:= snoc_inv κend; subst.
          { rewrite right_id in Hpre. subst. naive_solver. }
          move: Hpre => /=. rewrite assoc. move => /(app_inj_tail _ _ _ _)[??]. subst.
          have [|? [κs3' [[? Heq1] [[? Heq]?]]]]:= link_trace_related_inv_r _ _ _ _ κ' _ Hrelold; subst.
          { by apply prefix_app_r. }
          move: Hs1 => /(steps_app_inv _ _ _)[σ2 [??]].
          have []:= Hsafe (σ2,σs) κs3' => //.
          - apply prefix_app_r. by apply prefix_app_r.
          - by apply: link_trace_related_step.
        }
        have [|σs2' [Hsteps2 {}Hwp2]]:= Hwp2 _ n' _ H5 => //.
        naive_solver.
Qed.
(*   (* The following is a failed attempt at simplifying the previous proof. *) *)
(*   move => HLEM [Hr1] [Hr2]. *)
(*   constructor => κs σi Hsteps Hsafe. *)
(*   have [κs1 [κs2 [Hrel [Hs1 Hs2]]]] := link_trace_related_create _ _ _ _ _ _ Hsteps. *)
(*   have [[of2 Hfsteps]|Hnof2]:= HLEM κs2. *)
(*   - have [|? [σs1 Hsteps1]]:= Hr1 _ _ Hs1. { *)
(*       move => σs κ' Hpre Hsteps1. *)
(*       have [? [κs3' [[??] [[??]?]]]]:= link_trace_related_inv_l _ _ _ _ _ Hpre Hrel; subst. *)
(*       move: Hfsteps => /(steps_app_inv _ _ _)[σ2 [??]]. *)
(*       have []:= Hsafe (σs, σ2) κs3' => //. *)
(*       - by apply prefix_app_r. *)
(*       - by apply: link_trace_related_step. *)
(*     } *)
(*     have [|? [σs2 ?]]:= Hr2 _ _ Hs2. { *)
(*       move => σs κ' Hpre ?. *)
(*       have [? [κs3' [[??] [[??]?]]]]:= link_trace_related_inv_r _ _ _ _ _ Hpre Hrel; subst. *)
(*       move: Hsteps1 => /(steps_app_inv _ _ _)[σ2 [??]]. *)
(*       have []:= Hsafe (σ2, σs) κs3' => //. *)
(*       - by apply prefix_app_r. *)
(*       - by apply: link_trace_related_step. *)
(*     } *)
(*     split => //. *)
(*     eexists (σs1, σs2). *)
(*     by apply: link_trace_related_step. *)
(*   - have [|? [σs2 ?]]:= Hr2 _ _ Hs2; [|naive_solver]. *)
(*     move => σs κ' [κend Hpre] ?. *)
(*     subst. *)
(*     have [?|[κ'' [κend' ?] ]]:= snoc_inv κend; subst. *)
(*     { rewrite right_id in Hs1, Hnof2. naive_solver. } *)
(*     have [||||_ [? Hs]]:= IH (length (κ' ++ κend')) _ (κ' ++ κend') => //. { *)
(*       rewrite !app_length /=. lia. *)
(*     } { *)
(*       admit. *)
(*     } { *)
(*       admit. *)
(*     } *)

(*     (* TODO: need steps (m_step m1') (m_initial m1') ?? σ here *) *)
(* Abort. *)

(* TODO: prove something like the following? *)
Lemma refines_horizontal_mut_rec {EV1 EV2 EV3} m1 m2 m1' m2' (R : option EV1 → option EV2 → option EV3 → Prop) :
  (* TODO: it is also ok to get this for m1' *)
  (∀ κs, LEM (∃ σf2, steps (m_step m2') (m_initial m2') κs σf2)) →
  refines (link m1 m2' R) (link m1' m2' R) →
  refines (link m1' m2 R) (link m1' m2' R) →
  refines (link m1 m2 R) (link m1' m2' R).
Proof.
Abort.


(*

  fib(n) := mathematical


  fibA(n) :=                     fibB(n) :=
  if (n = 0) ...

  mem... fibB(n-1) + fibB(n-2)


  (link fibA fib) refines (link fib fib)

  (link fibB fib) refines (link fib fib)

*)



(*** Proving refinement *)
Lemma inv_implies_refines {EV} (m1 m2 : module EV) (inv : m1.(m_state) → m2.(m_state) → Prop):
  inv m1.(m_initial) m2.(m_initial) →
  (∀ σi σs, inv σi σs → m1.(m_is_good) σi) →
  (∀ σi1 σs1 σi2 e,
      inv σi1 σs1 → m1.(m_step) σi1 e σi2 →
      safe_trace m2 σs1 (option_list e) →
      ∃ σs2, inv σi2 σs2 ∧ steps m2.(m_step) σs1 (option_list e) σs2) →
  refines m1 m2.
Proof.
  move => Hinvinit Hinvsafe Hinvstep.
  constructor => // κ σi2. move: m1.(m_initial) m2.(m_initial) Hinvinit => σi1 σs1 Hinv Hsteps Hspec.
  elim: Hsteps σs1 Hinv Hspec => {σi1 κ σi2}.
  - by eauto using steps_refl.
  - move => σi1 σi2 σi3 κ κs Hstep Hsteps IH σs1 Hinv Hspec.
    case: (Hinvstep _ _ _ _ Hinv Hstep).
    { move => ???. apply: Hspec. etrans; first done. destruct κ; [apply prefix_cons|]; apply prefix_nil. }
    move => σs2 [Hinv2 Hssteps]. case: (IH _ Hinv2) => //.
    + move => σs κ' Hprefix Hs. apply: Hspec. 2: by apply: steps_trans. by apply prefix_app.
    + move => Hsafe [σs3 Hs]. split => //. eexists. by apply: steps_trans.
Qed.

(* TODO: another version: keep track of a set of states for the source. See POPL13 paper by Aaron and Derek. Can you prove equivalence with wp'? *)

Inductive wp {EV} (m1 m2 : module EV) : nat → m1.(m_state) -> m2.(m_state) -> Prop :=
| Wp_step σi1 σs1 n:
    (∀ κ, safe_trace m2 σs1 (option_list κ) → m1.(m_is_good) σi1 ∧
    (∀ σi2 n', n = S n' → m1.(m_step) σi1 κ σi2 ->
       ∃ σs2, steps (m2.(m_step)) σs1 (option_list κ) σs2 ∧ wp m1 m2 n' σi2 σs2)) ->
    wp m1 m2 n σi1 σs1
.

Lemma wp_implies_refines {EV} (m1 m2 : module EV):
  (∀ n, wp m1 m2 n m1.(m_initial) m2.(m_initial)) →
  refines m1 m2.
Proof.
  move => Hwp. apply: wp'_implies_refines.
  move => n. move: (Hwp n).
  have : (steps m2.(m_step) m2.(m_initial) [] m2.(m_initial)). { by left. }
  move: {2 3}m2.(m_initial) => σs. move: m1.(m_initial) => σi.
  move: [] => κs.
  elim/lt_wf_ind: n σi σs κs => n IH σi σs κs Hsteps {}Hwp.
  constructor => κ Hsafe.
  inversion Hwp as [??? Hwp']; clear Hwp; simplify_eq.
  have [|? {}Hwp]:= Hwp' κ. {
    move => ????. apply: Hsafe. 2: by apply: steps_trans.
      by apply prefix_app.
  }
  split => // σi2 n' ? Hstep. subst.
  have [|?[??]]:= Hwp _ n' _ Hstep => //.
  eexists _. split; [ by apply: steps_trans |].
  apply: IH => //. lia.
  by apply: steps_trans.
Qed.

Ltac inv_step :=
  repeat lazymatch goal with
  | H : m_step _ _ _ _  |- _ => inversion H; clear H
  end; simplify_eq/=.

(*** Tests *)
(*
  TODO: add the following tests:
  with P undecidable:

  guarantee P; ->
    if P
  1 ----> 2
   \
    \ if neg P, UB
     ----------

  rely P;
    if P
  1 ----> 2
   \
    \ if neg P, NB
     ----------

  First should refine the second?
 *)

(*
  TODO: prove the following refinement for which wp is probably not enough

            A     B
           /- 2  --- 3
  spec: 1 -
           \- 2' --- 4
            A     C

                  B
           A     /- 3
  impl: 1 --- 2 -
                 \- 4
                 C

*)
(*
  TODO: prove the following refinement for which wp is probably not enough

   x := N;            x := N;          x := N;
   y := alloc()       y := alloc()     y := N;
   *y = 1;       -->  *y = 1;      --> *y := 1;
   *x = 2;            *x = 2;          *x := 2;
   return *y;         return 1;        return 1;

   Memory model:
   - heap: Z -fin> Z
   - alloc returns non-deterministically a free address
   - store is UB for unallocated address

*)
Module test.

(*   2
  1 --- 2 (done)
 *)
Inductive mod1_step : bool → option nat → bool → Prop :=
| T1False: mod1_step false (Some 2) true.


Definition mod1 : module nat := {|
  m_state := bool;
  m_initial := false;
  m_step := mod1_step;
  m_is_good s:= True;
|}.

(*         2
  1 --- 2 --- 3 (done)
 *)
Inductive mod2_state := | S1 | S2 | S3.
Inductive mod2_step : mod2_state → option nat → mod2_state → Prop :=
| T2S1: mod2_step S1 None S2
| T2S2: mod2_step S2 (Some 2) S3.
Definition mod2 : module nat := {|
  m_state := mod2_state;
  m_initial := S1;
  m_step := mod2_step;
  m_is_good s:= True;
|}.

Definition t2_to_t1_inv (σ1 : mod2_state) (σ2 : bool) : Prop :=
  σ2 = match σ1 with
  | S1 | S2 => false
  | _ => true
  end.
Lemma test_refines1 :
  refines mod2 mod1.
Proof.
  apply: (inv_implies_refines mod2 mod1 t2_to_t1_inv).
  - done.
  - done.
  - move => σi1 σs1 σi2 e -> ? Hsafe. inv_step; eexists _; split => //.
    + by left.
    + apply: steps_Some; last by left. constructor.
Qed.

Definition mod_loop {A} : module A := {|
  m_state := unit;
  m_initial := tt;
  m_step _ e _ := e = None;
  m_is_good s:= True;
|}.
Lemma test_refines2 {A} (m : module A) :
  refines mod_loop m.
Proof.
  apply: (inv_implies_refines mod_loop m (λ _ _, True)).
  - done.
  - done.
  - move => ???????. inv_step. eexists. split => //. left.
Qed.

Lemma test_refines2_wp {A} (m : module A) :
  refines mod_loop m.
Proof.
  apply: wp_implies_refines => /=.
  move => n. elim/lt_wf_ind: n => n Hloop.
  constructor => κ' Hsafe. split => // [[]] n' ??.
  inv_step. eexists. split; [left|]. apply Hloop.
  lia.
Qed.


(*   1
      /- 2 (done)
  1 --
      \- 3 (stuck)
     2
 *)

Inductive stuck1_state := | S1S1 | S1S2 | S1S3.
Inductive stuck1_step : stuck1_state → option nat → stuck1_state → Prop :=
| S1_1To2: stuck1_step S1S1 (Some 1) S1S2
| S1_1To3: stuck1_step S1S1 (Some 2) S1S3.
Definition mod_stuck1 : module nat := {|
  m_state := stuck1_state;
  m_initial := S1S1;
  m_step := stuck1_step;
  m_is_good s:= s ≠ S1S3;
|}.

Lemma test_refines_stuck1 :
  refines mod_stuck1 mod_stuck1.
Proof.
  apply: (inv_implies_refines mod_stuck1 mod_stuck1 (λ σ1 σ2, σ1 = σ2 ∧ σ1 ≠ S1S3)).
  - done.
  - move => [] ?[??] => //.
  - move => σi1 σs1 σi2 e [-> ?] ? Hsafe. inv_step.
    + (* 1 -> 2 *) eexists _. split => //. apply: steps_Some; last by left. constructor.
    + (* 1 -> 3 *)
      exfalso.
      have [||]:= (Hsafe S1S3 [2]) => //.
      apply: steps_Some; last by left. econstructor.
Qed.

(*   1
      /- 2 (done)
  1 --
      \- 3 ---- 4 (stuck)
     2      3
 *)

Inductive stuck2_state := | S2S1 | S2S2 | S2S3 | S2S4.
Inductive stuck2_step : stuck2_state → option nat → stuck2_state → Prop :=
| S2_1To2: stuck2_step S2S1 (Some 1) S2S2
| S2_1To3: stuck2_step S2S1 (Some 2) S2S3
| S2_3To4: stuck2_step S2S3 (Some 3) S2S4.
Definition mod_stuck2 : module nat := {|
  m_state := stuck2_state;
  m_initial := S2S1;
  m_step := stuck2_step;
  m_is_good s:= s ≠ S2S4;
|}.

Definition stuck2_inv (σ1 : stuck2_state) (σ2 : stuck1_state) :=
  (* We could prove an even stronger invariant with also σ1 ≠ S2S3
  since we don't need to reestablish it for a stuck source state. *)
  σ1 ≠ S2S4 ∧
  σ2 = match σ1 with | S2S1 => S1S1 | S2S2 => S1S2 | S2S3 => S1S3 | S2S4 => S1S1 end.

Lemma test_refines_stuck2 :
  refines mod_stuck2 mod_stuck1.
Proof.
  apply: (inv_implies_refines mod_stuck2 mod_stuck1 stuck2_inv).
  - done.
  - move => [] ?[??] => //.
  - move => σi1 σs1 σi2 e [? ->] ? Hsafe. inv_step.
    + (* 1 -> 2 *) eexists _. split => //. apply: steps_Some; last by left. constructor.
    + (* 1 -> 3 *) eexists _. split => //. apply: steps_Some; last by left. constructor.
    + (* 3 -> 4 *) exfalso.
      have [||]:= (Hsafe S1S3 []) => //.
      * apply prefix_nil.
      * econstructor.
Qed.

Lemma test_refines_stuck2_wp :
  refines mod_stuck2 mod_stuck1.
Proof.
  apply: wp_implies_refines => n.
  (* S2S1 *)
  constructor => e1 Hsafe.
  split => // σ2 ???. inv_step.
  - (* S2S2 *)
    eexists _. split. {
      apply: steps_Some; last by left. constructor.
    }
    constructor => {}e1 {}Hsafe.
    split => // {}σ2 ???; inv_step.
  - (* S2S3 *)
    eexists _. split. {
      apply: steps_Some; last by left. constructor.
    }
    constructor => {}e1 {}Hsafe.
    split => // {}σ2 ???. inv_step.
    have []:= Hsafe S1S3 [] => //.
    * apply prefix_nil.
    * apply steps_refl.
Qed.

(*   1       3
      /- 2 ---- 4 (done)
  1 --
      \- 3 (stuck)
     2
 *)

Inductive stuck3_state := | S3S1 | S3S2 | S3S3 | S3S4.
Inductive stuck3_step : stuck3_state → option nat → stuck3_state → Prop :=
| S3_1To2: stuck3_step S3S1 (Some 1) S3S2
| S3_1To3: stuck3_step S3S1 (Some 2) S3S3
| S3_2To4: stuck3_step S3S2 (Some 3) S3S4.
Definition mod_stuck3 : module nat := {|
  m_state := stuck3_state;
  m_initial := S3S1;
  m_step := stuck3_step;
  m_is_good s:= s ≠ S3S3;
|}.

Definition stuck3_inv (σ1 : stuck3_state) (σ2 : stuck1_state) :=
  σ1 ≠ S3S3 ∧
  σ2 = match σ1 with | S3S1 => S1S1 | S3S2 => S1S2 | S3S3 => S1S3 | S3S4 => S1S2 end.

(* The following is not provable: *)
Lemma test_refines_stuck3 :
  refines mod_stuck3 mod_stuck1.
Proof.
  apply: (inv_implies_refines mod_stuck3 mod_stuck1 stuck3_inv).
  - done.
  - move => [] ?[??] => //.
  - move => σi1 σs1 σi2 e [? ->] ? Hsafe. inv_step.
    + (* 1 -> 2 *) eexists _. split => //. apply: steps_Some; last by left. constructor.
    + (* 1 -> 3 *) exfalso.
      have [||]:= (Hsafe S1S3 [2]) => //.
      apply: steps_Some; last by left. econstructor.
    + (* 2 -> 4 *) eexists _. split => //. apply: steps_Some; last by left.
      (* Not provable! *)
Abort.


Record call_event : Type := {
  call_nat : nat;
}.
(*
     Call 1
  1 -------- 2
 *)

Inductive call1_step : bool → option call_event → bool → Prop :=
| C1_1To2: call1_step false (Some ({| call_nat := 1 |})) true.
Definition mod_call1 : module call_event := {|
  m_state := bool;
  m_initial := false;
  m_step := call1_step;
  m_is_good s := True;
|}.

(*
            -> Call n     1 + n
  1 (done) ---------- 2 -------- 3
 *)

Inductive call2_state := | C2S1 | C2S2 (n : nat) | C2S3.
Inductive call2_step : call2_state → option (call_event + nat) → call2_state → Prop :=
| C2_1To2 cn: call2_step C2S1 (Some (inl cn)) (C2S2 cn.(call_nat))
| C2_2To3 n: call2_step (C2S2 n) (Some (inr (1 + n))) C2S3.
Definition mod_call2 : module _ := {|
  m_state := call2_state;
  m_initial := C2S1;
  m_step := call2_step;
  m_is_good s := True;
|}.

Inductive call_merge_rel : option call_event → option (call_event + nat) → option nat → Prop :=
| CallMergeCall ev:
    call_merge_rel (Some ev) (Some (inl ev)) None
| CallMergeOut n:
    call_merge_rel None (Some (inr n)) (Some n).

Definition call_merge_inv (σ1 : bool * call2_state) (σ2 : bool) :=
  match σ1.1, σ1.2 with
  | false, C2S3 => False
  | false, C2S2 _ => False
  | _, C2S2 n => n = 1
  | _, _ => True
  end ∧ σ2 = if σ1.2 is C2S3 then true else false.
Lemma test_refines_call_merge :
  refines (link mod_call1 mod_call2 call_merge_rel) mod1.
Proof.
  apply: (inv_implies_refines (link mod_call1 mod_call2 call_merge_rel) mod1 call_merge_inv).
  - done.
  - done.
  - move => σi1 σs1 σi2 e [??] ? Hsafe.
    inv_step; match goal with | H : call_merge_rel _ _ _ |- _ => inversion H; clear H end; simplify_eq/=.
    + (* mod_call2 *)
      destruct σ1 => //. simplify_eq/=.
      exists true. split => //.
      apply: steps_Some; last by left. constructor.
    + (* mod_call1 *)
      exists false. split => //. apply steps_refl.
Qed.

Definition call_split_inv (σ1 : bool) (σ2 : bool * call2_state) :=
  if σ1 then True else σ2 = (false, C2S1).
Lemma test_refines_call_split :
  refines mod1 (link mod_call1 mod_call2 call_merge_rel).
Proof.
  apply: (inv_implies_refines mod1 (link mod_call1 mod_call2 call_merge_rel) call_split_inv).
  - done.
  - done.
  - move => σi1 [σs1 σs2] σi2 e Hinv ? Hsafe. inv_step.
    exists (true, C2S3). split => //=.
    apply: (steps_None (true, C2S2 1)). 2: apply: steps_Some. 3: by left.
    + apply: LinkStepBoth. 3: constructor.
      * constructor.
      * constructor.
    + apply: LinkStepR. constructor => //. simpl. constructor.
Qed.

Lemma test_refines_call_merge_wp :
  refines (link mod_call1 mod_call2 call_merge_rel) mod1.
Proof.
  apply: (wp_implies_refines) => n.
  constructor => κ1 Hsafe1.
  split => // σi1 n' ? Hstep. subst.
  inv_step; match goal with | H : call_merge_rel _ _ _ |- _ => inversion H; clear H end; simplify_eq/=.
  exists false.
  split. by left.

  constructor => κ2 Hsafe2.
  split => // σi2 n ? Hstep. subst.
  inv_step; match goal with | H : call_merge_rel _ _ _ |- _ => inversion H; clear H end; simplify_eq/=.
  exists true.
  split. { apply: steps_Some; last by left. constructor. }

  constructor => κ3 Hsafe3.
  split => // σi3 n' ? Hstep. subst.
  inv_step; match goal with | H : call_merge_rel _ _ _ |- _ => inversion H; clear H end; simplify_eq/=.
Qed.

Lemma test_refines_call_split_wp :
  refines mod1 (link mod_call1 mod_call2 call_merge_rel).
Proof.
  apply: (wp_implies_refines) => n.
  constructor => κ1 Hsafe1.
  split => // σi1 n' ? Hstep. subst.
  inv_step.
  exists (true, C2S3).
  split. {
    apply: steps_None.
    - apply: LinkStepBoth. 3: constructor. all: constructor.
    - apply: steps_Some.
      + apply: LinkStepR. constructor. simpl. constructor.
      + apply: steps_refl.
  }

  constructor => κ2 Hsafe2.
  split => // σi2 n ? Hstep. subst.
  inv_step.
Qed.

(*
   x := N;            x := N;          x := N;
   y := alloc()       y := alloc()     y := N;
   *y = 1;       -->  *y = 1;      --> *y := 1;
   *x = 2;            *x = 2;          *x := 2;
   return *y;         return 1;        return 1;
 *)

Inductive expr :=
| VarE (b : string)
| ConstE (v : nat)
| AllocE
| AllocConcreteE (e : expr)
| LetE (b : string) (e1 e2 : expr)
| Store (e1 e2 : expr)
| Load (e : expr)
| Event (e : expr).

Fixpoint subst (e : expr) (s : string) (v : nat) : expr :=
  match e with
  | VarE b => (if bool_decide (b = s) then ConstE v else VarE b)
  | ConstE _ | AllocE => e
  | AllocConcreteE e => AllocConcreteE (subst e s v)
  | LetE b e1 e2 => LetE b (subst e1 s v) (if bool_decide (b = s) then e2 else (subst e2 s v))
  | Store e1 e2 => Store (subst e1 s v) (subst e2 s v)
  | Load e => Load (subst e s v)
  | Event e => Event (subst e s v)
  end.

Definition heap := gmap nat nat.
Inductive expr_step : (heap * expr) -> option nat → (heap * expr) → Prop :=
| AllocStep v h:
    h !! v = None →
    expr_step (h, AllocE) None (<[v := 0]>h, ConstE v)
| AllocConcreteStep v h:
    h !! v = None →
    expr_step (h, AllocConcreteE (ConstE v)) None (<[v := 0]>h, ConstE v)
| LetStepCtx h e1 e1' e2 h' κ b:
    expr_step (h, e1) κ (h', e1') →
    expr_step (h, LetE b e1 e2) None (h', LetE b e1' e2)
| LetStepConst h e2 b v:
    expr_step (h, LetE b (ConstE v) e2) None (h, subst e2 b v)
| StoreStep h v1 v2 vold:
    h !! v1 = Some vold →
    expr_step (h, Store (ConstE v1) (ConstE v2)) None (<[v1 := v2]>h, ConstE 0)
| LoadStep h v1 v:
    h !! v1 = Some v →
    expr_step (h, Load (ConstE v1)) None (h, ConstE v)
| EventStep h v:
    expr_step (h, Event (ConstE v)) (Some v) (h, ConstE v)
.

Definition expr_module (h : heap) (prog : expr) : module nat := {|
  m_state := (heap * expr);
  m_step := expr_step;
  m_initial := (h, prog);
  m_is_good '(h, e) :=
    (∃ v, e = ConstE v) ∨ ∃ κ σ', expr_step (h, e) κ σ'
|}.


Definition prog1 (N : nat) : expr :=
  LetE "x" (ConstE N) $
  LetE "y" AllocE $
  LetE "_" (Store (VarE "y") (ConstE 1)) $
  LetE "_" (Store (VarE "x") (ConstE 2)) $
  LetE "l" (Load (VarE "y")) $
  Event (VarE "l").

Definition prog2 (N : nat) : expr :=
  LetE "x" (ConstE N) $
  LetE "y" AllocE $
  LetE "_" (Store (VarE "y") (ConstE 1)) $
  LetE "_" (Store (VarE "x") (ConstE 2)) $
  Event (ConstE 1).

Definition prog3 (N : nat) : expr :=
  LetE "x" (ConstE N) $
  LetE "y" (ConstE N) $
  LetE "_" (Store (VarE "y") (ConstE 1)) $
  LetE "_" (Store (VarE "x") (ConstE 2)) $
  Event (ConstE 1).

Ltac inv_expr_step :=
  lazymatch goal with
  | H : expr_step _ _ _ |- _ => inversion H; clear H; simplify_eq/=; try easy
  end.

Lemma prog2_refined_prog1 h N :
  refines (expr_module h (prog2 N)) (expr_module h (prog1 N)).
Proof.
  apply: wp_implies_refines => n.

  constructor => ? _. split. { right. eauto using LetStepConst. }
  move => //= ??? Hstep.
  inv_expr_step.
  eexists (_, _). split. { apply: steps_None. by apply LetStepConst. by left. }
  simpl.

  destruct (h !! N) eqn: HN.
  - constructor => ? Hsafe.
    efeed pose proof (Hsafe) as Hsafe. by apply prefix_nil. by left.
    have {Hsafe}[[??]|[?[??]]]:= Hsafe => //.
    inv_expr_step.
    inv_expr_step.
    split. { right. eauto using LetStepCtx, AllocStep. }
    move => //= ??? Hstep.
    inv_expr_step.
    inv_expr_step.
    eexists (_, _). split. { apply: steps_None; [ | by left]. apply: LetStepCtx. apply: AllocStep. done. }

    destruct (decide (v0 = N)); simplify_eq.

    constructor => ? _. split. { right. eauto using LetStepConst. }
    move => //= ??? Hstep.
    inv_expr_step.
    eexists (_, _). split. { apply: steps_None; [ | by left ]. constructor. }

    constructor => ? _.
    split. { right. eexists _, _. apply: LetStepCtx. apply: StoreStep. apply lookup_insert. }
    move => //= ??? Hstep.
    inv_expr_step.
    inv_expr_step.
    eexists (_, _). split. {
      apply: steps_None; [ | by left ].
      apply: LetStepCtx.
      by apply: StoreStep.
    }

    constructor => ? _. split. { right. eauto using LetStepConst. }
    move => //= ??? Hstep.
    inv_expr_step.
    eexists (_, _). split. { apply: steps_None; [ | by left ]. constructor. }

    constructor => ? _.
    split. { right. eexists _, _. apply: LetStepCtx. apply: StoreStep. rewrite !lookup_insert_ne //. }
    move => //= ??? Hstep.
    inv_expr_step.
    inv_expr_step.
    eexists (_, _). split. {
      apply: steps_None; [ | by left ].
      apply: LetStepCtx.
        by econstructor.
    }

    constructor => ? _. split. { right. eauto using LetStepConst. }
    move => //= ??? Hstep.
    inv_expr_step.
    eexists (_, _). split. { apply: steps_None; [ | by left ]. constructor. }

    constructor => ? _. split. { right. eauto using EventStep. }
    move => //= ??? Hstep.
    inv_expr_step.
    eexists (_, _). split. {
      apply: steps_None; [ | apply: steps_None; [ | apply: steps_Some; [ | by left] ] ].
      - econstructor. econstructor. by rewrite lookup_insert_ne // lookup_insert.
      - apply LetStepConst.
      - simpl. econstructor.
    }

    constructor => ? _. split. { left. eauto. }
    move => //= ??? Hstep.
    inv_expr_step.

  - constructor => ? Hsafe.
    efeed pose proof (Hsafe) as Hsafe. by apply prefix_nil. {
      apply: steps_None. {
        econstructor.
        apply: (AllocStep (fresh ({[N]} ∪ dom (gset _) h))).
        pose proof (is_fresh ({[N]} ∪ dom (gset nat) h)).
        apply/not_elem_of_dom. apply _.
        set_solver.
      }
      apply: steps_None => /=. constructor.
      apply: steps_None => /=. econstructor. econstructor. apply lookup_insert.
      apply: steps_None => /=. constructor. simpl.
        by left.
    }
    have {Hsafe}[[??]|[?[??]]]:= Hsafe => //.
    inv_expr_step.
    inv_expr_step.
    revert select (_ !! _ = Some _) => Hlookup.
    pose proof (is_fresh ({[N]} ∪ dom (gset nat) h)).
    rewrite !lookup_insert_ne in Hlookup; try set_solver.
    by rewrite Hlookup in HN.
Qed.

Lemma prog3_refined_prog2 h N :
  refines (expr_module h (prog3 N)) (expr_module h (prog2 N)).
Proof.
  apply: wp_implies_refines => n.

  constructor => ? _. split. { right. eauto using LetStepConst. }
  move => //= ??? Hstep.
  inv_expr_step.
  eexists (_, _). split. { apply: steps_None. by apply LetStepConst. by left. }
  simpl.

  constructor => ? _. split. { right. eauto using LetStepConst. }
  move => //= ??? Hstep.
  inv_expr_step.
  eexists (_, _). split. {
    apply: steps_None. {
      econstructor.
      apply: (AllocStep (fresh ({[N]} ∪ dom (gset _) h))).
      pose proof (is_fresh ({[N]} ∪ dom (gset nat) h)).
      apply/not_elem_of_dom. apply _.
      set_solver.
    }
    apply: steps_None. constructor.
      by left.
  }
  simpl.

  constructor => ? Hsafe.
  efeed pose proof (Hsafe) as Hsafe. by apply prefix_nil. {
    apply: steps_None => /=. econstructor. econstructor. apply lookup_insert.
    apply: steps_None => /=. constructor. simpl.
      by left.
  }
  have {Hsafe}[[??]|[?[??]]]:= Hsafe => //.
  inv_expr_step.
  inv_expr_step.
  revert select (_ !! _ = Some _) => Hlookup.
  pose proof (is_fresh ({[N]} ∪ dom (gset nat) h)).
  rewrite !lookup_insert_ne in Hlookup; try set_solver.

  split. { right. eexists _, _. apply: LetStepCtx. by apply: StoreStep. }
  move => //= ??? Hstep.
  inv_expr_step.
  inv_expr_step.
  eexists (_, _). split. {
    apply: steps_None; [ | by left ].
    apply: LetStepCtx.
    apply: StoreStep.
    apply lookup_insert.
  }

  constructor => ? _. split. { right. eauto using LetStepConst. }
  move => //= ??? Hstep.
  inv_expr_step.
  eexists (_, _). split. { apply: steps_None; [ | by left ]. constructor. }

  constructor => ? _.
  split. { right. eexists _, _. apply: LetStepCtx. apply: StoreStep. apply lookup_insert. }
  move => //= ??? Hstep.
  inv_expr_step.
  inv_expr_step.
  eexists (_, _). split. {
    apply: steps_None; [ | by left ].
    apply: LetStepCtx.
    econstructor.
    rewrite !lookup_insert_ne; try set_solver.
  }

  constructor => ? _. split. { right. eauto using LetStepConst. }
  move => //= ??? Hstep.
  inv_expr_step.
  eexists (_, _). split. { apply: steps_None; [ | by left ]. constructor. }

  constructor => ? _. split. { right. eauto using EventStep. }
  move => //= ??? Hstep.
  inv_expr_step.
  eexists (_, _). split. {
    apply: steps_Some; [ | by left ].
    by econstructor.
  }

  constructor => ? _. split. { left. eauto. }
  move => //= ??? Hstep.
  inv_expr_step.
Qed.

End test.
End version3.

Module version4.
(*** trace *)
Inductive trace (EV : Type) : Type :=
| ub | nb | vis (e : EV) (κ : trace EV).
Arguments ub {_}.
Arguments nb {_}.
Arguments vis {_}.

Fixpoint trace_events {EV} (l : trace EV) : list EV :=
  match l with
  | nb | ub => []
  | vis e l' => e :: trace_events l'
  end.

Fixpoint trace_is_ub {EV} (l : trace EV) : bool :=
  match l with
  | nb => false
  | ub => true
  | vis e l' => trace_is_ub l'
  end.

Fixpoint list_to_trace {EV} (is_ub : bool) (l : list EV) : trace EV :=
  match l with
  | [] => if is_ub then ub else nb
  | e :: l' => vis e (list_to_trace is_ub l')
  end.
Definition nb_trace {EV} := list_to_trace (EV:=EV) false.
Definition ub_trace {EV} := list_to_trace (EV:=EV) true.

Definition option_trace {EV} (o : option EV) : trace EV :=
  match o with
  | Some e => vis e nb
  | None => nb
  end.

Definition trace_app {EV} (κs1 κs2 : trace EV) : trace EV :=
  list_to_trace (trace_is_ub κs1 || trace_is_ub κs2) (trace_events κs1 ++ trace_events κs2).
Infix "+t+" := trace_app (right associativity, at level 60) : stdpp_scope.

Definition trace_prefix {EV} (κs1 κs2 : trace EV) : Prop :=
  ∃ κs', κs1 +t+ κs' = κs2.
Infix "`trace_prefix_of`" := trace_prefix (at level 70) : stdpp_scope.

Lemma list_to_trace_events {EV} u (l : list EV):
  trace_events (list_to_trace u l) = l.
Proof. elim: l => //=. { by destruct u. } by move => ?? ->. Qed.

Lemma list_to_trace_ub {EV} u (l : list EV):
  trace_is_ub (list_to_trace u l) = u.
Proof. elim: l => //=. by destruct u. Qed.

Lemma list_to_trace_id {EV} (κs : trace EV) :
  list_to_trace (trace_is_ub κs) (trace_events κs) = κs.
Proof. by elim: κs => //= ? ? ->. Qed.

Lemma option_trace_events {EV} (e : option EV) :
  trace_events (option_trace e) = option_list e.
Proof. by destruct e. Qed.

Lemma option_trace_ub {EV} (e : option EV) :
  trace_is_ub (option_trace e) = false.
Proof. by destruct e. Qed.

Global Instance trace_app_assoc {EV} : Assoc (=) (trace_app (EV:=EV)).
Proof.
  move => ???. by rewrite /trace_app !list_to_trace_events !list_to_trace_ub (assoc (++)) orb_assoc.
Qed.

Global Instance trace_app_left_id {EV} : LeftId (=) nb (trace_app (EV:=EV)).
Proof. move => ?. by rewrite /trace_app/= list_to_trace_id. Qed.

Global Instance trace_app_right_id {EV} : RightId (=) nb (trace_app (EV:=EV)).
Proof. move => ?. by rewrite /trace_app/= right_id_L orb_false_r list_to_trace_id. Qed.

Lemma trace_app_vis {EV} (κs : trace EV) e:
  vis e κs = (vis e nb) +t+ κs.
Proof. by rewrite /trace_app/= list_to_trace_id. Qed.

Lemma trace_app_events {EV} (κs1 κs2 : trace EV):
  trace_events (κs1 +t+ κs2) = trace_events κs1 ++ trace_events κs2.
Proof. by rewrite /trace_app list_to_trace_events. Qed.

Lemma trace_app_ub {EV} (κs1 κs2 : trace EV):
  trace_is_ub (κs1 +t+ κs2) = orb (trace_is_ub κs1) (trace_is_ub κs2).
Proof. by rewrite /trace_app list_to_trace_ub. Qed.

Global Instance trace_prefix_preorder EV: PreOrder (@trace_prefix EV).
Proof.
  split.
  - move => ?. exists nb. by rewrite right_id_L.
  - move => ??? [k1 <-] [k2 <-]. exists (k1 +t+ k2). by rewrite (assoc_L).
Qed.
Lemma trace_prefix_nb {EV} (l : trace EV) : nb `trace_prefix_of` l.
Proof. exists l. by rewrite left_id. Qed.

(*** module *)
Inductive mod_state_kind : Type :=
| kind_visible | kind_demonic | kind_angelic.
Global Instance mod_state_kind_eq_dec : EqDecision mod_state_kind.
Proof. solve_decision. Qed.

Record module (EV : Type) : Type := {
  m_state : Type;
  (* multiple initial states can be modeled by non-deterministically
  branching from the initial state *)
  m_initial : m_state;
  m_state_kind : m_state → mod_state_kind;
  m_step : m_state → option EV → m_state → Prop;

  m_vis_det σ σ1 σ2 e1 e2:
    m_state_kind σ = kind_visible →
    m_step σ e1 σ1 →
    m_step σ e2 σ2 →
    σ1 = σ2 ∧ e1 = e2;
  (* the following is problem for hiding *)
  (* m_vis_exists σ: *)
  (*   m_state_kind σ = kind_visible → *)
  (*   ∃ σ' e, m_step σ (Some e) σ'; *)
  (* sanity *)
  m_non_vis_silent σ σ' e:
    m_state_kind σ ≠ kind_visible →
    m_step σ e σ' →
    e = None;
}.
Arguments m_state {_}.
Arguments m_initial {_}.
Arguments m_state_kind {_}.
Arguments m_step {_}.

(*** trace of module *)

Section ind.
Inductive trace_step {EV} (m : module EV) (F : option EV → m.(m_state) → Prop) : m.(m_state) → Prop :=
| StepVis σ σ' e:
    m.(m_state_kind) σ = kind_visible →
    m.(m_step) σ e σ' →
    F e σ' →
    trace_step m F σ
| StepDemonic σ:
    m.(m_state_kind) σ = kind_demonic →
    (∃ σ', m.(m_step) σ None σ' ∧ F None σ') →
    trace_step m F σ
| StepAngelic σ:
    m.(m_state_kind) σ = kind_angelic →
    (∀ σ', m.(m_step) σ None σ' → F None σ') →
    trace_step m F σ.
(* Local Unset Elimination Schemes. *)
Inductive trace_of_state {EV} (m : module EV) : m.(m_state) → propset (trace EV) → Prop :=
| OfStateNb σ T:
    T ≡ {[ nb ]} →
    trace_of_state m σ T
(* | OfStateStep σ e T: *)
(*     trace_step m (λ e σ', trace_of_state m F σ' T) σ e → *)
(*     trace_of_state m σ (λ κs, ∃ κs', T κs' ∧ option_trace e +t+ κs' = κs) *)
| OfStateVis σ σ' e T T':
    m.(m_state_kind) σ = kind_visible →
    m.(m_step) σ e σ' →
    trace_of_state m σ' T →
    T' ≡ (T ∪ ((λ κs', option_trace e +t+ κs') <$> T)) →
    trace_of_state m σ T'
| OfStateDemonic σ T:
    m.(m_state_kind) σ = kind_demonic →
    (∃ σ', m.(m_step) σ None σ' ∧ trace_of_state m σ' T) →
    trace_of_state m σ T
| OfStateAngelic σ T:
    m.(m_state_kind) σ = kind_angelic →
    (∀ σ', m.(m_step) σ None σ' → trace_of_state m σ' T) →
    trace_of_state m σ T.
(* Inductive trace_of_state {EV} (m : module EV) (F : m.(m_state) → Prop) : m.(m_state) → propset (trace EV) → Prop := *)
(* | OfStateNb σ T: *)
(*     F σ → *)
(*     T ≡ {[ nb ]} → *)
(*     trace_of_state m F σ T *)
(* | OfStateStep σ e T: *)
(*     trace_step m (λ e σ', trace_of_state m F σ' T) σ e → *)
(*     trace_of_state m F σ (λ κs, ∃ κs', T κs' ∧ option_trace e +t+ κs' = κs). *)
End ind.

Global Instance trace_of_state_Proper {EV} (m : module EV) : Proper ((=) ==> (≡) ==> (iff)) (trace_of_state m).
Proof.
  move => ? σ -> T1 T2 HT.
  split => Hs; [move: T2 HT | move: T1 HT]; elim: Hs.
  all: try by move => *; apply: OfStateNb; setoid_subst.
  all: try by move => *; apply: OfStateVis; setoid_subst.
  (* all: try by move => *; apply: OfStateDemonic; setoid_subst; naive_solver. *)
Admitted.

(* Lemma trace_of_state_ind {EV} (m : module EV) (F : m_state m → Prop) (P : m_state m → (trace EV → Prop) → Prop) : *)
(*   (∀ (σ : m_state m) (T : trace EV → Prop), F σ → T nb → P σ T) *)
(*   → (∀ (σ : m_state m) (e : option EV) (T : trace EV → Prop), *)
(*         trace_step m (λ σ' : m_state m, trace_of_state m F σ' T ∧ P σ' T) σ e → P σ (λ κs : trace EV, ∃ κs' : trace EV, T κs' ∧ option_trace e +t+ κs' = κs)) *)
(*   → ∀ (m0 : m_state m) (t : trace EV → Prop), trace_of_state m F m0 t → P m0 t. *)
(* Proof. *)
(*   fix FIX 5. move => Hnb Hstep ??. *)
(*   case. *)
(*   - by apply: Hnb. *)
(*   - move => ??? Hs. eapply Hstep => //. *)
(*     case: Hs => *; [ apply: StepVis | apply: StepDemonic | apply: StepAngelic] => //; naive_solver. *)
(* Qed. *)
Definition trace_of_program {EV} (m : module EV) := PropSet (trace_of_state m m.(m_initial)).

Program Definition test_mod_1 : module unit := {|
  m_state := unit;
  m_initial := ();
  m_state_kind _ := kind_visible;
  m_step _ e _ := e = None;
|}.
Next Obligation. move => [] [] [] [|[]] //. Qed.
Next Obligation. done. Qed.
Lemma test_mod_1_traces:
  trace_of_program test_mod_1 ≡ {[ x | x ≡ {[ nb ]} ]}.
Proof.
  move => κs.
  split.
  - rewrite !elem_of_PropSet.
    elim => //.
    + move => [] [] ? T T' //= _ -> ? -> ->.
      set_unfold. move => ?. split; [ naive_solver|]. move => ->. by left.
  - rewrite !elem_of_PropSet => ->. by apply OfStateNb.
Qed.

Program Definition test_mod_2 : module nat := {|
  m_state := bool;
  m_initial := false;
  m_state_kind b := if b then kind_demonic else kind_visible;
  m_step b1 e b2 := b1 = false ∧ e = Some 2 ∧ b2 = true;
|}.
Next Obligation. move => []//[][]//; naive_solver. Qed.
Next Obligation. move => [][]//; naive_solver. Qed.

Lemma test_mod_2_traces:
  trace_of_program test_mod_2 ≡ {[ x | x ≡ {[ nb ]} ]} ∪ {[ x | x ≡ {[ nb; vis 2 nb ]} ]}.
Proof.
  move => κs.
  split.
  - rewrite !elem_of_PropSet.
    inversion_clear 1; simplify_eq/=; destruct_and?; simplify_eq/=. naive_solver.
    revert select (trace_of_state _ _ _).
    inversion_clear 1; simplify_eq; setoid_subst.
    + right. set_unfold. move => ?. split; [ naive_solver|]. move => [] ->. by left. right. by exists nb.
    + naive_solver.
  - rewrite !elem_of_PropSet => -[|] ->.
    + by apply OfStateNb.
    + apply: OfStateVis => //. by apply OfStateNb.
      set_unfold. move => ?. split. { move => [] ->. by left. right. exists nb. naive_solver. }
      move => [->|]. by left. move => [? [H1 H2]]. naive_solver.
Qed.

Inductive test_mod3_state := | S3S1 | S3S2 (n : nat) | S3S3.
Program Definition test_mod_3 (dem : bool) : module nat := {|
  m_state := test_mod3_state;
  m_initial := S3S1;
  m_state_kind b := if b is S3S2 _ then kind_visible else if b is S3S3 then kind_demonic else if dem then kind_demonic else kind_angelic;
  m_step b1 e b2 :=
    (b1 = S3S1 ∧ e = None ∧ ∃ n, b2 = S3S2 n) ∨
    (∃ n, b1 = S3S2 n ∧ e = Some n ∧ b2 = S3S3)
|}.
Next Obligation. move => []//[][]//; naive_solver. Qed.
Next Obligation. move => [][]//; naive_solver. Qed.

Lemma test_mod_3_traces_demonic:
  (* {{nb}, {nb, vis 0 nb}, ..., {nb, vis n nb}, ...}*)
  trace_of_program (test_mod_3 true) ≡ {[ x | x ≡ {[ nb ]} ]} ∪ {[ x | ∃ n, x ≡ {[ nb; vis n nb ]} ]}.
Proof.
  move => κs.
  split.
  - rewrite !elem_of_PropSet.
    inversion_clear 1; simplify_eq/=; destruct_and?; simplify_eq/=. naive_solver.
    revert select (∃ x, _) => -[? [[[?[? [? ->]]]|?] ?]]. 2: naive_solver.
    revert select (trace_of_state _ _ _).
    inversion_clear 1; simplify_eq; setoid_subst. by left.
    revert select (_ ∨ _) => -[|[n [?[??]]]]; simplify_eq. 1: naive_solver.
    revert select (trace_of_state _ _ _).
    inversion_clear 1; simplify_eq; setoid_subst.
    + right. exists n. set_unfold. move => ?. split; [ naive_solver|]. move => [] ->. by left. right. by exists nb.
    + naive_solver.
  - rewrite !elem_of_PropSet => -[|] HS.
    + by apply OfStateNb.
    + move: HS => [n ->]. apply: OfStateDemonic => //.
      exists (S3S2 n). split. naive_solver.
      apply: OfStateVis => //. naive_solver. by apply OfStateNb.
      set_unfold. move => ?. split. { move => [] ->. by left. right. exists nb. naive_solver. }
      move => [->|]. by left. move => [? [H1 H2]]. naive_solver.
Qed.

Lemma test_mod_3_traces_angelic:
  (* {{nb}, {nb, vis 0 nb, ..., vis n nb, ...} }*)
  (* trace_of_program (test_mod_3 false) ≡ {[ x | x ≡ {[ nb ]} ]} ∪ {[ x | ∃ n, x ≡ {[nb; vis n nb ]} ]}. *)
  trace_of_program (test_mod_3 false) ≡ {[ x | x ≡ {[ nb ]} ]} ∪ {[ x | x ≡ {[nb]} ∪ {[ y | ∃ n, y = vis n nb ]} ]}.
Proof.
  move => κs.
  split.
  - rewrite !elem_of_PropSet.
    inversion_clear 1; simplify_eq/=; destruct_and?; simplify_eq/=. naive_solver.
    right. move => κs'. split. {
      revert select (∀ x, _) => Hstep.
      efeed pose proof (Hstep (S3S2 0)). naive_solver. clear Hstep.
      revert select (trace_of_state _ _ _).
      inversion_clear 1; simplify_eq; setoid_subst. by left.
      revert select (_ ∨ _) => -[|[n [?[??]]]]; simplify_eq. 1: naive_solver.
      revert select (trace_of_state _ _ _).
      inversion_clear 1; simplify_eq; setoid_subst.
      + move => []. by left. right. exists 0. set_unfold. naive_solver.
      + naive_solver.
    }
    set_unfold.
    move => []. {
      move => ?. subst.
      revert select (∀ x, _) => Hstep.
      efeed pose proof (Hstep (S3S2 0)). naive_solver. clear Hstep.
      revert select (trace_of_state _ _ _).
      inversion_clear 1; simplify_eq; setoid_subst. done.
      revert select (_ ∨ _) => -[|[n [?[??]]]]; simplify_eq. 1: naive_solver.
      revert select (trace_of_state _ _ _).
      inversion_clear 1; simplify_eq; setoid_subst.
      - by left.
      - naive_solver.
    }
    move => [n Hn]. subst.
    revert select (∀ x, _) => Hstep.
    efeed pose proof (Hstep (S3S2 n)). naive_solver. clear Hstep.
    revert select (trace_of_state _ _ _).
    inversion_clear 1; simplify_eq; setoid_subst. admit.
    revert select (_ ∨ _) => -[|[n2 [?[??]]]]; simplify_eq. 1: naive_solver.
    revert select (trace_of_state _ _ _).
    inversion_clear 1; simplify_eq; setoid_subst.
    + set_unfold. right. exists nb. rewrite right_id. naive_solver.
    + naive_solver.
  - rewrite !elem_of_PropSet => -[|] HS.
    + by apply OfStateNb.
    + move: HS => ->. apply: OfStateAngelic => // -[|n|] //=. naive_solver. 2: naive_solver.
      move => [|]. 2: naive_solver. move => [? [? [n' [->]]]].
      apply: OfStateVis => //. { right. exists n'. done. } by apply OfStateNb.
      set_unfold. move => ?. split. { move => [-> | [? ->]]. by left. right. exists nb. admit. }
      move => [->|]. by left. move => [? [H1 H2]]. naive_solver.
Abort.

(* Lemma trace_of_state_ind {EV} (m : module EV) (F : m_state m → Prop) (P : m_state m → (trace EV → Prop) → Prop) : *)
(*   (∀ (σ : m_state m) (T : trace EV → Prop), F σ → T nb → P σ T) *)
(*   → (∀ (σ : m_state m) (e : option EV) (T : trace EV → Prop), *)
(*         trace_step m (λ σ' : m_state m, trace_of_state m F σ' T ∧ P σ' T) σ e → P σ (λ κs : trace EV, ∃ κs' : trace EV, T κs' ∧ option_trace e +t+ κs' = κs)) *)
(*   → ∀ (m0 : m_state m) (t : trace EV → Prop), trace_of_state m F m0 t → P m0 t. *)
(* Proof. *)
(*   fix FIX 5. move => Hnb Hstep ??. *)
(*   case. *)
(*   - by apply: Hnb. *)
(*   - move => ??? Hs. eapply Hstep => //. *)
(*     case: Hs => *; [ apply: StepVis | apply: StepDemonic | apply: StepAngelic] => //; naive_solver. *)
(* Qed. *)

(* Lemma trace_of_state_ind {EV} (m : module EV) (F : m_state m → Prop) (P : m_state m → trace EV → Prop) : *)
(*   (∀ σ : m_state m, F σ → P σ nb) *)
(*   → (∀ (σ : m_state m) (κs : trace EV) (e : option EV), *)
(*         trace_step m (λ σ' : m_state m, trace_of_state m F σ' κs ∧ P σ' κs) σ e → P σ (option_trace e +t+ κs)) *)
(*   → ∀ (m0 : m_state m) (t : trace EV), trace_of_state m F m0 t → P m0 t. *)
(* Proof. *)
(*   fix FIX 5. move => Hnb Hstep ??. *)
(*   case. *)
(*   - by apply: Hnb. *)
(*   - move => ??? Hs. eapply Hstep => //. *)
(*     case: Hs => *; [ apply: StepVis | apply: StepDemonic | apply: StepAngelic] => //; naive_solver. *)
(* Qed. *)
(* Inductive trace_of_state {EV} (m : module EV) (F : m.(m_state) → Prop) : m.(m_state) → trace EV → Prop := *)
(* | OfStateNb σ: *)
(*     F σ → *)
(*     trace_of_state m F σ nb *)
(* | OfStateVis σ σ' κs e: *)
(*     m.(m_state_kind) σ = kind_visible → *)
(*     m.(m_step) σ e σ' → *)
(*     trace_of_state m F σ' κs → *)
(*     trace_of_state m F σ (option_trace e +t+ κs) *)
(* | OfStateDemonic σ κs: *)
(*     m.(m_state_kind) σ = kind_demonic → *)
(*     (∃ σ', m.(m_step) σ None σ' ∧ trace_of_state m F σ' κs) → *)
(*     trace_of_state m F σ κs *)
(* | OfStateAngelic σ κs: *)
(*     m.(m_state_kind) σ = kind_angelic → *)
(*     (∀ σ', m.(m_step) σ None σ' → trace_of_state m F σ' κs) → *)
(*     trace_of_state m F σ κs. *)
(* End ind. *)

(* Lemma trace_of_state_ind {EV} (m : module EV) (F : m_state m → Prop) (P : m_state m → trace EV → Prop) : *)
(*   (∀ (σ : m_state m), F σ → P σ nb) → *)
(*   (∀ (σ σ' : m_state m) (κs : trace EV) (e : option EV), *)
(*       m_state_kind m σ = kind_visible *)
(*       → m_step m σ e σ' → trace_of_state m F σ' κs → P σ' κs → P σ (option_trace e +t+ κs)) → *)
(*   (∀ (σ : m_state m) (κs : trace EV), *)
(*       m_state_kind m σ = kind_demonic *)
(*       → (∃ σ' : m_state m, m_step m σ None σ' ∧ trace_of_state m F σ' κs ∧ P σ' κs) → P σ κs) → *)
(*   (∀ (σ : m_state m) (κs : trace EV), *)
(*         m_state_kind m σ = kind_angelic *)
(*         → (∀ σ' : m_state m, m_step m σ None σ' → trace_of_state m F σ' κs) *)
(*         → (∀ σ' : m_state m, m_step m σ None σ' → P σ' κs) → P σ κs) → *)
(*   ∀ (m0 : m_state m) (t : trace EV), trace_of_state m F m0 t → P m0 t. *)
(* Proof. *)
(*   fix FIX 7. move => Hnb Hvs HDem HAng ??. *)
(*   case => *. *)
(*   - by apply: Hnb. *)
(*   - eapply Hvs => //. naive_solver. *)
(*   - eapply HDem => //. naive_solver. *)
(*   - eapply HAng => //. naive_solver. *)
(* Qed. *)

(* Definition trace_of_program {EV} (m : module EV) := trace_of_state m m.(m_initial). *)

(* (*** refinement *) *)
(* Record refines {EV} (mimpl mspec : module EV) := { *)
(*   ref_subset κs: trace_of_program mimpl κs → trace_of_program mspec κs *)
(* }. *)

(* (*** wp': equivalent definition of refines *) *)
(* Inductive wp' {EV} (m1 m2 : module EV) : nat → m1.(m_state) -> list EV -> Prop := *)
(* | WpVis' σi1 κs n: *)
(*     m1.(m_state_kind) σi1 = kind_visible → *)
(*     (∀ n', n = S n' → trace_of_program m2 (ub_trace κs) ∨ *)
(*         ∀ σi2 e, *)
(*         m1.(m_step) σi1 e σi2 → *)
(*         trace_of_program m2 (nb_trace (κs ++ option_list e)) ∧ wp' m1 m2 n' σi2 (κs ++ option_list e) *)
(*     ) → *)
(*     wp' m1 m2 n σi1 κs *)
(* | WpDemonic' σi1 κs n: *)
(*     m1.(m_state_kind) σi1 = kind_demonic → *)
(*     (∀ n', n = S n' → trace_of_program m2 (ub_trace κs) ∨ *)
(*         ∀ σi2, *)
(*         m1.(m_step) σi1 None σi2 → *)
(*         wp' m1 m2 n' σi2 κs *)
(*     ) → *)
(*     wp' m1 m2 n σi1 κs *)
(* | WpAngelic' σi1 κs n: *)
(*     m1.(m_state_kind) σi1 = kind_angelic → *)
(*     (∀ n', n = S n' → trace_of_program m2 (ub_trace κs) ∨ *)
(*         ∃ σi2, *)
(*         m1.(m_step) σi1 None σi2 ∧ *)
(*         wp' m1 m2 n' σi2 κs *)
(*     ) → *)
(*     wp' m1 m2 n σi1 κs. *)

(* Lemma wp'_constructor {EV} (m1 m2 : module EV) n σi1 κs: *)
(*   (∀ n', n = S n' → *)
(*     trace_of_program m2 (ub_trace κs) ∨ *)
(*     match m1.(m_state_kind) σi1 with *)
(*     | kind_visible => ∀ σi2 e, *)
(*         m1.(m_step) σi1 e σi2 → *)
(*         trace_of_program m2 (nb_trace (κs ++ option_list e)) ∧ wp' m1 m2 n' σi2 (κs ++ option_list e) *)
(*     | kind_demonic => ∀ σi2, *)
(*         m1.(m_step) σi1 None σi2 → *)
(*         wp' m1 m2 n' σi2 κs *)
(*     | kind_angelic => ∃ σi2, *)
(*         m1.(m_step) σi1 None σi2 ∧ wp' m1 m2 n' σi2 κs *)
(*     end) → *)
(*   wp' m1 m2 n σi1 κs. *)
(* Proof. *)
(*   by destruct (m_state_kind m1 σi1) eqn: Hkind => Hwp; [ apply: WpVis' | apply: WpDemonic' | apply: WpAngelic']. *)
(* Qed. *)

(* Lemma wp'_weaken {EV} (m1 m2 : module EV) κs σ n n': *)
(*   n' ≤ n → *)
(*   wp' m1 m2 n σ κs → *)
(*   wp' m1 m2 n' σ κs. *)
(* Proof. *)
(*   elim: n' n σ κs. *)
(*   - move => ???? Hwp. apply: wp'_constructor. lia. *)
(*   - move => n' IH [|n] σ κs ? Hwp. lia. *)
(*     apply: wp'_constructor => ? [?]. subst. *)
(*     inversion Hwp as [???? Hwp'|???? Hwp' |???? Hwp']; simplify_eq; case_match => //. *)
(*     all: have [|?|{}Hwp]:= Hwp' n => //; [ by left | right]. *)
(*     + move => ???. split; [naive_solver|]. apply: IH; [ |naive_solver]. lia. *)
(*     + move => ??. apply: IH; [ |naive_solver]. lia. *)
(*     + have [?[??]]:= Hwp. eexists. split => //. apply: IH; [ |naive_solver]. lia. *)
(* Qed. *)

(* Lemma forall_to_ex A B (P : A → B → Prop) (Q : B → Prop): *)
(*  (∃ n : A, ∀ y : B, P n y → Q y) -> ∀ y : B, ((∀ n : A, P n y) → Q y). *)
(* Proof. naive_solver. Qed. *)

(* Lemma wp'_implies_refines {EV} (m1 m2 : module EV): *)
(*   (∀ n, wp' m1 m2 n m1.(m_initial) []) → *)
(*   refines m1 m2. *)
(* Proof. *)
(*   move => Hwp. constructor => κs. rewrite {1}/trace_of_program. *)
(*   move: m1.(m_initial) Hwp => σi1. *)
(*   have : (trace_of_program m2 nb). { by apply OfStateNb. } *)
(*   have : κs = nb +t+ κs by rewrite left_id. *)
(*   have : trace_is_ub (@nb EV) = false by []. *)
(*   change ([]) with (trace_events (@nb EV)). *)
(*   move: (nb) => κstart. move: {2 3}(κs) => κend. *)
(*   move => Hnb Hκ Hs Hwp Htrace. *)
(*   move: κstart Hwp Hnb Hκ Hs. apply: forall_to_ex. *)
(*   elim: Htrace => {σi1 κend}. *)
(*   - move => σ _. exists 0 => κstart Hwp ? /=. by rewrite right_id_L => <-. *)
(*   - move => σ κs' e. *)
(*     case; clear. *)
(*     + move => σ σ' e Hkind Hstep [Htrace [n IH]]. exists (S n) => κstart Hwp /= Hnb Hκ ?. *)
(*       inversion Hwp as [???? Hwp'| |]; simplify_eq/=; try congruence. *)
(*       have [||{}Hwp]:= Hwp' n => //=. admit. *)
(*       have [??] := Hwp _ _ Hstep. *)
(*       apply: IH. 3: { by rewrite assoc_L. } *)
(*       * by rewrite trace_app_events option_trace_events. *)
(*       * by rewrite trace_app_ub Hnb option_trace_ub /=. *)
(*       * admit. *)
(*     + move => σ Hkind [σ' [Hstep [Htrace [n IH]]]]. exists (S n) => κstart Hwp /= Hκ ?. *)
(*       inversion Hwp as [| ???? Hwp' |]; simplify_eq; try congruence. *)
(*       have [||{}Hwp]:= Hwp' n => //. admit. *)
(*       apply: IH => //. by apply: Hwp. by rewrite left_id. *)
(*     + move => σ Hkind IH /=. *)
(*       admit. *)
(*     (* exists 1. *) *)
(*     (* move => κstart Hwp /= Hκ ?. *) *)
(*     (* inversion Hwp as [| | ???? Hwp']; simplify_eq; try congruence. *) *)
(*     (* have [||[σi2 [Hσi2 {}Hwp]]]:= Hwp' 0 => //. admit. *) *)
(*     (* admit. *) *)

(*     (* apply: IH => //. by apply: Hwp. *) *)
(*     (* have [|[σ' Hσ']|Hnot]:= HLEM σ => //. *) *)
(*     (* + have [//|n {}IH]:= IH σ'. exists (S n) => κstart Hwp /= Hκ ?. *) *)
(*     (*   inversion Hwp as [| | ???? Hwp']; simplify_eq; try congruence. *) *)
(*     (*   have [||{}Hwp]:= Hwp' n => //. admit.     *) *)
(*     (*   apply: IH => //. by apply: Hwp. *) *)
(*     (* admit. *) *)
(*     (* inversion Hwp as [???? Hwp'| |]; simplify_eq; try congruence. *) *)
(*     (* admit. *) *)
(*   (*   move => σi1. exists 0 => κstart Hwp σs Hsteps Hsafe Hκ. *) *)
(*   (*   rewrite right_id in Hκ; subst. split; eauto. *) *)
(*   (*   destruct Hwp as [??? Hwp]. *) *)
(*   (*   move: (Hwp None) => [|] //=. *) *)
(*   (*   by rewrite right_id. *) *)
(*   (* - move => σi1 σi2 σi3 κ κend Hstep Hsteps [n IH]. exists (S n) => κstart Hwp σs1 Hstepsi Hsafe Hκs. *) *)
(*   (*   inversion_clear Hwp as [??? Hwp2]; subst. *) *)
(*   (*   move : (Hwp2 κ) => [|? Hwp] //=. { move => ???. apply Hsafe. etrans => //. rewrite assoc. by eexists. } *) *)
(*   (*   have [|σs2 [Hsteps2 {}Hwp]]:= (Hwp _ n _ Hstep) => //. *) *)
(*   (*   have [||?[??]]:= (IH _ Hwp _ Hsteps2) => //. by rewrite assoc. *) *)
(*   (*   split => //. naive_solver. *) *)
(*     (* Qed. *) *)
(* Admitted. *)

(* (* *)
(*   What about the program: *)

(*   x <- AngelicChoice nat; *)
(*   iterate for x steps; *)
(*   event A *)

(*   vs. *)

(*   x <- DemonicChoice nat; *)
(*   iterate for x steps; *)
(*   event A *)

(*   How to prove that they refine "event A"? Can this be done by just looking at all the *)
(*   finite prefixes? What is the difference between the two? *)

(* *) *)

(* Lemma refines_implies_wp' {EV} (m1 m2 : module EV): *)
(*   refines m1 m2 → *)
(*   (∀ n, wp' m1 m2 n m1.(m_initial) []). *)
(* Proof. *)
(*   move => Hr n. *)
(*   (* have : (steps m1.(m_step) m1.(m_initial) [] m1.(m_initial)). { by left. } *) *)
(*   (* move: {2 3}(m1.(m_initial)) => σi. *) *)
(*   move: (m1.(m_initial)) => σi. *)
(*   move: ([]) => κstart. *)
(*   elim/lt_wf_ind: n κstart σi. *)
(*   move => n IH κstart σi. *)
(*   apply: wp'_constructor => n' ?. subst. *)
(*   case_match. *)
(*   - right. *)
(*     admit. *)
(*   - right. move => ??. apply: IH. lia. *)
(*   - right. *)
(* Admitted. *)

(* (*** properties of refines *) *)
(* Definition safe {EV} (m : module EV) := *)
(*   ∀ κs, trace_of_program m κs → trace_is_ub κs = false. *)
(* Lemma refines_preserves_safe EV (mspec mimpl : module EV): *)
(*   safe mspec → *)
(*   refines mimpl mspec → *)
(*   safe mimpl. *)
(* Proof. rewrite /safe => ? [Hr]. naive_solver. Qed. *)

(* Lemma refines_reflexive EV (m : module EV): *)
(*   refines m m. *)
(* Proof. constructor. naive_solver. Qed. *)

(* Lemma refines_vertical EV (m1 m2 m3 : module EV): *)
(*   refines m1 m2 → *)
(*   refines m2 m3 → *)
(*   refines m1 m3. *)
(* Proof. move => [Hr1] [Hr2]. constructor => /=. naive_solver. Qed. *)

(* (*** link *) *)
(* Inductive link_step_case : Type := *)
(* | LSCBase | LSCLeft | LSCRight | LSCBoth. *)
(* Inductive link_step {EV1 EV2 EV3} (m1 : module EV1) (m2 : module EV2) (R : option EV1 → option EV2 → option EV3 → Prop) : *)
(*   link_step_case * m1.(m_state) * m2.(m_state) → option EV3 → link_step_case * m1.(m_state) * m2.(m_state) → Prop := *)
(* | LinkStepBaseL σ1 σ2: *)
(*     link_step m1 m2 R (LSCBase, σ1, σ2) None (LSCLeft, σ1, σ2) *)
(* | LinkStepBaseR σ1 σ2: *)
(*     link_step m1 m2 R (LSCRight, σ1, σ2) None (LSCRight, σ1, σ2) *)
(* | LinkStepBaseBoth σ1 σ2: *)
(*     link_step m1 m2 R (LSCBase, σ1, σ2) None (LSCBoth, σ1, σ2) *)
(* | LinkStepL σ1 σ2 e1 e' σ1': *)
(*     m1.(m_step) σ1 e1 σ1' → *)
(*     (* TODO: is there a better way to formulate this? E.g. assume *)
(*     that there is no R None None Some in the theorem? *) *)
(*     (if e1 is Some es1 then R e1 None e' else e' = None) → *)
(*     link_step m1 m2 R (LSCLeft, σ1, σ2) e' (LSCBase, σ1', σ2) *)
(* | LinkStepR σ1 σ2 e2 e' σ2': *)
(*     m2.(m_step) σ2 e2 σ2' → *)
(*     (if e2 is Some es2 then R None e2 e' else e' = None) → *)
(*     link_step m1 m2 R (LSCRight, σ1, σ2) e' (LSCBase, σ1, σ2') *)
(* | LinkStepBoth σ1 σ2 e1 e2 e' σ1' σ2': *)
(*     m1.(m_state_kind) σ1 = kind_visible → m2.(m_state_kind) σ2 = kind_visible → *)
(*     m1.(m_step) σ1 (Some e1) σ1' → *)
(*     m2.(m_step) σ2 (Some e2) σ2' → *)
(*     R (Some e1) (Some e2) e' → *)
(*     link_step m1 m2 R (LSCBoth, σ1, σ2) e' (LSCBase, σ1', σ2'). *)

(* Program Definition link {EV1 EV2 EV3} (m1 : module EV1) (m2 : module EV2) (R : option EV1 → option EV2 → option EV3 → Prop) : module EV3 := {| *)
(*   m_state := link_step_case * m1.(m_state) * m2.(m_state); *)
(*   m_initial := (LSCBase, m1.(m_initial), m2.(m_initial)); *)
(*   m_step := (link_step m1 m2 R); *)
(*   m_state_kind '(lsc, σ1, σ2) := *)
(*     match lsc return _ with *)
(*     | LSCBase => kind_demonic *)
(*     | LSCBoth => kind_visible *)
(*     | LSCLeft => m1.(m_state_kind) σ1 *)
(*     | LSCRight => m2.(m_state_kind) σ2 *)
(*     end *)
(* |}. *)
(* Next Obligation. *)
(*   move => ??? m1 m2 R [[lsc ?]?] [[??]?] [[??]?] ?? /= ? Hstep1 Hstep2. *)
(*   destruct lsc => //. *)
(*   - inversion Hstep1 => //; simplify_eq. *)
(*     inversion Hstep2 => //; simplify_eq. *)
(*     (* efeed pose proof (m_vis_det _ m1). *) *)
(*     (* provable *) *)
(*     admit. *)
(*   - (* provable *) *)
(*     admit. *)
(*   - inversion Hstep1 => //; simplify_eq. *)
(*     inversion Hstep2 => //; simplify_eq. *)
(*     (* provable if R is functional *) *)
(*     admit. *)
(* Admitted. *)
(* Next Obligation. *)
(*   move => ??? m1 m2 R [[lsc ?]?] [[??]?] ? /= ? Hstep1. *)
(*   destruct lsc => //; inversion Hstep1 => //; simplify_eq. *)
(*     (* provable *) *)
(* Admitted. *)

(* (* Lemma link_empty_steps_l {EV1 EV2 EV3} m1 m2 σ1 σ1' σ2 (R : option EV1 → option EV2 → option EV3 → Prop) : *) *)
(* (*   steps (m_step m1) σ1 [] σ1' → *) *)
(* (*   steps (link_step m1 m2 R) (σ1, σ2) [] (σ1', σ2). *) *)
(* (* Proof. *) *)
(* (*   move Hκ: ([]) => κ Hsteps. *) *)
(* (*   elim: Hsteps Hκ. by left. *) *)
(* (*   move => ??? [] //= ?????. *) *)
(* (*   apply: (steps_l _ _ _ _ None); [ | naive_solver]. *) *)
(* (*     by econstructor. *) *)
(* (* Qed. *) *)

(* (* Lemma link_empty_steps_r {EV1 EV2 EV3} m1 m2 σ1 σ2' σ2 (R : option EV1 → option EV2 → option EV3 → Prop) : *) *)
(* (*   steps (m_step m2) σ2 [] σ2' → *) *)
(* (*   steps (link_step m1 m2 R) (σ1, σ2) [] (σ1, σ2'). *) *)
(* (* Proof. *) *)
(* (*   move Hκ: ([]) => κ Hsteps. *) *)
(* (*   elim: Hsteps Hκ. by left. *) *)
(* (*   move => ??? [] //= ?????. *) *)
(* (*   apply: (steps_l _ _ _ _ None); [ | naive_solver]. *) *)
(* (*     by econstructor. *) *)
(* (* Qed. *) *)

(* Inductive link_trace_related {EV1 EV2 EV3} (R : option EV1 → option EV2 → option EV3 → Prop) : trace EV1 → trace EV2 → trace EV3 → Prop := *)
(* | LinkTraceRelNil: *)
(*     link_trace_related R nb nb nb *)
(* | LinkTraceRelUbL κs2 κs3: *)
(*     link_trace_related R ub κs2 κs3 *)
(* | LinkTraceRelUbR κs1 κs3: *)
(*     link_trace_related R κs1 ub κs3 *)
(* | LinkTraceRelL κ1 κ1' κs1 κs2 κs3: *)
(*     link_trace_related R κs1 κs2 κs3 → *)
(*     R (Some κ1) None κ1' → *)
(*     link_trace_related R (vis κ1 nb +t+ κs1) κs2 (option_trace κ1' +t+ κs3) *)
(* | LinkTraceRelR κ2 κ2' κs1 κs2 κs3: *)
(*     link_trace_related R κs1 κs2 κs3 → *)
(*     R None (Some κ2) κ2' → *)
(*     link_trace_related R κs1 (vis κ2 nb +t+ κs2) (option_trace κ2' +t+ κs3) *)
(* | LinkTraceRelBoth κ1 κ2 κ3 κs1 κs2 κs3: *)
(*     link_trace_related R κs1 κs2 κs3 → *)
(*     R (Some κ1) (Some κ2) κ3 → *)
(*     link_trace_related R (vis κ1 nb +t+ κs1) (vis κ2 nb +t+ κs2) (option_trace κ3 +t+ κs3) *)
(* . *)

(* Lemma link_trace_related_create {EV1 EV2 EV3} (R : option EV1 → option EV2 → option EV3 → Prop) m1 m2 κs3 σ1: *)
(*   trace_of_state (link m1 m2 R) (λ _, True) σ1 κs3 → *)
(*   ∃ κs1 κs2, link_trace_related R κs1 κs2 κs3 ∧ *)
(*   trace_of_state m1 (λ _, True) σ1.1.2 κs1 ∧ *)
(*   trace_of_state m2 (λ _, True) σ1.2 κs2. *)
(* Proof. *)
(*   elim; clear. { move => ? ?. exists nb, nb. by split_and!; constructor. } *)
(*   move => σ κs e. *)
(*   case; clear. *)
(*   - move => σ σ' e Hkind Hstep [Hsteps [κs1 [κs2 [Hlink [Hκ1 Hκ2]]]]]. *)
(*     inversion Hstep; clear Hstep; simplify_eq/=. *)
(*     + admit. *)
(*     + admit. *)
(*     + admit. *)
(*     + admit. *)
(*   - move => σ Hkind [σ' [Hstep [Hsteps [κs1 [κs2 [Hlink [Hκ1 Hκ2]]]]]]]. *)
(*     inversion Hstep; clear Hstep; simplify_eq/=. *)
(*     + admit. *)
(*     + admit. *)
(*     + admit. *)
(*     + admit. *)
(*     + admit. *)
(*   - move => [[[]?] ?] //= Hkind IH. *)
(*     destruct σ. *)
(*   - exists (κs1 ++ option_list e1), κs2. *)
(*     split_and! => //; destruct e1; simplify_eq/= => //; rewrite ?right_id //. by constructor. *)
(*     + apply: steps_trans => //. apply: steps_Some => //. left. *)
(*     + rewrite -(right_id_L [] (++) κs1). *)
(*       apply: steps_trans => //. apply: steps_None => //. left. *)
(*   - exists κs1, (κs2 ++ option_list e2). *)
(*     split_and! => //; destruct e2; simplify_eq/= => //; rewrite ?right_id //. by constructor. *)
(*     + apply: steps_trans => //. apply: steps_Some => //. left. *)
(*     + rewrite -(right_id_L [] (++) κs2). *)
(*       apply: steps_trans => //. apply: steps_None => //. left. *)
(*   - exists (κs1 ++ [e1]), (κs2 ++ [e2]). *)
(*     split_and!. *)
(*     + by apply LinkTraceRelBoth. *)
(*     + apply: steps_trans => //. apply: steps_Some => //. left. *)
(*     + apply: steps_trans => //. apply: steps_Some => //. left. *)
(* Qed. *)

End version4.

Module version5.
(* alternating automata version *)
(*** trace *)
(* Tried using the following with
| OfStateAngelic σ A f:
    m.(m_state_kind) σ = kind_angelic →
    (∀ σ', m.(m_step) σ None σ' → ∃ x, trace_of_state m σ' (f x)) →
    trace_of_state m σ (branch A f).
but that did not work well (where do you learn anything about A or f)?*)
(* Inductive trace (EV : Type) : Type := *)
(* | ub | nb | vis (e : EV) (κ : trace EV) | branch (T : Type) (next : T → trace EV). *)
Inductive trace (EV : Type) : Type :=
| ub | nb | vis (e : EV) (κ : trace EV).
Arguments ub {_}.
Arguments nb {_}.
Arguments vis {_}.

Fixpoint trace_events {EV} (l : trace EV) : list EV :=
  match l with
  | nb | ub => []
  | vis e l' => e :: trace_events l'
  end.

Fixpoint trace_is_ub {EV} (l : trace EV) : bool :=
  match l with
  | nb => false
  | ub => true
  | vis e l' => trace_is_ub l'
  end.

Fixpoint list_to_trace {EV} (is_ub : bool) (l : list EV) : trace EV :=
  match l with
  | [] => if is_ub then ub else nb
  | e :: l' => vis e (list_to_trace is_ub l')
  end.
Definition nb_trace {EV} := list_to_trace (EV:=EV) false.
Definition ub_trace {EV} := list_to_trace (EV:=EV) true.

Definition option_trace {EV} (o : option EV) : trace EV :=
  match o with
  | Some e => vis e nb
  | None => nb
  end.

Definition trace_app {EV} (κs1 κs2 : trace EV) : trace EV :=
  list_to_trace (trace_is_ub κs1 || trace_is_ub κs2) (trace_events κs1 ++ trace_events κs2).
Infix "+t+" := trace_app (right associativity, at level 60) : stdpp_scope.

Definition trace_prefix {EV} (κs1 κs2 : trace EV) : Prop :=
  ∃ κs', κs1 +t+ κs' = κs2.
Infix "`trace_prefix_of`" := trace_prefix (at level 70) : stdpp_scope.

Lemma list_to_trace_events {EV} u (l : list EV):
  trace_events (list_to_trace u l) = l.
Proof. elim: l => //=. { by destruct u. } by move => ?? ->. Qed.

Lemma list_to_trace_ub {EV} u (l : list EV):
  trace_is_ub (list_to_trace u l) = u.
Proof. elim: l => //=. by destruct u. Qed.

Lemma list_to_trace_id {EV} (κs : trace EV) :
  list_to_trace (trace_is_ub κs) (trace_events κs) = κs.
Proof. by elim: κs => //= ? ? ->. Qed.

Lemma option_trace_events {EV} (e : option EV) :
  trace_events (option_trace e) = option_list e.
Proof. by destruct e. Qed.

Lemma option_trace_ub {EV} (e : option EV) :
  trace_is_ub (option_trace e) = false.
Proof. by destruct e. Qed.

Global Instance trace_app_assoc {EV} : Assoc (=) (trace_app (EV:=EV)).
Proof.
  move => ???. by rewrite /trace_app !list_to_trace_events !list_to_trace_ub (assoc (++)) orb_assoc.
Qed.

Global Instance trace_app_left_id {EV} : LeftId (=) nb (trace_app (EV:=EV)).
Proof. move => ?. by rewrite /trace_app/= list_to_trace_id. Qed.

Global Instance trace_app_right_id {EV} : RightId (=) nb (trace_app (EV:=EV)).
Proof. move => ?. by rewrite /trace_app/= right_id_L orb_false_r list_to_trace_id. Qed.

Lemma trace_app_vis {EV} (κs : trace EV) e:
  vis e κs = (vis e nb) +t+ κs.
Proof. by rewrite /trace_app/= list_to_trace_id. Qed.

Lemma trace_app_events {EV} (κs1 κs2 : trace EV):
  trace_events (κs1 +t+ κs2) = trace_events κs1 ++ trace_events κs2.
Proof. by rewrite /trace_app list_to_trace_events. Qed.

Lemma trace_app_ub {EV} (κs1 κs2 : trace EV):
  trace_is_ub (κs1 +t+ κs2) = orb (trace_is_ub κs1) (trace_is_ub κs2).
Proof. by rewrite /trace_app list_to_trace_ub. Qed.

Global Instance trace_prefix_preorder EV: PreOrder (@trace_prefix EV).
Proof.
  split.
  - move => ?. exists nb. by rewrite right_id_L.
  - move => ??? [k1 <-] [k2 <-]. exists (k1 +t+ k2). by rewrite (assoc_L).
Qed.
Lemma trace_prefix_nb {EV} (l : trace EV) : nb `trace_prefix_of` l.
Proof. exists l. by rewrite left_id. Qed.

(*** module *)
(* Inductive mod_state_kind : Type := *)
(* | kind_visible | kind_demonic | kind_angelic. *)
(* Global Instance mod_state_kind_eq_dec : EqDecision mod_state_kind. *)
(* Proof. solve_decision. Qed. *)

Record module (EV : Type) : Type := {
  m_state : Type;
  (* multiple initial states can be modeled by non-deterministically
  branching from the initial state *)
  m_initial : m_state;
  (* m_state_kind : m_state → mod_state_kind; *)
  m_step : m_state → option EV → propset m_state → Prop;

  (* m_vis_det σ σ1 σ2 e1 e2: *)
  (*   m_state_kind σ = kind_visible → *)
  (*   m_step σ e1 σ1 → *)
  (*   m_step σ e2 σ2 → *)
  (*   σ1 = σ2 ∧ e1 = e2; *)
  (* the following is problem for hiding *)
  (* m_vis_exists σ: *)
  (*   m_state_kind σ = kind_visible → *)
  (*   ∃ σ' e, m_step σ (Some e) σ'; *)
  (* sanity *)
  (* m_non_vis_silent σ σ' e: *)
  (*   m_state_kind σ ≠ kind_visible → *)
  (*   m_step σ e σ' → *)
  (*   e = None; *)
}.
Arguments m_state {_}.
Arguments m_initial {_}.
(* Arguments m_state_kind {_}. *)
Arguments m_step {_}.

(*** trace of module *)

Section ind.
(* Local Unset Elimination Schemes. *)

Definition propset_union {A} (S : propset (propset A)) : propset A :=
  {[ x | ∃ σ, σ ∈ S ∧ x ∈ σ ]}.
Definition propset_intersection {A} (S : propset (propset A)) : propset A :=
  {[ x | ∀ σ, σ ∈ S → x ∈ σ ]}.

Inductive trace_of_state {EV} (m : module EV) : propset m.(m_state) → propset (trace EV) → Prop :=
| OfStateNb S T:
    T ≡ {[ nb ]} →
    trace_of_state m S T
| OfStateVis (S : propset m.(m_state)) σ e S' T T':
    σ ∈ S →
    m.(m_step) σ e S' →
    ((∀ σ, σ ∈ S' → trace_of_state m {[σ]} T)) →
    T' ≡ ((λ κs', option_trace e +t+ κs') <$> T) →
    trace_of_state m S T'.
End ind.

Global Instance trace_of_state_Proper {EV} (m : module EV) : Proper ((=) ==> (≡) ==> (iff)) (trace_of_state m).
Proof.
  move => ? σ -> T1 T2 HT.
  split => Hs; [move: T2 HT | move: T1 HT]; elim: Hs.
  all: try by move => *; apply: OfStateNb; setoid_subst.
  all: try by move => *; apply: OfStateVis; setoid_subst.
Qed.
  (* all: try by move => *; apply: OfStateDemonic; setoid_subst; naive_solver. *)
(* Admitted. *)

(* Lemma trace_of_state_ind {EV} (m : module EV) (F : m_state m → Prop) (P : m_state m → (trace EV → Prop) → Prop) : *)
(*   (∀ (σ : m_state m) (T : trace EV → Prop), F σ → T nb → P σ T) *)
(*   → (∀ (σ : m_state m) (e : option EV) (T : trace EV → Prop), *)
(*         trace_step m (λ σ' : m_state m, trace_of_state m F σ' T ∧ P σ' T) σ e → P σ (λ κs : trace EV, ∃ κs' : trace EV, T κs' ∧ option_trace e +t+ κs' = κs)) *)
(*   → ∀ (m0 : m_state m) (t : trace EV → Prop), trace_of_state m F m0 t → P m0 t. *)
(* Proof. *)
(*   fix FIX 5. move => Hnb Hstep ??. *)
(*   case. *)
(*   - by apply: Hnb. *)
(*   - move => ??? Hs. eapply Hstep => //. *)
(*     case: Hs => *; [ apply: StepVis | apply: StepDemonic | apply: StepAngelic] => //; naive_solver. *)
(* Qed. *)
Definition trace_of_program {EV} (m : module EV) := PropSet (trace_of_state m {[m.(m_initial)]}).

Program Definition test_mod_1 : module unit := {|
  m_state := unit;
  m_initial := ();
  (* m_state_kind _ := kind_visible; *)
  m_step _ e σ := e = None ∧ σ = {[ tt ]};
|}.
(* Next Obligation. move => [] [] [] [|[]] //. Qed. *)
(* Next Obligation. done. Qed. *)
Lemma test_mod_1_traces:
  trace_of_program test_mod_1 ≡ {[ x | x ≡ {[ nb ]} ]}.
Proof.
  move => κs.
  split.
  - rewrite !elem_of_PropSet => /=.
    elim => //.
    move => ? [] ? ? T ? ? [-> ->] /= ? IH ->.
    rewrite (IH tt); set_solver.
  - rewrite !elem_of_PropSet => ->. by apply OfStateNb.
Qed.

Program Definition test_mod_2 : module nat := {|
  m_state := bool;
  m_initial := false;
  (* m_state_kind b := if b then kind_demonic else kind_visible; *)
  m_step b1 e b2 := b1 = false ∧ e = Some 2 ∧ b2 = {[ true ]};
|}.
(* Next Obligation. move => []//[][]//; naive_solver. Qed. *)
(* Next Obligation. move => [][]//; naive_solver. Qed. *)

Lemma test_mod_2_traces:
  trace_of_program test_mod_2 ≡ {[ x | x ≡ {[ nb ]} ]} ∪ {[ x | x ≡ {[ vis 2 nb ]} ]}.
Proof.
  move => κs.
  split.
  - rewrite !elem_of_PropSet.
    inversion_clear 1; simplify_eq/=; destruct_and?; simplify_eq/=. naive_solver.
    setoid_subst. right.
    revert select (∀ σ, _) => Hs. have := Hs true ltac:(set_solver).
    inversion_clear 1; simplify_eq; setoid_subst.
    + set_solver.
    + destruct σ; set_solver.
  - rewrite !elem_of_PropSet => -[|] ->.
    + by apply OfStateNb.
    + apply: OfStateVis => //. move => ??. by apply OfStateNb.
      set_unfold. move => ?. split. { move => ->. exists nb. naive_solver. }
      by move => [? [-> ->]].
Qed.

Inductive test_mod3_state := | S3S1 | S3S2 (n : nat) | S3S3.
Program Definition test_mod_3 (dem : bool) : module nat := {|
  m_state := test_mod3_state;
  m_initial := S3S1;
  m_step b1 e b2 :=
    (b1 = S3S1 ∧ e = None ∧ if dem then ∃ n, b2 = {[ S3S2 n ]} else b2 = {[ x | ∃ n, x = S3S2 n ]}) ∨
    (∃ n, b1 = S3S2 n ∧ e = Some n ∧ b2 = {[ S3S3 ]})
|}.
(* Next Obligation. move => []//[][]//; naive_solver. Qed. *)
(* Next Obligation. move => [][]//; naive_solver. Qed. *)

Lemma test_mod_3_traces_demonic:
  (* {{nb}, {nb, vis 0 nb}, ..., {nb, vis n nb}, ...}*)
  trace_of_program (test_mod_3 true) ≡ {[ x | x ≡ {[ nb ]} ]} ∪ {[ x | ∃ n, x ≡ {[ vis n nb ]} ]}.
Proof.
  move => κs.
  split.
  - rewrite !elem_of_PropSet.
    inversion_clear 1; simplify_eq/=; destruct_and?; simplify_eq/=. naive_solver.
    setoid_subst.
    destruct σ; try set_solver.
    revert select (_ ∨ _) => -[[? [? [n ?]]]|]. 2: naive_solver. subst.
    revert select (∀ σ, _) => Hs. have := Hs _ ltac:(set_solver).
    inversion_clear 1; simplify_eq. { left. set_solver. }
    right. clear Hs. exists n. setoid_subst.
    have ?: σ = S3S2 n by set_solver. subst.
    revert select (_ ∨ _) => -[|[n' [?[??]]]]; simplify_eq. 1: naive_solver.
    revert select (∀ σ, _) => Hs. have := Hs _ ltac:(set_solver).
    inversion_clear 1; simplify_eq; setoid_subst. 2: set_solver.
    set_unfold => ?. split; naive_solver.
  - rewrite !elem_of_PropSet => -[|] HS.
    + by apply OfStateNb.
    + move: HS => [n ->]. apply: OfStateVis => //. naive_solver.
      instantiate (2:=n).
      instantiate (1:={[ vis n nb]}).
      2: { set_unfold. split; try naive_solver. move => ->. exists (vis n nb). naive_solver. }
      set_unfold => ? ->.
      apply: OfStateVis => //. naive_solver. move => ??. by apply OfStateNb.
      set_unfold. split; try naive_solver. move => ->. by exists nb.
Qed.

Lemma test_mod_3_traces_angelic:
  (* {{nb}, {nb, vis 0 nb, ..., vis n nb, ...} }*)
  trace_of_program (test_mod_3 false) ≡ {[ x | x ≡ {[ nb ]} ]} ∪ {[ x | x ≡  {[ y | ∃ n, y = vis n nb ]} ]}.
Proof.
  move => κs.
  split.
  - rewrite !elem_of_PropSet.
    inversion_clear 1; simplify_eq/=; destruct_and?; simplify_eq/=. naive_solver.
    setoid_subst.
    destruct σ; try set_solver.
    revert select (_ ∨ _) => -[[? [? ?]]|]. 2: naive_solver. subst.
    revert select (∀ σ, _) => Hs.

    have [HT|?]: (T ≡ {[nb]}) ∨ ¬ (T ≡ {[nb]}). admit. {
      left. rewrite HT. set_unfold. split; naive_solver.
    }

    right.
    move => κs.
    have [[n ->]| ?]: (∃ n, κs = vis n nb) ∨ ¬(∃ n, κs = vis n nb) by destruct κs as [| |? []]; naive_solver.
    + have := Hs (S3S2 n) ltac:(set_solver).
      inversion_clear 1; simplify_eq/= => //.
      revert select (_ ∨ _) => -[|[n' [?[??]]]]; simplify_eq. 1: set_solver.
      setoid_subst.
      revert select (∀ σ, _) => {}Hs. have := Hs _ ltac:(set_solver).
      inversion_clear 1; simplify_eq; setoid_subst. 2: set_solver.
      set_unfold. split; naive_solver.
    + have := Hs (S3S2 0) ltac:(set_solver).
      inversion_clear 1; simplify_eq/= => //.
      revert select (_ ∨ _) => -[|[n' [?[??]]]]; simplify_eq. 1: set_solver.
      setoid_subst.
      revert select (∀ σ, _) => {}Hs. have := Hs _ ltac:(set_solver).
      inversion_clear 1; simplify_eq; setoid_subst. 2: set_solver.
      set_unfold. split; naive_solver.
  - rewrite !elem_of_PropSet => -[|] HS.
    + by apply OfStateNb.
    + move: HS => ->. apply: OfStateVis => //. naive_solver.
      instantiate (1 := {[ y | ∃ n : nat, y = vis n nb ]}). 2: {
        set_unfold. split; try naive_solver. move => [n ->]. exists (vis n nb). naive_solver.
      }
      move => σ [n ->]. apply: OfStateVis => //. naive_solver.
      * move => []// ?. apply OfStateNb. done.
      * set_unfold. split; try naive_solver. move => [n' ->]. exists (nb).
        admit.
Abort.
End version5.
(*
  Idea: have a judgment [m1 < m2 | m3] which desugars to
   ∀ m, m < m3 -> m1 + m < m2 + m
  and then prove
    Impl 1 High < Spec 1 | Memory High
  but it is not clear if this is enough as maybe the memory model changes between impl and spec.
  So maybe have a notion of adapter and then prove
    Impl 1 Low < Impl 1 High + High2LowAdapter | Memory Low
  The adapter could translate all calls to Memory High to calls to Memory Low

  Idea for modeling private memory of one module:
  - if we prove refinement m1 + memory < m2 + memory', this refinement can change the memory module!
  - especially it can make more things UB in memory'
  - This can be used to insert checks around access operations to ensure that no other module
    breaks the invariants placed on memory.

  Problem: Refinement of low-level memory to high-level memory depends on the C code (which is verified
    with the high-level memory) behaving correctly.
  - Is this really the case? Or could we simply make everything bad UB in the high-level memory?


  Other idea for modelling private memory:
  - The memory module splits the heap into two parts: One public part and one private part.
    The private part can change arbitrarily on each step and an fresh address is fresh for
    both public and private part.
    Then the refinement C + memory < Spec + memory can put the memory of the C code into the
    private part of the top level memory.
  - The can be a Reveal event of the memory which shows some part of the private memory. This
    could be useful for sharing memory between different modules / passing ownership between modules.
  - For more complicated stuff the memory module could put an (user-chosen) invariant on some parts
    of the memory.

  Example:
                  High-level spec
                  /------------\
          --------              -------
       Spec 1            +          Spec 2             Spec
            |                         |
            |                         |
       Impl 1 High+ Memory High       |                  C
            |           |             |
            |           |             |
       Impl 1 Low + Memory Low   +  Impl 2              ASM
         --------      |       /------->
                 \-----+-------
        Low-level code including memory model (or without memory model?)



  High-level spec:
                           Res 1
       Initial state  -------------->  Final State

    out_event: Res Z

  Spec 1:                      Spec 2:
                               (no main)
   main: let x := Call A;       A: return 1
         Emit (Res x + 1)

   out_event: Res Z | CallA    in_event: CallA
     | RetA Z                  out_event: RetA Z

  Impl 1 High:                                    Memory High:

   main: int* x1 = alloc_int;                      No offset operation on locations,
         int* x2 = alloc_int;                      Memory layout is hidden (i.e. integers are stored as
         x2 := 1;                                  mathematical integers, constraint that all integers on the
         Call A x1;                                heap are 0 ≤ n < 2 ^ 32
         Emit (Res *x1 * *x2)

   out_event: Res Z | CallA loc                   in_event: AllocInt loc | LoadInt loc Z | WriteInt loc Z
     | RetA | AllocInt loc
     | LoadInt loc Z

  Impl 1 Low:                  Impl 2 Low:        Memory Low:

   main: int* x1 = alloc_int;   A p: (p + 0) := 1; Flat memory model which stores bytes
         int* x2 = alloc_int;        (p + 1) := 0;
         x2 := 1;                    (p + 2) := 0;
         Call A x1;                  (p + 3) := 0;
         Emit (Res *x1 + *x2)


   out_event: Res Z | CallA loc in_event: CallA loc  in_event: AllocInt loc | WriteByte loc Z
     | RetA | AllocInt loc      out_event: RetA         | LoadInt loc Z | WriteInt loc Z
     | LoadInt loc Z              | WriteByte loc Z
     | WriteInt loc Z

  Low level code (i.e. code with inline assembly)
   main: int* x1 = alloc_int;     Flat memory model which stores bytes
         int* x2 = alloc_int;
         x2 := 1;
         (x1 + 0) := 1;
         (x1 + 1) := 0;
         (x1 + 1) := 0;
         (x1 + 1) := 0;
         Emit (Res *x1 + *x2)

   out_event: Res Z

 Proofs:

  m1 < m2 : [refines m1 m2]
  m1 + m2 : [link m1 m2]

  1: LLC < Impl 1 Low + Memory Low + Impl 2 / {CallA, RetA, AllocInt, ...}

  2: Impl 1 Low | Memory Low < Impl 1 High | Memory High

  3: ∀ X1 X2,
              calling convention change
                     X1 < X2
     ---------------------------------------------
      Impl 1 High | Memory High | X1 < Spec 1 | Memory High | X2

      calling convention change
  4: Impl 2 | Memory Low < Spec 2

  5: Spec 1 | Spec 2 < High-level Spec (HLS)

  6: Memory Low < Memory High

  Theorems:
    Refl ([refines_reflexive]): m < m

    VC ([refines_vertical]):     m1 < m2   m2 < m3
                                 -----------------
                                      m1 < m3

    HC:       m1 < m1'   m2 < m2'
             --------------------
              m1 + m2 < m1' + m2'

    | intro: (m1 | m2) + m2 < m1 + m2

    | elim:   m1 + m2 < (m1 | m2) + m2

    | ignore:       m1 < m2
              ---------------------
               (m1 | m) < (m2 | m)

    +-I:            X m2          requires some condition X on m2
              -----------------   something like none of its events appear in m3
                m1 + m2 < m1

    +-E:            X m2            requires some condition X on m2
              -----------------     something like none of its events appear in m3
                m1 < m1 + m2


  Proof tree:

   -------------------------------------- 1
   LLC < Impl 1 Low + Memory Low + Impl 2
   -------------------------------------------------------------------- VC, |-I
   LLC < (Impl 1 Low | Memory Low | Impl 2) + Memory Low + (Impl 2 | Memory Low)
   -------------------------------------------------------------------- HC, | ignore, 2, 4, 6
   LLC < (Impl 1 High | Memory High | Impl 2) + Memory High + Spec 2
   -------------------------------------------------------------------- HC, 3, 4
   LLC < (Spec 1 | Memory High | Spec 2) + Memory High + Spec 2
   ------------------------------------------------------------- VC,|-E
   LLC < Spec 1 + Memory High + Spec 2
                  |                                 ----------------------- 5
                  |                                 (Spec 1 | Spec 2) < HLS
                  |                                -------------------------------- VC, +-I
                  |                                (Spec 1 | Spec 2) + Spec 2 < HLS
    ------------------------------- VC,+-E         -------------------------------- VC, |-E
    LLC < Spec 1 + Spec 2                           Spec 1 + Spec 2 < HLS
   ------------------------------------------------ VC
            LLC < HLS




*)
