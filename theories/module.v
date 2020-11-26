Require Import refframe.base.
Require Import stdpp.namespaces.
Require Import stdpp.strings.
Require Import stdpp.gmap.
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

Definition all_reachable {A B} (R : A → option B → A → Prop) (σ : A) (κ : list B) (P : A → list B → Prop) : Prop :=
  (∀ σ' κ', κ' `prefix_of` κ → steps R σ κ' σ' → P σ' κ').

Definition safe_trace {EV} (m : module EV) (σ : m.(m_state)) (κ : list EV) : Prop :=
  all_reachable m.(m_step) σ κ (λ σ' κ', m.(m_is_good) σ').

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
    (∀ κ, safe_trace m2 m2.(m_initial) (κs ++ option_list κ) → m1.(m_is_good) σi1 ∧
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

(*** module_product *)
Inductive module_product_step {EV1 EV2 EV3} (m1 : module EV1) (m2 : module EV2) (R : option EV1 → option EV2 → option EV3 → Prop) :
  m1.(m_state) * m2.(m_state) → option EV3 → m1.(m_state) * m2.(m_state) → Prop :=
| MpStepL σ1 σ2 e1 e' σ1':
    m1.(m_step) σ1 e1 σ1' →
    (if e1 is Some es1 then R e1 None e' else e' = None) →
    module_product_step m1 m2 R (σ1, σ2) e' (σ1', σ2)
| MpStepR σ1 σ2 e2 e' σ2':
    m2.(m_step) σ2 e2 σ2' →
    (if e2 is Some es2 then R None e2 e' else e' = None) →
    module_product_step m1 m2 R (σ1, σ2) e' (σ1, σ2')
| MpStepBoth σ1 σ2 e1 e2 e' σ1' σ2':
    m1.(m_step) σ1 (Some e1) σ1' →
    m2.(m_step) σ2 (Some e2) σ2' →
    R (Some e1) (Some e2) e' →
    module_product_step m1 m2 R (σ1, σ2) e' (σ1', σ2').

Definition module_product {EV1 EV2 EV3} (m1 : module EV1) (m2 : module EV2) (R : option EV1 → option EV2 → option EV3 → Prop) : module EV3 := {|
  m_state := m1.(m_state) * m2.(m_state);
  m_initial := (m1.(m_initial), m2.(m_initial));
  m_step := (module_product_step m1 m2 R);
  m_is_good σ := m1.(m_is_good) σ.1 ∧ m2.(m_is_good) σ.2;
|}.


Lemma product_empty_steps_l {EV1 EV2 EV3} m1 m2 σ1 σ1' σ2 (R : option EV1 → option EV2 → option EV3 → Prop) :
  steps (m_step m1) σ1 [] σ1' →
  steps (module_product_step m1 m2 R) (σ1, σ2) [] (σ1', σ2).
Proof.
  move Hκ: ([]) => κ Hsteps.
  elim: Hsteps Hκ. by left.
  move => ??? [] //= ?????.
  apply: (steps_l _ _ _ _ None); [ | naive_solver].
    by econstructor.
Qed.

Lemma product_empty_steps_r {EV1 EV2 EV3} m1 m2 σ1 σ2' σ2 (R : option EV1 → option EV2 → option EV3 → Prop) :
  steps (m_step m2) σ2 [] σ2' →
  steps (module_product_step m1 m2 R) (σ1, σ2) [] (σ1, σ2').
Proof.
  move Hκ: ([]) => κ Hsteps.
  elim: Hsteps Hκ. by left.
  move => ??? [] //= ?????.
  apply: (steps_l _ _ _ _ None); [ | naive_solver].
    by econstructor.
Qed.

Inductive product_trace_related {EV1 EV2 EV3} (R : option EV1 → option EV2 → option EV3 → Prop) : list EV1 → list EV2 → list EV3 → Prop :=
| ProdTraceRelNil:
    product_trace_related R [] [] []
| ProdTraceRelL κ1 κ1' κs1 κs2 κs3:
    product_trace_related R κs1 κs2 κs3 →
    R (Some κ1) None κ1' →
    product_trace_related R (κs1 ++ [κ1]) κs2 (κs3 ++ option_list κ1')
| ProdTraceRelR κ2 κ2' κs1 κs2 κs3:
    product_trace_related R κs1 κs2 κs3 →
    R None (Some κ2) κ2' →
    product_trace_related R κs1 (κs2 ++ [κ2]) (κs3 ++ option_list κ2')
| ProdTraceRelBoth κ1 κ2 κ3 κs1 κs2 κs3:
    product_trace_related R κs1 κs2 κs3 →
    R (Some κ1) (Some κ2) κ3 →
    product_trace_related R (κs1 ++ [κ1]) (κs2 ++ [κ2]) (κs3 ++ option_list κ3)
.
Lemma product_trace_related_step {EV1 EV2 EV3} (R : option EV1 → option EV2 → option EV3 → Prop) m1 m2 κs1 κs2 κs3 σ1 σ1' σ2 σ2':
  product_trace_related R κs1 κs2 κs3 →
  steps m1.(m_step) σ1 κs1 σ1' →
  steps m2.(m_step) σ2 κs2 σ2' →
  steps (module_product m1 m2 R).(m_step) (σ1, σ2) κs3 (σ1', σ2').
Proof.
  move => Hrel.
  elim: Hrel σ1' σ2'; clear.
  - move => σ1' σ2' Hstep1 Hstep2.
    apply: (steps_trans  _ _ _ _ [] []). by apply: product_empty_steps_l.
      by apply: product_empty_steps_r.
  - move => κ1 κ1' κs1 κs2 κs3 ? IH HR σ1' σ2' /(steps_app_inv _ _ _)[σ' [? /(steps_cons_inv _ _ _ _)[?[?[?[??]]]]]] ?.
    apply: steps_trans. by apply IH.
    apply: (steps_trans _ _ _ _ []). by apply: product_empty_steps_l.
    rewrite -/option_list.
    rewrite -(right_id_L [] (++) (option_list _)).
    apply: steps_trans. { apply: steps_option_list. by apply: MpStepL. }
    by apply: product_empty_steps_l.
  - move => κ2 κ2' κs1 κs2 κs3 ? IH HR σ1' σ2' ? /(steps_app_inv _ _ _)[σ' [? /(steps_cons_inv _ _ _ _)[?[?[?[??]]]]]].
    apply: steps_trans. by apply IH.
    apply: (steps_trans _ _ _ _ []). by apply: product_empty_steps_r.
    rewrite -/option_list.
    rewrite -(right_id_L [] (++) (option_list _)).
    apply: steps_trans. { apply: steps_option_list. by apply: MpStepR. }
    by apply: product_empty_steps_r.
  - move => κ1 κ2 κ3 κs1 κs2 κs3 ? IH HR σ1' σ2' /(steps_app_inv _ _ _)[σ' [? /(steps_cons_inv _ _ _ _)[?[?[?[??]]]]]] /(steps_app_inv _ _ _)[? [? /(steps_cons_inv _ _ _ _)[?[?[?[??]]]]]].
    apply: steps_trans. by apply IH.
    apply: (steps_trans _ _ _ _ []). by apply: product_empty_steps_r.
    apply: (steps_trans _ _ _ _ []). by apply: product_empty_steps_l.
    rewrite -/option_list.
    rewrite -(right_id_L [] (++) (option_list _)).
    apply: steps_trans. { apply: steps_option_list. by apply: MpStepBoth. }
    apply: (steps_trans _ _ _ _ []). by apply: product_empty_steps_l.
    by apply: product_empty_steps_r.
Qed.

Lemma product_trace_related_inv_l {EV1 EV2 EV3} (R : option EV1 → option EV2 → option EV3 → Prop) κs1 κs2 κs3 κs1':
  κs1' `prefix_of` κs1 →
  product_trace_related R κs1 κs2 κs3 →
  ∃ κs2' κs3', κs2' `prefix_of` κs2 ∧ κs3' `prefix_of` κs3 ∧
               product_trace_related R κs1' κs2' κs3'.
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

Lemma product_trace_related_inv_r {EV1 EV2 EV3} (R : option EV1 → option EV2 → option EV3 → Prop) κs1 κs2 κs3 κs2':
  κs2' `prefix_of` κs2 →
  product_trace_related R κs1 κs2 κs3 →
  ∃ κs1' κs3', κs1' `prefix_of` κs1 ∧ κs3' `prefix_of` κs3 ∧
               product_trace_related R κs1' κs2' κs3'.
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
  (∀ κs, LEM (∃ σf2, steps (m_step m2') (m_initial m2') κs σf2)) →
  refines m1 m1' →
  refines m2 m2' →
  refines (module_product m1 m2 R) (module_product m1' m2' R).
Proof.
  move => HLEM /refines_implies_wp' Hr1 /refines_implies_wp' Hr2.
  apply: wp'_implies_refines => n /=.
  move: (Hr1 n) (Hr2 n).
  have : (∃ σ, steps m1'.(m_step) m1'.(m_initial) [] σ). { eexists. by left. }
  have : (∃ σ, steps m2'.(m_step) m2'.(m_initial) [] σ). { eexists. by left. }
  move: (m1.(m_initial)) => σi1. move: (m2.(m_initial)) => σi2.
  have := (ProdTraceRelNil R).
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
      have [? [κs3' [[??] [[??]?]]]]:= product_trace_related_inv_l _ _ _ _ _ Hpre Hrel; subst.
      move: Hs2 => /(steps_app_inv _ _ _)[σ2 [??]].
      have []:= Hsafe (σs, σ2) κs3' => //.
      - apply prefix_app_r. by apply prefix_app_r.
      - by apply: product_trace_related_step.
    }
    have [|? _] := Hwp2 None => /=. {
      rewrite right_id.
      move => σs κ' Hpre Hsteps.
      have [? [κs3' [[??] [[??]?]]]]:= product_trace_related_inv_r _ _ _ _ _ Hpre Hrel; subst.
      move: Hs1 => /(steps_app_inv _ _ _)[σ2 [??]].
      have []:= Hsafe (σ2, σs) κs3' => //.
      - apply prefix_app_r. by apply prefix_app_r.
      - by apply: product_trace_related_step.
    }
    done.
  - move => [σi1' σi2'] n' ? Hstep. subst.
    inversion Hstep; clear Hstep; simplify_eq/=.
    + have {}Hrel : product_trace_related R (κs1 ++ option_list e1) κs2 (κs3 ++ option_list κ). {
        destruct e1; simplify_eq/=; [| by rewrite !right_id].
        by apply ProdTraceRelL.
      }
      have {Hwp1 Hwp2}[|_ Hwp1] := Hwp1 e1. {
        move => σs κ' Hpre Hsteps.
        have [? [κs3' [[??] [[? Heq]?]]]]:= product_trace_related_inv_l _ _ _ _ _ Hpre Hrel; subst.
        move: Hs2 => /(steps_app_inv _ _ _)[σ2 [??]].
        have []:= Hsafe (σs, σ2) κs3' => //.
        - rewrite Heq. by apply prefix_app_r.
        - by apply: product_trace_related_step.
      }
      have [|σs1' [Hsteps {}Hwp1]]:= Hwp1 _ n' _ H3 => //.
      exists (σs1', σs2).
      split.
      * by apply: product_trace_related_step.
      * apply: IH => //; try by eexists. lia. apply: wp'_weaken; [| done]. lia.
    + have {}Hrel : product_trace_related R κs1 (κs2 ++ option_list e2) (κs3 ++ option_list κ). {
        destruct e2; simplify_eq/=; [| by rewrite !right_id].
        by apply ProdTraceRelR.
      }
      have {Hwp1 Hwp2}[|_ Hwp] := Hwp2 e2. {
        move => σs κ' Hpre Hsteps.
        have [? [κs3' [[??] [[? Heq]?]]]]:= product_trace_related_inv_r _ _ _ _ _ Hpre Hrel; subst.
        move: Hs1 => /(steps_app_inv _ _ _)[σ2 [??]].
        have []:= Hsafe (σ2, σs) κs3' => //.
        - rewrite Heq. by apply prefix_app_r.
        - by apply: product_trace_related_step.
      }
      have [|σs' [Hsteps {}Hwp]]:= Hwp _ n' _ H3 => //.
      exists (σs1, σs').
      split.
      * by apply: product_trace_related_step.
      * apply: IH => //; try by eexists. lia. apply: wp'_weaken; [| done]. lia.
    + move: Hrel => Hrelold.
      have Hrel : product_trace_related R (κs1 ++ [e1]) (κs2 ++ [e2]) (κs3 ++ option_list κ). {
        by apply ProdTraceRelBoth.
      }
      have [[of2 Hfsteps]|Hnof2]:= HLEM (κs2 ++ [e2]).
      * have {Hwp1}[|_ Hwp1] := Hwp1 (Some e1). {
          move => σs κ' Hpre Hsteps.
          have [? [κs3' [[? Heq1] [[? Heq]?]]]]:= product_trace_related_inv_l _ _ _ _ _ Hpre Hrel; subst.
          rewrite Heq1 in Hfsteps.
          move: Hfsteps => /(steps_app_inv _ _ _)[σ2 [??]].
          have []:= Hsafe (σs, σ2) κs3' => //.
          - rewrite Heq. by apply prefix_app_r.
          - by apply: product_trace_related_step.
        }
        have [|/=σs1' [Hsteps1 {}Hwp1]]:= Hwp1 _ n' _ H4 => //.
        have {Hwp2}[|_ Hwp2] := Hwp2 (Some e2). {
          move => σs κ' Hpre Hsteps.
          have [? [κs3' [[? Heq1] [[? Heq]?]]]]:= product_trace_related_inv_r _ _ _ _ _ Hpre Hrel; subst.
          rewrite Heq1 in Hsteps1.
          move: Hsteps1 => /(steps_app_inv _ _ _)[σ2 [??]].
          have []:= Hsafe (σ2,σs) κs3' => //.
          - rewrite Heq. by apply prefix_app_r.
          - by apply: product_trace_related_step.
        }
        have [|σs2' [Hsteps2 {}Hwp2]]:= Hwp2 _ n' _ H5 => //.
        exists (σs1', σs2').
        split.
        -- by apply: product_trace_related_step.
        -- apply: IH => //; try by eexists. lia.
      * have {Hwp2}[|_ Hwp2] := Hwp2 (Some e2). {
          move => σs κ' [κend Hpre] Hsteps.
          have [?|[κ'' [κend' ?] ]]:= snoc_inv κend; subst.
          { rewrite right_id in Hpre. subst. naive_solver. }
          move: Hpre => /=. rewrite assoc. move => /(app_inj_tail _ _ _ _)[??]. subst.
          have [|? [κs3' [[? Heq1] [[? Heq]?]]]]:= product_trace_related_inv_r _ _ _ _ κ' _ Hrelold; subst.
          { by apply prefix_app_r. }
          move: Hs1 => /(steps_app_inv _ _ _)[σ2 [??]].
          have []:= Hsafe (σ2,σs) κs3' => //.
          - apply prefix_app_r. by apply prefix_app_r.
          - by apply: product_trace_related_step.
        }
        have [|σs2' [Hsteps2 {}Hwp2]]:= Hwp2 _ n' _ H5 => //.
        naive_solver.
Qed.

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
   return *y          return 1;        return 1;

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
  refines (module_product mod_call1 mod_call2 call_merge_rel) mod1.
Proof.
  apply: (inv_implies_refines (module_product mod_call1 mod_call2 call_merge_rel) mod1 call_merge_inv).
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
  refines mod1 (module_product mod_call1 mod_call2 call_merge_rel).
Proof.
  apply: (inv_implies_refines mod1 (module_product mod_call1 mod_call2 call_merge_rel) call_split_inv).
  - done.
  - done.
  - move => σi1 [σs1 σs2] σi2 e Hinv ? Hsafe. inv_step.
    exists (true, C2S3). split => //=.
    apply: (steps_None (true, C2S2 1)). 2: apply: steps_Some. 3: by left.
    + apply: MpStepBoth. 3: constructor.
      * constructor.
      * constructor.
    + apply: MpStepR. constructor => //. simpl. constructor.
Qed.

Lemma test_refines_call_merge_wp :
  refines (module_product mod_call1 mod_call2 call_merge_rel) mod1.
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
  refines mod1 (module_product mod_call1 mod_call2 call_merge_rel).
Proof.
  apply: (wp_implies_refines) => n.
  constructor => κ1 Hsafe1.
  split => // σi1 n' ? Hstep. subst.
  inv_step.
  exists (true, C2S3).
  split. {
    apply: steps_None.
    - apply: MpStepBoth. 3: constructor. all: constructor.
    - apply: steps_Some.
      + apply: MpStepR. constructor. simpl. constructor.
      + apply: steps_refl.
  }

  constructor => κ2 Hsafe2.
  split => // σi2 n ? Hstep. subst.
  inv_step.
Qed.
End test.
End version3.

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
  m1 + m2 : [module_product m1 m2]

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
