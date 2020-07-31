Require Import refframe.base.
Require Import stdpp.namespaces.
Require Import stdpp.strings.

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
    steps R ρ1 (if κ is Some κ' then κ' :: κs else κs) ρ3.

Record event := {
  e_name: namespace;
  e_type: Type;
  e_data: e_type;
}.

Definition thread_id := positive.

Record module := {
  m_state : Type;
  (* multiple initial states can be modeled by non-deterministically
  branching from the initial state *)
  m_initial : m_state;
  m_in : m_state → thread_id → event → m_state → Prop;
  m_step : m_state → thread_id → option event → m_state → Prop;
  m_is_blocked : m_state → thread_id → Prop;
}.

Inductive module_step (m : module) : m.(m_state) → option (thread_id * (event + event)) → m.(m_state) → Prop :=
| MSStep σ1 tid e σ2:
    m.(m_step) σ1 tid e σ2 →
    module_step m σ1 ((λ e, (tid, inr e)) <$> e) σ2
| MSIn σ1 tid e σ2:
    m.(m_in) σ1 tid e σ2 →
    (* TODO should we have the following here?
    m.(m_is_blocked) σ1 tid →
     *)
    module_step m σ1 (Some (tid, inl e)) σ2.

Definition can_step (m : module) (σ : m.(m_state)) (tid : thread_id) : Prop :=
  ∃ e σ2, m.(m_step) σ tid e σ2.

Definition safe_state (m : module) (σ : m.(m_state)) : Prop :=
  ∀ tid, m.(m_is_blocked) σ tid ∨ can_step m σ tid.

Definition safe (m : module) : Prop :=
  ∀ κ σ', steps (module_step m) m.(m_initial) κ σ' → safe_state m σ'.

Record refines (mimpl mspec : module) := {
  (* ref_in σ tid e σs: *)
    (* mspec.(m_in) (ti σ) tid e σs → *)
    (* ∃ σi, mimpl.(m_in) σ tid e σi; *)
  ref_step κ σi:
    steps (module_step mimpl) mimpl.(m_initial) κ σi →
    (∀ σs κ', κ' `prefix_of` κ → steps (module_step mspec) mspec.(m_initial) κ' σs → safe_state mspec σs) →
    safe_state mimpl σi ∧ ∃ σs, steps (module_step mspec) mspec.(m_initial) κ σs;
}.

Lemma refines_preserves_safe mspec mimpl:
  safe mspec →
  refines mimpl mspec →
  safe mimpl.
Proof.
  move => Hs Hr κ σ' Hstep tid.
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


(*** Proving refinement *)
Lemma inv_implies_refines m1 m2 (inv : m1.(m_state) → m2.(m_state) → Prop):
  (* (∀ σ tid e σs, m_in m2 (ti σ) tid e σs → ∃ σi : m_state m1, m_in m1 σ tid e σi) → *)
  inv m1.(m_initial) m2.(m_initial) →
  (∀ σi σs, inv σi σs → safe_state m1 σi) →
  (∀ σi1 σs1 σi2 e,
      inv σi1 σs1 → module_step m1 σi1 e σi2 →
      (∀ σs κ', κ' `prefix_of` (option_list e) → steps (module_step m2) σs1 κ' σs → safe_state m2 σs ) →
      ∃ σs2, inv σi2 σs2 ∧ (module_step m2 σs1 e σs2 ∨ (e = None ∧ σs1 = σs2))) →
  refines m1 m2.
Proof.
  move => Hinvinit Hinvsafe Hinvstep.
  constructor => // κ σi2. move: m1.(m_initial) m2.(m_initial) Hinvinit => σi1 σs1 Hinv Hsteps Hspec.
  elim: Hsteps σs1 Hinv Hspec => {σi1 κ σi2}.
  - by eauto using steps_refl.
  - move => σi1 σi2 σi3 κ κs Hstep Hsteps IH σs1 Hinv Hspec.
    case: (Hinvstep _ _ _ _ Hinv Hstep).
    { move => ???. apply: Hspec. etrans; first done. case_match; [apply prefix_cons|]; apply prefix_nil. }
    move => σs2 [Hinv2 [Hsstep|[??]]]; subst; case: (IH _ Hinv2) => //.
    + move => σs κ' Hprefix Hs. apply: Hspec. 2: by apply: steps_l. case_match => //. by apply prefix_cons.
    + move => Hsafe [σs3 Hs]. split => //. eexists. by apply: steps_l.
Qed.

(*** Tests *)
Module test.
Definition nat_event (n : nat) : event := {|
  e_name := nroot.@"test";
  e_type := nat;
  e_data := n;
|}.
Inductive mod1_step : bool → thread_id → option event → bool → Prop :=
| T1False tid: mod1_step false tid (Some (nat_event 1)) true.


Definition mod1 : module := {|
  m_state := bool;
  m_initial := false;
  m_in _ _ _ _:= False;
  m_step := mod1_step;
  m_is_blocked s _:= s = true;
|}.

Inductive mod2_state := | S1 | S2 | S3.
Inductive mod2_step : mod2_state → thread_id → option event → mod2_state → Prop :=
| T2S1 tid: mod2_step S1 tid None S2
| T2S2 tid: mod2_step S2 tid (Some (nat_event 1)) S3.
Definition mod2 : module := {|
  m_state := mod2_state;
  m_initial := S1;
  m_in _ _ _ _:= False;
  m_step := mod2_step;
  m_is_blocked s _:= s = S3;
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
  - move => [] ??; [right| right|left] => //; eexists _, _; constructor.
  - move => σi1 σs1 σi2 e ->. inversion_clear 1 => //. revert select (m_step mod2 _ _ _ _) => /=.
    destruct 1 => _; eexists _; split => //.
    + by right.
    + left. constructor. constructor.
Qed.

Definition mod_loop : module := {|
  m_state := unit;
  m_initial := tt;
  m_in _ _ _ _ := False;
  m_step _ _ e _ := e = None;
  m_is_blocked s _:= False;
|}.
Lemma test_refines2 m :
  refines mod_loop m.
Proof.
  apply: (inv_implies_refines mod_loop m (λ _ _, True)).
  - done.
  - move => ???. right. eexists _, tt. constructor.
  - move => ?????. inversion_clear 1 => //. revert select (m_step mod_loop _ _ _ _) => /=.
    move => ->. eauto.
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
  m_initial := S1S1;
  m_in _ _ _ _:= False;
  m_step := stuck1_step;
  m_is_blocked s _:= s = S1S2;
|}.

Lemma test_refines_stuck1 :
  refines mod_stuck1 mod_stuck1.
Proof.
  apply: (inv_implies_refines mod_stuck1 mod_stuck1 (λ σ1 σ2, σ1 = σ2 ∧ σ1 ≠ S1S3)).
  - done.
  - move => [] ?[??]; try by [left]; right; eexists _, _; constructor.
  - move => σi1 σs1 σi2 e [-> ?]. inversion_clear 1 => //. revert select (m_step _ _ _ _ _) => /=.
    destruct 1 => Hsafe.
    + (* 1 -> 2 *) eexists _. split => //. left. constructor. constructor.
    + (* 1 -> 3 *) exfalso.
      have [|||[?[? Hstep]]]:= (Hsafe S1S3 [(tid, inr (nat_event 2))] _ _ tid) => //.
      { apply: (steps_l _ _ _ _ (Some (tid, inr (nat_event 2)))). 2: constructor. apply: (MSStep _ _ _ (Some (nat_event 2))). econstructor. }
      inversion Hstep.
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
  m_initial := S2S1;
  m_in _ _ _ _:= False;
  m_step := stuck2_step;
  m_is_blocked s _:= s = S2S2;
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
  - move => [] ?[??]; try by [left]; right; eexists _, _; constructor.
  - move => σi1 σs1 σi2 e [? ->]. inversion_clear 1 => //. revert select (m_step _ _ _ _ _) => /=.
    destruct 1 => Hsafe.
    + (* 1 -> 2 *) eexists _. split => //. left. constructor. constructor.
    + (* 1 -> 3 *) eexists _. split => //. left. constructor. constructor.
    + (* 3 -> 4 *) exfalso.
      have [|||[?[? Hstep]]]:= (Hsafe S1S3 [] _ _ tid) => //.
      * apply prefix_nil.
      * econstructor.
      * inversion Hstep.
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
  m_initial := S3S1;
  m_in _ _ _ _:= False;
  m_step := stuck3_step;
  m_is_blocked s _:= s = S3S4;
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
  - move => [] ?[??]; try by [left]; right; eexists _, _; constructor.
  - move => σi1 σs1 σi2 e [? ->]. inversion_clear 1 => //. revert select (m_step _ _ _ _ _) => /=.
    destruct 1 => Hsafe.
    + (* 1 -> 2 *) eexists _. split => //. left. constructor. constructor.
    + (* 1 -> 3 *) exfalso.
      have [|||[?[? Hstep]]]:= (Hsafe S1S3 [(tid, inr (nat_event 2))] _ _ tid) => //.
      { apply: (steps_l _ _ _ _ (Some (tid, inr (nat_event 2)))). 2: constructor. apply: (MSStep _ _ _ (Some (nat_event 2))). econstructor. }
      inversion Hstep.
    + (* 2 -> 4 *) eexists _. split => //. left. constructor.
      (* Not provable! *)
Abort.

End test.
End version2.

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
