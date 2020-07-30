Require Import refframe.base.

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

(*
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
