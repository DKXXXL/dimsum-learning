Require Import refframe.base.

Inductive steps {A B} (R : A → list B → A → Prop) : A → list (list B) → A → Prop :=
| steps_refl ρ :
    steps R ρ [] ρ
| steps_l ρ1 ρ2 ρ3 κ κs :
    R ρ1 κ ρ2 →
    steps R ρ2 κs ρ3 →
    steps R ρ1 (κ :: κs) ρ3.

Record module := {
  m_state : Type;
  m_event : Type;
  m_initial : m_state → Prop;
  m_step : m_state → list m_event → m_state → Prop;
  (* This cannot be defined based on m_step since m_state might e.g. contain a threadpool
     and a state should be bad if any thread is stuck. *)
  m_good : m_state → Prop;
}.

Definition safe (m : module) : Prop :=
  ∀ σ κ σ', m.(m_initial) σ → steps m.(m_step) σ κ σ' → m.(m_good) σ'.

Record refines (mimpl mspec : module) (trans_initial : mimpl.(m_state) → mspec.(m_state)) (trans_event : list mimpl.(m_event) → list mspec.(m_event)) := {
  ref_initial σ : mimpl.(m_initial) σ → mspec.(m_initial) (trans_initial σ);
  ref_step σ κ σi:
    mimpl.(m_initial) σ →
    steps mimpl.(m_step) σ κ σi →
    (∀ σs, steps mspec.(m_step) (trans_initial σ) (trans_event <$> κ) σs → mspec.(m_good) σs) →
    mimpl.(m_good) σi ∧ ∃ σs, steps mspec.(m_step) (trans_initial σ) (trans_event <$> κ) σs;
}.

Lemma refines_preserves_safe mspec mimpl ti te:
  safe mspec →
  refines mimpl mspec ti te →
  safe mimpl.
Proof.
  move => Hs Hr σ κ σ' Hinit Hstep.
  have [|]:= (ref_step _ _ _ _ Hr _ _ _ Hinit Hstep) => //.
  move => σs Hsteps. apply: Hs => //.
  by apply: ref_initial.
Qed.

Lemma refines_reflexive m:
  refines m m id id.
Proof. constructor => // σ κ σi Hi Hs. rewrite list_fmap_id. naive_solver. Qed.

Lemma refines_vertical m1 m2 m3 ti1 te1 ti2 te2:
  refines m1 m2 ti1 te1 →
  refines m2 m3 ti2 te2 →
  refines m1 m3 (ti2 ∘ ti1) (te2 ∘ te1).
Proof.
  move => Hr1 Hr2.
  constructor; first by destruct Hr1, Hr2; eauto.
  move => σ κ σi Hinit1 Hstep1 /=. rewrite list_fmap_compose => Hsafe3.
  have [|Hgood [σ2 Hstep2]] := (ref_step _ _ _ _ Hr1 _ _ _ Hinit1 Hstep1). {
    move => σs2 Hstep2.
    by have [||? _] := (ref_step _ _ _ _ Hr2 _ _ _ _ Hstep2); eauto using ref_initial.
  }
  split => //.
  have [||_ [σ3 Hstep3]] := (ref_step _ _ _ _ Hr2 _ _ _ _ Hstep2); eauto using ref_initial.
Qed.

Inductive module_product_step (m1 m2 : module) : m1.(m_state) * m2.(m_state) → list (m1.(m_event) + m2.(m_event)) → m1.(m_state) * m2.(m_state) → Prop :=
| ModuleStepBoth σ1 σ2 κs1 κs2 σ1' σ2' :
    m1.(m_step) σ1 κs1 σ1' →
    m2.(m_step) σ2 κs2 σ2' →
    module_product_step m1 m2 (σ1, σ2) ((inl <$> κs1) ++ (inr <$> κs2)) (σ1', σ2)
| ModuleStepLeft σ1 σ2 κs σ1' :
    m1.(m_step) σ1 κs σ1' →
    module_product_step m1 m2 (σ1, σ2) (inl <$> κs) (σ1', σ2)
| ModuleStepRight σ1 σ2 κs σ2' :
    m2.(m_step) σ2 κs σ2' →
    module_product_step m1 m2 (σ1, σ2) (inr <$> κs) (σ1, σ2')
.

Definition module_product (m1 m2 : module) : module := {|
  m_state := m1.(m_state) * m2.(m_state);
  m_event := m1.(m_event) + m2.(m_event);
  m_initial σ := m1.(m_initial) σ.1 ∧ m2.(m_initial) σ.2;
  m_step := module_product_step m1 m2;
  m_good σ := m1.(m_good) σ.1 ∧ m2.(m_good) σ.2;
|}.






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

  Spec 1:                      Spec 2:
                               (no main)
   main: let x := Call A;       A: return 1
         Emit (Res x)

  Impl 1 High:                                    Memory High:

   main: int* x = alloc_int;                      No offset operation on locations,
         Call A x;                                Memory layout is hidden (i.e. integers are stored aso
         Emit (Res *x)                            mathematical integers, constraint that all integers on the
                                                  heap are 0 ≤ n < 2 ^ 32

  Impl 1 Low:                  Impl 2 Low:        Memory Low:

   main: int* x = alloc_int;   A p: *(p + 0) = 1; Flat memory model which stores bytes
         Call A x;                  *(p + 1) = 0;
         Emit (Res load_int(x))     *(p + 2) = 0;
                                    *(p + 3) = 0;

  Low level code (i.e. code with inline assembly)
   main: int* x = alloc_int;     Flat memory model which stores bytes
         *(x + 0) = 1;
         *(x + 1) = 0;
         *(x + 1) = 0;
         *(x + 1) = 0;
         Emit (Res load_int(x))


 Proofs:

  m1 < m2 : [refines m1 m2]
  m1 + m2 : [module_product m1 m2]

  1: LLC < Impl 1 Low + Memory Low + Impl 2

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
