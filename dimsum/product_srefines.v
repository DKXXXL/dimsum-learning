From dimsum.core Require Export proof_techniques.
From dimsum.core Require Import srefines filter product.
From dimsum.core Require Import axioms.

(** * srefines for product *)

Module product_example.

(*

              1     3
        /- 1 --- 2 --- 3
M1: 0 -∀
        \- 4 --- 5 --- 6
              2     4

                    1     Y
       X      /- 2 --- 3 --- 4
MA: 0 --- 1 -∃
              \- 5 --- 6 --- 7
                    2     Y

              X     Y     3
        /- 1 --- 2 --- 3 --- 4
MB: 0 -∀
        \- 5 --- 6 --- 7 --- 8
              X     Y     4

                          3
        X     Y     /- 3 --- 4
MB': 0 --- 1 --- 2 -∀
                    \- 5 --- 6
                          4

We have [M1 ⊑ prod MA MB] and [MB ⊑ MB'], but ¬ [M1 ⊑ prod MA MB'].
Thus we cannot have [prod MA MB ⊑ prod MA MB'].

To see that this is a realistic case, consider [M1 ⊑ prod MA MB] in two steps:
First we have [M1 ⊑ M1'] which introduces the demonic choice:


                      1     3
                /- 2 --- 3 --- 4
          /- 1 -∃
         /      \- 5 --- 6 --- 7
        /             2     3
M1': 0 -∀
        \             1     4
         \      /- 9 --- A --- B
          \- 8 -∃
                \- C --- D --- E
                      2     4

Written as programs, we have :

M1 : x ← angelic_choice({3, 4}); y ← if x = 3 then 1 else 2; output(y); output(x)
M1': x ← angelic_choice({3, 4}); y ← demonic_choice({1, 2}); output(y); output(x)

Now we want to split the demonic choice in M1' into a separate function:

f   := y ← demonic_choice({1, 2}); output(y)
M1'': x ← angelic_choice({3, 4}); f(); output(x)

If one now one wants to verify M1'' and f separately, it might seem that one can
commute the angelic choice over the call to f (which would just be an external
event). But this is not sound!

(If the angelic choice and demonic choice seems to abstract, one can think of the
angelic choice as a integer to pointer cast and the demonic choice as an allocation.)


Question: Should one be able to do the following optimization if integer to pointer
casts are defined via angelic choice?

Either if f is an unknown function call or a call to malloc or a call to a function
where we know that it does not do a non-deterministic choice?

int x = ...;
int *a = (int * )x;
//f();
int *y = malloc();
return y + *a;

-optimize to>

int x = ...;
//f();
int *y = malloc();
return y + *(int * )x;


For malloc, the commutation is probably invalid and thus also for the case of unknown
function. But is there a model where one can commute the angelic choice over the
external function call if one knows that it does not do demonic choices?
Maybe, but such a model might be quite complicated and it is not clear how much it is worth
to be able to do this commutation in this quite specific case (or it is not clear how common
the case where the commutation is sound is).

 *)

Inductive prod_mod1_step : nat → option nat → (nat → Prop) → Prop :=
| PM1S0: prod_mod1_step 0 None (λ σ', σ' = 1 ∨ σ' = 4)
| PM1S1: prod_mod1_step 1 (Some 1) (λ σ', σ' = 2)
| PM1S2: prod_mod1_step 2 (Some 3) (λ σ', σ' = 3)
| PM1S4: prod_mod1_step 4 (Some 2) (λ σ', σ' = 5)
| PM1S5: prod_mod1_step 5 (Some 4) (λ σ', σ' = 6)
.

Definition prod_mod1_trans : mod_trans nat := ModTrans prod_mod1_step.
Definition prod_mod1 : module nat := Mod prod_mod1_trans 0.

Inductive prod_modA_step : nat → option nat → (nat → Prop) → Prop :=
| PMAS0 : prod_modA_step 0 (Some 10) (λ σ', σ' = 1)
| PMAS11: prod_modA_step 1 None (λ σ', σ' = 2)
| PMAS12: prod_modA_step 1 None (λ σ', σ' = 5)
| PMAS2 : prod_modA_step 2 (Some 1) (λ σ', σ' = 3)
| PMAS3 : prod_modA_step 3 (Some 11) (λ σ', σ' = 4)
| PMAS5 : prod_modA_step 5 (Some 2) (λ σ', σ' = 6)
| PMAS6 : prod_modA_step 6 (Some 11) (λ σ', σ' = 7)
.

Definition prod_modA_trans : mod_trans nat := ModTrans prod_modA_step.
Definition prod_modA : module nat := Mod prod_modA_trans 0.

Inductive prod_modB_step : nat → option nat → (nat → Prop) → Prop :=
| PMBS0: prod_modB_step 0 None (λ σ', σ' = 1 ∨ σ' = 5)
| PMBS1: prod_modB_step 1 (Some 10) (λ σ', σ' = 2)
| PMBS2: prod_modB_step 2 (Some 11) (λ σ', σ' = 3)
| PMBS3: prod_modB_step 3 (Some 3) (λ σ', σ' = 4)
| PMBS5: prod_modB_step 5 (Some 10) (λ σ', σ' = 6)
| PMBS6: prod_modB_step 6 (Some 11) (λ σ', σ' = 7)
| PMBS7: prod_modB_step 7 (Some 4) (λ σ', σ' = 8)
.

Definition prod_modB_trans : mod_trans nat := ModTrans prod_modB_step.
Definition prod_modB : module nat := Mod prod_modB_trans 0.

Inductive prod_modB'_step : nat → option nat → (nat → Prop) → Prop :=
| PMB'S0: prod_modB'_step 0 (Some 10) (λ σ', σ' = 1)
| PMB'S1: prod_modB'_step 1 (Some 11) (λ σ', σ' = 2)
| PMB'S2: prod_modB'_step 2 None (λ σ', σ' = 3 ∨ σ' = 5)
| PMB'S3: prod_modB'_step 3 (Some 3) (λ σ', σ' = 4)
| PMB'S5: prod_modB'_step 5 (Some 4) (λ σ', σ' = 6)
.

Definition prod_modB'_trans : mod_trans nat := ModTrans prod_modB'_step.
Definition prod_modB' : module nat := Mod prod_modB'_trans 0.

Definition filterR (e1 : (option nat * option nat)) (e2 : option nat) : Prop :=
    (e1 = (Some 10, Some 10) ∧ e2 = None)
  ∨ (e1 = (Some 11, Some 11) ∧ e2 = None)
  ∨ (e1 = (Some 1, None) ∧ e2 = Some 1)
  ∨ (e1 = (Some 2, None) ∧ e2 = Some 2)
  ∨ (e1 = (None, Some 3) ∧ e2 = Some 3)
  ∨ (e1 = (None, Some 4) ∧ e2 = Some 4).
Arguments filterR _ _ /.
Definition prod_mod : module nat := filter_mod (product_mod prod_modA prod_modB) filterR.
Definition prod_mod' : module nat := filter_mod (product_mod prod_modA prod_modB') filterR.

Lemma prod_mod1_srefines_prod_mod:
  srefines prod_mod1 prod_mod.
Proof.
  constructor => Pκs /= Himpl.
  inversion Himpl; simplify_eq. 1: by apply: STraceEnd.
  inv_all @m_step.

  apply: STraceStep. { econstructor. { apply: ProductStepR. constructor. } done. } 2: done.
  move => [??] [?[?|?]]; simplify_eq.
  - have {}H := (H0 1 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: by apply: STraceEnd.
    inv_all @m_step => //. specialize_hyps.

    apply: STraceStep. { econstructor. { apply: ProductStepBoth; constructor. } naive_solver. }
    2: done. move => [??] [??]; simplify_eq/=.
    apply: STraceStep. { econstructor. { apply: ProductStepL. apply: PMAS11. } naive_solver. }
    2: done. move => [??] [??]; simplify_eq/=.
    apply: STraceStep. { econstructor. { apply: ProductStepL. constructor. } naive_solver. }
    2: done. move => [??] [??]; simplify_eq/=.
    apply: STraceStep. { econstructor. { apply: ProductStepBoth; constructor. } naive_solver. }
    2: naive_solver. move => [??] [??]; simplify_eq/=.

    inversion H3; simplify_eq. 1: by apply: STraceEnd.
    inv_all @m_step => //. specialize_hyps.
    apply: STraceStep. { econstructor. { apply: ProductStepR. constructor. } naive_solver. }
    2: naive_solver. move => [??] [??]; simplify_eq/=.
    inversion H5; simplify_eq. 1: by apply: STraceEnd.
    inv_all @m_step => //.
  - have {}H := (H0 4 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: by apply: STraceEnd.
    inv_all @m_step => //. specialize_hyps.

    apply: STraceStep. { econstructor. { apply: ProductStepBoth; constructor. } naive_solver. }
    2: done. move => [??] [??]; simplify_eq/=.
    apply: STraceStep. { econstructor. { apply: ProductStepL. apply: PMAS12. } naive_solver. }
    2: done. move => [??] [??]; simplify_eq/=.
    apply: STraceStep. { econstructor. { apply: ProductStepL. constructor. } naive_solver. }
    2: done. move => [??] [??]; simplify_eq/=.
    apply: STraceStep. { econstructor. { apply: ProductStepBoth; constructor. } naive_solver. }
    2: naive_solver. move => [??] [??]; simplify_eq/=.

    inversion H3; simplify_eq. 1: by apply: STraceEnd.
    inv_all @m_step => //. specialize_hyps.
    apply: STraceStep. { econstructor. { apply: ProductStepR. constructor. } naive_solver. }
    2: naive_solver. move => [??] [??]; simplify_eq/=.
    inversion H5; simplify_eq. 1: by apply: STraceEnd.
    inv_all @m_step => //.
Qed.

Lemma prod_mod1_not_refines_prod_mod':
  ¬ srefines prod_mod1 prod_mod'.
Proof.
  move => [/=Hr].
  feed pose proof (Hr (λ κs, κs = [] ∨ κs = [Vis 1] ∨ κs = [Vis 1; Vis 3] ∨ κs = [Vis 1; Vis 3; Nb] ∨
                             κs = [Vis 2] ∨ κs = [Vis 2; Vis 4] ∨ κs = [Vis 2; Vis 4; Nb])) as Hr'.
  - apply: STraceStep. { constructor. } 2: naive_solver.
    move => /= ? [?|?]; simplify_eq.
    + apply: STraceStep. { constructor. } 2: naive_solver.
      move => /= ??; simplify_eq.
      apply: STraceStep. { constructor. } 2: naive_solver.
      move => /= ??; simplify_eq.
      apply: STraceEnd; [done|]. naive_solver.
    + apply: STraceStep. { constructor. } 2: naive_solver.
      move => /= ??; simplify_eq.
      apply: STraceStep. { constructor. } 2: naive_solver.
      move => /= ??; simplify_eq.
      apply: STraceEnd; [done|]. naive_solver.
  - inversion Hr'; simplify_eq. 1: naive_solver.
    inv_all @m_step. 1,2: naive_solver.
    have ? : κ = None by naive_solver. subst κ. clear H3 H1 Hr Hr'.
    have {}H := (H0 (_, _) ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    inv_all @m_step => //. 3: naive_solver.
    (* This should work by passing the opposite of the demonic choice
    to the angelic choice but has many case distinctions *)
Abort.
End product_example.

(** The following section contains some proof ideas for proving that
product respects srefines, but they are all doomed to fail because it
does not hold. *)
Module failed_product_proof_attempts.
Inductive mod_product_rel1 {EV1 EV2} (m2 : mod_trans EV2) : list (event EV1) → m2.(m_state) → list (event (option EV1 * option EV2)) → Prop :=
|MPR1_nil σ:
   mod_product_rel1 m2 [] σ []
|MPR1_nb σ:
   mod_product_rel1 m2 [Nb] σ [Nb]
.

Lemma mod_product_to_mod_1 {EV1 EV2} (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ Pσ Pκs:
  σ ~{ product_trans m1 m2, Pκs }~>ₛ Pσ →
  σ.1 ~{ m1, λ κs, ∃ κs', mod_product_rel1 m2 κs σ.2 κs' ∧ Pκs κs' }~>ₛ (λ _, True).
Proof.
  elim.
  - move => ????[??]. apply: STraceEnd; [done|]. split; eexists _; (split; [constructor|done]).
  - move => [??]???? Hstep ? IH [He1 He2].
    inversion Hstep; simplify_eq.
    + apply: STraceStep; [done| |].
      * move => ??. apply: shas_trace_mono; [ by apply: (IH (_, _)) | |done].
        move => /=? [?[??]]. eexists _. split; [|done]. destruct e => //=.
        shelve.
      * split; eexists _; split; [| apply: He1 | | apply: He2] => /=.
        -- constructor.
        -- shelve.
    + apply: shas_trace_mono; [ apply: (IH (_, _)) | |done].
Abort.


Inductive mod_product_rel2 {EV1 EV2} : ((list (event (option EV1 * option EV2))) → Prop) → (list (event EV1) → Prop) → (list (event EV2) → Prop) → Prop :=.
(*
| MPR_nil κs :
    tnil ⊆ κs →
    mod_product_rel κs tnil tnil
| MPR_ex1 T f κs κs2 :
    (∀ x, mod_product_rel κs (f x) κs2) →
    mod_product_rel κs (tex T f) κs2
| MPR_ex2 T f κs κs2 :
    (∀ x, mod_product_rel κs κs2 (f x)) →
    mod_product_rel κs κs2 (tex T f)
| MPR_all1 {T} x f κs κs2 F :
    mod_product_rel κs (f x) κs2 →
    mod_product_rel κs (tall T F f) κs2
| MPR_all2 {T} x f κs κs2 F :
    mod_product_rel κs κs2 (f x) →
    mod_product_rel κs κs2 (tall T F f)
| MPR_all T f κs κs1 κs2 F:
    (∀ x, mod_product_rel (f x) κs1 κs2) →
    (tall T F f) ⊆ κs →
    mod_product_rel κs κs1 κs2
| MPR_cons_l κ κs κs' κs1' κs2 :
    mod_product_rel κs' κs1' κs2 →
    tcons (Some κ, None) κs' ⊆ κs →
    mod_product_rel κs (tcons κ κs1') κs2
| MPR_cons_r κ κs κs' κs1 κs2' :
    mod_product_rel κs' κs1 κs2' →
    tcons (None, Some κ) κs' ⊆ κs →
    mod_product_rel κs κs1 (tcons κ κs2')
| MPR_cons_both κ1 κ2 κs κs' κs1' κs2' :
    mod_product_rel κs' κs1' κs2' →
    tcons (Some κ1, Some κ2) κs' ⊆ κs →
    mod_product_rel κs (tcons κ1 κs1') (tcons κ2 κs2')
.
*)

Lemma mod_product_to_mods {EV1 EV2} (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ Pσ κs:
  σ ~{ product_trans m1 m2, κs }~>ₛ Pσ → ∃ κs', mod_product_rel2 κs κs'.1 κs'.2 ∧
    σ.1 ~{ m1, κs'.1 }~>ₛ (λ _, True) ∧ σ.2 ~{ m2, κs'.2 }~>ₛ (λ _, True).
Proof.
  elim.
  - move => [σ1 σ2] ????. eexists (_, _) => /=.
    split_and!.
    + shelve.
    + apply: STraceEnd; [done| ]. shelve.
    + apply: STraceEnd; [done| ]. shelve.
  - move => [σ1 σ2] ???? Hstep _ IH [??].
    inversion Hstep; simplify_eq.
    + have {}IH := IH (_, σ2) (conj _ ltac:(exact (eq_refl σ2))).
      have {IH}[f Hf]:= AxChoice1 IH.
      eexists (
          (λ κs, κs = [] ∨ κs = option_list (Vis <$> e) ∨ ∃ κs', κs = (option_list (Vis <$> e)) ++ κs' ∧ ∃ x, (f x).1 κs')
          , (λ κs, ∀ x, (f x).2 κs)) => /=.
      split_and!.
      * shelve.
      * apply: STraceStep; [done| |naive_solver]. move => ??.
        apply: shas_trace_mono; [naive_solver| |done] => /=.
        move => ??. naive_solver.
      * have [[[??]?]|?]:= AxClassic (∃ x, ∀ κs, (f x).2 κs → ∀ x', (f x').2 κs).
        -- apply: shas_trace_mono; [naive_solver| |done] => /=. done.
        -- apply: STraceEnd. done.
           split. shelve.
           move => [??].
Abort.
End failed_product_proof_attempts.
