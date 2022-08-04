From dimsum.core Require Export proof_techniques.
From dimsum.core Require Import srefines filter.
From dimsum.core Require Import axioms.

(** * product *)
Inductive product_step {EV1 EV2} (m1 : mod_trans EV1) (m2 : mod_trans EV2) :
  (m1.(m_state) * m2.(m_state)) → option (option EV1 * option EV2) → ((m1.(m_state) * m2.(m_state)) → Prop) → Prop :=
| ProductStepL e σ1 σ2 Pσ:
    m1.(m_step) σ1 e Pσ →
    product_step m1 m2 (σ1, σ2)
                 (if e is Some e' then Some (Some e', None) else None)
                 (λ '(σ1', σ2'), Pσ σ1' ∧ σ2 = σ2')
| ProductStepR e σ1 σ2 Pσ:
    m2.(m_step) σ2 e Pσ →
    product_step m1 m2 (σ1, σ2)
                 (if e is Some e' then Some (None, Some e') else None)
                 (λ '(σ1', σ2'), σ1 = σ1' ∧ Pσ σ2')
| ProductStepBoth e1 e2 σ1 σ2 Pσ1 Pσ2:
    m1.(m_step) σ1 (Some e1) Pσ1 →
    m2.(m_step) σ2 (Some e2) Pσ2 →
    product_step m1 m2 (σ1, σ2)
                 (Some (Some e1, Some e2))
                 (λ '(σ1', σ2'), Pσ1 σ1' ∧ Pσ2 σ2')
.
Arguments ProductStepL {_ _ _ _} _ _ _ _ _.
Arguments ProductStepR {_ _ _ _} _ _ _ _ _.
Arguments ProductStepBoth {_ _ _ _} _ _ _ _ _.

Definition product_trans {EV1 EV2} (m1 : mod_trans EV1) (m2 : mod_trans EV2)
  : mod_trans (option EV1 * option EV2) :=
  ModTrans (product_step m1 m2).

Global Instance product_vis_no_all {EV1 EV2} (m1 : mod_trans EV1) (m2 : mod_trans EV2) `{!VisNoAng m1} `{!VisNoAng m2}:
  VisNoAng (product_trans m1 m2).
Proof.
  move => [??]???. inv_all @m_step; try case_match => //; simplify_eq.
  - have [??]:= vis_no_all _ _ _ ltac:(done). eexists (_, _) => -[??]. naive_solver.
  - have [??]:= vis_no_all _ _ _ ltac:(done). eexists (_, _) => -[??]. naive_solver.
  - have [??]:= vis_no_all _ _ _ ltac:(done). clear H4.
    have [??]:= vis_no_all _ _ _ ltac:(done).
    eexists (_, _) => -[??]. naive_solver.
Qed.

Definition product_mod {EV1 EV2} (m1 : module EV1) (m2 : module EV2) :=
  Mod (product_trans m1.(m_trans) m2.(m_trans)) (m1.(m_init), m2.(m_init)).

(** ** trefines for [product] *)
Inductive mod_product_rel {EV1 EV2} : trace (option EV1 * option EV2) → trace EV1 → trace EV2 → Prop :=
| MPR_nil κs :
    tnil ⊆ κs →
    mod_product_rel κs tnil tnil
| MPR_ex1 T f κs κs2 :
    (∀ x, mod_product_rel κs (f x) κs2) →
    mod_product_rel κs (tex T f) κs2
| MPR_ex2 T f κs κs2 :
    (∀ x, mod_product_rel κs κs2 (f x)) →
    mod_product_rel κs κs2 (tex T f)
| MPR_all1 {T} x f κs κs2 :
    mod_product_rel κs (f x) κs2 →
    mod_product_rel κs (tall T f) κs2
| MPR_all2 {T} x f κs κs2 :
    mod_product_rel κs κs2 (f x) →
    mod_product_rel κs κs2 (tall T f)
| MPR_all T f κs κs1 κs2:
    (∀ x, mod_product_rel (f x) κs1 κs2) →
    (tall T f) ⊆ κs →
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


Lemma mod_product_rel_mono {EV1 EV2} κs κs' (κs1 : trace EV1) (κs2 : trace EV2) :
  mod_product_rel κs κs1 κs2 →
  κs ⊆ κs' →
  mod_product_rel κs' κs1 κs2.
Proof.
  move => Ht.
  elim: Ht κs'.
  - move => ????. constructor. by etrans.
  - move => *. constructor. naive_solver.
  - move => *. constructor. naive_solver.
  - move => *. econstructor. naive_solver.
  - move => *. econstructor; naive_solver.
  - move => *. eapply MPR_all. 2: by etrans. naive_solver.
  - move => ????? ?? IH ??.
    apply: MPR_cons_l; [| by etrans]. naive_solver.
  - move => ????? ?? IH ??.
    apply: MPR_cons_r; [| by etrans]. naive_solver.
  - move => *.
    apply: MPR_cons_both; [| by etrans]. naive_solver.
Qed.


Lemma tmod_product_to_mods {EV1 EV2} (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ Pσ κs:
  σ ~{ product_trans m1 m2, κs }~>ₜ Pσ → ∃ κs', mod_product_rel κs κs'.1 κs'.2 ∧
    σ.1 ~{ m1, κs'.1 }~>ₜ - ∧ σ.2 ~{ m2, κs'.2 }~>ₜ -.
Proof.
  elim.
  - move => [σ1 σ2] ????. eexists (tnil, tnil) => /=.
    split_and!.
    + apply: mod_product_rel_mono; [|done]. by constructor.
    + by constructor.
    + by constructor.
  - move => [σ1 σ2] ????? Hstep _ IH ?.
    inversion Hstep; simplify_eq.
    + have {}IH := IH (_, σ2) (conj _ ltac:(exact (eq_refl σ2))).
      have [f Hf]:= AxChoice1 IH.
      unshelve eexists (tapp (option_trace e) (tex _ (λ x, (f x).1)), (tall _ (λ x, (f x).2))) => /=.
      split_and!.
      -- apply: mod_product_rel_mono; [|done].
         destruct e => //=.
         ++ apply: MPR_cons_l; [|done].
            constructor => -[??]. econstructor.
            naive_solver.
         ++ constructor => -[??]. econstructor. naive_solver.
      -- apply: TTraceStep; [ done | | done].
         move => σ' Hσ'. apply: (thas_trace_ex (exist _ σ' Hσ')).
         apply: thas_trace_mono. naive_solver. done. naive_solver.
      -- apply: thas_trace_all => -[??].
         apply: thas_trace_mono. naive_solver. done. naive_solver.
    + have {}IH := IH (σ1, _) (conj ltac:(exact (eq_refl σ1)) _).
      have [f Hf]:= AxChoice1 IH.
      unshelve eexists ((tall _ (λ x, (f x).1)), tapp (option_trace e) (tex _ (λ x, (f x).2))) => /=.
      split_and!.
      -- apply: mod_product_rel_mono; [|done].
         destruct e => //=.
         ++ apply: MPR_cons_r; [|done].
            constructor => -[??]. econstructor.
            naive_solver.
         ++ constructor => -[??]. econstructor. naive_solver.
      -- apply: thas_trace_all => -[??].
         apply: thas_trace_mono. naive_solver. done. naive_solver.
      -- apply: TTraceStep; [ done | | done].
         move => σ' Hσ'. apply: (thas_trace_ex (exist _ σ' Hσ')).
         apply: thas_trace_mono. naive_solver. done. naive_solver.
    + have {}IH := IH (_, _) (conj _ _).
      have [f Hf]:= AxChoice2 IH.
      unshelve eexists (tcons e1 (tex _ (λ x1, (tall _ (λ x2, (f x1 x2).1)))),
                        tcons e2 (tex _ (λ x2, (tall _ (λ x1, (f x1 x2).2))))) => /=.
      split_and!.
      -- apply: mod_product_rel_mono; [|done]. simpl.
         econstructor; [|done..].
         constructor => -[??].
         constructor => -[??].
         econstructor.
         econstructor. naive_solver.
      -- apply: TTraceStep; [ done | | simpl; done].
         move => ??.
         apply: thas_trace_ex. apply: thas_trace_all => -[??]. naive_solver.
      -- apply: TTraceStep; [ done | | simpl; done].
         move => ??.
         apply: thas_trace_ex. apply: thas_trace_all => -[??]. naive_solver.
  - move => T f ???? IH ?.
    have [fx Hfx]:= AxChoice _ _ _ IH.
    eexists (tall T (λ x, (fx x).1), tall T (λ x, (fx x).2)) => /=.
    split_and! => //.
    -- apply: mod_product_rel_mono; [|done].
       eapply MPR_all; [|done] => ?.
       econstructor. econstructor. naive_solver.
    -- apply: thas_trace_all. naive_solver.
    -- apply: thas_trace_all. naive_solver.
       Unshelve. done. done.
Qed.

Lemma mod_product_nil_l {EV1 EV2} (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2 Pσ κs:
  σ1 ~{ m1, κs }~>ₜ Pσ → κs ⊆ tnil →
  (σ1, σ2) ~{ product_trans m1 m2, tnil }~>ₜ (λ σ', Pσ σ'.1 ∧ σ2 = σ'.2).
Proof.
  elim.
  - move => ??????. constructor; [|done]. naive_solver.
  - move => ??? κ ????? Hs1 Hs2.
    pose proof (transitivity Hs1 Hs2) as Hs.
    destruct κ; [inversion Hs|]; simplify_eq/=.
    apply: TTraceStep; [ by apply: ProductStepL | | simpl;done].
    move => [??] /=. naive_solver.
  - move => ??????? Hs1 Hs2.
    pose proof (transitivity Hs1 Hs2) as [??]%subtrace_all_nil_inv. naive_solver.
Qed.

Lemma mod_product_nil_r {EV1 EV2} (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2 Pσ κs:
  σ2 ~{ m2, κs }~>ₜ Pσ → κs ⊆ tnil →
  (σ1, σ2) ~{ product_trans m1 m2, tnil }~>ₜ (λ σ', Pσ σ'.2 ∧ σ1 = σ'.1).
Proof.
  elim.
  - move => ??????. constructor; [|done]. naive_solver.
  - move => ??? κ ????? Hs1 Hs2.
    pose proof (transitivity Hs1 Hs2) as Hs.
    destruct κ; [inversion Hs|]; simplify_eq/=.
    apply: TTraceStep; [ by apply: ProductStepR | | simpl;done].
    move => [??] /=. naive_solver.
  - move => ??????? Hs1 Hs2.
    pose proof (transitivity Hs1 Hs2) as [??]%subtrace_all_nil_inv. naive_solver.
Qed.

Lemma tmods_to_mod_product {EV1 EV2} (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ κs κs1 κs2:
  mod_product_rel κs κs1 κs2 →
  σ.1 ~{ m1, κs1 }~>ₜ - → σ.2 ~{ m2, κs2 }~>ₜ - →
  σ ~{ product_trans m1 m2, κs }~>ₜ -.
Proof.
  move => Hrel.
  elim: Hrel σ.
  - move => ?????. by constructor.
  - move => ????? /= IH [??] /thas_trace_ex_inv ??.
    apply: (thas_trace_trans tnil). { by apply: mod_product_nil_l. }
    move => [??] /= [[??]?]. naive_solver.
  - move => ????? IH [??] ? /thas_trace_ex_inv ?.
    apply: (thas_trace_trans tnil). { by apply: mod_product_nil_r. }
    move => [??] /= [[??]?]. naive_solver.
  - move => ?????? IH ? /thas_trace_all_inv ??. apply: IH; [|done]. naive_solver.
  - move => ?????? IH ?? /thas_trace_all_inv ?. apply: IH; [done|]. naive_solver.
  - move => ?????? IH ????.
    apply: thas_trace_mono; [|done| done].
    apply: thas_trace_all => ?. naive_solver.
  - move => ?????? IH ? [??]/= /(thas_trace_cons_inv _ _) ??.
    apply: thas_trace_mono; [|done| done].
    apply: (thas_trace_trans tnil). { by apply: mod_product_nil_l. }
    move => /= [??] /= [[?[??]]?]. subst.
    apply: TTraceStep; [ by apply: ProductStepL |  | simpl;done].
    move => [??] /= [??]. subst. naive_solver.
  - move => ?????? IH ? [??]/=? /(thas_trace_cons_inv _ _)?.
    apply: thas_trace_mono; [|done| done].
    apply: (thas_trace_trans tnil). { by apply: mod_product_nil_r. }
    move => /= [??] /= [[?[??]]?]. subst.
    apply: TTraceStep; [ by apply: ProductStepR |  | simpl;done].
    move => [??] /= [??]. subst. naive_solver.
  - move => ??????? IH ? [??]/= /(thas_trace_cons_inv _ _)? /(thas_trace_cons_inv _ _)?.
    apply: thas_trace_mono; [|done| done].
    apply: (thas_trace_trans tnil). { by apply: mod_product_nil_l. }
    move => /= [??] /= [[?[??]]?]. subst.
    apply: (thas_trace_trans tnil). { by apply: mod_product_nil_r. }
    move => /= [??] /= [[?[??]]?]. subst.
    apply: TTraceStep; [ by apply: ProductStepBoth |  | simpl;done].
    move => [??] /= [??]. subst. naive_solver.
Qed.

Lemma product_mod_trefines {EV1 EV2} (m1 m1' : module EV1) (m2 m2' : module EV2):
  trefines m1 m1' →
  trefines m2 m2' →
  trefines (product_mod m1 m2) (product_mod m1' m2').
Proof.
  move => [/=Hr1] [/=Hr2]. constructor => κs /= /tmod_product_to_mods[κs1 [κs2 [/Hr1 ? /Hr2 ?]]].
  by apply: tmods_to_mod_product.
Qed.

(* simpler proof that uses completeness of wp *)
Lemma product_mod_trefines' {EV1 EV2} (m1 m1' : module EV1) (m2 m2' : module EV2) :
  trefines m1 m1' →
  trefines m2 m2' →
  trefines (product_mod m1 m2) (product_mod m1' m2').
Proof.
  destruct m1 as [m1 σ1], m1' as [m1' σ1'], m2 as [m2 σ2], m2' as [m2' σ2'].
  move => /wp_complete /= Hr1 /wp_complete/=Hr2.
  apply wp_implies_refines => n. elim/o_lt_ind: n σ1 σ1' σ2 σ2' {Hr1 Hr2} (Hr1 n) (Hr2 n).
  move => n IH σ1 σ1' σ2 σ2' Hr1 Hr2.
  apply Wp_step => Pσi n' κ Hsub Hstep. inv_all @m_step.
  - inversion Hr1 as [??? Hr1']; simplify_eq.
    have [?[Ht HP]]:= Hr1' _ _ _ ltac:(done) ltac:(done).
    case_match; simplify_eq/=.
    + move: Ht => /(thas_trace_cons_inv _ _)?.
      apply: (thas_trace_trans tnil); [ by apply: mod_product_nil_l|].
      move => [??]/= [[?[? HP']] ?]; subst.
      tstep_Some; [by apply (ProductStepL (Some _))|].
      move => [??]/= [/HP'? ?]; subst.
      apply: thas_trace_mono; [by apply: mod_product_nil_l|done|] => -[??] /= [/HP[?[??]]?]; subst. eexists (_, _).
      split; [done|]. apply: IH; [done..|]. apply: wp_mono; [done|]. by apply o_lt_impl_le.
    + apply: thas_trace_mono; [by apply: mod_product_nil_l|done|] => -[??] /= [/HP[?[??]]?]; subst. eexists (_, _).
      split; [done|]. apply: IH; [done..|]. apply: wp_mono; [done|]. by apply o_lt_impl_le.
  - inversion Hr2 as [??? Hr2']; simplify_eq.
    have [?[Ht HP]]:= Hr2' _ _ _ ltac:(done) ltac:(done).
    case_match; simplify_eq/=.
    + move: Ht => /(thas_trace_cons_inv _ _)?.
      apply: (thas_trace_trans tnil); [ by apply: mod_product_nil_r|].
      move => [??]/= [[?[? HP']] ?]; subst.
      tstep_Some; [by apply (ProductStepR (Some _))|].
      move => [??]/= [? /HP'?]; subst.
      apply: thas_trace_mono; [by apply: mod_product_nil_r|done|] => -[??] /= [/HP[?[??]] ?]; subst. eexists (_, _).
      split; [done|]. apply: IH; [done| |done]. apply: wp_mono; [done|]. by apply o_lt_impl_le.
    + apply: thas_trace_mono; [by apply: mod_product_nil_r|done|] => -[??] /= [/HP[?[??]]?]; subst. eexists (_, _).
      split; [done|]. apply: IH; [done| |done]. apply: wp_mono; [done|]. by apply o_lt_impl_le.
  - inversion Hr1 as [??? Hr1']; simplify_eq.
    inversion Hr2 as [??? Hr2']; simplify_eq.
    have [?[Ht1 HP1]]:= Hr1' _ _ _ ltac:(done) ltac:(done).
    have [?[Ht2 HP2]]:= Hr2' _ _ _ ltac:(done) ltac:(done).
    move: Ht1 => /(thas_trace_cons_inv _ _)?.
    apply: (thas_trace_trans tnil); [ by apply: mod_product_nil_l|].
    move => [??]/= [[?[? HP1']] ?]. simplify_eq/=.
    move: Ht2 => /(thas_trace_cons_inv _ _)?.
    apply: (thas_trace_trans tnil); [ by apply: mod_product_nil_r|].
    move => [??]/= [[?[? HP2']] ?]; subst.
    tstep_Some; [by econs|].
    move => [??]/= [/HP1'? /HP2'?]; subst.
    apply: (thas_trace_trans tnil); [by apply: mod_product_nil_l|] => -[??] /= [/HP1[?[??]] ?]; subst.
    apply: thas_trace_mono; [by apply: mod_product_nil_r|done|] => -[??] /= [/HP2[?[??]] ?]; subst.
    eexists (_, _). split; [done|]. by apply: IH.
Qed.

(** * map *)
Definition map_mod_fn EV1 EV2 S :=
  S → EV1 → option EV2 → S → bool → Prop.
Inductive map_mod_step {EV1 EV2 S} (f : map_mod_fn EV1 EV2 S) :
  (S * bool) → option (EV1 * option EV2) → ((S * bool) → Prop) → Prop :=
| MapS σ e1 e2 σ' ok:
  f σ e1 e2 σ' ok →
  map_mod_step f (σ, true) (Some (e1, e2)) (λ σ'', σ'' = (σ', ok))
| MapUbS σ:
  map_mod_step f (σ, false) None (λ _, False).
Definition map_mod_trans {EV1 EV2 S} (f : map_mod_fn EV1 EV2 S) : mod_trans (EV1 * option EV2) :=
  ModTrans (map_mod_step f).

Global Instance map_mod_mod_vis_no_all {EV1 EV2 S} (f : map_mod_fn EV1 EV2 S):
  VisNoAng (map_mod_trans f).
Proof. move => ????. inv_all @m_step; try case_match => //; simplify_eq. naive_solver. Qed.

Definition map_trans {EV1 EV2 S} (m : mod_trans EV1) (f : map_mod_fn EV1 EV2 S) : mod_trans EV2 :=
  filter_trans (product_trans m (map_mod_trans f)) (λ e er, e.2 = (λ x, (x, er)) <$> e.1).

Definition map_mod {EV1 EV2 S} (m : module EV1) (f : map_mod_fn EV1 EV2 S) (σf : S) : module EV2 :=
  Mod (map_trans m.(m_trans) f) (m.(m_init), (σf, true)).

Lemma map_mod_trefines {EV1 EV2 S} m1 m2 (f : map_mod_fn EV1 EV2 S) σf :
  trefines m1 m2 →
  trefines (map_mod m1 f σf) (map_mod m2 f σf).
Proof.
  move => ?. destruct m1, m2.
  apply: (filter_mod_trefines _ (Mod _ _) (Mod _ _)).
  by apply: (product_mod_trefines (Mod _ _) (Mod _ _) (Mod _ _) (Mod _ _) ).
Qed.

Lemma map_trans_nil {EV1 EV2 S} m (f : map_mod_fn EV1 EV2 S) σ Pσ Pσf σf κs:
  σ ~{ m, tnil }~>ₜ Pσ →
  (∀ σ', Pσ σ' → (σ', σf) ~{ map_trans m f, κs }~>ₜ Pσf) →
  (σ, σf) ~{ map_trans m f, κs }~>ₜ Pσf.
Proof.
  move => Hσ Hcont. apply: (thas_trace_trans tnil).
  - apply (tmod_to_mod_filter _ _ _ _ tnil). by apply: mod_product_nil_l.
  - move => [??]/= [??]. naive_solver.
Qed.

Lemma map_trans_step_i {EV1 EV2 S} m (f : map_mod_fn EV1 EV2 S) σ σf P `{!TStepI m σ P} :
  TStepI (map_trans m f) (σ, (σf, true)) (λ G, P (λ b κ P',
   ∀ κ' σf' ok, (if κ is Some e then f σf e κ' σf' ok else κ' = None ∧ σf' = σf ∧ ok = true) →
               G b κ' (λ G', P' (λ x, G' (x, (σf', ok)))))).
Proof.
  constructor => G /(@tstepi_proof _ _ _ _ ltac:(done)) HP.
  apply: (steps_impl_submodule _ (map_trans _ _) (λ x, (x, (σf, true)))); [done| |].
  - move => ?? /= [?[?[HG [? HG']]]]. eexists _, _. split_and!; [by apply HG|done|] => ? /= /HG'[?[??]]. naive_solver.
  - move => ????. inv_all/= @m_step; eexists _, _.
    all: split_and!; [done| |repeat case_match => //;naive_solver].
    + move => [?[?[HG [? HG']]]]. case_match; simplify_eq.
      eexists _, _. split_and!; [by apply HG|done|] => ? /= /HG'[?[??]]. naive_solver.
    + move => [?[?[HG [? HG']]]]. eexists _,_. split_and!; [by apply HG|done|] => ? /= /HG'[?[??]]. naive_solver.
Qed.
Global Hint Resolve map_trans_step_i : typeclass_instances.

Lemma map_trans_step_s {EV1 EV2 S} m (f : map_mod_fn EV1 EV2 S) σ σf P `{!TStepS m σ P} :
  TStepS (map_trans m f) (σ, (σf, true)) (λ G, P (λ κ P',
   ∃ κ' σf' ok, (if κ is Some e then f σf e κ' σf' ok else κ' = None ∧ σf' = σf ∧ ok = true) ∧
               G κ' (λ G', P' (λ x, G' (x, (σf', ok)))))).
Proof.
  constructor => G /(@tsteps_proof _ _ _ _ ltac:(done)) [κ [? [[? [κ' [?[??]]]] HG']]].
  eexists _, _. split; [done|].
  move => ? /HG'. move => /steps_spec_has_trace_1 Ht. apply steps_spec_has_trace_elim.
  apply: map_trans_nil; [done|] => ?/=?. tend. destruct κ; destruct!/=.
  - apply: steps_spec_step_end. { econs. { apply: ProductStepBoth; [done|]. by econs. } done. }
    move => [??]/=?. naive_solver.
  - by apply steps_spec_end.
Qed.
Global Hint Resolve map_trans_step_s : typeclass_instances.

Lemma map_trans_ub_s {EV1 EV2 S} m (f : map_mod_fn EV1 EV2 S) σ σf:
  TStepS (map_trans m f) (σ, (σf, false)) (λ G, G None (λ G', True)).
Proof.
  constructor => G ?. split!; [done|].
  move => *.
  apply: steps_spec_step_end. { econs. { by apply: ProductStepR; econs. } done. }
  move => [??]. naive_solver.
Qed.
Global Hint Resolve map_trans_ub_s : typeclass_instances.
