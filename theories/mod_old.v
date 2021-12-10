

(*** [trefines] *)

Inductive seq_step {EV1 EV2 EV3} (m1 : module EV1) (m2 : module EV2) (ext1 : EV1 → option EV3) (ext2 : EV2 → option EV3) (R : bool → EV1 → EV2 → Prop) :
  (bool * m1.(m_state) * m2.(m_state)) → option EV3 → ((bool * m1.(m_state) * m2.(m_state)) → Prop) → Prop :=
| SeqStepLNone Pσ σ1 σ2 e:
    m1.(m_step) σ1 e Pσ →
    seq_step m1 m2 ext1 ext2 R (false, σ1, σ2) None (λ '(b', σ1', σ2'), false = b' ∧ Pσ σ1' ∧ σ2 = σ2')
| SeqStepLExt Pσ σ1 σ2 e e':
    m1.(m_step) σ1 (Some e) Pσ →
    ext1 e = Some e' →
    seq_step m1 m2 ext1 ext2 R (false, σ1, σ2) (Some e') (λ '(b', σ1', σ2'), false = b' ∧ Pσ σ1' ∧ σ2 = σ2')
| SeqStepLToR Pσ σ1 σ2 e e' Pσ2:
    m1.(m_step) σ1 (Some e) Pσ →
    ext1 e = None →
    R false e e' →
    σ2 ~{ m2, tcons e' tnil }~>ₛ Pσ2 →
    seq_step m1 m2 ext1 ext2 R (false, σ1, σ2) None (λ '(b', σ1', σ2'), true = b' ∧ Pσ σ1' ∧ Pσ2 σ2)
(* TODO: same as above for right side *)
.

Definition mod_seq {EV1 EV2 EV3} (m1 : module EV1) (m2 : module EV2) (ext1 : EV1 → option EV3) (ext2 : EV2 → option EV3) (R : bool → EV1 → EV2 → Prop) := {|
  m_step := seq_step m1 m2 ext1 ext2 R;
|}.





           Unshelve. 8: {
      unshelve eexists (tapp (option_trace e) (tex _ (λ x, (f x).1)), (tall _ _ (λ x, (f x).2))) => /=.
      { by apply: m_ang_finite. }
      split_and!.
      -- apply: mod_product_rel_mono; [|done].
         destruct e => //=.
         ++ apply: MPR_cons_l; [|done].
            constructor => -[??]. econstructor.
            naive_solver.
         ++ constructor => -[??]. econstructor. naive_solver.
      -- apply: TraceStep; [ done | | done |]. 2: {
           unfold VisNoUb, is_Some in *. destruct e => //. 2: naive_solver.
           have [|[??]?]:= Hnub. naive_solver. naive_solver.
         }
         move => σ' Hσ'. apply: (has_trace_ex (exist _ σ' Hσ')).
         apply: has_trace_mono. naive_solver. done. naive_solver.
      -- apply: has_trace_all => -[??].
         apply: has_trace_mono. naive_solver. done. naive_solver.
    + have {}IH := IH (σ1, _) (conj ltac:(exact (eq_refl σ1)) _).
      have [f Hf]:= CHOICE IH.
      unshelve eexists ((tall _ _ (λ x, (f x).1)), tapp (option_trace e) (tex _ (λ x, (f x).2))) => /=.
      { by apply: m_ang_finite. }
      split_and!.
      -- apply: mod_product_rel_mono; [|done].
         destruct e => //=.
         ++ apply: MPR_cons_r; [|done].
            constructor => -[??]. econstructor.
            naive_solver.
         ++ constructor => -[??]. econstructor. naive_solver.
      -- apply: has_trace_all => -[??].
         apply: has_trace_mono. naive_solver. done. naive_solver.
      -- apply: TraceStep; [ done | | done |]. 2: {
           unfold VisNoUb, is_Some in *. destruct e => //. 2: naive_solver.
           have [|[??]?]:= Hnub. naive_solver. naive_solver.
         }
         move => σ' Hσ'. apply: (has_trace_ex (exist _ σ' Hσ')).
         apply: has_trace_mono. naive_solver. done. naive_solver.
    + have {}IH := IH (_, _) (conj _ _).
      have [f Hf]:= CHOICE2 IH.
      unshelve eexists (tcons e1 (tex _ (λ x1, (tall _ _ (λ x2, (f x1 x2).1)))),
                        tcons e2 (tex _ (λ x2, (tall _ _ (λ x1, (f x1 x2).2))))) => /=.
      { by apply: m_ang_finite. }
      { by apply: m_ang_finite. }
      split_and!.
      -- apply: mod_product_rel_mono; [|done]. simpl.
         econstructor; [|done..].
         constructor => -[??].
         constructor => -[??].
         econstructor.
         econstructor. naive_solver.
      -- apply: TraceStep; [ done | | simpl; done |]. 2: {
           unfold VisNoUb, is_Some in *. have [|[??]?]:= Hnub. naive_solver. naive_solver.
         }
         move => ??.
         apply: has_trace_ex. apply: has_trace_all => -[??]. naive_solver.
      -- apply: TraceStep; [ done | | simpl; done |]. 2: {
           unfold VisNoUb, is_Some in *. have [|[??]?]:= Hnub. naive_solver. naive_solver.
         }
         move => ??.
         apply: has_trace_ex. apply: has_trace_all => -[??]. naive_solver.
  - move => T f ????? IH ?.
    have [fx Hfx]:= AxCHOICE _ _ _ IH.
    eexists (tall T ltac:(done) (λ x, (fx x).1), tall T ltac:(done) (λ x, (fx x).2)) => /=.
    split_and! => //.
    -- apply: mod_product_rel_mono; [|done].
       eapply MPR_all; [|done] => ?.
       econstructor. econstructor. naive_solver.
    -- apply: has_trace_all. naive_solver.
    -- apply: has_trace_all. naive_solver.
       Unshelve. done. done.
Qed.

Lemma mod_product_nil_l {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ1 σ2 Pσ κs:
  σ1 ~{ m1, κs }~> Pσ → κs ⊆ tnil →
  (σ1, σ2) ~{ mod_product m1 m2, tnil }~> (λ σ', Pσ σ'.1 ∧ σ2 = σ'.2).
Proof.
  elim.
  - move => ??????. constructor; [|done]. naive_solver.
  - move => ??? κ ????? Hs1 ? Hs2.
    pose proof (transitivity Hs1 Hs2) as Hs.
    destruct κ; [inversion Hs|]; simplify_eq/=.
    apply: TraceStep; [ by apply: ProductStepL | | simpl;done | by move => -[??]].
    move => [??] /=. naive_solver.
  - move => ???????? Hs1 Hs2.
    pose proof (transitivity Hs1 Hs2) as [??]%subtrace_all_nil_inv. naive_solver.
Qed.

Lemma mod_product_nil_r {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ1 σ2 Pσ κs:
  σ2 ~{ m2, κs }~> Pσ → κs ⊆ tnil →
  (σ1, σ2) ~{ mod_product m1 m2, tnil }~> (λ σ', Pσ σ'.2 ∧ σ1 = σ'.1).
Proof.
  elim.
  - move => ??????. constructor; [|done]. naive_solver.
  - move => ??? κ ????? Hs1 ? Hs2.
    pose proof (transitivity Hs1 Hs2) as Hs.
    destruct κ; [inversion Hs|]; simplify_eq/=.
    apply: TraceStep; [ by apply: ProductStepR | | simpl;done | by move => -[??]].
    move => [??] /=. naive_solver.
  - move => ???????? Hs1 Hs2.
    pose proof (transitivity Hs1 Hs2) as [??]%subtrace_all_nil_inv. naive_solver.
Qed.

Lemma mods_to_mod_product {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ κs κs1 κs2:
  mod_product_rel κs κs1 κs2 →
  σ.1 ~{ m1, κs1 }~> (λ _, True) → σ.2 ~{ m2, κs2 }~> (λ _, True) →
  σ ~{ mod_product m1 m2, κs }~> (λ _, True).
Proof.
  move => Hrel.
  elim: Hrel σ.
  - move => ?????. by constructor.
  - move => ????? /= IH [??] /has_trace_ex_inv ??.
    apply: (has_trace_trans tnil). { by apply: mod_product_nil_l. }
    move => [??] /= [[??]?]. naive_solver.
  - move => ????? IH [??] ? /has_trace_ex_inv ?.
    apply: (has_trace_trans tnil). { by apply: mod_product_nil_r. }
    move => [??] /= [[??]?]. naive_solver.
  - move => ?????? ? IH ? /has_trace_all_inv ??. apply: IH; [|done]. naive_solver.
  - move => ?????? ? IH ?? /has_trace_all_inv ?. apply: IH; [done|]. naive_solver.
  - move => ??????? IH ????.
    apply: has_trace_mono; [|done| done].
    apply: has_trace_all => ?. naive_solver.
  - move => ?????? IH ? [??]/= /(has_trace_cons_inv _ _) ??.
    apply: has_trace_mono; [|done| done].
    apply: (has_trace_trans tnil). { by apply: mod_product_nil_l. }
    move => /= [??] /= [[?[?[Hvis ?]]]?]. subst.
    apply: TraceStep; [ by apply: ProductStepL |  | simpl;done |]. 2: {
      have [|??]:= Hvis. naive_solver. unfold VisNoUb in *. eexists (_,_). naive_solver.
    }
    move => [??] /= [??]. subst. naive_solver.
  - move => ?????? IH ? [??]/=? /(has_trace_cons_inv _ _)?.
    apply: has_trace_mono; [|done| done].
    apply: (has_trace_trans tnil). { by apply: mod_product_nil_r. }
    move => /= [??] /= [[?[?[Hvis ?]]]?]. subst.
    apply: TraceStep; [ by apply: ProductStepR |  | simpl;done |]. 2: {
      have [|??]:= Hvis. naive_solver. unfold VisNoUb in *. eexists (_,_). naive_solver.
    }
    move => [??] /= [??]. subst. naive_solver.
  - move => ??????? IH ? [??]/= /(has_trace_cons_inv _ _)? /(has_trace_cons_inv _ _)?.
    apply: has_trace_mono; [|done| done].
    apply: (has_trace_trans tnil). { by apply: mod_product_nil_l. }
    move => /= [??] /= [[?[?[Hvis ?]]]?]. subst.
    apply: (has_trace_trans tnil). { by apply: mod_product_nil_r. }
    move => /= [??] /= [[?[?[Hvis2 ?]]]?]. subst.
    apply: TraceStep; [ by apply: ProductStepBoth |  | simpl;done |]. 2: {
      have [|??]:= Hvis. naive_solver.
      have [|??]:= Hvis2. naive_solver.
      unfold VisNoUb in *. eexists (_,_). naive_solver.
    }
    move => [??] /= [??]. subst. naive_solver.
Qed.

Lemma mod_product_refines {EV1 EV2} (m1 m1' : module EV1) (m2 m2' : module EV2) σ1 σ1' σ2 σ2':
  MS m1 σ1 ⊑ MS m1' σ1' →
  MS m2 σ2 ⊑ MS m2' σ2' →
  MS (mod_product m1 m2) (σ1, σ2) ⊑ MS (mod_product m1' m2') (σ1', σ2').
Proof.
  move => [/=Hr1] [/=Hr2]. constructor => κs /= /mod_product_to_mods[κs1 [κs2 [/Hr1 ? /Hr2 ?]]].
  by apply: mods_to_mod_product.
Qed.

(*** link *)
Record link_mediator EV1 EV2 EV3 := {
  lm_state : Type;
  lm_initial : lm_state;
  lm_step : lm_state → option EV1 → option EV2 → option EV3 → lm_state → Prop;
}.
Arguments lm_state {_ _ _}.
Arguments lm_initial {_ _ _}.
Arguments lm_step {_ _ _}.

Definition stateless_mediator {EV1 EV2 EV3} (R : option EV1 → option EV2 → option EV3 → Prop) : link_mediator EV1 EV2 EV3 := {|
  lm_state := unit;
  lm_initial := tt;
  lm_step _ e1 e2 e3 _:= R e1 e2 e3;
|}.

Inductive link_step {EV1 EV2 EV3} (m1 : module EV1) (m2 : module EV2) (M : link_mediator EV1 EV2 EV3) :
  m1.(m_state) * m2.(m_state) * M.(lm_state) → option EV3 → m1.(m_state) * m2.(m_state) * M.(lm_state) → Prop :=
| LinkStepL σ1 σ2 e1 e' σ1' σm σm':
    m1.(m_step) σ1 e1 σ1' →
    (* TODO: is there a better way to formulate this? E.g. assume
    that there is no R None None Some in the theorem? *)
    (if e1 is Some es1 then M.(lm_step) σm e1 None e' σm' else e' = None ∧ σm' = σm) →
    link_step m1 m2 M (σ1, σ2, σm) e' (σ1', σ2, σm')
| LinkStepR σ1 σ2 e2 e' σ2' σm σm':
    m2.(m_step) σ2 e2 σ2' →
    (if e2 is Some es2 then M.(lm_step) σm None e2 e' σm' else e' = None ∧ σm' = σm) →
    link_step m1 m2 M (σ1, σ2, σm) e' (σ1, σ2', σm')
| LinkStepBoth σ1 σ2 e1 e2 e' σ1' σ2' σm σm':
    m1.(m_step) σ1 (Some e1) σ1' →
    m2.(m_step) σ2 (Some e2) σ2' →
    M.(lm_step) σm (Some e1) (Some e2) e' σm' →
    link_step m1 m2 M (σ1, σ2, σm) e' (σ1', σ2', σm').

Definition link {EV1 EV2 EV3} (m1 : module EV1) (m2 : module EV2) (M : link_mediator EV1 EV2 EV3) : module EV3 := {|
  m_state := m1.(m_state) * m2.(m_state) * M.(lm_state);
  m_step := (link_step m1 m2 M);
  m_is_ub σ := m1.(m_is_ub) σ.1.1 ∨ m2.(m_is_ub) σ.1.2;
|}.


Lemma link_empty_steps_l {EV1 EV2 EV3} m1 m2 (M : link_mediator EV1 EV2 EV3) σ1 Pσ1' σ2 σm  :
  σ1 ~{ m1, [] }~> Pσ1' →
  (σ1, σ2, σm) ~{ link m1 m2 M, [] }~> (λ '(σ1', σ2', σm'), Pσ1' σ1' ∧ σ2' = σ2 ∧ σm = σm').
Proof.
  move Hκ: ([]) => κ Hsteps.
  elim: Hsteps Hκ.
  - move => ????. by apply: TraceEnd.
  - move => ??? [] //= ?????. apply: (TraceStepNone); [ | naive_solver]. by econstructor.
  - move => ?????. apply: TraceUb. naive_solver.
Qed.

Lemma link_empty_steps_r {EV1 EV2 EV3} m1 m2 (M : link_mediator EV1 EV2 EV3) σ1 Pσ2' σ2 σm :
  σ2 ~{ m2, [] }~> Pσ2' →
  (σ1, σ2, σm) ~{ link m1 m2 M, [] }~> (λ '(σ1', σ2', σm'), σ1' = σ1 ∧ Pσ2' σ2' ∧ σm = σm').
Proof.
  move Hκ: ([]) => κ Hsteps.
  elim: Hsteps Hκ.
  - move => ????. by apply: TraceEnd.
  - move => ??? [] //= ?????. apply: (TraceStepNone); [ | naive_solver]. by econstructor.
  - move => ?????. apply: TraceUb. naive_solver.
Qed.

Inductive link_trace_related {EV1 EV2 EV3} (M : link_mediator EV1 EV2 EV3) : M.(lm_state) → list (event EV1) → list (event EV2) → list (event EV3) → M.(lm_state) → Prop :=
| LinkTraceRelNil σm:
    link_trace_related M σm [] [] [] σm
| LinkTraceRelUbL κs2 κs3 σm σm2:
    link_trace_related M σm [Ub] κs2 κs3 σm2
| LinkTraceRelUbR κs1 κs3 σm σm2:
    link_trace_related M σm κs1 [Ub] κs3 σm2
| LinkTraceRelL κ1 κ1' κs1 κs2 κs3 σm σm' σm2:
    link_trace_related M σm' κs1 κs2 κs3 σm2 →
    M.(lm_step) σm (Some κ1) None κ1' σm' →
    link_trace_related M σm ([Vis κ1] ++ κs1) κs2 (option_list (Vis <$> κ1') ++ κs3) σm2
| LinkTraceRelR κ2 κ2' κs1 κs2 κs3 σm σm' σm2:
    link_trace_related M σm' κs1 κs2 κs3 σm2 →
    M.(lm_step) σm None (Some κ2) κ2' σm' →
    link_trace_related M σm κs1 ([Vis κ2] ++ κs2) (option_list (Vis <$> κ2') ++ κs3) σm2
| LinkTraceRelBoth κ1 κ2 κ3 κs1 κs2 κs3 σm σm' σm2:
    link_trace_related M σm' κs1 κs2 κs3 σm2 →
    M.(lm_step) σm (Some κ1) (Some κ2) κ3 σm' →
    link_trace_related M σm ([Vis κ1] ++ κs1) ([Vis κ2] ++ κs2) (option_list (Vis <$> κ3) ++ κs3) σm2
.

Lemma link_trace_related_create {EV1 EV2 EV3} (M : link_mediator EV1 EV2 EV3) m1 m2 κs3 σ1 :
  σ1 ~{ link m1 m2 M, κs3 }~> (λ _, True) →
  ∃ κs1 κs2 σm', link_trace_related M σ1.2 κs1 κs2 κs3 σm' ∧
  σ1.1.1 ~{ m1, κs1 }~> (λ _, True) ∧
  σ1.1.2 ~{ m2, κs2 }~> (λ _, True).
Proof.
  elim; clear.
  - move => σ ? ?. eexists [], [], _. split_and!; by constructor.
  - move => σ1 σ2 Pσ3 κ κs Hstep Hsteps [κs1 [κs2 [σm' [Hlink [Hκ1 Hκ2]]]]].
    inversion Hstep; clear Hstep; simplify_eq.
    + eexists (option_list (Vis <$> e1) ++ κs1), κs2, _.
      split_and! => //; destruct e1; destruct_and?; simplify_eq/= => //; rewrite ?right_id //. by econstructor.
      * by apply: TraceStepSome.
      * by apply: TraceStepNone.
    + eexists κs1, (option_list (Vis <$> e2) ++ κs2), _.
      split_and! => //; destruct e2; destruct_and?; simplify_eq/= => //; rewrite ?right_id //. by econstructor.
      * by apply: TraceStepSome.
      * by apply: TraceStepNone.
    + eexists ([Vis e1] ++ κs1), ([Vis e2] ++ κs2), _.
      split_and!.
      * by apply: LinkTraceRelBoth.
      * by apply: TraceStepSome.
      * by apply: TraceStepSome.
  - move => [σ1 σm] κs σ2 /= [] Hub.
    + eexists [Ub], [], σm => /=. split_and!. by econstructor.
      * by apply: TraceUb.
      * by apply: TraceEnd.
    + eexists [], [Ub], σm. split_and!. by econstructor.
      * by apply: TraceEnd.
      * by apply: TraceUb.
Qed.

Lemma link_trace_related_step {EV1 EV2 EV3} (M : link_mediator EV1 EV2 EV3) m1 m2 κs1 κs2 κs3 σ1 σ2 σm σm':
  link_trace_related M σm κs1 κs2 κs3 σm' →
  σ1 ~{ m1, κs1 }~> (λ _, True) →
  σ2 ~{ m2, κs2 }~> (λ _, True) →
  (σ1, σ2, σm) ~{ link m1 m2 M, κs3 }~> (λ _, True).
Proof.
  move => Hrel.
  elim: Hrel σ1 σ2; clear.
  - move => σm σ1 σ2 Hstep1 Hstep2.
    apply: (has_trace_trans [] []). { by apply: link_empty_steps_l. }
    move => [[??]?] [?[??]]. subst.
    apply: has_trace_mono; [|done]. by apply: link_empty_steps_r.
  - move => ?????? /has_trace_ub_inv??.
    apply: (has_trace_trans []). { by apply: link_empty_steps_l. }
    move => [[??]?] [?[??]]. done.
  - move => ??????? /has_trace_ub_inv?.
    apply: (has_trace_trans []). { by apply: link_empty_steps_r. }
    move => [[??]?] [?[??]]. done.
  - move => κ1 κ1' κs1 κs2 κs3 ??? ? IH HR σ1 σ2 /= /(has_trace_cons_inv _ _)??.
    apply: (has_trace_trans []). { by apply: link_empty_steps_l. }
    move => [[??]?] [[?[??]][??]] /=. subst.
    apply: TraceStep; [ | by apply: IH].
    by apply: LinkStepL.
  - move => κ1 κ1' κs1 κs2 κs3 ??? ? IH HR σ1 σ2 /= ?/(has_trace_cons_inv _ _)?.
    apply: (has_trace_trans []). { by apply: link_empty_steps_r. }
    move => [[??]?] [?[[?[??]]?]] /=. subst.
    apply: TraceStep; [ | by apply: IH].
    by apply: LinkStepR.
  - move => κ1 κ2 κ3 κs1 κs2 κs3 ??? ? IH HR σ1 σ2 /= /(has_trace_cons_inv _ _)? /(has_trace_cons_inv _ _)?.
    apply: (has_trace_trans []). { by apply: link_empty_steps_l. }
    move => [[??]?] [[?[??]][??]] /=. subst.
    apply: (has_trace_trans []). { by apply: link_empty_steps_r. }
    move => [[??]?] [?[[?[??]]?]] /=. subst.
    apply: TraceStep; [ | by apply: IH].
    by apply: LinkStepBoth.
Qed.

Lemma refines_horizontal {EV1 EV2 EV3} (m1 m2 m1' m2' : module _) σ1 σ2 σ1' σ2' (M : link_mediator EV1 EV2 EV3) :
  MS m1 σ1 ⊑ MS m1' σ1' →
  MS m2 σ2 ⊑ MS m2' σ2' →
  MS (link m1 m2 M) (σ1, σ2, M.(lm_initial)) ⊑ MS (link m1' m2' M) (σ1', σ2', M.(lm_initial)).
Proof.
  move => [Hr1] [Hr2].
  constructor => κs /= /link_trace_related_create [?[?[?[?[??]]]]].
  apply: link_trace_related_step; [done|..].
  - by apply: Hr1.
  - by apply: Hr2.
Qed.

(*** has_non_ub_trace *)
Inductive has_non_ub_trace {EV} (m : module EV) : m.(m_state) → list EV → m.(m_state) → Prop :=
| NUBTraceEnd σ:
    has_non_ub_trace m σ [] σ
| NUBTraceStep σ1 σ2 σ3 κ κs:
    m.(m_step) σ1 κ σ2 →
    has_non_ub_trace m σ2 κs σ3 →
    has_non_ub_trace m σ1 (option_list κ ++ κs) σ3
.
Notation " σ '~{' m , κ '}~>ₙ' σ' " := (has_non_ub_trace m σ κ σ') (at level 40).
Notation " σ '~{' m , κ '}~>ₙ' - " := (∃ σ', has_non_ub_trace m σ κ σ') (at level 40).

Lemma NUBTraceStepNone {EV} κs (m : module EV) σ2 σ1 σ3 :
  m.(m_step) σ1 None σ2 →
  σ2 ~{ m, κs }~>ₙ σ3 →
  σ1 ~{ m, κs }~>ₙ σ3.
Proof. move => ??. by apply: (NUBTraceStep _ _ _ _ None). Qed.

Lemma NUBTraceStepSome {EV} κs (m : module EV) σ2 σ1 σ3 κ :
  m.(m_step) σ1 (Some κ) σ2 →
  σ2 ~{ m, κs }~>ₙ σ3 →
  σ1 ~{ m, κ :: κs }~>ₙ σ3.
Proof. move => ??. by apply: (NUBTraceStep _ _ _ _ (Some _)). Qed.

Lemma has_non_ub_trace_trans {EV} κs1 κs2 (m : module EV) σ1 σ2 σ3 :
  σ1 ~{ m, κs1 }~>ₙ σ2 →
  σ2 ~{ m, κs2 }~>ₙ σ3 →
  σ1 ~{ m, κs1 ++ κs2 }~>ₙ σ3.
Proof.
  elim => //.
  move => ?????????. rewrite -app_assoc. econstructor; eauto.
Qed.

Lemma has_non_ub_trace_add_empty {EV} κs1 (m : module EV) σ1 σ2 :
  σ1 ~{ m, κs1 ++ [] }~>ₙ σ2 →
  σ1 ~{ m, κs1 }~>ₙ σ2.
Proof. by rewrite -{2}[κs1](right_id_L [] (++)). Qed.

Lemma has_trace_to_non_ub_trace EV (m : module EV) σ1 κs Pσ2:
  σ1 ~{ m, κs }~> Pσ2 →
  ∃ κs' σ2', Vis <$> κs' `prefix_of` κs ∧ σ1 ~{ m, κs' }~>ₙ σ2' ∧
             ((Vis <$> κs' = κs ∧ Pσ2 σ2') ∨ m.(m_is_ub) σ2').
Proof.
  elim.
  - move => ?. eexists [], _. naive_solver constructor.
  - move => ??? κ ??? [κs' [σ2' [?[??]]]]. eexists (option_list κ ++ κs'), σ2'.
    split_and! => //.
    + destruct κ => //. by apply: prefix_cons.
    + by econstructor.
    + destruct κ; naive_solver.
  - move => ????. eexists [], _. split_and! => //=.
    + by apply prefix_nil.
    + by constructor.
    + by right.
Qed.

(*** has_no_behavior *)
Definition has_no_behavior {EV} (m : module EV) (σ : m.(m_state)) :=
  ∀ σ' κs, σ ~{ m, κs }~> σ' → κs = [].

Lemma no_behavior_step {EV} (m : module EV) σ:
  (∀ e σ', m.(m_step) σ e σ' → e = None ∧ has_no_behavior m σ') → ¬(m_is_ub m σ) → has_no_behavior m σ.
Proof. move => Hstep ??? Htrace. inversion Htrace; simplify_eq/= => //. efeed pose proof Hstep => //. naive_solver. Qed.

(*** state_set *)
Definition power_reach {EV} (m : module EV) (σs : propset m.(m_state)) (κs : list (event EV)) : propset m.(m_state) :=
  {[ σ2 | ∃ σ1, σ1 ∈ σs ∧ σ1 ~{ m, κs }~> (σ2 =.) ]}.

Global Instance power_reach_proper {EV} (m : module EV) :
  Proper ((≡) ==> (=) ==> (≡)) (power_reach m).
Proof. move => ?? ? ?? ?. set_solver. Qed.

Global Instance power_reach_subseteq_proper {EV} (m : module EV) :
  Proper ((⊆) ==> (=) ==> (⊆)) (power_reach m).
Proof. move => ?? ? ?? ?. set_solver. Qed.

Lemma power_reach_refl {EV} (m : module EV) σs:
  σs ⊆ power_reach m σs [].
Proof. set_unfold. move => ??. eexists _. split; [done|]. by apply: TraceEnd. Qed.

Lemma power_reach_trans {EV} κs1 κs2 (m : module EV) σs:
  (* TODO: one can prove an equivalence using has_trace_inv *)
  power_reach m (power_reach m σs κs1) κs2 ⊆ power_reach m σs (κs1 ++ κs2).
Proof.
  set_unfold => ?.
  move => [? [[?[??]]?]]. eexists _. split; [done|]. apply: has_trace_trans; [done|naive_solver].
Qed.

Lemma elem_of_power_reach {EV} (m : module EV) σ σ' σs κs:
  σ' ∈ σs →
  σ' ~{ m, κs }~> (σ =.) →
  σ ∈ power_reach m σs κs.
Proof. move => ?. eexists _. naive_solver. Qed.

Definition power_module {EV} (m : module EV) : module EV := {|
  m_state := propset m.(m_state);
  m_step σs1 κ σs2 :=
    (σs2 ≡ power_reach m σs1 (option_list (Vis <$> κ))) ∧ ∃ σ, σ ∈ σs2;
  m_is_ub σs := ∃ σ, σ ∈ σs ∧ m.(m_is_ub) σ;
|}.

Lemma power_step_mono {EV} (m : module EV) σ1 σ2 σ κ:
  m_step (power_module m) σ1 κ σ →
  σ1 ⊆ σ2 →
  ∃ σ', σ ⊆ σ' ∧ m_step (power_module m) σ2 κ σ'.
Proof. move => [Heq ?] ?. eexists _. split; [|split;[done|]]; set_solver. Qed.

Lemma power_mono {EV} (m : module EV) σ1 σ2 κs:
  σ1 ~{ power_module m, κs }~> (λ _, True) →
  σ1 ⊆ σ2 →
  σ2 ~{ power_module m, κs }~> (λ _, True).
Proof.
  move HPσ: (λ _, True) => Pσ.
  move => HT. elim: HT σ2 HPσ.
  - move => ???? <- ?. by apply: TraceEnd.
  - move => ??????? IH ???. subst.
    have [?[??]]:= power_step_mono _ _ _ _ _ ltac:(done) ltac:(done).
    apply: TraceStep; [done|]. by apply: IH.
  - move => ???????. apply: TraceUb. simplify_eq/=. set_solver.
Qed.

Lemma power_elim {EV} (m : module EV) Pσ κs:
  Pσ ~{ power_module m, κs }~> (λ _, True) →
  (∃ σ, σ ∈ Pσ) →
  ∃ σ, σ ∈ Pσ ∧ σ ~{ m, κs }~> (λ _, True).
Proof.
  elim.
  - move => ??? [??]. eexists _. split. 2: by apply: TraceEnd. done.
  - move => ????? [Heq [? Hin]] ? IH [??].
    move: Hin. rewrite Heq => -[?[??]].
    case: IH. { set_unfold. naive_solver. }
    move => ?. rewrite Heq. move => [[?[??]]?].
    eexists _. split. 2: apply: has_trace_trans; [done|]. done. naive_solver.
  - move => ??? [?[??]] [??]. eexists _.
    split. 2: by apply: TraceUb. done.
Qed.

Lemma power_elim_singleton {EV} (m : module EV) σ κs:
  {[σ]} ~{ power_module m, κs }~> (λ _, True) →
  σ ~{ m, κs }~> (λ _, True).
Proof. move => /power_elim -[|??]; set_solver. Qed.

Lemma power_intro {EV} (m : module EV) Pσ σ κs:
  σ ~{ m, κs }~> (λ _, True) →
  σ ∈ Pσ → Pσ ~{ power_module m, κs }~> (λ _, True).
Proof.
  move => Htrace.
  elim: Htrace Pσ.
  - move => ? Pσ ?. move => ??. by apply: TraceEnd.
  - move => ??? κ ??? IH ??.
    apply: TraceStep.
    + split; [ done|]. set_unfold.
      eexists _, _. split; [done|].
      apply: TraceStep'; [done| | by apply: TraceEnd].
        by rewrite right_id.
    + apply: IH. set_unfold.
      eexists _. split => //.
      apply: TraceStep'; [done| | by apply: TraceEnd].
        by rewrite right_id.
  - move => ??????.
    apply: TraceUb => /=. naive_solver.
Qed.
Lemma power_intro_singleton {EV} (m : module EV) σ κs:
  σ ~{ m, κs }~> (λ _, True) →
  {[σ]} ~{ power_module m, κs }~> (λ _, True).
Proof. move => ?. apply: power_intro; set_solver. Qed.

Lemma power_nil {EV} (m : module EV) σs Pσ:
  σs ~{ power_module m, [] }~> Pσ →
  ∃ σs', σs' ⊆ (power_reach m σs []) ∧ (m_is_ub (power_module m) σs' ∨ Pσ σs').
Proof.
  move Hκ: [] => κ Htrace.
  elim: Htrace Hκ; clear.
  - move => σs ???. eexists σs. split; [|naive_solver]. by apply: power_reach_refl.
  - move => ??? [//|] ? [Heq [? Hin]] ? IH /= ?.
    have [//|σs'[? Hor]]:= IH.
    eexists σs'. split; [|done].
    etrans; [done|]. rewrite Heq /=. by apply: power_reach_trans.
  - move => ??? ??. subst. eexists _. split; [| by left].
    by apply: power_reach_refl.
Qed.

Definition state_set_refines {EV} (mimpl mspec : module EV) (σi : mimpl.(m_state)) (σs : propset mspec.(m_state)) : Prop :=
  (∃ σ, σ ∈ σs) ∧ ∀ κs, σi ~{ mimpl, κs }~> (λ _, True) → σs ~{ power_module mspec, κs }~> (λ _, True).


Lemma inv_set_implies_refines {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → propset m2.(m_state) → Prop):
  inv m1.(ms_state) {[ m2.(ms_state) ]} →
  (∀ σi1 σs1 σi2 e, inv σi1 σs1 → m_ub_step m1 σi1 e σi2 →
      σs1 ~{ power_module m2, option_list e }~> (λ σs2, inv σi2 σs2)) →
  m1 ⊑ m2.
Proof.
  move => Hinvinit Hinvstep.
  constructor => // κs.
  move: m1.(ms_state) Hinvinit => σi1 Hinv Hsteps.
  have : ({[ms_state m2]} ~{ power_module m2, κs }~> (λ _, True)). 2: {
    apply: power_elim_singleton.
  }
  move: {[ m2.(ms_state) ]} Hinv => σs1 Hinv.
  elim: Hsteps σs1 Hinv => {σi1 κs}.
  - move => ?????. by apply: TraceEnd.
  - move => σi1 σi2 σi3 κ κs Hstep Hsteps IH σs1 Hinv.
    have {}Hs := Hinvstep _ _ _ _ Hinv ltac:(by constructor).
    apply: has_trace_trans;[done|] => ? /=?.
    by apply: IH.
  - move => ??? Hs σs Hinv.
    have /has_trace_ub_inv? := Hinvstep _ _ _ _ Hinv ltac:(by constructor).
    by apply: (has_trace_trans []).
Qed.

Lemma state_set_refines_inhabited {EV} (m1 m2 : module EV) σi σs:
  state_set_refines m1 m2 σi σs → ∃ σ, σ ∈ σs.
Proof. by move => []. Qed.

Lemma state_set_refines_initial {EV} (m1 m2 : mod_state EV):
  m1 ⊑ m2 →
  state_set_refines m1 m2 (ms_state m1) {[ms_state m2]}.
Proof. move => [Hr]. split; [set_solver|]. move => ? /Hr/power_intro_singleton?. done. Qed.

Lemma state_set_refines_step_Some {EV} (m1 m2 : module EV) σi1 σs1 σi2 e:
  state_set_refines m1 m2 σi1 σs1 →
  m1.(m_step) σi1 (Some e) σi2 →
  state_set_refines m1 m2 σi2 (power_reach m2 σs1 [Vis e]).
Proof.
  move => [[??] Hstate] Hstep. split. {
    have := Hstate [Vis e] ltac:(by apply: TraceStepSome; [|apply: TraceEnd]).
    move => /(has_trace_cons_inv _ _)/power_nil[?[?[[σ[??]]|[?[[Heq[??]]?]]]]].
    -- eexists σ.
       apply: elem_of_subseteq_1; [apply: (power_reach_trans [])|].
       apply: elem_of_power_reach; [ by apply: elem_of_subseteq_1|].
         by apply: TraceUb.
    -- eexists _.
       apply: elem_of_subseteq_1; [|done]. rewrite Heq.
       etrans; [| apply: (power_reach_trans [])].
         by apply: power_reach_subseteq_proper.
  }
  move => κs ?.
  have /(has_trace_cons_inv _ _):= Hstate (Vis e :: κs) ltac:(by apply: TraceStepSome).
  move => /power_nil [? [? Hor]].
  apply: power_mono; [| apply: (power_reach_trans [])].
  apply: power_mono; [|by apply: power_reach_subseteq_proper].
  case: Hor.
  - move => [?[??]]. apply: TraceUb. eexists _. split; [|done].
    eexists _. split; [done|]. by apply: TraceUb.
  - move => [?[[??]?]]. apply: power_mono; [done|]. set_solver.
Qed.

Lemma state_set_refines_step_None {EV} (m1 m2 : module EV) σi1 σs1 σi2:
  state_set_refines m1 m2 σi1 σs1 →
  m1.(m_step) σi1 None σi2 →
  state_set_refines m1 m2 σi2 σs1.
Proof. move => [? Hstate] Hstep. split; [done|] => κs ?. apply: Hstate. by apply: TraceStepNone. Qed.

Lemma state_set_refines_step {EV} (m1 m2 : module EV) σi1 σs1 σi2 κ:
  state_set_refines m1 m2 σi1 σs1 →
  m1.(m_step) σi1 κ σi2 →
  state_set_refines m1 m2 σi2 (power_reach m2 σs1 (option_list (Vis <$> κ))).
Proof.
  move => Hstate ?. destruct κ.
  - by apply: state_set_refines_step_Some.
  - move: Hstate => [[??] Hstate].
    split. { eexists _. apply: elem_of_power_reach; [done|]. by apply: TraceEnd. }
    move => κs ?.
    have ?:= Hstate (κs) ltac:(by apply: TraceStepNone).
    apply: power_mono; [done|]. apply: power_reach_refl.
Qed.

Lemma state_set_refines_ub {EV} (m1 m2 : module EV) σi1 σs1:
  state_set_refines m1 m2 σi1 σs1 →
  m1.(m_is_ub) σi1 →
  σs1 ~{ power_module m2, [] }~> (λ _, False).
Proof.
  move => [? Hstate] ?.
  have /has_trace_ub_inv ?:= Hstate [Ub] ltac:(by apply: TraceUb).
  by apply: (has_trace_trans []).
Qed.

Lemma state_set_refines_ub_step {EV} (m1 m2 : module EV) σi1 σs1 σi2 e:
  state_set_refines m1 m2 σi1 σs1 →
  m_ub_step m1 σi1 e σi2 →
  σs1 ~{ power_module m2, option_list e }~> (λ σs2 : m_state (power_module m2), state_set_refines m1 m2 σi2 σs2).
Proof.
  move => Hstate. inversion 1; simplify_eq.
  - have Hstate' := state_set_refines_step _ _ _ _ _ _ ltac:(done) ltac:(done).
    move: (Hstate') => /state_set_refines_inhabited?.
    apply: (TraceStep' _ []); [done| by rewrite right_id |].
    apply: TraceEnd. by apply: state_set_refines_step.
  - apply: (has_trace_trans []); [ by apply: state_set_refines_ub | done].
Qed.

Lemma refines_implies_inv_set {EV} (m1 m2 : mod_state EV):
  m1 ⊑ m2 →
  ∃ (inv : m1.(m_state) → propset m2.(m_state) → Prop),
  inv m1.(ms_state) {[ m2.(ms_state) ]} ∧
  (∀ σi1 σs1 σi2 e, inv σi1 σs1 → m_ub_step m1 σi1 e σi2 →
      σs1 ~{ power_module m2, option_list e }~> (λ σs2, inv σi2 σs2)).
Proof.
  move => Href.
  eexists (state_set_refines m1 m2).
  split_and!.
  - by apply: state_set_refines_initial.
  - move => ????. apply: state_set_refines_ub_step.
Qed.


(*
Definition state_set_refines {EV} (mimpl mspec : module EV) (σi : mimpl.(m_state)) (σs : propset mspec.(m_state)) : Prop :=
  ∀ κs, σi ~{ mimpl, κs }~> (λ _, True) → ∃ σs1, σs1 ∈ σs ∧ σs1 ~{ mspec, κs }~> (λ _, True).

Lemma inv_set_implies_refines {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → propset m2.(m_state) → Prop):
  inv m1.(ms_state) {[ m2.(ms_state) ]} →
  (∀ σi σs, inv σi σs → ∃ σ, σ ∈ σs) →
  (∀ σi σs, inv σi σs → m1.(m_is_ub) σi → ∃ σs1, σs1 ∈ σs ∧ σs1 ~{ m2, [] }~> (λ _, False)) →
  (∀ σi1 σs1 σi2 e, inv σi1 σs1 → m1.(m_step) σi1 e σi2 →
      ∃ σs2, inv σi2 σs2 ∧ σs2 ⊆ {[ σ2 | ∃ σ1, σ1 ∈ σs1 ∧ σ1 ~{ m2, option_list (Vis <$> e) }~> (σ2 =.) ]}) →
  m1 ⊑ m2.
Proof.
  move => Hinvinit Hinvnonempty Hinvsafe Hinvstep.
  constructor => // κs.
  move: m1.(ms_state) Hinvinit => σi1 Hinv Hsteps.
  have : (∃ σs1, σs1 ∈ ({[ms_state m2]} : propset _) ∧ σs1 ~{ m2, κs }~> (λ _, True)); last set_solver.
  move: {[ m2.(ms_state) ]} Hinv => σs1 Hinv.
  elim: Hsteps σs1 Hinv => {σi1 κs}.
  - move => ???? /Hinvnonempty [??]. eexists _. split => //. by apply: TraceEnd.
  - move => σi1 σi2 σi3 κ κs Hstep Hsteps IH σs1 Hinv.
    have [σs2 [Hinv2 Hsub]]:= Hinvstep _ _ _ _ Hinv Hstep.
    have [σs3 [Hin ?]]:= IH _ Hinv2.
    have [σ1 [??]]:= Hsub _ Hin.
    eexists _. split => //. apply: has_trace_trans; [done|] => ??.
    by subst.
  - move => ??? /Hinvsafe Hs σs Hinv.
    have [? [? ?]]:= Hs _ Hinv.
    eexists _. split => //.
    by apply: (has_trace_trans []).
Qed.

Lemma state_set_refines_initial {EV} (m1 m2 : mod_state EV):
  m1 ⊑ m2 →
  state_set_refines m1 m2 (ms_state m1) {[ms_state m2]}.
Proof. move => [Hr] ??. naive_solver. Qed.

Lemma state_set_refines_step {EV} (m1 m2 : module EV) σi1 σs1 σi2 e:
  state_set_refines m1 m2 σi1 σs1 →
  m1.(m_step) σi1 e σi2 →
  state_set_refines m1 m2 σi2 {[ σ2 | ∃ σ1, σ1 ∈ σs1 ∧ σ1 ~{ m2, option_list (Vis <$> e) }~> (σ2 =.) ]}.
Proof.
  move => Hinv Hstep κs Hκs.
  have [|? [? /has_trace_app_inv?]]:= Hinv (option_list (Vis <$> e) ++ κs).
  (* have [|? [? ?]]:= Hinv (option_list (Vis <$> e) ++ κs). *)
  { by apply: TraceStep. }
  set_unfold.
  eexists _.
  split.
  eexists _. split => //. apply: has_trace_mono.
  done.
  move => ?/=.
Admitted.

Lemma state_set_refines_step_None {EV} (m1 m2 : module EV) σi1 σs1 σi2:
  state_set_refines m1 m2 σi1 σs1 →
  m1.(m_step) σi1 None σi2 →
  state_set_refines m1 m2 σi2 σs1.
Proof.
  move => Hinv Hstep κs Hκs.
  have [|? [? ?]]:= Hinv κs.
  { by apply: TraceStepNone. }
  set_solver.
Qed.

Lemma state_set_refines_non_empty {EV} (m1 m2 : module EV) σi σs:
  state_set_refines m1 m2 σi σs → ∃ σ, σ ∈ σs.
Proof.
  move => Hs.
  have [|?[??]]:= Hs []. by apply: TraceEnd.
  naive_solver.
Qed.

Lemma state_set_refines_ub {EV} (m1 m2 : module EV) σi σs:
  state_set_refines m1 m2 σi σs →
  m1.(m_is_ub) σi →
  ∃ σ, σ ∈ σs ∧ σ ~{ m2, [] }~> (λ _, False).
Proof.
  move => Hs Hub.
  have [|?[?/has_trace_ub_inv?]]:= Hs [Ub]. by apply: TraceUb.
  set_solver.
Qed.

Lemma refines_implies_inv_set {EV} (m1 m2 : mod_state EV):
  m1 ⊑ m2 →
  ∃ (inv : m1.(m_state) → propset m2.(m_state) → Prop),
  inv m1.(ms_state) {[ m2.(ms_state) ]} ∧
  (∀ σi σs, inv σi σs → ∃ σ, σ ∈ σs) ∧
  (∀ σi σs, inv σi σs → m1.(m_is_ub) σi → ∃ σs1, σs1 ∈ σs ∧ σs1 ~{ m2, [] }~> (λ _, False)) ∧
  (∀ σi1 σs1 σi2 e, inv σi1 σs1 → m1.(m_step) σi1 e σi2 →
      ∃ σs2, inv σi2 σs2 ∧ σs2 ⊆ {[ σ2 | ∃ σ1, σ1 ∈ σs1 ∧ σ1 ~{ m2, option_list (Vis <$> e) }~> (σ2 =.) ]}).
Proof.
  move => Href.
  eexists (state_set_refines m1 m2).
  split_and!.
  - by apply: state_set_refines_initial.
  - by apply: state_set_refines_non_empty.
  - move => σi σs Hinv Hub. by apply: state_set_refines_ub.
  - move => σi1 σs1 σi2 e Hinv Hstep.
    eexists _. split_and!; last reflexivity.
    by apply: state_set_refines_step.
Qed.
*)
(*** wp': equivalent definition of refines *)
Inductive wp' {EV} (m1 : module EV) (m2 : mod_state EV) : nat → m1.(m_state) -> list (event EV) -> Prop :=
| Wp_step' σi1 κs n:
       (∀ σi2 κ n', n = S n' → m_ub_step m1 σi1 κ σi2 ->
         m2.(ms_state) ~{ m2, κs ++ option_list κ }~> (λ _, True) ∧
         wp' m1 m2 n' σi2 (κs ++ option_list κ)) ->
    wp' m1 m2 n σi1 κs
.

Lemma wp'_weaken {EV} (m1 : module EV) m2 κs σ n n':
  n' ≤ n →
  wp' m1 m2 n σ κs →
  wp' m1 m2 n' σ κs.
Proof.
  elim: n' n σ κs.
  - move => ???? Hwp. constructor. done.
  - move => n' IH [|n] σ κs ? Hwp. lia.
    inversion Hwp as [??? Hwp']; simplify_eq.
    constructor => σi2 κ ?[?]?. subst.
    have [//|? ?]:= Hwp' σi2 κ _ ltac:(done).
    split; [done|]. apply: IH; [|done]. lia.
Qed.

Lemma forall_to_ex A B (P : A → B → Prop) (Q : B → Prop):
 (∃ n : A, ∀ y : B, P n y → Q y) -> ∀ y : B, ((∀ n : A, P n y) → Q y).
Proof. naive_solver. Qed.

Lemma wp'_implies_refines {EV} (m1 m2 : mod_state EV):
  (∀ n, wp' m1 m2 n m1.(ms_state) []) →
  m1 ⊑ m2.
Proof.
  move => Hwp.
  constructor => κs.
  move: m1.(ms_state) Hwp => σi1.
  have : (has_trace m2 m2.(ms_state) [] (λ _, True)). { by apply: TraceEnd. }
  (* move: {2}m2.(ms_state) => σs1. *)
  have : κs = [] ++ κs by [].
  move: ([]) => κstart. move: {2 3}(κs) => κend.
  move => Hκ Hs Hwp Hsteps.
  move: κstart Hwp Hκ Hs. apply: forall_to_ex.
  elim: Hsteps => {σi1 κend}.
  - move => σi1 ??. exists 0 => κstart Hwp Hκ Hs.
    by rewrite right_id in Hκ; subst.
  - move => σi1 σi2 σi3 κ κend Hstep Hsteps [n IH]. exists (S n) => κstart Hwp Hs Hκs.
    inversion_clear Hwp as [??? Hwp2]; subst.
    have [//|??]:= (Hwp2 _ _ n _ ltac:(by constructor)) => //.
    apply: IH; [done| |done].
    by rewrite assoc.
  - move => σ1 ???. exists 1 => ? Hwp ??.
    inversion_clear Hwp as [??? Hwp2]; subst.
    have [//|/has_trace_ub_app_inv? ?]:= (Hwp2 _ _ 0 _ ltac:(by constructor)) => //.
    by apply: has_trace_trans.
Qed.

Lemma refines_implies_wp' {EV} (m1 m2 : mod_state EV):
  m1 ⊑ m2 →
  (∀ n, wp' m1 m2 n m1.(ms_state) []).
Proof.
  move => [Hr] n.
  have : (has_trace m1 m1.(ms_state) [] (m1.(ms_state) =.)). { by apply: TraceEnd. }
  move: {2 3}(m1.(ms_state)) => σi.
  move: ([]) => κstart.
  elim/lt_wf_ind: n κstart σi.
  move => n IH κstart σi Hstepi.
  constructor => σi2 κ n' ? Hstep; subst.
  inversion Hstep; simplify_eq.
  - have : ms_state m1 ~{ m1, κstart ++ option_list (Vis <$> κ0) }~> eq σi2. {
      apply: has_trace_trans; [done|] => ? <-.
      rewrite -(right_id_L [] (++) (option_list _)).
      apply: TraceStep => //.
        by apply: TraceEnd.
    }
    split. { apply: Hr. by apply: has_trace_mono. }
      by apply: IH; [ lia|].
  - split.
    + apply: Hr.
      apply: has_trace_trans; [done|] => ? <-. by apply: TraceUb.
    + apply: IH; [lia|].
      apply: has_trace_trans; [done|] => ? <-. by apply: TraceUb.
Qed.

(*** Proving refinement *)
Lemma inv_implies_refines {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → m2.(m_state) → Prop):
  inv m1.(ms_state) m2.(ms_state) →
  (∀ σi1 σs1 σi2 e,
      inv σi1 σs1 → m_ub_step m1 σi1 e σi2 →
      σs1 ~{ m2, option_list e }~> (λ σs2, inv σi2 σs2)) →
  m1 ⊑ m2.
Proof.
  move => Hinvinit Hinvstep.
  constructor => // κs. move: m1.(ms_state) m2.(ms_state) Hinvinit => σi1 σs1 Hinv Hsteps.
  elim: Hsteps σs1 Hinv => {σi1 κs}.
  - by eauto using TraceEnd.
  - move => σi1 σi2 σi3 κ κs Hstep Hsteps IH σs1 Hinv.
    have ?:= (Hinvstep _ _ _ _ Hinv ltac:(by constructor)).
    apply: has_trace_trans; [done|] => ? /=?.
    by apply: IH.
  - move => ????? Hinv.
    have /has_trace_ub_inv ?:= (Hinvstep _ _ _ _ Hinv ltac:(by constructor)).
    by apply: (has_trace_trans []).
Qed.
(* This does not seem nice to work work. *)
Lemma inv_implies_refines_equiv {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → m2.(m_state) → Prop):
  inv m1.(ms_state) m2.(ms_state) →
  (∀ σi1 σs1 σi2 e, inv σi1 σs1 → m_ub_step m1 σi1 e σi2 →
      σs1 ~{ m2, option_list e }~> (λ σs2, inv σi2 σs2)) →
  (∀ σi1 σs1 σs2 e, inv σi1 σs1 → m_ub_step m2 σs1 e σs2 →
      σi1 ~{ m1, option_list e }~> (λ σi2, inv σi2 σs2)) →
  refines_equiv m1 m2.
Proof.
  move => Hinvinit Hinvstep1 Hinvstep2.
  split; [ apply: inv_implies_refines => //; naive_solver |].
  apply: (inv_implies_refines _ _ (flip inv)) => //=; naive_solver.
Qed.

(*
Lemma inv_implies_refines' {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → m2.(m_state) → Prop):
  inv m1.(ms_state) m2.(ms_state) →
  (∀ σi σs, inv σi σs → m1.(m_is_ub) σi → σs ~{ m2, [] }~> (λ _, False)) →
  (∀ σi1 σs1 σi2 e, inv σi1 σs1 → m1.(m_step) σi1 e σi2 →
      m1.(m_is_ub) σi1 ∨ σs1 ~{ m2, option_list (Vis <$> e) }~> (λ σs2, (inv σi2 σs2 ∨ has_no_behavior m1 σi2))) →
  m1 ⊑ m2.
Proof.
  move => Hinvinit Hinvsafe Hinvstep.
  constructor => // κs.
  move: m1.(ms_state) m2.(ms_state) Hinvinit => σi1 σs1 Hinv Hsteps.
  elim: Hsteps σs1 Hinv => {σi1 κs}.
  - by eauto using TraceEnd.
  - move => σi1 σi2 σi3 κ κs Hstep Hsteps IH σs1 Hinv.
    case: (Hinvstep _ _ _ _ Hinv Hstep) => [|?]. {
      move => /Hinvsafe Hub. apply: (has_trace_trans []); [naive_solver|].
      done.
    }
    apply: has_trace_trans; [done|] => ? [?| Hnb].
    + naive_solver.
    + move: Hsteps => /Hnb ->. by apply: TraceEnd.
  - move => ??? /Hinvsafe Hs σs Hinv.
    apply: (has_trace_trans []); naive_solver.
Qed.
 *)
(*
(* This does not seem nice to work work. *)
Lemma inv_implies_refines_equiv {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → m2.(m_state) → Prop):
  inv m1.(ms_state) m2.(ms_state) →
  (∀ σi σs, inv σi σs → m1.(m_is_ub) σi → σs ~{ m2, [] }~> (λ _, False)) →
  (∀ σi σs, inv σs σi → m2.(m_is_ub) σi → σs ~{ m1, [] }~> (λ _, False)) →
  (∀ σi1 σs1 σi2 e, inv σi1 σs1 → m1.(m_step) σi1 e σi2 →
      m1.(m_is_ub) σi1 ∨ σs1 ~{ m2, option_list (Vis <$> e) }~> (λ σs2, (inv σi2 σs2 ∨ has_no_behavior m1 σi2))) →
  (∀ σi1 σs1 σs2 e, inv σi1 σs1 → m2.(m_step) σs1 e σs2 →
      m2.(m_is_ub) σs1 ∨ σi1 ~{ m1, option_list (Vis <$> e) }~> (λ σi2, (inv σi2 σs2 ∨ has_no_behavior m2 σs2))) →
  refines_equiv m1 m2.
Proof.
  move => Hinvinit Hinvsafe1 Hinvsafe2 Hinvstep1 Hinvstep2.
  split; [ apply: inv_implies_refines' => //; naive_solver |].
  apply: (inv_implies_refines' _ _ (flip inv)) => //=; naive_solver.
Qed.
*)
(* This does not seem nice to work work. *)
(* Lemma link_merge_calls {EV1 EV2 EV3} (m1 : module EV1) (m2 : module EV2) (m3 : module EV3) (inv : m1.(m_state) → m2.(m_state) → m3.(m_state) → Prop) R : *)
(*   let R' e1 e2 e3 := if (e1, e2) is (None, None) then e3 = None else R e1 e2 e3 in *)
(*   inv m1.(m_initial) m2.(m_initial) m3.(m_initial) → *)
(*   (∀ σ1 σ2 σ3, inv σ1 σ2 σ3 → m3.(m_is_ub) σ3 ↔ (m1.(m_is_ub) σ1 ∨ m2.(m_is_ub) σ2)) → *)
(*   (∀ σ1 σ2 σ3, inv σ1 σ2 σ3 → ∀ e σ32, m_step m3 σ3 e σ32 → ∃ σ12 σ22, link_step m1 m2 R (σ1, σ2) e (σ12, σ22) ∧ inv σ12 σ22 σ32) → *)
(*   (∀ σ1 σ2 σ3, inv σ1 σ2 σ3 → ∀ e σ12 e', m_step m1 σ1 e σ12 → R' e None e' → ∃ σ32, m3.(m_step) σ3 e' σ32 ∧ inv σ12 σ2 σ32) → *)
(*   (∀ σ1 σ2 σ3, inv σ1 σ2 σ3 → ∀ e σ22 e', m_step m2 σ2 e σ22 → R' None e e' → ∃ σ32, m3.(m_step) σ3 e' σ32 ∧ inv σ1 σ22 σ32) → *)
(*   (∀ σ1 σ2 σ3, inv σ1 σ2 σ3 → ∀ e1 e2 σ12 σ22 e', m_step m1 σ1 (Some e1) σ12 → m_step m2 σ2 (Some e2) σ22 → R (Some e1) (Some e2) e' → ∃ σ32, m3.(m_step) σ3 e' σ32 ∧ inv σ12 σ22 σ32) → *)
(*   refines_equiv (link m1 m2 R) m3. *)
(* Proof. *)
(*   move => R' Hinit Hub Hmstep3 Hmstep1 Hmstep2 Hmstepboth. *)
(*   apply: (inv_implies_refines_equiv (link m1 m2 R) m3 (λ '(σ1, σ2) σ3, inv σ1 σ2 σ3)). *)
(*   - done. *)
(*   - move => [??] ?. naive_solver. *)
(*   - move => [σ11 σ21] σ31 [σ12 σ22] e Hinv Hstep. inversion Hstep; simplify_eq/=. *)
(*     + revert select (m_step _ _ _ _) => /(Hmstep1 _ _ _ Hinv) Hm3. *)
(*       destruct e1; simplify_eq; move: (Hm3 _ ltac:(done)) => [σ32 [? ?]]. *)
(*       all: eexists σ32; split => //; apply: has_trace_add_empty; apply: TraceStep => //; by apply: TraceEnd. *)
(*     + revert select (m_step _ _ _ _) => /(Hmstep2 _ _ _ Hinv) Hm3. *)
(*       destruct e2; simplify_eq; move: (Hm3 _ ltac:(done)) => [σ32 [? ?]]. *)
(*       all: eexists σ32; split => //; apply: has_trace_add_empty; apply: TraceStep => //; by apply: TraceEnd. *)
(*     + revert select (m_step _ _ _ _) => /(Hmstepboth _ _ _ Hinv) Hm3. *)
(*       revert select (m_step _ _ _ _) => /Hm3 {}Hm3. *)
(*       revert select (R _ _ _) => /Hm3 [σ32 [? ?]]. *)
(*       eexists σ32; split => //. *)
(*       apply: has_trace_add_empty. *)
(*       apply: TraceStep => //. *)
(*       by apply: TraceEnd. *)
(*   - move => [σ11 σ21] σ31 σ32 e Hinv /(Hmstep3 _ _ _ Hinv) [σ12 [σ22 [? ?]]]. *)
(*     eexists (σ12, σ22). split => //. *)
(*     apply: has_trace_add_empty. *)
(*     apply: TraceStep => //. *)
(*     by apply: TraceEnd. *)
(* Qed. *)

(*
Definition next_states {EV} (m : module EV) (σ : m.(m_state)) : propset (option (event EV) * m.(m_state)) :=
  {[ eσ | ∃ e, Vis <$> e = eσ.1 ∧ m.(m_step) σ e eσ.2 ]} ∪ {[ eσ | m.(m_is_ub) σ ]}.

Lemma in_next_states_has_trace {EV} (m : module EV) e σ1 σ2 :
  (e, σ2) ∈ next_states m σ1 → σ1 ~{ m, option_list e }~> σ2.
Proof.
  move => [[? /= [<- ?]]| ?].
  - apply: has_trace_add_empty. apply: TraceStep => //. by apply: TraceEnd.
  - by apply: TraceUb.
Qed.

Definition all_states_in {A B} (a : propset A) (e : propset B) (Φ : A → B → Prop) : Prop :=
  ∀ x, x ∈ a → ∃ y, y ∈ e ∧ Φ x y.

Definition all_states_in_equiv {A B} (a : propset A) (e : propset B) (Φ : A → B → Prop) : Prop :=
  all_states_in a e Φ ∧ all_states_in e a (flip Φ).

Global Instance all_states_in_proper {A B} : Proper ((≡) ==> (≡) ==> (pointwise_relation A (pointwise_relation B impl)) ==> impl) (@all_states_in A B).
Proof.
  move => a1 a2 Ha e1 e2 He Φ1 Φ2 HΦ Hall x. rewrite -Ha => Hx.
  case: (Hall _ Hx) => y. rewrite He => -[??]. eexists. split => //.
  by apply: HΦ.
Qed.

Global Instance all_states_in_equiv_proper {A B} : Proper ((≡) ==> (≡) ==> (pointwise_relation A (pointwise_relation B impl)) ==> impl) (@all_states_in_equiv A B).
Proof.
  move => ???????? HΦ [??]. split; [ by apply: all_states_in_proper|].
  apply: all_states_in_proper; [..| done] => //. move => ?? /=?. by apply: HΦ.
Qed.

Definition deterministic_step {EV} (m : module EV) (σ1 : m.(m_state)) (e : option EV) (σ2 : m.(m_state)) : Prop :=
  m.(m_step) σ1 e σ2 ∧ (∀ e' σ2', m.(m_step) σ1 e' σ2' → e' = e ∧ σ2' = σ2).

Lemma next_states_det {EV} (m : module EV) σ1 e σ2:
  deterministic_step m σ1 e σ2 → ¬ m.(m_is_ub) σ1 →
  next_states m σ1 ≡ {[(Vis <$> e, σ2)]}.
Proof.
  move => [Hdet1 Hdet2] Hub [??]. split.
  - move => [[?/=[<- /Hdet2 ?]]|//]. naive_solver.
  - move => [<- <-]. left. set_solver.
Qed.

Lemma next_states_empty {EV} (m : module EV) σ1:
  (¬ ∃ e σ2, m.(m_step) σ1 e σ2) → ¬ m.(m_is_ub) σ1 →
  next_states m σ1 ≡ ∅.
Proof. move => Hnotstep Hub [??]. split; set_solver. Qed.

Lemma all_states_in_equiv_singleton {A B} a e x y (Φ : A → B → Prop) :
  a ≡ {[ x ]} →
  e ≡ {[ y ]} →
  Φ x y →
  all_states_in_equiv a e Φ.
Proof. move => -> -> ?. split => ?; set_solver. Qed.

Lemma all_states_in_equiv_empty {A B} a e (Φ : A → B → Prop) :
  a ≡ ∅ →
  e ≡ ∅ →
  all_states_in_equiv a e Φ.
Proof. move => -> ->. split => ?; set_solver. Qed.

Lemma next_states_implies_refines {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → m2.(m_state) → Prop):
  inv m1.(ms_state) m2.(ms_state) →
  (∀ σi σs, inv σi σs → all_states_in (next_states m1 σi) (next_states m2 σs) (λ eσi2 eσs2,
      m2.(m_is_ub) σs ∨ (eσi2.1 = eσs2.1 ∧ (m2.(m_is_ub) eσs2.2 ∨ inv eσi2.2 eσs2.2)) )) →
  m1 ⊑ m2.
Proof.
  move => Hinvinit Hinvstep.
  constructor => // κs [σi2].
  move: m1.(ms_state) m2.(ms_state) Hinvinit => σi1 σs1 Hinv Hsteps.
  elim: Hsteps σs1 Hinv => {σi1 σi2 κs}.
  - by eauto using TraceEnd.
  - move => σi1 σi2 σi3 κ κs Hstep Hsteps IH σs1 Hinv.
    case: (Hinvstep _ _ Hinv (Vis<$> κ, σi2)). { set_solver. }
    move => [? σ2] [/in_next_states_has_trace ? /= [ Hub | [? Hor]]]; simplify_eq/=.
    { eexists _. by apply: TraceUbRefl. }
    case: Hor => [? | Hinv2]. { exists σ2. apply: has_trace_trans => //. by apply: TraceUb. }
    case: (IH _ Hinv2) => ? ?.
    eexists. by apply: has_trace_trans.
  - move => σi1 ?? ? σs Hinv.
    case: (Hinvstep _ _ Hinv (Some Ub, σi1)). { set_solver. }
    move => [? ?] [Hin [? |[??]]]; simplify_eq/=.
    { eexists _. by apply: TraceUbRefl. }
    eexists. apply: TraceUbRefl. case: Hin; [ | set_solver].
    by move => [[?|][/=??]].
Qed.

Lemma next_states_implies_refines_equiv {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → m2.(m_state) → Prop):
  inv m1.(ms_state) m2.(ms_state) →
  (∀ σi σs, inv σi σs → all_states_in_equiv (next_states m1 σi) (next_states m2 σs) (λ eσi2 eσs2,
      (m1.(m_is_ub) σi ∧ m2.(m_is_ub) σs) ∨ (eσi2.1 = eσs2.1 ∧ ((m1.(m_is_ub) eσi2.2 ∧ m2.(m_is_ub) eσs2.2) ∨ inv eσi2.2 eσs2.2)) )) →
  refines_equiv m1 m2.
Proof.
  move => Hinvinit Hinvstep.
  split.
  - apply: (next_states_implies_refines m1 m2 inv) => // σi σs Hinv.
    case: (Hinvstep _ _ Hinv) => ? _.
    apply: all_states_in_proper => // -[? ?] [??] /= ?. naive_solver.
  - apply: (next_states_implies_refines m2 m1 (flip inv)) => // σi σs Hinv.
    case: (Hinvstep _ _ Hinv) => _ ?.
    apply: all_states_in_proper => // -[? ?] [??] /= ?. naive_solver.
Qed.
*)
Inductive wp {EV} (m1 m2 : module EV) : nat → m1.(m_state) -> m2.(m_state) -> Prop :=
| Wp_step'' σi1 σs1 n:
    (∀ σi2 κ n', n = S n' → m_ub_step m1 σi1 κ σi2 -> ∃ Pσ2,
      σs1 ~{ m2, option_list κ }~> Pσ2 ∧
      ∀ σs2, Pσ2 σs2 → wp m1 m2 n' σi2 σs2) ->
    wp m1 m2 n σi1 σs1
.

Lemma Wp_step {EV} (m1 m2 : module EV) σi1 σs1 n:
    (∀ σi2 κ n', n = S n' → m_ub_step m1 σi1 κ σi2 ->
      σs1 ~{ m2, option_list κ }~> (λ σs2, wp m1 m2 n' σi2 σs2)) ->
    wp m1 m2 n σi1 σs1
.
Proof. move => ?. constructor. naive_solver. Qed.

Lemma wp_implies_refines {EV} (m1 m2 : mod_state EV):
  (∀ n, wp m1 m2 n m1.(ms_state) m2.(ms_state)) →
  m1 ⊑ m2.
Proof.
  move => Hwp.
  constructor => κs.
  move: m1.(ms_state) Hwp => σi1.
  move: m2.(ms_state) => σs1.
  move => Hwp Hsteps.
  move: σs1 Hwp. apply: forall_to_ex.
  elim: Hsteps => {σi1 κs}.
  - move => σi1. exists 0 => σs1 Hwp. by apply: TraceEnd.
  - move => σi1 σi2 σi3 κ κs Hstep Hsteps [n IH]. exists (S n) => σs1 Hwp.
    inversion_clear Hwp as [??? Hwp2]; subst.
    have [|?[??]]:= (Hwp2 _ _ n _ ltac:(by constructor)) => //.
    apply: has_trace_trans; naive_solver.
  - move => σ1 ???. exists 1 => ? Hwp.
    inversion_clear Hwp as [??? Hwp2]; subst.
    have [|?[/has_trace_ub_inv??]]:= (Hwp2 _ _ 0 _ ltac:(by constructor)) => //.
    by apply: (has_trace_trans []).
Qed.

Ltac invert_all_tac f :=
  let do_invert H := inversion H; clear H in
  repeat lazymatch goal with
         | H : f |- _ => do_invert H
         | H : f _ |- _ => do_invert H
         | H : f _ _|- _ => do_invert H
         | H : f _ _ _|- _ => do_invert H
         | H : f _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _ _ _ _ _|- _ => do_invert H
         end.

Tactic Notation "invert_all" constr(f) := invert_all_tac f; simplify_eq/=.
Tactic Notation "invert_all'" constr(f) := invert_all_tac f.


Ltac inv_step := invert_all' @m_ub_step; invert_all @m_step.

Definition module_empty {A} : module A := {|
  m_state := unit;
  m_step _ _ _ := False;
  m_is_ub s := False;
|}.
Global Instance module_empty_inst A : Empty (module A) := module_empty.

(*** Tests *)

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
Module test.

(*   2
  1 --- 2 (done)
 *)
Inductive mod1_step : bool → option nat → bool → Prop :=
| T1False: mod1_step false (Some 2) true.


Definition mod1 : module nat := {|
  m_state := bool;
  m_step := mod1_step;
  m_is_ub s:= False;
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
  m_step := mod2_step;
  m_is_ub s:= False;
|}.

Definition t2_to_t1_inv (σ1 : mod2_state) (σ2 : bool) : Prop :=
  σ2 = match σ1 with
  | S1 | S2 => false
  | _ => true
  end.
Lemma test_refines1 :
  MS mod2 S1 ⊑ MS mod1 false.
Proof.
  apply (inv_implies_refines (MS mod2 S1) (MS mod1 false) t2_to_t1_inv).
  - done.
  - move => σi1 σs1 σi2 e -> ?. inv_step => //.
    + by apply: TraceEnd.
    + apply: TraceStepSome; last by apply: TraceEnd. constructor.
Qed.

Definition mod_loop {A} : module A := {|
  m_state := unit;
  m_step _ e _ := e = None;
  m_is_ub s:= False;
|}.
Lemma test_refines2 {A} (m : mod_state A) :
  MS mod_loop tt ⊑ m.
Proof.
  apply: (inv_implies_refines (MS mod_loop tt) m (λ _ _, True)).
  - done.
  - move => ??????. inv_step => //. by apply: TraceEnd.
Qed.

Lemma test_refines2_wp {A} (m : mod_state A) :
  MS mod_loop tt ⊑ m.
Proof.
  apply: wp_implies_refines => /=.
  move => n. elim/lt_wf_ind: n => n Hloop.
  apply: Wp_step => -[]  κ n' ??.
  inv_step => //. apply: TraceEnd.
  naive_solver lia.
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
  m_step := stuck1_step;
  m_is_ub s:= s = S1S3;
|}.

Lemma test_refines_stuck1 :
  MS mod_stuck1 S1S1 ⊑ MS mod_stuck1 S1S1.
Proof.
  apply: (inv_implies_refines (MS mod_stuck1 S1S1) (MS mod_stuck1 S1S1) (λ σ1 σ2, σ1 = σ2 ∧ σ1 ≠ S1S3)).
  - done.
  - move => σi1 σs1 σi2 e [-> ?] ?. inv_step => //.
    + (* 1 -> 2 *) apply: TraceStepSome; last by apply: TraceEnd. constructor.
    + (* 1 -> 3 *)
      apply: TraceStepSome; [constructor|]. by constructor.
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
  m_step := stuck2_step;
  m_is_ub s:= s = S2S4;
|}.

Definition stuck2_inv (σ1 : stuck2_state) (σ2 : stuck1_state) :=
  (* We could prove an even stronger invariant with also σ1 ≠ S2S3
  since we don't need to reestablish it for a stuck source state. *)
  σ1 ≠ S2S4 ∧
  σ2 = match σ1 with | S2S1 => S1S1 | S2S2 => S1S2 | S2S3 => S1S3 | S2S4 => S1S1 end.

Lemma test_refines_stuck2 :
  MS mod_stuck2 S2S1 ⊑ MS mod_stuck1 S1S1.
Proof.
  apply: (inv_implies_refines (MS mod_stuck2 S2S1) (MS mod_stuck1 S1S1) stuck2_inv).
  - done.
  - move => σi1 σs1 σi2 e [? ->] ?. inv_step.
    + (* 1 -> 2 *) apply: TraceStepSome; last by constructor. constructor.
    + (* 1 -> 3 *) apply: TraceStepSome; last by constructor. constructor.
    + (* 3 -> 4 *) by apply: TraceUb.
Qed.

Lemma test_refines_stuck2_wp :
  MS mod_stuck2 S2S1 ⊑ MS mod_stuck1 S1S1.
Proof.
  apply: wp_implies_refines => n.
  (* S2S1 *)
  apply: Wp_step => σ2 ????. inv_step => //.
  - (* S2S2 *)
    apply: TraceStepSome; [ constructor |].
    apply: TraceEnd.
    apply: Wp_step => {}σ2 ????; inv_step.
  - (* S2S3 *)
    apply: TraceStepSome; [ constructor |].
    apply: TraceEnd.
    apply: Wp_step => {}σ2 ????; inv_step.
    by apply: TraceUb.
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
  m_step := stuck3_step;
  m_is_ub s:= s = S3S3;
|}.

Definition stuck3_inv (σ1 : stuck3_state) (σ2 : stuck1_state) :=
  σ1 ≠ S3S3 ∧
  σ2 = match σ1 with | S3S1 => S1S1 | S3S2 => S1S2 | S3S3 => S1S3 | S3S4 => S1S2 end.

(* The following is not provable: *)
Lemma test_refines_stuck3 :
  MS mod_stuck3 S3S1 ⊑ MS mod_stuck1 S1S1.
Proof.
  apply: (inv_implies_refines (MS mod_stuck3 S3S1) (MS mod_stuck1 S1S1) stuck3_inv).
  - done.
  - move => σi1 σs1 σi2 e [? ->] ?. inv_step.
    + (* 1 -> 2 *) apply: TraceStepSome; last by constructor. constructor.
    + (* 1 -> 3 *)
      apply: TraceStepSome; [ constructor|]. by apply: TraceUb.
    + (* 2 -> 4 *) apply: TraceStepSome; last by constructor.
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
  m_step := call1_step;
  m_is_ub s := False;
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
  m_step := call2_step;
  m_is_ub s := False;
|}.

Inductive call_merge_rel : option call_event → option (call_event + nat) → option nat → Prop :=
| CallMergeCall ev:
    call_merge_rel (Some ev) (Some (inl ev)) None
| CallMergeOut n:
    call_merge_rel None (Some (inr n)) (Some n).

Definition call_merge_inv (σ1 : bool * call2_state * unit) (σ2 : bool) :=
  match σ1.1.1, σ1.1.2 with
  | false, C2S3 => False
  | false, C2S2 _ => False
  | _, C2S2 n => n = 1
  | _, _ => True
  end ∧ σ2 = if σ1.1.2 is C2S3 then true else false.
Lemma test_refines_call_merge :
  MS (link mod_call1 mod_call2 (stateless_mediator call_merge_rel)) (false, C2S1, tt) ⊑ MS mod1 false.
Proof.
  apply: (inv_implies_refines (MS (link mod_call1 mod_call2 (stateless_mediator call_merge_rel)) (false, C2S1, tt)) (MS mod1 _) call_merge_inv).
  - done.
  - move => σi1 σs1 σi2 e [??] ?.
    inv_step; try match goal with | H : call_merge_rel _ _ _ |- _ => inversion H; clear H end; simplify_eq/=.
    + (* mod_call2 *)
      destruct σ0 => //. simplify_eq/=.
      apply: TraceStepSome; last by constructor. constructor.
    + (* mod_call1 *)
        by constructor.
    + naive_solver.
Qed.

Definition call_split_inv (σ1 : bool) (σ2 : bool * call2_state * unit) :=
  if σ1 then True else σ2 = (false, C2S1, tt).
Lemma test_refines_call_split :
  MS mod1 false ⊑ MS (link mod_call1 mod_call2 (stateless_mediator call_merge_rel)) (false, C2S1, tt).
Proof.
  apply: (inv_implies_refines (MS mod1 _) (MS (link mod_call1 mod_call2 (stateless_mediator call_merge_rel)) _) call_split_inv).
  - done.
  - move => σi1 [σs1 σs2] σi2 e Hinv ?. inv_step => //.
    apply: (TraceStepNone _ (link mod_call1 mod_call2 (stateless_mediator _)) (true, C2S2 1, tt)). {
      apply: LinkStepBoth. 3: constructor. all: constructor.
    }
    apply: TraceStepSome. 2: by constructor.
    apply: LinkStepR. constructor => //. simpl. constructor.
    Unshelve.
    constructor.
Qed.

Lemma test_refines_call_merge_wp :
  MS (link mod_call1 mod_call2 (stateless_mediator call_merge_rel)) (false, C2S1, tt) ⊑ MS mod1 false.
Proof.
  apply: (wp_implies_refines) => n.
  apply: Wp_step => σi1 n' ? ? Hstep. subst.
  inv_step; try match goal with | H : call_merge_rel _ _ _ |- _ => inversion H; clear H end; simplify_eq/=. 2: naive_solver.
  apply: TraceEnd.

  apply: Wp_step => σi1 n' ? ? Hstep. subst.
  inv_step; try match goal with | H : call_merge_rel _ _ _ |- _ => inversion H; clear H end; simplify_eq/=. 2: naive_solver.
  apply: TraceStepSome; [constructor| apply: TraceEnd].

  apply: Wp_step => σi1 n' ? ? Hstep. subst.
  inv_step; try match goal with | H : call_merge_rel _ _ _ |- _ => inversion H; clear H end; simplify_eq/=.
  naive_solver.
Qed.

Lemma test_refines_call_split_wp :
  MS mod1 false ⊑ MS (link mod_call1 mod_call2 (stateless_mediator call_merge_rel)) (false, C2S1, tt).
Proof.
  apply: (wp_implies_refines) => n.
  apply: Wp_step => σi1 n' ? ? Hstep. subst.
  inv_step => //.
  apply: (TraceStepNone _ (link mod_call1 mod_call2 (stateless_mediator _)) (true, C2S2 1, tt)). {
      apply: LinkStepBoth. 3: constructor. all: constructor.
    }
  apply: TraceStepSome. { apply: LinkStepR. constructor => //. simpl. constructor. }
  apply: TraceEnd.


  apply: Wp_step => σi1 n' ? ? Hstep. subst.
  inv_step => //.
  Unshelve. constructor.
Qed.

Definition call_equiv_inv (σ1 : bool * call2_state * unit) (σ2 : bool) :=
  match σ1, σ2 with
  | (false, C2S1, _), false => True
  | (true, C2S2 n, _), false => n = 1
  | (true, C2S3, _), true => True
  | _, _ => False
  end.

Lemma test_refines_call_equiv :
  refines_equiv (MS (link mod_call1 mod_call2 (stateless_mediator call_merge_rel)) (false, C2S1, tt)) (MS mod1 false).
Proof.
  apply: (inv_implies_refines_equiv (MS (link mod_call1 mod_call2 (stateless_mediator _)) _) (MS mod1 _) call_equiv_inv).
  - done.
  - move => σi1 σs1 σi2 e ? ?.
    inv_step; try match goal with | H : call_merge_rel _ _ _ |- _ => inversion H; clear H end; simplify_eq/=. 3: naive_solver.
    + destruct σ0, σs1 => //. simplify_eq.
      apply: TraceStepSome; [econstructor|]. by apply: TraceEnd.
    + destruct σs1 => //. by apply: TraceEnd.
  - move => [[σi11 σi12] ?] σs1 σi2 e ? ?. inv_step => //.
    destruct σi11, σi12 => //; simplify_eq.
    (* TODO: it is quite bad that we have two subproofs here while with the other methods we only have 1 *)
    + apply: TraceStepSome. { apply: LinkStepR. constructor => //. simpl. constructor. }
      by apply: TraceEnd.
    + apply: (TraceStepNone _ (link mod_call1 mod_call2 (stateless_mediator _)) (true, C2S2 1, tt)). {
        apply: LinkStepBoth. 3: constructor. all: constructor.
      }
      apply: TraceStepSome. { apply: LinkStepR. constructor => //. simpl. constructor. }
      by apply: TraceEnd.

      Unshelve. all: constructor.
Qed.

(* Definition call_equiv_inv2 (σ1 : bool) (σ2 : call2_state) (σ3 : mod2_state) := *)
(*   match σ1, σ2, σ3 with *)
(*   | false, C2S1, S1 => True *)
(*   | true, C2S2 n, S2 => n = 1 *)
(*   | true, C2S3, S3 => True *)
(*   | _, _, _ => False *)
(*   end. *)

(* Lemma test_refines_call_equiv' : *)
(*   refines_equiv (link mod_call1 mod_call2 call_merge_rel) mod2. *)
(* Proof. *)
(*   apply: (link_merge_calls mod_call1 mod_call2 mod2 call_equiv_inv2). *)
(*   - done. *)
(*   - naive_solver. *)
(*   - move => σ1 σ2 ? Hinv ???. inv_step; destruct σ1, σ2 => //. *)
(*     + eexists true, (C2S2 1). split => //. apply: LinkStepBoth. 3: constructor. all: constructor. *)
(*     + eexists true, C2S3. simplify_eq/=. split => //. apply: LinkStepR. by constructor. simpl. constructor. *)
(*   - move => ?????????. *)
(*     inv_step; match goal with | H : call_merge_rel _ _ _ |- _ => inversion H; clear H end; simplify_eq/=. *)
(*   - move => σ1 σ2 σ3 ??????. *)
(*     inv_step; match goal with | H : call_merge_rel _ _ _ |- _ => inversion H; clear H end; simplify_eq/=. *)
(*     destruct σ1, σ3 => //. simplify_eq/=. exists S3. split => //. constructor. *)
(*   - move => σ1 σ2 σ3 ?????????. *)
(*     match goal with | H : call_merge_rel _ _ _ |- _ => inversion H; clear H end; simplify_eq/=. *)
(*     match goal with | H : call1_step _ _ _ |- _ => inversion H; clear H end; simplify_eq/=. *)
(*     match goal with | H : call2_step _ _ _ |- _ => inversion H; clear H end; simplify_eq/=. *)
(*     destruct σ3 => //. eexists S2. split => //. constructor. *)
(* Qed. *)
(*
Definition call_equiv_inv2 (σ1 : bool * call2_state * unit) (σ2 : mod2_state) :=
  match σ1, σ2 with
  | (false, C2S1, _), S1 => True
  | (true, C2S2 n, _), S2 => n = 1
  | (true, C2S3, _), S3 => True
  | _, _ => False
  end.

Local Ltac solve_refines_call_next_equiv_det :=
  split; [ by repeat econstructor | move => ???; invert_all @m_step; destruct_hyps; by invert_all call_merge_rel].
Lemma test_refines_call_next_equiv :
  refines_equiv (MS (link mod_call1 mod_call2 (stateless_mediator call_merge_rel)) (false, C2S1, tt)) (MS mod2 S1).
Proof.
  apply (next_states_implies_refines_equiv (MS (link mod_call1 mod_call2 (stateless_mediator call_merge_rel)) _) (MS mod2 _) (call_equiv_inv2)).
  - done.
  - move => [[σi1 σi2] []] σs /=.
    destruct σi1, σi2, σs => //= [->|_|_].
    + apply: all_states_in_equiv_singleton;
        [ rewrite next_states_det; [done| solve_refines_call_next_equiv_det |naive_solver].. |].
      naive_solver.
    + apply: all_states_in_equiv_empty;
        (rewrite next_states_empty; [done | move => [?[??]]; inv_step | naive_solver]).
    + apply: all_states_in_equiv_singleton;
        [ rewrite next_states_det; [done| solve_refines_call_next_equiv_det |naive_solver].. |].
      naive_solver.
Qed.
*)

End test.