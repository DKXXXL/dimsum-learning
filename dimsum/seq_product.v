From dimsum.core Require Export proof_techniques.
From dimsum.core Require Import product state_transform.
From dimsum.core Require Import axioms.

(** * [seq_product] *)
Inductive seq_product_case :=
| SPLeft | SPRight | SPNone.

Global Instance seq_product_case_inhabited : Inhabited seq_product_case := populate SPNone.
Global Instance seq_product_eq_dec : EqDecision seq_product_case.
Proof. solve_decision. Qed.

Inductive seq_product_event EV1 EV2 :=
| SPELeft (e : EV1) (s : seq_product_case)
| SPERight (e : EV2) (s : seq_product_case)
| SPENone (s : seq_product_case).
Arguments SPELeft {_ _}.
Arguments SPERight {_ _}.
Arguments SPENone {_ _}.

Inductive seq_product_step {EV1 EV2} (m1 : mod_trans EV1) (m2 : mod_trans EV2) :
  (seq_product_case * m1.(m_state) * m2.(m_state)) →
  option (seq_product_event EV1 EV2) → (seq_product_case * m1.(m_state) * m2.(m_state) → Prop) → Prop :=
| SPNoneS σ1 σ2 s:
    seq_product_step m1 m2 (SPNone, σ1, σ2)
                 (Some (SPENone s))
                 (λ σ, σ = (s, σ1, σ2))
| SPLeftS e σ1 σ2 s Pσ:
  m1.(m_step) σ1 e Pσ →
  (if e is None then s = SPLeft else True) →
  seq_product_step m1 m2 (SPLeft, σ1, σ2)
    (if e is Some e' then Some (SPELeft e' s) else None)
    (λ '(s', σ1', σ2'), s = s' ∧ Pσ σ1' ∧ σ2 = σ2')
| SPRightS e σ1 σ2 s Pσ:
  m2.(m_step) σ2 e Pσ →
  (if e is None then s = SPRight else True) →
  seq_product_step m1 m2 (SPRight, σ1, σ2)
    (if e is Some e' then Some (SPERight e' s) else None)
    (λ '(s', σ1', σ2'), s = s' ∧ σ1 = σ1' ∧ Pσ σ2')
.

Definition seq_product_trans {EV1 EV2} (m1 : mod_trans EV1) (m2 : mod_trans EV2)
  : mod_trans (seq_product_event EV1 EV2) :=
  ModTrans (seq_product_step m1 m2).

Global Instance seq_product_vis_no_all {EV1 EV2} (m1 : mod_trans EV1) (m2 : mod_trans EV2) `{!VisNoAng m1} `{!VisNoAng m2}:
  VisNoAng (seq_product_trans m1 m2).
Proof.
  move => [[??]?]???. inv_all @m_step; try case_match => //; simplify_eq.
  - naive_solver.
  - have [??]:= vis_no_all _ _ _ ltac:(done). eexists (_, _, _) => -[[??]?]. naive_solver.
  - have [??]:= vis_no_all _ _ _ ltac:(done). eexists (_, _, _) => -[[??]?]. naive_solver.
Qed.

Definition seq_product_mod {EV1 EV2} (m1 : module EV1) (m2 : module EV2) (σp : seq_product_case)
  : module (seq_product_event EV1 EV2) :=
  Mod (seq_product_trans m1.(m_trans) m2.(m_trans)) (σp, m1.(m_init), m2.(m_init)).

(** ** trefines for [seq_product] *)
Inductive seq_product_rel {EV1 EV2} : seq_product_case → trace (seq_product_event EV1 EV2) → trace EV1 → trace EV2 → Prop :=
| SPR_nil s κs :
  tnil ⊆ κs →
  seq_product_rel s κs tnil tnil
| SPR_None s' κs κs' κs1 κs2:
  seq_product_rel s' κs' κs1 κs2 →
  tcons (SPENone s') κs' ⊆ κs →
  seq_product_rel SPNone κs κs1 κs2
| SPR_cons_l κ κs κs' κs1' κs2 s':
  seq_product_rel s' κs' κs1' κs2 →
  tcons (SPELeft κ s') κs' ⊆ κs →
  seq_product_rel SPLeft κs (tcons κ κs1') κs2
| SPR_cons_r κ κs κs' κs1' κs2 s':
  seq_product_rel s' κs' κs1' κs2 →
  tcons (SPERight κ s') κs' ⊆ κs →
  seq_product_rel SPRight κs κs1' (tcons κ κs2)
| SPR_ex1 T f κs κs2:
  (∀ x, seq_product_rel SPLeft κs (f x) κs2) →
  seq_product_rel SPLeft κs (tex T f) κs2
| SPR_ex2 T f κs κs2 :
  (∀ x, seq_product_rel SPRight κs κs2 (f x)) →
  seq_product_rel SPRight κs κs2 (tex T f)
| SPR_all1 {T} x f κs κs2 s:
  seq_product_rel s κs (f x) κs2 →
  seq_product_rel s κs (tall T f) κs2
| SPR_all2 {T} x f κs κs2 s:
  seq_product_rel s κs κs2 (f x) →
  seq_product_rel s κs κs2 (tall T f)
| SPR_all T f κs κs1 κs2 s:
  (∀ x, seq_product_rel s (f x) κs1 κs2) →
  (tall T f) ⊆ κs →
  seq_product_rel s κs κs1 κs2
.


Lemma seq_product_rel_mono {EV1 EV2} s κs κs' (κs1 : trace EV1) (κs2 : trace EV2) :
  seq_product_rel s κs κs1 κs2 →
  κs ⊆ κs' →
  seq_product_rel s κs' κs1 κs2.
Proof.
  move => Ht.
  elim: Ht κs'.
  - move => *. econs. by etrans.
  - move => *. econs. 2: by etrans. naive_solver.
  - move => *. econs. 2: by etrans. naive_solver.
  - move => *. econs. 2: by etrans. naive_solver.
  - move => *. econs. naive_solver.
  - move => *. econs. naive_solver.
  - move => *. econs. naive_solver.
  - move => *. econs. naive_solver.
  - move => *. econs. 2: by etrans. naive_solver.
Qed.


Lemma seq_product_to_mods {EV1 EV2} (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ Pσ κs `{!VisNoAng m1} `{!VisNoAng m2}:
  σ ~{ seq_product_trans m1 m2, κs }~>ₜ Pσ → ∃ κs', seq_product_rel σ.1.1 κs κs'.1 κs'.2 ∧
    σ.1.2 ~{ m1, κs'.1 }~>ₜ - ∧ σ.2 ~{ m2, κs'.2 }~>ₜ -.
Proof.
  elim.
  - move => [[s σ1] σ2] ????. eexists (tnil, tnil) => /=.
    split_and!.
    + by econs.
    + tend.
    + tend.
  - move => [[s σ1] σ2] ????? Hstep _ IH Hsub /=.
    inversion Hstep; simplify_eq/=.
    + have [κs'/= [?[??]]]:= IH _ ltac:(done).
      eexists κs'.
      split_and!.
      * by econs.
      * done.
      * done.
    + have {}IH := IH (s0, _, σ2) (conj ltac:(exact (eq_refl s0)) (conj _ ltac:(exact (eq_refl σ2)))).
      destruct e as [κ|].
      * have [σ' Hσ']:= vis_no_all _ _ _ ltac:(done).
        have /=[?[?[??]]]:= IH _ ltac:(naive_solver).
        eexists ((tcons κ _), _) => /=. split_and!.
        -- by econs.
        -- tstep_Some; [done|]. naive_solver.
        -- done.
      * have [f Hf]:= AxChoice1 IH.
        unshelve eexists ((tex _ (λ x, (f x).1)), (tall _ (λ x, (f x).2))) => /=.
        split_and!.
        -- apply: seq_product_rel_mono; [|done] => /=. econs => -[??]. econs. naive_solver.
        -- tstep_None; [done|] => σ' Hσ'. apply: (thas_trace_ex (exist _ σ' Hσ')). naive_solver.
        -- apply: thas_trace_all => -[??]. naive_solver.
    + have {}IH := IH (s0, σ1, _) (conj ltac:(exact (eq_refl s0)) (conj ltac:(exact (eq_refl σ1)) _)).
      destruct e as [κ|].
      * have [σ' Hσ']:= vis_no_all _ _ _ ltac:(done).
        have /=[?[?[??]]]:= IH _ ltac:(naive_solver).
        eexists (_, (tcons κ _)) => /=. split_and!.
        -- by econs.
        -- done.
        -- tstep_Some; [done|]. naive_solver.
      * have [f Hf]:= AxChoice1 IH.
        unshelve eexists ((tall _ (λ x, (f x).1)), (tex _ (λ x, (f x).2))) => /=.
        split_and!.
        -- apply: seq_product_rel_mono; [|done] => /=. econs => -[??]. econs. naive_solver.
        -- apply: thas_trace_all => -[??]. naive_solver.
        -- tstep_None; [done|] => σ' Hσ'. apply: (thas_trace_ex (exist _ σ' Hσ')). naive_solver.
  - move => T f ???? IH ?.
    have [fx Hfx]:= AxChoice _ _ _ IH.
    eexists (tall T (λ x, (fx x).1), tall T (λ x, (fx x).2)) => /=.
    split_and! => //.
    -- eapply SPR_all; [|done] => ?. econstructor. econstructor. naive_solver.
    -- apply: thas_trace_all. naive_solver.
    -- apply: thas_trace_all. naive_solver.
Qed.

Lemma seq_product_nil_l {EV1 EV2} (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2 Pσ κs:
  σ1 ~{ m1, κs }~>ₜ Pσ → κs ⊆ tnil →
  (SPLeft, σ1, σ2) ~{ seq_product_trans m1 m2, tnil }~>ₜ (λ σ', σ'.1.1 = SPLeft ∧ Pσ σ'.1.2 ∧ σ2 = σ'.2).
Proof.
  elim.
  - move => ??????. tend.
  - move => ??? κ ????? Hs1 Hs2. rewrite <-Hs1 in Hs2.
    destruct κ; [inversion Hs2|]; simplify_eq/=.
    tstep_None. { by eapply (SPLeftS _ _ None). }
    move => [[??]?] /=. naive_solver.
  - move => ??????? <-. move => /subtrace_all_nil_inv. naive_solver.
Qed.

Lemma seq_product_nil_r {EV1 EV2} (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2 Pσ κs:
  σ2 ~{ m2, κs }~>ₜ Pσ → κs ⊆ tnil →
  (SPRight, σ1, σ2) ~{ seq_product_trans m1 m2, tnil }~>ₜ (λ σ', σ'.1.1 = SPRight ∧ σ1 = σ'.1.2 ∧ Pσ σ'.2).
Proof.
  elim.
  - move => ??????. tend.
  - move => ??? κ ????? Hs1 Hs2. rewrite <-Hs1 in Hs2.
    destruct κ; [inversion Hs2|]; simplify_eq/=.
    tstep_None. { by eapply (SPRightS _ _ None). }
    move => [[??]?] /=. naive_solver.
  - move => ??????? <-. move => /subtrace_all_nil_inv. naive_solver.
Qed.

Lemma mods_to_seq_product {EV1 EV2} (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2 κs κs1 κs2 s:
  seq_product_rel s κs κs1 κs2 →
  σ1 ~{ m1, κs1 }~>ₜ - → σ2 ~{ m2, κs2 }~>ₜ - →
  (s, σ1, σ2) ~{ seq_product_trans m1 m2, κs }~>ₜ -.
Proof.
  move => Hrel.
  elim: Hrel σ1 σ2.
  - move => ???????. tend.
  - move => ?????? IH Hsub ????. rewrite -Hsub.
    tstep_Some. { econs. } naive_solver.
  - move => ??????? IH Hsub ??/(thas_trace_cons_inv _ _)??. rewrite -Hsub.
    apply: (thas_trace_trans tnil). { by apply: seq_product_nil_l. }
    move => [[??]?] /= [?[[?[??]]?]]. simplify_eq.
    tstep_Some. { by eapply (SPLeftS _ _ (Some _)). }
    move => [[??]?]. naive_solver.
  - move => ??????? IH Hsub ???/(thas_trace_cons_inv _ _)?. rewrite -Hsub.
    apply: (thas_trace_trans tnil). { by apply: seq_product_nil_r. }
    move => [[??]?] /= [?[?[?[??]]]]. simplify_eq.
    tstep_Some. { by eapply (SPRightS _ _ (Some _)). }
    move => [[??]?]. naive_solver.
  - move => ???????? /thas_trace_ex_inv ??.
    apply: (thas_trace_trans tnil). { by apply: seq_product_nil_l. }
    move => [[??]?] /=. naive_solver.
  - move => ????????? /thas_trace_ex_inv ?.
    apply: (thas_trace_trans tnil). { by apply: seq_product_nil_r. }
    move => [[??]?] /=. naive_solver.
  - move => ?????????? /thas_trace_all_inv??. naive_solver.
  - move => ??????????? /thas_trace_all_inv?. naive_solver.
  - move => ???????? Hsub ????. rewrite -Hsub.
    apply thas_trace_all. naive_solver.
Qed.

Lemma seq_product_mod_trefines {EV1 EV2} (m1 m1' : module EV1) (m2 m2' : module EV2) σp `{!VisNoAng m1.(m_trans)} `{!VisNoAng m2.(m_trans)}:
  trefines m1 m1' →
  trefines m2 m2' →
  trefines (seq_product_mod m1 m2 σp) (seq_product_mod m1' m2' σp).
Proof.
  move => [/=Hr1] [/=Hr2]. constructor => κs /= /seq_product_to_mods[κs1 [κs2 [/Hr1 ? /Hr2 ?]]].
  by apply: mods_to_seq_product.
Qed.

(** ** tstep *)
Lemma seq_product_trans_step_None_i {EV1 EV2} (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2:
  TStepI (seq_product_trans m1 m2) (SPNone, σ1, σ2) (λ G, ∀ s, G true (Some (SPENone s)) (λ G', G' (s, σ1, σ2))).
Proof.
  constructor => G HG. apply: steps_impl_step_end => ???. inv_all @m_step.
  eexists _, _. split_and!; [done..|]. naive_solver.
Qed.
Global Hint Resolve seq_product_trans_step_None_i : typeclass_instances.

Lemma seq_product_trans_step_l_i {EV1 EV2} (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2 P `{!TStepI m1 σ1 P}:
  TStepI (seq_product_trans m1 m2) (SPLeft, σ1, σ2) (λ G, P (λ b κ P',
    ∀ s', (if κ is None then s' = SPLeft else True) →
     G b ((λ e, SPELeft e s') <$> κ) (λ G', P' (λ x, G' (s', x, σ2))))).
Proof.
  constructor => G /(@tstepi_proof _ _ _ _ ltac:(done)) HP.
  apply: (steps_impl_submodule _ (seq_product_trans _ _) (λ x, (SPLeft, x, σ2))); [done| |].
  - move => ?? /= [?[?[HG[? HG']]]]. eexists _, _. split_and!; [by apply HG|done|] => ? /= /HG'[?[??]]. naive_solver.
  - move => ????. inv_all/= @m_step; eexists _, _.
    split_and!; [done| |naive_solver].
    move => [?[?[HG [? HG']]]]. eexists _, _. split_and!; [by apply HG|done|] => ? /= /HG'[?[??]]. naive_solver.
Qed.
Global Hint Resolve seq_product_trans_step_l_i : typeclass_instances.

Lemma seq_product_trans_step_r_i {EV1 EV2} (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2 P `{!TStepI m2 σ2 P}:
  TStepI (seq_product_trans m1 m2) (SPRight, σ1, σ2) (λ G, P (λ b κ P',
    ∀ s', (if κ is None then s' = SPRight else True) →
     G b ((λ e, SPERight e s') <$> κ) (λ G', P' (λ x, G' (s', σ1, x))))).
Proof.
  constructor => G /(@tstepi_proof _ _ _ _ ltac:(done)) HP.
  apply: (steps_impl_submodule _ (seq_product_trans _ _) (λ x, (SPRight, σ1, x))); [done| |].
  - move => ?? /= [?[?[HG [? HG']]]]. eexists _,_. split_and!; [by apply HG|done|] => ? /= /HG'[?[??]]. naive_solver.
  - move => ????. inv_all/= @m_step; eexists _, _.
    split_and!; [done| |naive_solver].
    move => [?[?[HG [? HG']]]]. eexists _, _. split_and!; [by apply HG|done|] => ? /= /HG'[?[??]]. naive_solver.
Qed.
Global Hint Resolve seq_product_trans_step_r_i : typeclass_instances.

Lemma seq_product_trans_step_None_s {EV1 EV2} (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2:
  TStepS (seq_product_trans m1 m2) (SPNone, σ1, σ2) (λ G, ∃ s, G (Some (SPENone s)) (λ G', G' (s, σ1, σ2))).
Proof.
  constructor => G [s HG]. eexists _, _. split; [done|]. move => ??.
  apply: steps_spec_step_end. { econs. }
  move => *. by simplify_eq/=.
Qed.
Global Hint Resolve seq_product_trans_step_None_s : typeclass_instances.

Lemma seq_product_trans_step_l_s {EV1 EV2} (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2 P `{!TStepS m1 σ1 P}:
  TStepS (seq_product_trans m1 m2) (SPLeft, σ1, σ2) (λ G, P (λ κ P',
    ∃ s', (if κ is None then s' = SPLeft else True) ∧ G ((λ e, SPELeft e s') <$> κ) (λ G',
       P' (λ σ, G' (s', σ, σ2))))).
Proof.
  constructor => G /(@tsteps_proof _ _ _ _ ltac:(done))[?[?[? HG']]]. destruct!.
  eexists _, _. split; [done|] => ?/= /HG' /steps_spec_has_trace_1 Ht.
  apply steps_spec_has_trace_elim.
  apply: thas_trace_mono; [ by apply: seq_product_nil_l |done|] => /= [[[??]?]?].
  case_match; destruct!/=. 2: apply steps_spec_end; naive_solver.
  apply: steps_spec_step_end. { by eapply (SPLeftS _ _ (Some _)). }
  move => [[??]?]? /=. naive_solver.
Qed.
Global Hint Resolve seq_product_trans_step_l_s : typeclass_instances.

Lemma seq_product_trans_step_r_s {EV1 EV2} (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2 P `{!TStepS m2 σ2 P}:
  TStepS (seq_product_trans m1 m2) (SPRight, σ1, σ2) (λ G, P (λ κ P',
    ∃ s', (if κ is None then s' = SPRight else True) ∧ G ((λ e, SPERight e s') <$> κ) (λ G',
       P' (λ σ, G' (s', σ1, σ))))).
Proof.
  constructor => G /(@tsteps_proof _ _ _ _ ltac:(done))[?[?[? HG']]]. destruct!.
  eexists _, _. split; [done|] => ?/= /HG' /steps_spec_has_trace_1 Ht.
  apply steps_spec_has_trace_elim.
  apply: thas_trace_mono; [ by apply: seq_product_nil_r |done|] => /= [[[??]?]?].
  case_match; destruct!/=. 2: apply steps_spec_end; naive_solver.
  apply: steps_spec_step_end. { by eapply (SPRightS _ _ (Some _)). }
  move => [[??]?]? /=. naive_solver.
Qed.
Global Hint Resolve seq_product_trans_step_r_s : typeclass_instances.

(** * [seq_map] *)
Inductive seq_map_case {EV1} :=
| SMProg
| SMProgRecv (e : EV1)
| SMFilter
| SMFilterRecv (e : EV1)
.
Arguments seq_map_case _ : clear implicits.

Inductive sm_event {EV1 EV2} :=
| SMERecv (e : EV1)
| SMEEmit (e : EV2)
| SMEReturn (e : option EV1).
Arguments sm_event _ _ : clear implicits.

Inductive seq_map_filter {EV1 EV2} :
  seq_map_case EV1 → (seq_product_event EV1 (sm_event EV1 EV2)) → option EV2 → seq_map_case EV1 → bool → Prop :=
| SeqMapToFilter e:
  seq_map_filter SMProg (SPELeft e SPRight) None (SMFilterRecv e) true
| SeqMapFilterRecv e:
  seq_map_filter (SMFilterRecv e) (SPERight (SMERecv e) SPRight) None SMFilter true
| SeqMapFilterOut e:
  seq_map_filter SMFilter (SPERight (SMEEmit e) SPRight) (Some e) SMFilter true
| SeqMapFilterToProg e:
  seq_map_filter SMFilter (SPERight (SMEReturn e) SPLeft) None
    (if e is Some e' then SMProgRecv e' else SMProg) true
| SeqMapProgRecv e:
  seq_map_filter (SMProgRecv e) (SPELeft e SPLeft) None SMProg true
.

Definition seq_map_state_trans {EV1 EV2} (m : mod_trans EV1) (f : mod_trans (sm_event EV1 EV2)) (σ : seq_map_case EV1 * m.(m_state) * f.(m_state)) :=
  (match σ.1.1 with
        | SMProg | SMProgRecv _ => SPLeft
        | SMFilter | SMFilterRecv _ => SPRight
        end, σ.1.2, σ.2, (σ.1.1, true)).
Arguments seq_map_state_trans _ _ _ /.
Global Instance seq_map_state_trans_inj {EV1 EV2} (m : mod_trans EV1) (f : mod_trans (sm_event EV1 EV2)) :
  Inj (=) (=) (seq_map_state_trans m f).
Proof. move => [[??]?] [[??]?] /=?. by simplify_eq. Qed.

Definition seq_map_trans {EV1 EV2} (m : mod_trans EV1) (f : mod_trans (sm_event EV1 EV2)) : mod_trans EV2 :=
  (state_transform_trans (map_trans (seq_product_trans m f) seq_map_filter)
                       (λ σ σ', σ' = seq_map_state_trans m f σ)).

Global Instance seq_map_trans_transform_wf {EV1 EV2} (m : mod_trans EV1) (f : mod_trans (sm_event EV1 EV2)) :
  StateTransformWf (map_trans (seq_product_trans m f) seq_map_filter)
                   (λ σ σ', σ' = seq_map_state_trans m f σ).
Proof.
  constructor; [naive_solver|].
  unfold seq_map_state_trans. move => [[??]?] [[[??]?]?] [[[??]?]?] ?????; simplify_eq.
  inv_all @m_step; inv_all @seq_map_filter; destruct!.
  all: eexists (_, _, _); do 3 f_equal;repeat case_match => //; by simplify_eq/=.
Qed.

Global Instance seq_map_vis_no_all {EV1 EV2} (m : mod_trans EV1) (f : mod_trans (sm_event EV1 EV2)) `{!VisNoAng m} `{!VisNoAng f}:
  VisNoAng (seq_map_trans m f).
Proof.
  apply: mod_state_transform_vis_no_all.
  move => ??? [[[sp σ1]σf][σ ?]] ??. eexists (σ, σ1, σf) => -[[??]?].
  inv_all @m_step; inv_all @seq_map_filter; destruct!.
  all: repeat case_match => //; simplify_eq/=.
  naive_solver.
Qed.

Definition seq_map_mod {EV1 EV2} (m : module EV1) (f : module (sm_event EV1 EV2)) (σ : seq_map_case EV1) : module EV2 :=
  Mod (seq_map_trans m.(m_trans) f.(m_trans)) (σ, m.(m_init), f.(m_init)).

Lemma seq_map_mod_trefines {EV1 EV2} (m1 m2 : module EV1) (f : module (sm_event EV1 EV2)) σ `{!VisNoAng m1.(m_trans)} `{!VisNoAng f.(m_trans)}:
  trefines m1 m2 →
  trefines (seq_map_mod m1 f σ) (seq_map_mod m2 f σ).
Proof.
  move => ?.
  eapply (state_transform_mod_trefines (Mod (map_trans _ _) _) (Mod (map_trans _ _) _)); [simpl; apply _| |done..].
  apply: (map_mod_trefines (Mod (seq_product_trans _ _) _) (Mod (seq_product_trans _ _) _)).
  by apply seq_product_mod_trefines.
Qed.

(*
Lemma mod_seq_map_nil_l {EV1 EV2} m (f : module (sm_event EV1 EV2)) σ Pσ Pσf σf κs σm:
  σ ~{ m, tnil }~>ₜ Pσ →
  (∀ σ', Pσ σ' → (SPLeft, σ', σf, σm) ~{ mod_seq_map m f, κs }~>ₜ Pσf) →
  (SPLeft, σ, σf, σm) ~{ mod_seq_map m f, κs }~>ₜ Pσf.
Proof.
  move => Hσ Hcont.
  apply: mod_map_nil.
  - by apply: seq_product_nil_l.
  - move => [[??]?] /=. naive_solver.
Qed.

Lemma mod_seq_map_nil_r {EV1 EV2} m (f : module (sm_event EV1 EV2)) σ Pσ Pσf σf κs σm:
  σf ~{ f, tnil }~>ₜ Pσ →
  (∀ σ', Pσ σ' → (SPRight, σ, σ', σm) ~{ mod_seq_map m f, κs }~>ₜ Pσf) →
  (SPRight, σ, σf, σm) ~{ mod_seq_map m f, κs }~>ₜ Pσf.
Proof.
  move => Hσ Hcont.
  apply: mod_map_nil.
  - by apply: seq_product_nil_r.
  - move => [[??]?] /=. naive_solver.
Qed.
*)

(** ** [mod_seq_map] tstep *)
Lemma seq_map_trans_step_filter_i {EV1 EV2} m (f : mod_trans (sm_event EV1 EV2)) σ σf P `{!TStepI f σf P} :
  TStepI (seq_map_trans m f) (SMFilter, σ, σf) (λ G, P (λ b κ P',
    match κ with
    | None => G b None (λ G', P' (λ x, G' (SMFilter, σ, x)))
    | Some (SMEEmit e) => G b (Some e) (λ G', P' (λ x, G' (SMFilter, σ, x)))
    | Some (SMEReturn e) => G b None (λ G', P' (λ x, G' (if e is Some e' then SMProgRecv e' else SMProg, σ, x)))
    | _ => True
    end)).
Proof.
  constructor => G /(@tstepi_proof _ _ _ _ ltac:(done))?. clear TStepI0.
  (* Set Typeclasses Debug. *)
  (* tstep_i. *)
  (* apply: steps_impl_mono; [done|]. *)
  (* move => ? κ ?/= [?[?[?[??]]]] ?? κ' ??. *)
  (* destruct κ as [[e|e]|]; simplify_eq/=. *)
  apply: (steps_impl_submodule _ (seq_map_trans _ _) (λ x, (SMFilter, σ, x))); [done| |].
  - naive_solver.
  - move => /= ??? Hs. inv_all @state_transform_step. inv_all/= @m_step.
    + case_match; simplify_eq. naive_solver.
    + case_match; simplify_eq. inv_all @seq_map_filter; try destruct e; naive_solver.
Qed.
Global Hint Resolve seq_map_trans_step_filter_i | 4 : typeclass_instances.

Lemma seq_map_trans_step_filter_recv_i {EV1 EV2} m (f : mod_trans (sm_event EV1 EV2)) σ σf P `{!TStepI f σf P} e :
  TStepI (seq_map_trans m f) (SMFilterRecv e, σ, σf) (λ G, P (λ b κ P',
       if κ is Some e' then SMERecv e = e' → G b None (λ G', P' (λ x, G' (SMFilter, σ, x)))
       else G b None (λ G', P' (λ x, G' (SMFilterRecv e, σ, x))))).
Proof.
  constructor => G /(@tstepi_proof _ _ _ _ ltac:(done))?.
  apply: (steps_impl_submodule _ (seq_map_trans _ _) (λ x, (SMFilterRecv e, σ, x))); [done| |].
  - naive_solver.
  - move => /= ??? Hs. inv_all @state_transform_step. inv_all/= @m_step.
    + case_match; simplify_eq. eexists _, _. split_and!;[done| |naive_solver] => /= ?.
      destruct!. eexists _, _. split_and!;[done..|]. move => ? /H3[?[??]].
      eexists (_, _, _). split!; [|done] => /=. done.
    + case_match; simplify_eq. eexists _, _. split_and!;[done| |naive_solver] => /= ?.
      inv_all @seq_map_filter. destruct!. eexists _, _. split_and!;[naive_solver..|].
      move => ? /H2[?[??]]. eexists (_, _, _). split!; [|done] => /=. done.
Qed.
Global Hint Resolve seq_map_trans_step_filter_recv_i | 4 : typeclass_instances.

Lemma seq_map_trans_step_prog_i {EV1 EV2} m (f : mod_trans (sm_event EV1 EV2)) σ σf P `{!TStepI m σ P}:
  TStepI (seq_map_trans m f) (SMProg, σ, σf) (λ G, P (λ b κ P',
   G b None (λ G', P' (λ x, if κ is Some e then G' (SMFilterRecv e, x, σf)
                            else G' (SMProg, x, σf))))).
Proof.
  constructor => G /(@tstepi_proof _ _ _ _ ltac:(done))?.
  apply: (steps_impl_submodule _ (seq_map_trans _ _) (λ x, (SMProg, x, σf))); [done| |].
  - naive_solver.
  - move => /= ??? Hs. inv_all @state_transform_step. inv_all/= @m_step.
    + case_match; simplify_eq. eexists _, _. split_and!;[done| |naive_solver] => /= ?.
      destruct!. eexists _, _. split_and!;[done..|]. move => ? /H3[?[??]].
      eexists (_, _, _). split!; [|done] => /=. done.
    + case_match; simplify_eq. eexists _, _. split_and!;[done| |naive_solver] => /= ?.
      inv_all @seq_map_filter. destruct!. eexists _, _. split_and!;[naive_solver..|].
      move => ? /H2[?[??]]. eexists (_, _, _). split!; [|done] => /=. done.
Qed.
Global Hint Resolve seq_map_trans_step_prog_i | 4 : typeclass_instances.

Lemma seq_map_trans_step_prog_recv_i {EV1 EV2} m (f : mod_trans (sm_event EV1 EV2)) σ σf P `{!TStepI m σ P} e:
  TStepI (seq_map_trans m f) (SMProgRecv e, σ, σf) (λ G, P (λ b κ P',
   if κ is Some e' then e = e' → G b None (λ G', P' (λ x, G' (SMProg, x, σf)))
                 else G b None (λ G', P' (λ x, G' (SMProgRecv e, x, σf))))).
Proof.
  constructor => G /(@tstepi_proof _ _ _ _ ltac:(done))?.
  apply: (steps_impl_submodule _ (seq_map_trans _ _) (λ x, (SMProgRecv e, x, σf))); [done| |].
  - naive_solver.
  - move => /= ??? Hs. inv_all @state_transform_step. inv_all/= @m_step.
    + case_match; simplify_eq. eexists _, _. split_and!;[done| |naive_solver] => /= ?.
      destruct!. eexists _, _. split_and!;[done..|]. move => ? /H3[?[??]].
      eexists (_, _, _). split!; [|done] => /=. done.
    + case_match; simplify_eq. eexists _, _. split_and!;[done| |naive_solver] => /= ?.
      inv_all @seq_map_filter. destruct!. eexists _, _. split_and!;[naive_solver..|].
      move => ? /H2[?[??]]. eexists (_, _, _). split!; [|done] => /=. done.
Qed.
Global Hint Resolve seq_map_trans_step_prog_recv_i | 4 : typeclass_instances.

Lemma seq_map_trans_step_filter_s {EV1 EV2} m (f : mod_trans (sm_event EV1 EV2)) σ σf P `{!TStepS f σf P} :
  TStepS (seq_map_trans m f) (SMFilter, σ, σf) (λ G, P (λ κ P',
    match κ with
    | None => G None (λ G', P' (λ x, G' (SMFilter, σ, x)))
    | Some (SMEEmit e) => G (Some e) (λ G', P' (λ x, G' (SMFilter, σ, x)))
    | Some (SMEReturn e) => G None (λ G', P' (λ x, G' (if e is Some e' then SMProgRecv e' else SMProg, σ, x)))
    | _ => False
    end)).
Proof.
  constructor => G /(@tsteps_proof _ _ _ _ ltac:(done)) [κ [? [? HG']]]. clear TStepS0.
  destruct κ as [[e|e|e]|]. 1: done. all: eexists _, _; split; [done|] => G' /= /HG'?; tstep_s.
  - eexists (Some (SMEEmit e)), _. split; [done|]. eexists _,_, _ => /=. split_and!; [econs|done|].
    apply: steps_spec_mono; [done|] => /= ? ? [[[|||]]]/=; naive_solver.
  - eexists (Some (SMEReturn e)), _. split; [done|]. eexists _,_, _ => /=. split_and!; [econs|done|].
    apply: steps_spec_mono; [done|] => /= ? ? [[[|||]]]/=; destruct e; naive_solver.
  - eexists None, _. split; [done|]. eexists _, _,_ => /=. split_and!; [done..|].
    apply: steps_spec_mono; [done|] => /= ? ? [[[|||]]]/=; naive_solver.
Qed.
Global Hint Resolve seq_map_trans_step_filter_s | 4 : typeclass_instances.

Lemma seq_map_trans_step_filter_recv_s {EV1 EV2} m (f : mod_trans (sm_event EV1 EV2)) σ σf P `{!TStepS f σf P} e:
  TStepS (seq_map_trans m f) (SMFilterRecv e, σ, σf) (λ G, P (λ κ P',
   G None (λ G', if κ is Some e' then SMERecv e = e' ∧ P' (λ x, G' (SMFilter, σ, x))
                 else P' (λ x, G' (SMFilterRecv e, σ, x))))).
Proof.
  constructor => G /(@tsteps_proof _ _ _ _ ltac:(done)) [κ [? [? HG']]]. eexists _, _. split; [done|].
  move => ? /=?. clear TStepS0. tstep_s. eexists κ, _. split; [by case_match|].
  case_match; destruct!; eexists _, _, _ => /=.
  - split_and!; [econs|done|].
    apply: steps_spec_mono; [naive_solver|] => /= ? ? [[[|||]]]/=; naive_solver.
  - split_and!; [done..|].
    apply: steps_spec_mono; [naive_solver|] => /= ? ? [[[|||]]]/=; naive_solver.
Qed.
Global Hint Resolve seq_map_trans_step_filter_recv_s | 4 : typeclass_instances.

Lemma seq_map_trans_step_prog_s {EV1 EV2} m (f : mod_trans (sm_event EV1 EV2)) σ σf P `{!TStepS m σ P}:
  TStepS (seq_map_trans m f) (SMProg, σ, σf) (λ G, P (λ κ P',
   G None (λ G', P' (λ x, if κ is Some e then G' (SMFilterRecv e, x, σf)
                          else G' (SMProg, x, σf))))).
Proof.
  constructor => G /(@tsteps_proof _ _ _ _ ltac:(done)) [κ [? [? HG']]]. eexists _, _. split; [done|].
  move => ? /=?. clear TStepS0. tstep_s.
  eexists κ; case_match; eexists _; (split; [done|]); eexists _, _, _ => /=.
  - split_and!; [econs|done|].
    apply: steps_spec_mono; [naive_solver|] => /= ? ? [[[|||]]]/=; naive_solver.
  - split_and!; [done..|].
    apply: steps_spec_mono; [naive_solver|] => /= ? ? [[[|||]]]/=; naive_solver.
Qed.
Global Hint Resolve seq_map_trans_step_prog_s | 4 : typeclass_instances.

Lemma seq_map_trans_step_prog_recv_s {EV1 EV2} m (f : mod_trans (sm_event EV1 EV2)) σ σf P `{!TStepS m σ P} e:
  TStepS (seq_map_trans m f) (SMProgRecv e, σ, σf) (λ G, P (λ κ P',
   G None (λ G', if κ is Some e' then e = e' ∧ P' (λ x, G' (SMProg, x, σf))
                 else P' (λ x, G' (SMProgRecv e, x, σf))))).
Proof.
  constructor => G /(@tsteps_proof _ _ _ _ ltac:(done)) [κ [? [? HG']]]. eexists _, _. split; [done|].
  move => ? /=?. clear TStepS0. tstep_s. eexists κ, _. split; [by case_match|].
  case_match; destruct!; eexists _, _, _ => /=.
  - split_and!; [econs|done|].
    apply: steps_spec_mono; [naive_solver|] => /= ? ? [[[|||]]]/=; naive_solver.
  - split_and!; [done..|].
    apply: steps_spec_mono; [naive_solver|] => /= ? ? [[[|||]]]/=; naive_solver.
Qed.
Global Hint Resolve seq_map_trans_step_prog_recv_s | 4 : typeclass_instances.
