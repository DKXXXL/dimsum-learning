Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.proof_techniques.
Require Import refframe.product.
Require Import refframe.filter.
Require Import refframe.state_transform.

(*** [seq_product] *)
Inductive seq_product_state :=
| SPLeft | SPRight | SPNone.
Inductive seq_product_event (EV1 EV2 : Type) :=
| SPELeft (e : EV1) (s : seq_product_state)
| SPERight (e : EV2) (s : seq_product_state)
| SPENone (s : seq_product_state).
Arguments SPELeft {_ _}.
Arguments SPERight {_ _}.
Arguments SPENone {_ _}.

Inductive seq_product_step {EV1 EV2} (m1 : module EV1) (m2 : module EV2) :
  (seq_product_state * m1.(m_state) * m2.(m_state)) →
  option (seq_product_event EV1 EV2) → (seq_product_state * m1.(m_state) * m2.(m_state) → Prop) → Prop :=
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

Definition mod_seq_product {EV1 EV2} (m1 : module EV1) (m2 : module EV2) : module (seq_product_event EV1 EV2) :=
  Mod (seq_product_step m1 m2).

Global Instance seq_product_vis_no_all {EV1 EV2} (m1 : module EV1) (m2 : module EV2) `{!VisNoAll m1} `{!VisNoAll m2}:
  VisNoAll (mod_seq_product m1 m2).
Proof.
  move => [[??]?]???. invert_all @m_step; try case_match => //; simplify_eq.
  - naive_solver.
  - have [??]:= vis_no_all _ _ _ ltac:(done). eexists (_, _, _) => -[[??]?]. naive_solver.
  - have [??]:= vis_no_all _ _ _ ltac:(done). eexists (_, _, _) => -[[??]?]. naive_solver.
Qed.

(*** trefines for [seq_product] *)
Inductive seq_product_rel {EV1 EV2} : seq_product_state → trace (seq_product_event EV1 EV2) → trace EV1 → trace EV2 → Prop :=
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
*)

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
  (*
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
*)
Qed.


Lemma seq_product_to_mods {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ Pσ κs `{!VisNoAll m1} `{!VisNoAll m2}:
  σ ~{ mod_seq_product m1 m2, κs }~>ₜ Pσ → ∃ κs', seq_product_rel σ.1.1 κs κs'.1 κs'.2 ∧
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
      * have [f Hf]:= CHOICE IH.
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
      * have [f Hf]:= CHOICE IH.
        unshelve eexists ((tall _ (λ x, (f x).1)), (tex _ (λ x, (f x).2))) => /=.
        split_and!.
        -- apply: seq_product_rel_mono; [|done] => /=. econs => -[??]. econs. naive_solver.
        -- apply: thas_trace_all => -[??]. naive_solver.
        -- tstep_None; [done|] => σ' Hσ'. apply: (thas_trace_ex (exist _ σ' Hσ')). naive_solver.
  - move => T f ???? IH ?.
    have [fx Hfx]:= AxCHOICE _ _ _ IH.
    eexists (tall T (λ x, (fx x).1), tall T (λ x, (fx x).2)) => /=.
    split_and! => //.
    -- eapply SPR_all; [|done] => ?. econstructor. econstructor. naive_solver.
    -- apply: thas_trace_all. naive_solver.
    -- apply: thas_trace_all. naive_solver.
Qed.

Lemma seq_product_nil_l {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ1 σ2 Pσ κs:
  σ1 ~{ m1, κs }~>ₜ Pσ → κs ⊆ tnil →
  (SPLeft, σ1, σ2) ~{ mod_seq_product m1 m2, tnil }~>ₜ (λ σ', σ'.1.1 = SPLeft ∧ Pσ σ'.1.2 ∧ σ2 = σ'.2).
Proof.
  elim.
  - move => ??????. tend.
  - move => ??? κ ????? Hs1 Hs2. rewrite <-Hs1 in Hs2.
    destruct κ; [inversion Hs2|]; simplify_eq/=.
    tstep_None. { by eapply (SPLeftS _ _ None). }
    move => [[??]?] /=. naive_solver.
  - move => ??????? <-. move => /subtrace_all_nil_inv. naive_solver.
Qed.

Lemma seq_product_nil_r {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ1 σ2 Pσ κs:
  σ2 ~{ m2, κs }~>ₜ Pσ → κs ⊆ tnil →
  (SPRight, σ1, σ2) ~{ mod_seq_product m1 m2, tnil }~>ₜ (λ σ', σ'.1.1 = SPRight ∧ σ1 = σ'.1.2 ∧ Pσ σ'.2).
Proof.
  elim.
  - move => ??????. tend.
  - move => ??? κ ????? Hs1 Hs2. rewrite <-Hs1 in Hs2.
    destruct κ; [inversion Hs2|]; simplify_eq/=.
    tstep_None. { by eapply (SPRightS _ _ None). }
    move => [[??]?] /=. naive_solver.
  - move => ??????? <-. move => /subtrace_all_nil_inv. naive_solver.
Qed.

Lemma mods_to_seq_product {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ1 σ2 κs κs1 κs2 s:
  seq_product_rel s κs κs1 κs2 →
  σ1 ~{ m1, κs1 }~>ₜ - → σ2 ~{ m2, κs2 }~>ₜ - →
  (s, σ1, σ2) ~{ mod_seq_product m1 m2, κs }~>ₜ -.
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

Lemma mod_seq_product_trefines {EV1 EV2} (m1 m1' : module EV1) (m2 m2' : module EV2) σ1 σ1' σ2 σ2' s `{!VisNoAll m1} `{!VisNoAll m2}:
  trefines (MS m1 σ1) (MS m1' σ1') →
  trefines (MS m2 σ2) (MS m2' σ2') →
  trefines (MS (mod_seq_product m1 m2) (s, σ1, σ2)) (MS (mod_seq_product m1' m2') (s, σ1', σ2')).
Proof.
  move => [/=Hr1] [/=Hr2]. constructor => κs /= /seq_product_to_mods[κs1 [κs2 [/Hr1 ? /Hr2 ?]]].
  by apply: mods_to_seq_product.
Qed.

(** * tstep *)
Lemma mod_seq_product_step_None_i {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ1 σ2:
  TStepI (mod_seq_product m1 m2) (SPNone, σ1, σ2) (λ G, ∀ s, G true (Some (SPENone s)) (λ G', G' (s, σ1, σ2))).
Proof.
  constructor => G HG. apply: steps_impl_step_end => ???. invert_all @m_step.
  eexists _, _. split_and!; [done..|]. naive_solver.
Qed.
Global Hint Resolve mod_seq_product_step_None_i : tstep.

Lemma mod_seq_product_step_l_i {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ1 σ2 P `{!TStepI m1 σ1 P}:
  TStepI (mod_seq_product m1 m2) (SPLeft, σ1, σ2) (λ G, P (λ b κ P',
    ∀ s', (if κ is None then s' = SPLeft else True) →
     G b ((λ e, SPELeft e s') <$> κ) (λ G', P' (λ x, G' (s', x, σ2))))).
Proof.
  constructor => G /tstepi_proof HP.
  apply: (steps_impl_submodule _ (mod_seq_product _ _) (λ x, (SPLeft, x, σ2))); [done| |].
  - move => ?? /= [?[?[HG[? HG']]]]. eexists _, _. split_and!; [by apply HG|done|] => ? /= /HG'[?[??]]. naive_solver.
  - move => ????. invert_all' @m_step; simplify_eq/=; eexists _, _.
    split_and!; [done| |naive_solver].
    move => [?[?[HG [? HG']]]]. eexists _, _. split_and!; [by apply HG|done|] => ? /= /HG'[?[??]]. naive_solver.
Qed.
Global Hint Resolve mod_seq_product_step_l_i : tstep.

Lemma mod_seq_product_step_r_i {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ1 σ2 P `{!TStepI m2 σ2 P}:
  TStepI (mod_seq_product m1 m2) (SPRight, σ1, σ2) (λ G, P (λ b κ P',
    ∀ s', (if κ is None then s' = SPRight else True) →
     G b ((λ e, SPERight e s') <$> κ) (λ G', P' (λ x, G' (s', σ1, x))))).
Proof.
  constructor => G /tstepi_proof HP.
  apply: (steps_impl_submodule _ (mod_seq_product _ _) (λ x, (SPRight, σ1, x))); [done| |].
  - move => ?? /= [?[?[HG [? HG']]]]. eexists _,_. split_and!; [by apply HG|done|] => ? /= /HG'[?[??]]. naive_solver.
  - move => ????. invert_all' @m_step; simplify_eq/=; eexists _, _.
    split_and!; [done| |naive_solver].
    move => [?[?[HG [? HG']]]]. eexists _, _. split_and!; [by apply HG|done|] => ? /= /HG'[?[??]]. naive_solver.
Qed.
Global Hint Resolve mod_seq_product_step_r_i : tstep.

Lemma mod_seq_product_step_None_s {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ1 σ2:
  TStepS (mod_seq_product m1 m2) (SPNone, σ1, σ2) (λ G, ∃ s, G (Some (SPENone s)) (λ G', G' (s, σ1, σ2))).
Proof.
  constructor => G [s HG]. eexists _, _. split; [done|]. move => ??.
  apply: steps_spec_step_end. { econs. }
  move => *. by simplify_eq/=.
Qed.
Global Hint Resolve mod_seq_product_step_None_s : tstep.

Lemma mod_seq_product_step_l_s {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ1 σ2 P `{!TStepS m1 σ1 P}:
  TStepS (mod_seq_product m1 m2) (SPLeft, σ1, σ2) (λ G, P (λ κ P',
    ∃ s', (if κ is None then s' = SPLeft else True) ∧ G ((λ e, SPELeft e s') <$> κ) (λ G',
       P' (λ σ, G' (s', σ, σ2))))).
Proof.
  constructor => G /tsteps_proof[?[?[? HG']]]. destruct_all!.
  eexists _, _. split; [done|] => ?/= /HG' /steps_spec_has_trace_1 Ht.
  apply steps_spec_has_trace_elim.
  apply: thas_trace_mono; [ by apply: seq_product_nil_l |done|] => /= [[[??]?]?].
  case_match; destruct_all?; simplify_eq/=. 2: apply steps_spec_end; naive_solver.
  apply: steps_spec_step_end. { by eapply (SPLeftS _ _ (Some _)). }
  move => [[??]?]? /=. naive_solver.
Qed.
Global Hint Resolve mod_seq_product_step_l_s : tstep.

Lemma mod_seq_product_step_r_s {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ1 σ2 P `{!TStepS m2 σ2 P}:
  TStepS (mod_seq_product m1 m2) (SPRight, σ1, σ2) (λ G, P (λ κ P',
    ∃ s', (if κ is None then s' = SPRight else True) ∧ G ((λ e, SPERight e s') <$> κ) (λ G',
       P' (λ σ, G' (s', σ1, σ))))).
Proof.
  constructor => G /tsteps_proof[?[?[? HG']]]. destruct_all!.
  eexists _, _. split; [done|] => ?/= /HG' /steps_spec_has_trace_1 Ht.
  apply steps_spec_has_trace_elim.
  apply: thas_trace_mono; [ by apply: seq_product_nil_r |done|] => /= [[[??]?]?].
  case_match; destruct_all?; simplify_eq/=. 2: apply steps_spec_end; naive_solver.
  apply: steps_spec_step_end. { by eapply (SPRightS _ _ (Some _)). }
  move => [[??]?]? /=. naive_solver.
Qed.
Global Hint Resolve mod_seq_product_step_r_s : tstep.

(*** [mod_seq_map] *)
Inductive mod_seq_map_state {EV1 : Type} :=
| SMProg
| SMProgRecv (e : EV1)
| SMFilter
| SMFilterRecv (e : EV1)
.
Arguments mod_seq_map_state _ : clear implicits.

Inductive mod_seq_map_filter {EV1 EV2} :
  mod_seq_map_state EV1 → (seq_product_event EV1 (EV1 + EV2)) → option EV2 → mod_seq_map_state EV1 → Prop :=
| SeqMapToFilter e:
  mod_seq_map_filter SMProg (SPELeft e SPRight) None (SMFilterRecv e)
| SeqMapFilterRecv e:
  mod_seq_map_filter (SMFilterRecv e) (SPERight (inl e) SPRight) None SMFilter
| SeqMapFilterOut e:
  mod_seq_map_filter SMFilter (SPERight (inr e) SPRight) (Some e) SMFilter
| SeqMapFilterToProg e:
  mod_seq_map_filter SMFilter (SPERight (inl e) SPLeft) (None) (SMProgRecv e)
| SeqMapProgRecv e:
  mod_seq_map_filter (SMProgRecv e) (SPELeft e SPLeft) None SMProg
.

Definition mod_seq_map_trans {EV1 EV2} (m : module EV1) (f : module (EV1 + EV2)) (σ : mod_seq_map_state EV1 * m.(m_state) * f.(m_state)) :=
  (match σ.1.1 with
        | SMProg | SMProgRecv _ => SPLeft
        | SMFilter | SMFilterRecv _ => SPRight
        end, σ.1.2, σ.2, σ.1.1).
Arguments mod_seq_map_trans _ _ _ /.
Global Instance mod_seq_map_trans_inj {EV1 EV2} (m : module EV1) (f : module (EV1 + EV2)) :
  Inj (=) (=) (mod_seq_map_trans m f).
Proof. move => [[??]?] [[??]?] /=?. by simplify_eq. Qed.

Definition mod_seq_map {EV1 EV2} (m : module EV1) (f : module (EV1 + EV2)) : module EV2 :=
  (mod_state_transform (mod_map (mod_seq_product m f) mod_seq_map_filter)
                       (λ σ σ', σ' = mod_seq_map_trans m f σ)).

Global Instance mod_seq_map_vis_no_all {EV1 EV2} (m : module EV1) (f : module (EV1 + EV2)) `{!VisNoAll m} `{!VisNoAll f}:
  VisNoAll (mod_seq_map m f).
Proof.
  apply: mod_state_transform_vis_no_all.
  move => ??? [[[sp σ1]σf]σ] ??. eexists (σ, σ1, σf) => -[[??]?].
  invert_all @m_step; invert_all @mod_seq_map_filter; destruct_all?; simplify_eq.
  all: repeat case_match => //; simplify_eq/=.
  naive_solver.
Qed.

Lemma mod_seq_map_trefines {EV1 EV2} (m1 m2 : module EV1) (f : module (EV1 + EV2)) σ1 σ2 σ σf `{!VisNoAll m1} `{!VisNoAll f}:
  trefines (MS m1 σ1) (MS m2 σ2) →
  trefines (MS (mod_seq_map m1 f) (σ, σ1, σf)) (MS (mod_seq_map m2 f) (σ, σ2, σf)).
Proof.
  move => ?.
  apply: mod_state_transform_trefines; [| | |done..].
  - move => [[??]?] [[[??]?]?] [[[??]?]?]. unfold mod_seq_map_trans. naive_solver.
  - unfold mod_seq_map_trans. move => [[??]?] [[[??]?]?] [[[??]?]?] ?????; simplify_eq.
    invert_all @m_step; invert_all @mod_seq_map_filter; destruct_all?; simplify_eq.
    all: eexists (_, _, _); do 3 f_equal;repeat case_match => //; by simplify_eq/=.
  - apply mod_map_trefines. by apply mod_seq_product_trefines.
Qed.

(*
Lemma mod_seq_map_nil_l {EV1 EV2} m (f : module (EV1 + EV2)) σ Pσ Pσf σf κs σm:
  σ ~{ m, tnil }~>ₜ Pσ →
  (∀ σ', Pσ σ' → (SPLeft, σ', σf, σm) ~{ mod_seq_map m f, κs }~>ₜ Pσf) →
  (SPLeft, σ, σf, σm) ~{ mod_seq_map m f, κs }~>ₜ Pσf.
Proof.
  move => Hσ Hcont.
  apply: mod_map_nil.
  - by apply: seq_product_nil_l.
  - move => [[??]?] /=. naive_solver.
Qed.

Lemma mod_seq_map_nil_r {EV1 EV2} m (f : module (EV1 + EV2)) σ Pσ Pσf σf κs σm:
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

Lemma mod_seq_map_step_filter_i {EV1 EV2} m (f : module (EV1 + EV2)) σ σf P `{!TStepI f σf P} :
  TStepI (mod_seq_map m f) (SMFilter, σ, σf) (λ G, P (λ b κ P',
    match κ with
    | None => G b None (λ G', P' (λ x, G' (SMFilter, σ, x)))
    | Some (inr e) => G b (Some e) (λ G', P' (λ x, G' (SMFilter, σ, x)))
    | Some (inl e) => G b None (λ G', P' (λ x, G' (SMProgRecv e, σ, x)))
    end)).
Proof.
  constructor => G /tstepi_proof?. clear TStepI0.
  (* Set Typeclasses Debug. *)
  (* tstep_i. *)
  (* apply: steps_impl_mono; [done|]. *)
  (* move => ? κ ?/= [?[?[?[??]]]] ?? κ' ??. *)
  (* destruct κ as [[e|e]|]; simplify_eq/=. *)
  apply: (steps_impl_submodule _ (mod_seq_map _ _) (λ x, (SMFilter, σ, x))); [done| |].
  - naive_solver.
  - move => /= ??? Hs. invert_all' @state_transform_step; simplify_eq. invert_all' @m_step; simplify_eq/=.
    + case_match; simplify_eq. naive_solver.
    + case_match; simplify_eq. invert_all @mod_seq_map_filter; naive_solver.
Qed.
Global Hint Resolve mod_seq_map_step_filter_i | 1 : tstep.

Lemma mod_seq_map_step_filter_recv_i {EV1 EV2} m (f : module (EV1 + EV2)) σ σf P `{!TStepI f σf P} e :
  TStepI (mod_seq_map m f) (SMFilterRecv e, σ, σf) (λ G, P (λ b κ P',
       if κ is Some e' then inl e = e' → G b None (λ G', P' (λ x, G' (SMFilter, σ, x)))
       else G b None (λ G', P' (λ x, G' (SMFilterRecv e, σ, x))))).
Proof.
  constructor => G /tstepi_proof?.
  apply: (steps_impl_submodule _ (mod_seq_map _ _) (λ x, (SMFilterRecv e, σ, x))); [done| |].
  - naive_solver.
  - move => /= ??? Hs. invert_all' @state_transform_step; simplify_eq. invert_all' @m_step; simplify_eq/=.
    + case_match; simplify_eq. eexists _, _. split_and!;[done| |naive_solver] => /= ?.
      destruct_all?. eexists _, _. split_and!;[done..|]. move => ? /H2[?[??]].
      eexists (_, _, _). split!; [|done] => /=. done.
    + case_match; simplify_eq. eexists _, _. split_and!;[done| |naive_solver] => /= ?.
      invert_all @mod_seq_map_filter. destruct_all?. eexists _, _. split_and!;[naive_solver..|].
      move => ? /H2[?[??]]. eexists (_, _, _). split!; [|done] => /=. done.
Qed.
Global Hint Resolve mod_seq_map_step_filter_recv_i | 1 : tstep.

Lemma mod_seq_map_step_prog_i {EV1 EV2} m (f : module (EV1 + EV2)) σ σf P `{!TStepI m σ P}:
  TStepI (mod_seq_map m f) (SMProg, σ, σf) (λ G, P (λ b κ P',
   G b None (λ G', P' (λ x, if κ is Some e then G' (SMFilterRecv e, x, σf)
                            else G' (SMProg, x, σf))))).
Proof.
  constructor => G /tstepi_proof?.
  apply: (steps_impl_submodule _ (mod_seq_map _ _) (λ x, (SMProg, x, σf))); [done| |].
  - naive_solver.
  - move => /= ??? Hs. invert_all' @state_transform_step; simplify_eq. invert_all' @m_step; simplify_eq/=.
    + case_match; simplify_eq. eexists _, _. split_and!;[done| |naive_solver] => /= ?.
      destruct_all?. eexists _, _. split_and!;[done..|]. move => ? /H2[?[??]].
      eexists (_, _, _). split!; [|done] => /=. done.
    + case_match; simplify_eq. eexists _, _. split_and!;[done| |naive_solver] => /= ?.
      invert_all @mod_seq_map_filter. destruct_all?. eexists _, _. split_and!;[naive_solver..|].
      move => ? /H2[?[??]]. eexists (_, _, _). split!; [|done] => /=. done.
Qed.
Global Hint Resolve mod_seq_map_step_prog_i | 1 : tstep.

Lemma mod_seq_map_step_prog_recv_i {EV1 EV2} m (f : module (EV1 + EV2)) σ σf P `{!TStepI m σ P} e:
  TStepI (mod_seq_map m f) (SMProgRecv e, σ, σf) (λ G, P (λ b κ P',
   if κ is Some e' then e = e' → G b None (λ G', P' (λ x, G' (SMProg, x, σf)))
                 else G b None (λ G', P' (λ x, G' (SMProgRecv e, x, σf))))).
Proof.
  constructor => G /tstepi_proof?.
  apply: (steps_impl_submodule _ (mod_seq_map _ _) (λ x, (SMProgRecv e, x, σf))); [done| |].
  - naive_solver.
  - move => /= ??? Hs. invert_all' @state_transform_step; simplify_eq. invert_all' @m_step; simplify_eq/=.
    + case_match; simplify_eq. eexists _, _. split_and!;[done| |naive_solver] => /= ?.
      destruct_all?. eexists _, _. split_and!;[done..|]. move => ? /H2[?[??]].
      eexists (_, _, _). split!; [|done] => /=. done.
    + case_match; simplify_eq. eexists _, _. split_and!;[done| |naive_solver] => /= ?.
      invert_all @mod_seq_map_filter. destruct_all?. eexists _, _. split_and!;[naive_solver..|].
      move => ? /H2[?[??]]. eexists (_, _, _). split!; [|done] => /=. done.
Qed.
Global Hint Resolve mod_seq_map_step_prog_recv_i | 1 : tstep.

Lemma mod_seq_map_step_filter_s {EV1 EV2} m (f : module (EV1 + EV2)) σ σf P `{!TStepS f σf P} :
  TStepS (mod_seq_map m f) (SMFilter, σ, σf) (λ G, P (λ κ P',
    match κ with
    | None => G None (λ G', P' (λ x, G' (SMFilter, σ, x)))
    | Some (inr e) => G (Some e) (λ G', P' (λ x, G' (SMFilter, σ, x)))
    | Some (inl e) => G None (λ G', P' (λ x, G' (SMProgRecv e, σ, x)))
    end)).
Proof.
  constructor => G /tsteps_proof [κ [? [? HG']]]. clear TStepS0.
  destruct κ as [[e|e]|]. all: eexists _, _; split; [done|] => G' /= /HG'?; tstep_s.
  - eexists (Some (inl e)), _. split; [done|]. eexists _, _ => /=. split_and!; [econs|done|].
    apply: steps_spec_mono; [done|] => /= ? ? [[[|||]]]/=; naive_solver.
  - eexists (Some (inr e)), _. split; [done|]. eexists _, _ => /=. split_and!; [econs|done|].
    apply: steps_spec_mono; [done|] => /= ? ? [[[|||]]]/=; naive_solver.
  - eexists None, _. split; [done|]. eexists _, _ => /=. split_and!; [done..|].
    apply: steps_spec_mono; [done|] => /= ? ? [[[|||]]]/=; naive_solver.
Qed.
Global Hint Resolve mod_seq_map_step_filter_s | 1 : tstep.

Lemma mod_seq_map_step_filter_recv_s {EV1 EV2} m (f : module (EV1 + EV2)) σ σf P `{!TStepS f σf P} e:
  TStepS (mod_seq_map m f) (SMFilterRecv e, σ, σf) (λ G, P (λ κ P',
   G None (λ G', if κ is Some e' then inl e = e' ∧ P' (λ x, G' (SMFilter, σ, x))
                 else P' (λ x, G' (SMFilterRecv e, σ, x))))).
Proof.
  constructor => G /tsteps_proof [κ [? [? HG']]]. eexists _, _. split; [done|].
  move => ? /=?. clear TStepS0. tstep_s. eexists κ, _. split; [by case_match|].
  case_match; destruct_all?; simplify_eq; eexists _, _ => /=.
  - split_and!; [econs|done|].
    apply: steps_spec_mono; [naive_solver|] => /= ? ? [[[|||]]]/=; naive_solver.
  - split_and!; [done..|].
    apply: steps_spec_mono; [naive_solver|] => /= ? ? [[[|||]]]/=; naive_solver.
Qed.
Global Hint Resolve mod_seq_map_step_filter_recv_s | 1 : tstep.

Lemma mod_seq_map_step_prog_s {EV1 EV2} m (f : module (EV1 + EV2)) σ σf P `{!TStepS m σ P}:
  TStepS (mod_seq_map m f) (SMProg, σ, σf) (λ G, P (λ κ P',
   G None (λ G', P' (λ x, if κ is Some e then G' (SMFilterRecv e, x, σf)
                          else G' (SMProg, x, σf))))).
Proof.
  constructor => G /tsteps_proof [κ [? [? HG']]]. eexists _, _. split; [done|].
  move => ? /=?. clear TStepS0. tstep_s.
  eexists κ; case_match; eexists _; (split; [done|]); eexists _, _ => /=.
  - split_and!; [econs|done|].
    apply: steps_spec_mono; [naive_solver|] => /= ? ? [[[|||]]]/=; naive_solver.
  - split_and!; [done..|].
    apply: steps_spec_mono; [naive_solver|] => /= ? ? [[[|||]]]/=; naive_solver.
Qed.
Global Hint Resolve mod_seq_map_step_prog_s | 1 : tstep.

Lemma mod_seq_map_step_prog_recv_s {EV1 EV2} m (f : module (EV1 + EV2)) σ σf P `{!TStepS m σ P} e:
  TStepS (mod_seq_map m f) (SMProgRecv e, σ, σf) (λ G, P (λ κ P',
   G None (λ G', if κ is Some e' then e = e' ∧ P' (λ x, G' (SMProg, x, σf))
                 else P' (λ x, G' (SMProgRecv e, x, σf))))).
Proof.
  constructor => G /tsteps_proof [κ [? [? HG']]]. eexists _, _. split; [done|].
  move => ? /=?. clear TStepS0. tstep_s. eexists κ, _. split; [by case_match|].
  case_match; destruct_all?; simplify_eq; eexists _, _ => /=.
  - split_and!; [econs|done|].
    apply: steps_spec_mono; [naive_solver|] => /= ? ? [[[|||]]]/=; naive_solver.
  - split_and!; [done..|].
    apply: steps_spec_mono; [naive_solver|] => /= ? ? [[[|||]]]/=; naive_solver.
Qed.
Global Hint Resolve mod_seq_map_step_prog_recv_s | 1 : tstep.
