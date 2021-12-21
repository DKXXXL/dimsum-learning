Require Export refframe.module.
Require Import refframe.trefines.

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