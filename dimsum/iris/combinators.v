From dimsum.core Require Import product seq_product state_transform prepost.
From dimsum.core.iris Require Import sat.
From dimsum.core.iris Require Export sim.
Set Default Proof Using "Type".

(** * map_mod *)

Section map.
  Context {Σ : gFunctors} {EV1 EV2 : Type} {S : Type} `{!dimsumGS Σ}.
  Implicit Types (f : map_mod_fn EV1 EV2 S).

  Lemma sim_tgt_map m f σ σf Π :
    (σ ≈{m}≈>ₜ λ κ Pσ,
      ∀ κ' σf' ok, ⌜if κ is Some e then f σf e κ' σf' ok else κ' = None ∧ σf' = σf ∧ ok = true⌝ -∗
         Π κ' (λ P, Pσ (λ σ', P (σ', (σf', ok))))) -∗
    (σ, (σf, true)) ≈{map_trans m f}≈>ₜ Π.
  Proof.
    iIntros "Hsim".
    pose (F := (λ σ Π', (∀ κ Pσ, Π' κ Pσ -∗
         ∀ κ' σf' ok, ⌜if κ is Some e then f σf e κ' σf' ok else κ' = None ∧ σf' = σf ∧ ok = true⌝ -∗
          Π κ' (λ P, Pσ (λ σ', P (σ', (σf', ok))))) -∗ (σ, (σf, true)) ≈{map_trans m f}≈>ₜ Π)%I).
    iAssert (∀ Π, σ ≈{ m }≈>ₜ Π -∗ F σ Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"). iIntros (??) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_tgt_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros "Hc".
    iApply (sim_tgt_ctx with "[-]"). iIntros "?".
    iApply (sim_tgt_bi_mono1 with "[-]").
    iApply (fupd_sim_tgt with "[-]").
    iMod ("Hsim" with "[$]") as "[[% [? HP]]| Hs ]". {
      iModIntro. iDestruct ("Hc" with "[$] [//]") as "Hc".
      iApply (sim_tgt_stop with "[-]").
      iApply (bi_mono1_intro with "Hc"). iIntros (?) "?".
      iDestruct ("HP" with "[$]") as "$".
    }
    iModIntro. iApply (sim_tgt_step with "[-]"). iIntros (?? Hstep). inv_all/= @m_step.
    all: iMod ("Hs" with "[//]") as "Hs"; do 2 iModIntro.
    - do 2 case_match; simplify_eq. iDestruct "Hs" as "[[% [? HP]]|[%[%[% HF]]]]".
      + iDestruct ("Hc" with "[$] [//]") as "Hc".
        iLeft. iApply (bi_mono1_intro with "Hc"). iIntros (?) "?".
        iDestruct ("HP" with "[$]") as (??) "?".
        iExists (_, _). iFrame. iSplit!.
      + iRight. iExists (_, _). iSplit!; [done|].
        iApply (sim_tgt_wand with "[-] []"); [by iApply "HF"|].
        iIntros (??) "HΠ". by iApply bi_mono1_intro0.
    - iDestruct "Hs" as "[[% [? HP]]|[%[%[% HF]]]]"; simplify_eq.
      iDestruct ("Hc" with "[$] [//]") as "Hc".
      iLeft. iExists _. iFrame. iIntros (?) "?".
      iDestruct ("HP" with "[$]") as (??) "?".
      iExists (_, _). iFrame. iSplit!.
  Qed.

  Lemma sim_src_map m f σ σf Π `{!VisNoAng m} :
    (σ ≈{m}≈>ₛ λ κ σ',
      ∃ κ' σf' ok, ⌜if κ is Some e then f σf e κ' σf' ok else κ' = None ∧ σf' = σf ∧ ok = true⌝ ∗
         Π κ' (σ', (σf', ok))) -∗
    (σ, (σf, true)) ≈{map_trans m f}≈>ₛ Π.
  Proof.
    iIntros "Hsim".
    pose (F := (λ σ Π', (∀ κ σ', Π' κ σ' -∗
         ∃ κ' σf' ok, ⌜if κ is Some e then f σf e κ' σf' ok else κ' = None ∧ σf' = σf ∧ ok = true⌝ ∗
          Π κ' (σ', (σf', ok))) -∗ (σ, (σf, true)) ≈{map_trans m f}≈>ₛ Π)%I).
    iAssert (∀ Π, σ ≈{ m }≈>ₛ Π -∗ F σ Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"). iIntros (??) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_src_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros "Hc".
    iApply (sim_src_ctx with "[-]"). iIntros "?".
    iApply (fupd_sim_src with "[-]").
    iMod ("Hsim" with "[$]") as "[?| [%κ [% [% Hs]]] ]". {
      iModIntro. iApply (sim_src_stop with "[-]").
      iDestruct ("Hc" with "[$]") as (???[?[??]]) "Hc". by simplify_eq.
    }
    destruct κ.
    - exploit vis_no_all; [done|] => -[σ'' ?].
      iMod ("Hs" with "[%]") as "Hs"; [naive_solver|]. iModIntro.
      iDestruct ("Hc" with "[$]") as (????) "Hs".
      iApply (sim_src_step_end with "[-]"). { econs. { apply: ProductStepBoth; [done|]. by econs. } done. }
      iIntros ([σ' ?] [??]) "!>". have ? : σ' = σ'' by naive_solver. by simplify_eq.
    - iModIntro. iApply (sim_src_step with "[-]"). { econs; [by econs|done]. }
      iIntros ([??][??]). simplify_eq. iMod ("Hs" with "[//]") as "HF". iModIntro.
      by iApply "HF".
  Qed.

  Lemma sim_src_map_ub m f σ σf Π `{!VisNoAng m} :
    ⊢ (σ, (σf, false)) ≈{map_trans m f}≈>ₛ Π.
  Proof.
    iStartProof. iApply sim_src_step. { econs. { by apply: ProductStepR; econs. } done. }
    iIntros ([??] [??]). done.
  Qed.
End map.

(** * seq_product *)

Section seq_product.
  Context {Σ : gFunctors} {EV1 EV2 : Type} `{!dimsumGS Σ}.

  Lemma sim_tgt_seq_product_None (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2 Π :
    (∀ p, ▷ₒ Π (Some (SPENone p)) (λ P, P (p, σ1, σ2))) -∗
    (SPNone, σ1, σ2) ≈{seq_product_trans m1 m2}≈>ₜ Π.
  Proof.
    iIntros "HΠ". iApply (sim_tgt_bi_mono with "[-]").
    iApply (sim_tgt_step_end with "[-]"). iIntros (???). inv_all @m_step. iSpecialize ("HΠ" $! _).
    do 2 iModIntro. iApply (bi_mono1_intro with "HΠ"). iIntros (?) "?".
    iApply bi_mono1_intro0. iSplit!.
  Qed.

  Lemma sim_tgt_seq_product_left (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2 Π :
    (σ1 ≈{m1}≈>ₜ λ κ Pσ,
      ∀ s', ⌜if κ is None then s' = SPLeft else True⌝ -∗
         Π ((λ e, SPELeft e s') <$> κ) (λ P, Pσ (λ σ', P (s', σ', σ2)))) -∗
    (SPLeft, σ1, σ2) ≈{seq_product_trans m1 m2}≈>ₜ Π.
  Proof.
    iIntros "Hsim".
    pose (F := (λ σ Π', (∀ κ Pσ, Π' κ Pσ -∗
         ∀ s', ⌜if κ is None then s' = SPLeft else True⌝ -∗
         Π ((λ e, SPELeft e s') <$> κ) (λ P, Pσ (λ σ', P (s', σ', σ2)))) -∗
         (SPLeft, σ, σ2) ≈{seq_product_trans m1 m2}≈>ₜ Π)%I).
    iAssert (∀ Π, σ1 ≈{ m1 }≈>ₜ Π -∗ F σ1 Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"). iIntros (??) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_tgt_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros "Hc".
    iApply (sim_tgt_ctx with "[-]"). iIntros "?".
    iApply (sim_tgt_bi_mono1 with "[-]").
    iApply (fupd_sim_tgt with "[-]").
    iMod ("Hsim" with "[$]") as "[[% [? HP]]| Hs ]". {
      iModIntro. iDestruct ("Hc" with "[$] [//]") as "Hc".
      iApply sim_tgt_stop.
      iApply (bi_mono1_intro with "[Hc] [-]"); [done|].
      iIntros (?) "?". by iDestruct ("HP" with "[$]") as "HP".
    }
    iModIntro. iApply (sim_tgt_step with "[-]"). iIntros (?? Hstep). inv_all/= @m_step.
    iMod ("Hs" with "[//]") as "Hs"; do 2 iModIntro.
    iDestruct "Hs" as "[[% [? HP]]|[%[%[% HF]]]]"; simplify_eq/=.
    - iDestruct ("Hc" with "[$] [//]") as "Hc".
      iLeft. iApply (bi_mono1_intro with "Hc").
      iIntros (?) "?".
      iDestruct ("HP" with "[$]") as (??) "?".
      iExists (_, _, _). iSplit!; [done|]. by iFrame.
    - iRight. iExists (_, _, _). iSplit!; [done|].
      iApply (sim_tgt_wand with "[-] []"); [by iApply "HF"|].
      iIntros (??) "HΠ". by iApply bi_mono1_intro0.
  Qed.

  Lemma sim_tgt_seq_product_right (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2 Π :
    (σ2 ≈{m2}≈>ₜ λ κ Pσ,
      ∀ s', ⌜if κ is None then s' = SPRight else True⌝ -∗
         Π ((λ e, SPERight e s') <$> κ) (λ P, Pσ (λ σ', P (s', σ1, σ')))) -∗
    (SPRight, σ1, σ2) ≈{seq_product_trans m1 m2}≈>ₜ Π.
  Proof.
    iIntros "Hsim".
    pose (F := (λ σ Π', (∀ κ Pσ, Π' κ Pσ -∗
         ∀ s', ⌜if κ is None then s' = SPRight else True⌝ -∗
         Π ((λ e, SPERight e s') <$> κ) (λ P, Pσ (λ σ', P (s', σ1, σ')))) -∗
         (SPRight, σ1, σ) ≈{seq_product_trans m1 m2}≈>ₜ Π)%I).
    iAssert (∀ Π, σ2 ≈{ m2 }≈>ₜ Π -∗ F σ2 Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"). iIntros (??) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_tgt_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros "Hc".
    iApply (sim_tgt_ctx with "[-]"). iIntros "?".
    iApply (sim_tgt_bi_mono1 with "[-]").
    iApply (fupd_sim_tgt with "[-]").
    iMod ("Hsim" with "[$]") as "[[% [? HP]]| Hs ]". {
      iModIntro. iDestruct ("Hc" with "[$] [//]") as "Hc".
      iApply sim_tgt_stop.
      iApply (bi_mono1_intro with "[Hc] [-]"); [done|].
      iIntros (?) "?". by iDestruct ("HP" with "[$]") as "HP".
    }
    iModIntro. iApply (sim_tgt_step with "[-]"). iIntros (?? Hstep). inv_all/= @m_step.
    iMod ("Hs" with "[//]") as "Hs"; do 2 iModIntro.
    iDestruct "Hs" as "[[% [? HP]]|[%[%[% HF]]]]"; simplify_eq/=.
    - iDestruct ("Hc" with "[$] [//]") as "Hc".
      iLeft. iApply (bi_mono1_intro with "Hc").
      iIntros (?) "?".
      iDestruct ("HP" with "[$]") as (??) "?".
      iExists (_, _, _). iSplit!; [done|]. by iFrame.
    - iRight. iExists (_, _, _). iSplit!; [done|].
      iApply (sim_tgt_wand with "[-] []"); [by iApply "HF"|].
      iIntros (??) "HΠ". by iApply bi_mono1_intro0.
  Qed.

  Lemma sim_src_seq_product_None p (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2 Π :
    Π (Some (SPENone p)) (p, σ1, σ2) -∗
    (SPNone, σ1, σ2) ≈{seq_product_trans m1 m2}≈>ₛ Π.
  Proof.
    iIntros "HΠ". iApply (sim_src_step_end with "[-]"); [by econs|].
    iIntros (??). by simplify_eq.
  Qed.

  Lemma sim_src_seq_product_left (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2 Π `{!VisNoAng m1} :
    (σ1 ≈{m1}≈>ₛ λ κ σ', ∃ s', ⌜if κ is None then s' = SPLeft else True⌝ ∗
       Π ((λ e, SPELeft e s') <$> κ) (s', σ', σ2)) -∗
    (SPLeft, σ1, σ2) ≈{seq_product_trans m1 m2}≈>ₛ Π.
  Proof.
    iIntros "Hsim".
    pose (F := (λ σ Π', (∀ κ σ, Π' κ σ -∗
         ∃ s', ⌜if κ is None then s' = SPLeft else True⌝ ∗
         Π ((λ e, SPELeft e s') <$> κ) (s', σ, σ2)) -∗
         (SPLeft, σ, σ2) ≈{seq_product_trans m1 m2}≈>ₛ Π)%I).
    iAssert (∀ Π, σ1 ≈{ m1 }≈>ₛ Π -∗ F σ1 Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"). iIntros (??) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_src_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros "Hc".
    iApply (sim_src_ctx with "[-]"). iIntros "?".
    iApply (fupd_sim_src with "[-]").
    iMod ("Hsim" with "[$]") as "[?| [%κ [% [% Hsim]]] ]". {
      iModIntro. iDestruct ("Hc" with "[$]") as (??) "Hc".
      iApply (sim_src_stop with "[-]"). by simplify_eq/=.
    }
    destruct κ.
    - exploit vis_no_all; [done|] => -[σs1 ?].
      iMod ("Hsim" with "[%]") as "?"; [naive_solver|].
      iDestruct ("Hc" with "[$]") as (s ?) "?".
      iApply (sim_src_step with "[-]"). { by apply: (SPLeftS _ _ _ _ _ s). }
      iIntros ([[? σs2]?] [?[??]]). have ? : σs1 = σs2 by naive_solver. by simplify_eq/=.
    - iModIntro. iApply (sim_src_step with "[-]"). { by econs. }
      iIntros ([[??] ?] [?[??]]). simplify_eq.
      iMod ("Hsim" with "[//]") as "Hsim". iModIntro. by iApply "Hsim".
  Qed.

  Lemma sim_src_seq_product_right (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2 Π `{!VisNoAng m2} :
    (σ2 ≈{m2}≈>ₛ λ κ σ', ∃ s', ⌜if κ is None then s' = SPRight else True⌝ ∗
       Π ((λ e, SPERight e s') <$> κ) (s', σ1, σ')) -∗
    (SPRight, σ1, σ2) ≈{seq_product_trans m1 m2}≈>ₛ Π.
  Proof.
    iIntros "Hsim".
    pose (F := (λ σ Π', (∀ κ σ, Π' κ σ -∗
         ∃ s', ⌜if κ is None then s' = SPRight else True⌝ ∗
         Π ((λ e, SPERight e s') <$> κ) (s', σ1, σ)) -∗
         (SPRight, σ1, σ) ≈{seq_product_trans m1 m2}≈>ₛ Π)%I).
    iAssert (∀ Π, σ2 ≈{ m2 }≈>ₛ Π -∗ F σ2 Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"). iIntros (??) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_src_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros "Hc".
    iApply (sim_src_ctx with "[-]"). iIntros "?".
    iApply (fupd_sim_src with "[-]").
    iMod ("Hsim" with "[$]") as "[?| [%κ [% [% Hsim]]] ]". {
      iModIntro. iDestruct ("Hc" with "[$]") as (??) "Hc".
      iApply (sim_src_stop with "[-]"). by simplify_eq/=.
    }
    destruct κ.
    - exploit vis_no_all; [done|] => -[σs1 ?].
      iMod ("Hsim" with "[%]") as "?"; [naive_solver|].
      iDestruct ("Hc" with "[$]") as (s ?) "?".
      iApply (sim_src_step with "[-]"). { by apply: (SPRightS _ _ _ _ _ s). }
      iIntros ([[? ?]σs2] [?[??]]). have ? : σs1 = σs2 by naive_solver. by simplify_eq/=.
    - iModIntro. iApply (sim_src_step with "[-]"). { by econs. }
      iIntros ([[??] ?] [?[??]]). simplify_eq.
      iMod ("Hsim" with "[//]") as "Hsim". iModIntro. by iApply "Hsim".
  Qed.
End seq_product.

(** * state_transform_mod *)

Section state_transform.
  Context {Σ : gFunctors} {EV : Type} {S : Type} `{!dimsumGS Σ}.

  Lemma sim_tgt_state_transform (m : mod_trans EV) σ' (R : S → m.(m_state) → Prop) σ Π `{!StateTransformWf m R} :
   R σ σ' →
   (σ' ≈{m}≈>ₜ λ κ Pσ, Π κ (λ P, Pσ (λ σ'', ∀ σ''', ⌜R σ''' σ''⌝ -∗ P σ'''))) -∗
    σ ≈{state_transform_trans m R}≈>ₜ Π.
  Proof.
    destruct StateTransformWf0 as [Heq HRstep].
    iIntros (HR) "Hsim".
    pose (F := (λ σ' Π', ∀ σ,
                   ⌜R σ σ'⌝ -∗
                   (∀ κ Pσ, Π' κ Pσ -∗ Π κ (λ P, Pσ (λ σ'', ∀ σ''', ⌜R σ''' σ''⌝ -∗ P σ'''))) -∗
                   σ ≈{state_transform_trans m R}≈>ₜ Π)%I).
    iAssert (∀ Π, σ' ≈{ m }≈>ₜ Π -∗ F σ' Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"); [done|]. iIntros (??) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_tgt_ind with "[] Hsim"). { solve_proper. }
    clear σ' σ HR. iIntros "!>" (σ'?) "Hsim". iIntros (σ HR) "Hc".
    iApply (sim_tgt_ctx with "[-]"). iIntros "?".
    iApply (sim_tgt_bi_mono1 with "[-]").
    iApply (fupd_sim_tgt with "[-]").
    iMod ("Hsim" with "[$]") as "[[% [HΠ HP]]| Hs ]". {
      iModIntro. iApply (sim_tgt_stop with "[-]").
      iApply (bi_mono1_intro with "[Hc HΠ]"); [by iApply "Hc"|] => /=.
      iIntros (?) "?". iDestruct ("HP" with "[$]") as "HP". by iApply "HP".
    }
    iModIntro. iApply (sim_tgt_step with "[-]"). iIntros (?? Hstep). inv_all/= @m_step.
    have ?: σ' = σ'0 by naive_solver. subst.
    iMod ("Hs" with "[//]") as "Hs"; do 2 iModIntro.
    iDestruct "Hs" as "[[% [? HP]]|[%[%[% HF]]]]".
    - iDestruct ("Hc" with "[$]") as "Hc".
      iLeft. iApply (bi_mono1_intro with "Hc"). iIntros (?) "?".
      iDestruct ("HP" with "[$]") as (??) "HP".
      exploit HRstep; [done..|] => -[??].
      iSplit!; [done..|]. by iApply "HP".
    - iRight. simplify_eq. exploit HRstep; [done..|] => -[??].
      iSplit!; [done..|]. iApply (sim_tgt_wand with "[-] []"); [by iApply "HF"|].
      iIntros (??) "HΠ". by iApply bi_mono1_intro0.
  Qed.

  Lemma sim_src_state_transform (m : mod_trans EV) σ' (R : S → m.(m_state) → Prop) σ Π :
   R σ σ' →
   (σ' ≈{m}≈>ₛ λ κ σ'', ∀ σ''', ⌜R σ''' σ''⌝ -∗ Π κ σ''') -∗
    σ ≈{state_transform_trans m R}≈>ₛ Π.
  Proof.
    iIntros (HR) "Hsim".
    pose (F := (λ σ' Π', ∀ σ,
                   ⌜R σ σ'⌝ -∗
                   (∀ κ σ'', Π' κ σ'' -∗ ∀ σ''', ⌜R σ''' σ''⌝ -∗ Π κ σ''') -∗
                   σ ≈{state_transform_trans m R}≈>ₛ Π)%I).
    iAssert (∀ Π, σ' ≈{ m }≈>ₛ Π -∗ F σ' Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"); [done|]. iIntros (??) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_src_ind with "[] Hsim"). { solve_proper. }
    clear σ' σ HR. iIntros "!>" (σ'?) "Hsim". iIntros (σ HR) "Hc".
    iApply (sim_src_ctx with "[-]"). iIntros "?".
    iApply (fupd_sim_src with "[-]").
    iMod ("Hsim" with "[$]") as "[?| [%κ [% [% Hs]]] ]". {
      iModIntro. iApply (sim_src_stop with "[-]"). by iApply ("Hc" with "[$]").
    }
    iModIntro. iApply (sim_src_step with "[-]"); [by econs|].
    iIntros (? [?[??]]). iMod ("Hs" with "[//]") as "Hs". iModIntro.
    case_match.
    - by iApply ("Hc" with "Hs").
    - by iApply ("Hs" with "[//]").
  Qed.
End state_transform.

(** * seq_map *)

Section seq_map.
  Context {Σ : gFunctors} {EV1 EV2 : Type} `{!dimsumGS Σ}.
  Implicit Types (f : mod_trans (sm_event EV1 EV2)).

  Lemma sim_tgt_seq_map_filter m f σ σf Π :
    (σf ≈{f}≈>ₜ λ κ Pσ,
      match κ with
      | None => Π None (λ P, Pσ (λ x, P (SMFilter, σ, x)))
      | Some (SMEEmit e) => Π (Some e) (λ P, Pσ (λ x, P (SMFilter, σ, x)))
      | Some (SMEReturn e) => Π None (λ P, Pσ (λ x, P (if e is Some e' then SMProgRecv e' else SMProg, σ, x)))
      | _ => True
      end) -∗
    (SMFilter, σ, σf) ≈{seq_map_trans m f}≈>ₜ Π.
  Proof.
    iIntros "HΠ". iApply (sim_tgt_bi_mono1 with "[-]").
    iApply sim_tgt_state_transform; [done|] => /=.
    iApply (sim_tgt_map with "[-]").
    iApply (sim_tgt_seq_product_right with "[-]").
    iApply (sim_tgt_bi_mono2 with "[-]").
    iApply (sim_tgt_wand with "HΠ").
    iIntros (κ Pσ) "Hκ". iIntros (s' ? κ' ???).
    destruct κ; destruct!/=; [inv_all @seq_map_filter|].
    all: iApply (bi_mono1_intro with "Hκ"); iIntros (?) "HP".
    all: iApply (bi_mono1_intro with "HP"); iIntros (?) "?"; iIntros ([[??]?] ?); by simplify_eq/=.
  Qed.

  Lemma sim_tgt_seq_map_filter_recv m f σ σf e Π :
    (σf ≈{f}≈>ₜ λ κ Pσ,
      if κ is Some e' then ⌜SMERecv e = e'⌝ -∗ Π None (λ P, Pσ (λ x, P (SMFilter, σ, x)))
      else Π None (λ P, Pσ (λ x, P (SMFilterRecv e, σ, x)))
      ) -∗
    (SMFilterRecv e, σ, σf) ≈{seq_map_trans m f}≈>ₜ Π.
  Proof.
    iIntros "HΠ". iApply (sim_tgt_bi_mono1 with "[-]").
    iApply sim_tgt_state_transform; [done|] => /=.
    iApply (sim_tgt_map with "[-]").
    iApply (sim_tgt_seq_product_right with "[-]").
    iApply (sim_tgt_bi_mono2 with "[-]").
    iApply (sim_tgt_wand with "HΠ").
    iIntros (κ Pσ) "Hκ". iIntros (s' ? κ' ???).
    destruct κ; destruct!/=; [inv_all @seq_map_filter|].
    1: iSpecialize ("Hκ" with "[//]").
    all: iApply (bi_mono1_intro with "Hκ"); iIntros (?) "HP".
    all: iApply (bi_mono1_intro with "HP"); iIntros (?) "?"; iIntros ([[??]?] ?); by simplify_eq/=.
  Qed.

  Lemma sim_tgt_seq_map_prog m f σ σf Π :
    (σ ≈{m}≈>ₜ λ κ Pσ,
      if κ is Some e' then Π None (λ P, Pσ (λ x, P (SMFilterRecv e', x, σf)))
      else Π None (λ P, Pσ (λ x, P (SMProg, x, σf)))
    ) -∗
    (SMProg, σ, σf) ≈{seq_map_trans m f}≈>ₜ Π.
  Proof.
    iIntros "HΠ". iApply (sim_tgt_bi_mono1 with "[-]").
    iApply sim_tgt_state_transform; [done|] => /=.
    iApply (sim_tgt_map with "[-]").
    iApply (sim_tgt_seq_product_left with "[-]").
    iApply (sim_tgt_bi_mono2 with "[-]").
    iApply (sim_tgt_wand with "HΠ").
    iIntros (κ Pσ) "Hκ". iIntros (s' ? κ' ???).
    destruct κ; destruct!/=; [inv_all @seq_map_filter|].
    all: iApply (bi_mono1_intro with "Hκ"); iIntros (?) "HP".
    all: iApply (bi_mono1_intro with "HP"); iIntros (?) "?"; iIntros ([[??]?] ?); by simplify_eq/=.
  Qed.

  Lemma sim_tgt_seq_map_prog_recv m f σ σf e Π :
    (σ ≈{m}≈>ₜ λ κ Pσ,
      if κ is Some e' then ⌜e = e'⌝ -∗ Π None (λ P, Pσ (λ x, P (SMProg, x, σf)))
      else Π None (λ P, Pσ (λ x, P (SMProgRecv e, x, σf)))
      ) -∗
    (SMProgRecv e, σ, σf) ≈{seq_map_trans m f}≈>ₜ Π.
  Proof.
    iIntros "HΠ". iApply (sim_tgt_bi_mono1 with "[-]").
    iApply sim_tgt_state_transform; [done|] => /=.
    iApply (sim_tgt_map with "[-]").
    iApply (sim_tgt_seq_product_left with "[-]").
    iApply (sim_tgt_bi_mono2 with "[-]").
    iApply (sim_tgt_wand with "HΠ").
    iIntros (κ Pσ) "Hκ". iIntros (s' ? κ' ???).
    destruct κ; destruct!/=; [inv_all @seq_map_filter|].
    1: iSpecialize ("Hκ" with "[//]").
    all: iApply (bi_mono1_intro with "Hκ"); iIntros (?) "HP".
    all: iApply (bi_mono1_intro with "HP"); iIntros (?) "?"; iIntros ([[??]?] ?); by simplify_eq/=.
  Qed.

  Lemma sim_src_seq_map_filter m f σ σf Π `{!VisNoAng m} `{!VisNoAng f} :
    (σf ≈{f}≈>ₛ λ κ σf',
      match κ with
      | None => Π None (SMFilter, σ, σf')
      | Some (SMEEmit e) => Π (Some e) (SMFilter, σ, σf')
      | Some (SMEReturn e) => Π None (if e is Some e' then SMProgRecv e' else SMProg, σ, σf')
      | _ => False
      end) -∗
    (SMFilter, σ, σf) ≈{seq_map_trans m f}≈>ₛ Π.
  Proof.
    iIntros "HΠ".
    iApply sim_src_state_transform; [done|] => /=.
    iApply (sim_src_map with "[-]").
    iApply (sim_src_seq_product_right with "[-]").
    iApply (sim_src_wand with "HΠ").
    iIntros (κ σ') "Hκ".
    repeat case_match => //; simplify_eq.
    all: iSplit!; (once try econs).
    all: iIntros ([[??]?] ?); by simplify_eq/=.
  Qed.

  Lemma sim_src_seq_map_filter_recv m f σ σf Π e `{!VisNoAng m} `{!VisNoAng f} :
    (σf ≈{f}≈>ₛ λ κ σf',
      if κ is Some e' then ⌜SMERecv e = e'⌝ ∗ Π None (SMFilter, σ, σf')
      else Π None (SMFilterRecv e, σ, σf')
    ) -∗
    (SMFilterRecv e, σ, σf) ≈{seq_map_trans m f}≈>ₛ Π.
  Proof.
    iIntros "HΠ".
    iApply sim_src_state_transform; [done|] => /=.
    iApply (sim_src_map with "[-]").
    iApply (sim_src_seq_product_right with "[-]").
    iApply (sim_src_wand with "HΠ").
    iIntros (κ σ') "Hκ".
    repeat case_match => //; iDestruct!; simplify_eq.
    all: iSplit!; (once try econs).
    all: iIntros ([[??]?] ?); by simplify_eq/=.
  Qed.

  Lemma sim_src_seq_map_prog m f σ σf Π `{!VisNoAng m} `{!VisNoAng f} :
    (σ ≈{m}≈>ₛ λ κ σ',
      if κ is Some e' then Π None (SMFilterRecv e', σ', σf)
      else Π None (SMProg, σ', σf)) -∗
    (SMProg, σ, σf) ≈{seq_map_trans m f}≈>ₛ Π.
  Proof.
    iIntros "HΠ".
    iApply sim_src_state_transform; [done|] => /=.
    iApply (sim_src_map with "[-]").
    iApply (sim_src_seq_product_left with "[-]").
    iApply (sim_src_wand with "HΠ").
    iIntros (κ σ') "Hκ".
    repeat case_match => //; simplify_eq.
    all: iSplit!; (once try econs).
    all: iIntros ([[??]?] ?); by simplify_eq/=.
  Qed.

  Lemma sim_src_seq_map_prog_recv m f σ σf Π e `{!VisNoAng m} `{!VisNoAng f} :
    (σ ≈{m}≈>ₛ λ κ σ',
      if κ is Some e' then ⌜e = e'⌝ ∗ Π None (SMProg, σ', σf)
      else Π None (SMProgRecv e, σ', σf)
    ) -∗
    (SMProgRecv e, σ, σf) ≈{seq_map_trans m f}≈>ₛ Π.
  Proof.
    iIntros "HΠ".
    iApply sim_src_state_transform; [done|] => /=.
    iApply (sim_src_map with "[-]").
    iApply (sim_src_seq_product_left with "[-]").
    iApply (sim_src_wand with "HΠ").
    iIntros (κ σ') "Hκ".
    repeat case_match => //; iDestruct!; simplify_eq.
    all: iSplit!; (once try econs).
    all: iIntros ([[??]?] ?); by simplify_eq/=.
  Qed.
End seq_map.

(** * prepost *)

Section prepost.
  Context {Σ : gFunctors} `{!dimsumGS Σ}.
  Context {EV1 EV2 S : Type}.
  Context {M : ucmra} `{!Shrink M} `{!satG Σ M} `{!CmraDiscrete M} `{!∀ x : M, CoreCancelable x}.
  Implicit Types (i : EV2 → S → prepost (EV1 * S) M) (o : EV1 → S → prepost (EV2 * S) M).

  Lemma sim_tgt_prepost_Outside i o m s σ x Π :
    (∀ e, ▷ₒ Π (Some e) (λ P, P (SMFilter, σ, (PPRecv1 e, s, x)))) -∗
    (SMFilter, σ, (PPOutside, s, x)) ≈{prepost_trans i o m}≈>ₜ Π.
  Proof.
    iIntros "HΠ".
    iApply (sim_tgt_bi_mono1 with "[-]").
    iApply (sim_tgt_seq_map_filter with "[-]").
    iApply (sim_tgt_step_end with "[-]"). iIntros (???). inv_all @m_step. iSpecialize ("HΠ" $! _).
    do 2 iModIntro. iApply (bi_mono1_intro with "HΠ"). iIntros (?) "?".
    iSplit!.
  Qed.

  Lemma sim_tgt_prepost_Recv1 i o m s σ x Π e γ :
    (∃ r y, ⌜pp_to_ex (i e s) (λ r' y', r = r' ∧ y = y')⌝ ∗
        |==> sat_open γ ∗ sat γ (x ∗ y) ∗
           ∀ x', sat_closed γ false x' -∗ Π None (λ P, P (SMProgRecv r.1, σ, (PPInside, r.2, uPred_shrink x')))) -∗
    (SMFilter, σ, (PPRecv1 e, s, uPred_shrink x)) ≈{prepost_trans i o m}≈>ₜ Π.
  Proof using Type*.
    iIntros "HΠ".
    iApply (sim_tgt_bi_mono1 with "[-]").
    iApply (sim_tgt_seq_map_filter with "[-]").
    iApply (sim_tgt_step with "[-]"). iIntros (???). inv_all @m_step.
    iDestruct "HΠ" as (???) ">[? [? HΠ]]".
    iDestruct (sat_close with "[$] [$]") as (??) "?".
    do 2 iModIntro. iRight.
    iSplit!. {
      apply: pp_to_ex_mono; [done|]. move => ?? [??]; simplify_eq. split!.
      by rewrite assoc uPred_expand_shrink.
    }
    iApply (sim_tgt_step_end with "[-]"). iIntros (???). inv_all @m_step.
    do 2 iModIntro.
    iApply (bi_mono1_intro with "[-]"). { by iApply "HΠ". }
    iIntros (?) "?". iSplit!.
  Qed.

  Lemma sim_tgt_prepost_Inside i o m s σ x Π e γ b :
    (sat_closed γ b x ∗ ∀ r y x', ⌜pp_to_ex (o e s) (λ r' y', r' = r ∧ y' = y)⌝ -∗
       sat_open γ -∗ sat γ (if b then x ∗ y else y) -∗ sat γ x' -∗
        ▷ₒ Π (Some r.1) (λ P, P (SMFilter, σ, (PPOutside, r.2, uPred_shrink x')))) -∗
    (SMFilterRecv e, σ, (PPInside, s, uPred_shrink x)) ≈{prepost_trans i o m}≈>ₜ Π.
  Proof using Type*.
    iIntros "[Hclosed HΠ]".
    iApply (sim_tgt_bi_mono1 with "[-]").
    iApply sim_tgt_bind.
    iApply (sim_tgt_seq_map_filter_recv with "[-]").
    iApply (sim_tgt_step_end with "[-]"). iIntros (???). inv_all @m_step.
    do 2 iModIntro. iIntros (?). iRight. iSplit!.
    iApply (sim_tgt_seq_map_filter with "[-]").
    iApply (sim_tgt_step with "[-]"). iIntros (???). inv_all @m_step.
    revert select (satisfiable _). rewrite uPred_expand_shrink assoc => ?.
    iMod ("Hclosed" with "[//]") as "[Ha Hsat]".
    iAssert (sat γ (if b then x ∗ y else y) ∗ sat γ x')%I with "[Hsat]" as "[??]".
    { destruct b; rewrite !sat_sep; iDestruct!; iFrame. }
    iSpecialize ("HΠ" with "[//] [$] [$] [$]").
    do 2 iModIntro. iRight. iSplit!.
    iApply (sim_tgt_step with "[-]"). iIntros (???). inv_all @m_step.
    do 2 iModIntro. iLeft.
    iApply (bi_mono1_intro with "HΠ").
    iIntros (?) "?". iSplit!.
  Qed.

  Lemma sim_src_prepost_Outside i o m s σ x Π `{!VisNoAng m}:
    (∃ e, Π (Some e) (SMFilter, σ, (PPRecv1 e, s, x))) -∗
    (SMFilter, σ, (PPOutside, s, x)) ≈{prepost_trans i o m}≈>ₛ Π.
  Proof.
    iIntros "[% HΠ]".
    iApply (sim_src_seq_map_filter with "[-]").
    iApply (sim_src_step_end with "[-]"). { econs. } iIntros ([[??]?] ?). simplify_eq.
    by iModIntro.
  Qed.

  Lemma sim_src_prepost_Recv1 i o m s σ x Π e γ b `{!VisNoAng m}:
    (sat_closed γ b x ∗ ∀ r y x', ⌜pp_to_ex (i e s) (λ r' y', r' = r ∧ y' = y)⌝ -∗
           sat_open γ -∗ sat γ (if b then x ∗ y else y) -∗ sat γ x' -∗
           Π None (SMProgRecv r.1, σ, (PPInside, r.2, uPred_shrink x'))) -∗
    (SMFilter, σ, (PPRecv1 e, s, uPred_shrink x)) ≈{prepost_trans i o m}≈>ₛ Π.
  Proof using Type*.
    iIntros "[Hclosed HΠ]".
    iApply (sim_src_seq_map_filter with "[-]").
    iApply (sim_src_step with "[-]"). { econs. }
    iIntros ([[??]?] [?[y[[x' [Hsat ?]]?]]]%pp_to_ex_exists). simplify_eq.
    rewrite uPred_expand_shrink in Hsat.
    iMod ("Hclosed" with "[%]") as "[Ha Hsat]". { by rewrite comm. }
    iAssert (sat γ (if b then x ∗ y else y) ∗ sat γ x')%I with "[Hsat]" as "[??]".
    { destruct b; rewrite !sat_sep; iDestruct!; iFrame. }
    iModIntro. iApply (sim_src_step with "[-]"). { econs. }
    iIntros ([[??]?] ?). iModIntro. simplify_eq.
    iApply ("HΠ" with "[//] [$] [$] [$]").
  Qed.

  Lemma sim_src_prepost_Inside i o m s σ x Π e γ `{!VisNoAng m} :
    (∃ r y, ⌜pp_to_ex (o e s) (λ r' y', r' = r ∧ y' = y)⌝ ∗
       |==> sat_open γ ∗ sat γ (x ∗ y) ∗
        ∀ x', sat_closed γ false x' -∗ Π (Some r.1) (SMFilter, σ, (PPOutside, r.2, uPred_shrink x'))) -∗
    (SMFilterRecv e, σ, (PPInside, s, uPred_shrink x)) ≈{prepost_trans i o m}≈>ₛ Π.
  Proof using Type*.
    iIntros "HΠ".
    iApply (sim_src_bind with "[-]").
    iApply (sim_src_seq_map_filter_recv with "[-]").
    iApply (sim_src_step_end with "[-]"). { econs. }
    iIntros ([[??]?]?). simplify_eq.
    iDestruct "HΠ" as (???) ">[? [? HΠ]]".
    iDestruct (sat_close with "[$] [$]") as (? Hsat ) "?".
    iModIntro. iSplit!. iRight. iSplit!.
    iApply (sim_src_seq_map_filter with "[-]").
    iApply (sim_src_step with "[-]").
    { econs; [|done]. by rewrite uPred_expand_shrink comm (comm _ _ x). }
    iIntros ([[??]?] ?). simplify_eq. iModIntro.
    iApply (sim_src_step with "[-]"). { econs. }
    iIntros ([[??]?] ?). simplify_eq. iModIntro.
    iApply ("HΠ" with "[$]").
  Qed.
End prepost.
