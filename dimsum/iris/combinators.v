From dimsum.core Require Import product seq_product state_transform.
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
  Context {Σ : gFunctors} {EV : Type} `{!dimsumGS Σ}.

  Lemma sim_tgt_seq_product_None (m1 m2 : mod_trans EV) σ1 σ2 Π :
    (∀ p, ▷ₒ Π (Some (SPENone p)) (λ P, P (p, σ1, σ2))) -∗
    (SPNone, σ1, σ2) ≈{seq_product_trans m1 m2}≈>ₜ Π.
  Proof.
    iIntros "HΠ". iApply (sim_tgt_bi_mono with "[-]").
    iApply (sim_tgt_step_end with "[-]"). iIntros (???). inv_all @m_step. iSpecialize ("HΠ" $! _).
    do 2 iModIntro. iApply (bi_mono1_intro with "HΠ"). iIntros (?) "?".
    iApply bi_mono1_intro0. iSplit!.
  Qed.

  Lemma sim_tgt_seq_product_left (m1 m2 : mod_trans EV) σ1 σ2 Π :
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

  Lemma sim_tgt_seq_product_right (m1 m2 : mod_trans EV) σ1 σ2 Π :
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

  Lemma sim_src_seq_product_None p (m1 m2 : mod_trans EV) σ1 σ2 Π :
    Π (Some (SPENone p)) (p, σ1, σ2) -∗
    (SPNone, σ1, σ2) ≈{seq_product_trans m1 m2}≈>ₛ Π.
  Proof.
    iIntros "HΠ". iApply (sim_src_step_end with "[-]"); [by econs|].
    iIntros (??). by simplify_eq.
  Qed.

  Lemma sim_src_seq_product_left (m1 m2 : mod_trans EV) σ1 σ2 Π `{!VisNoAng m1} :
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

  Lemma sim_src_seq_product_right (m1 m2 : mod_trans EV) σ1 σ2 Π `{!VisNoAng m2} :
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
