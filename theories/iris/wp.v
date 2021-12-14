From iris.bi Require Import bi fixpoint.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export refframe.module.
Require Import refframe.trefines.
Set Default Proof Using "Type".

Structure language := Language {
  expr : Type;
  state : Type;
  events : Type;
  lang_module : module events;
  to_expr : lang_module.(m_state) → expr;
  to_state : lang_module.(m_state) → state;
}.
Definition exprO {Λ : language} := leibnizO (expr Λ).

Class refirisGS (Λ : language) (Σ : gFunctors) := RefirisG {
  refiris_invGS :> invGS Σ;
  spec_module : module (events Λ);
  state_interp : state Λ → spec_module.(m_state) → iProp Σ;
}.
Global Opaque refiris_invGS.

Definition wp_pre `{!refirisGS Λ Σ}
    (wp : leibnizO coPset -d> exprO -d> (exprO -d> iPropO Σ) -d> iPropO Σ) :
    leibnizO coPset -d> exprO -d> (exprO -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  (∀ σ σs, ⌜e1 = to_expr Λ σ⌝ -∗ state_interp (to_state Λ σ) σs ={E}=∗
    (state_interp (to_state Λ σ) σs ∗ Φ e1) ∨
    ∀ κ Pσ, ⌜(lang_module Λ).(m_step) σ κ Pσ⌝ ={E,∅}=∗
      ∃ Pσs, ⌜σs ~{spec_module, option_trace κ}~>ₜ Pσs⌝ ∗
        ∀ σs', ⌜Pσs σs'⌝ ={∅, E}=∗
          ∃ σ', ⌜Pσ σ'⌝ ∗ state_interp (to_state Λ σ') σs' ∗ wp E (to_expr Λ σ') Φ)%I.

Global Instance wp_pre_ne `{!refirisGS Λ Σ} n:
  Proper ((dist n ==> dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n ==> dist n) wp_pre.
Proof.
  move => ?? Hwp ?? -> ?? -> ?? HΦ. rewrite /wp_pre.
  repeat (f_equiv || eapply Hwp || eapply HΦ || reflexivity).
Qed.

Lemma wp_pre_mono `{!refirisGS Λ Σ} wp1 wp2:
  ⊢ □ (∀ E e Φ, wp1 E e Φ -∗ wp2 E e Φ )
  → ∀ E e Φ , wp_pre wp1 E e Φ -∗ wp_pre wp2 E e Φ.
Proof.
  iIntros "#Hinner" (E e Φ) "Hwp".
  iIntros (σ σs ?) "Hσ". iMod ("Hwp" with "[//] Hσ") as "[Hwp|Hwp]"; [by iLeft|iRight]. iModIntro.
  iIntros (κ Pσ ?). iMod ("Hwp" with "[//]") as (??) "Hwp". iModIntro. iExists _. iSplit; [done|].
  iIntros (??). iMod ("Hwp" with "[//]") as (??) "[??]". iModIntro. iExists _. iSplit; [done|]. iFrame.
  by iApply "Hinner".
Qed.

Local Instance wp_pre_monotone `{!refirisGS Λ Σ} :
  BiMonoPred (λ wp : prodO (prodO (leibnizO coPset) exprO) (exprO -d> iPropO Σ) -d> iPropO Σ, uncurry3 (wp_pre (curry3 wp))).
Proof.
  constructor.
  - iIntros (Φ Ψ ??) "#Hinner". iIntros ([[??]?]) "Hwp" => /=. iApply wp_pre_mono; [|done].
    iIntros "!>" (???) "HΦ". by iApply ("Hinner" $! (_, _, _)).
  - move => wp Hwp n [[E1 e1]Φ1] [[E2 e2]Φ2] /= [[/=??]?].
    apply wp_pre_ne; eauto. move => ????????? /=. by apply: Hwp.
Qed.

Definition wp_def `{!refirisGS Λ Σ} : Wp (iProp Σ) (expr Λ) (expr Λ) stuckness :=
  λ s : stuckness, curry3 (bi_least_fixpoint (λ wp : prodO (prodO (leibnizO coPset) exprO) (exprO -d> iPropO Σ) -d> iPropO Σ, uncurry3 (wp_pre (curry3 wp)))).
Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {Λ Σ _}.
Global Existing Instance wp'.
Lemma wp_eq `{!refirisGS Λ Σ} : wp = @wp_def Λ Σ _.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Section wp.
Context `{!refirisGS Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : expr Λ → iProp Σ.
Implicit Types e : expr Λ.

(* Weakest pre *)
Lemma wp_unfold E e Φ s:
  WP e @ s; E {{ Φ }} ⊣⊢ wp_pre (wp s (PROP:=iProp Σ)) E e Φ.
Proof. rewrite wp_eq /wp_def /curry3. apply: least_fixpoint_unfold. Qed.

Lemma wp_strong_ind (R: leibnizO coPset -d> exprO -d> (exprO -d> iPropO Σ) -d> iPropO Σ):
  NonExpansive3 R →
  ⊢ (□ ∀ E e Φ, wp_pre (λ E e Ψ, R E e Ψ ∧ wp NotStuck E e Ψ) E e Φ -∗ R E e Φ)
    -∗ ∀ E e Φ, wp NotStuck E e Φ -∗ R E e Φ .
Proof.
  iIntros (Hne) "#HPre". iIntros (E e Φ) "Hwp".
  rewrite wp_eq {2}/wp_def {1}/curry3.
  iApply (least_fixpoint_ind _ (uncurry3 R) with "[] Hwp").
  iIntros "!>" ([[??]?]) "Hwp" => /=. by iApply "HPre".
Qed.

Lemma wp_ind (R: leibnizO coPset -d> exprO -d> (exprO -d> iPropO Σ) -d> iPropO Σ):
  NonExpansive3 R →
  ⊢ (□ ∀ E e Φ, wp_pre R E e Φ -∗ R E e Φ)
    -∗ ∀ E e Φ, wp NotStuck E e Φ -∗ R E e Φ .
Proof.
  iIntros (Hne) "#HPre". iApply wp_strong_ind. iIntros "!>" (E e Φ) "Hwp".
  iApply "HPre". iApply (wp_pre_mono with "[] Hwp").
  iIntros "!>" (???) "[? _]". by iFrame.
Qed.

Lemma wp_stop' E e Φ:
  (|={E}=> Φ e) -∗ WP e @ E {{ Φ }}.
Proof. rewrite wp_unfold. iIntros "HΦ" (σ σs ?) "Hσ". iLeft. iFrame. Qed.
Lemma wp_stop E e Φ:
  Φ e -∗ WP e @ E {{ Φ }}.
Proof. iIntros "HΦ". iApply wp_stop'. by iFrame. Qed.

Lemma wp_bind E e Φ:
  WP e @ E {{ e', WP e' @ E {{ Φ }} }} -∗ WP e @ E {{ Φ }}.
Proof.
  iIntros "HΦ".
  pose (F := (λ E e Ψ, ∀ Φ, (∀ e, Ψ e -∗ wp NotStuck E e Φ) -∗ wp NotStuck E e Φ)%I).
  iAssert (∀ Φ, wp NotStuck E e Φ -∗ F E e Φ)%I as "Hgen"; last first.
  { iApply ("Hgen" with "HΦ"). iIntros (?) "$". }
  iIntros (?) "HWP".
  iApply (wp_ind with "[] HWP"). { solve_proper. }
  iIntros "!>" (???) "Hwp". iIntros (?) "Hc".
  rewrite wp_unfold. iIntros (???) "Hσ".
  iMod ("Hwp" with "[//] Hσ") as "[[? ?]|Hwp]".
  - iDestruct ("Hc" with "[$]") as "Hc". rewrite wp_unfold. by iApply "Hc".
  - iModIntro. iRight. iIntros (???). iMod ("Hwp" with "[//]") as (??) "Hwp". iModIntro.
    iExists _. iSplit; [done|]. iIntros (??). iMod ("Hwp" with "[//]") as (??) "[? HF]". iModIntro.
    iExists _. iSplit; [done|]. iFrame. by iApply "HF".
Qed.

End wp.

Theorem wp_adequacy Σ Λ `{!invGpreS Σ} mspec σi σs :
  (∀ `{Hinv : !invGS Σ},
    ⊢ |={⊤}=> ∃ (stateI : state Λ → mspec.(m_state) → iProp Σ),
       let _ : refirisGS Λ Σ := RefirisG _ _ _ mspec stateI
       in
       stateI (to_state Λ σi) σs ∗
       WP (to_expr Λ σi) @ ⊤ {{ _, |={⊤, ∅}=> False }}) →
  trefines (MS (lang_module Λ) σi) (MS mspec σs).
Proof.
  intros Hwp. constructor => κs Htrace.
  apply (step_fupdN_soundness _ 0) => ? /=. simpl in *.
  iMod Hwp as (stateI) "(Hσ & Hwp)". clear Hwp.
  iInduction Htrace as [???? Hκs|?????? Hstep ?? Hκs|??????? Hκs] "IH" forall (σs).
  - rewrite -Hκs. iApply fupd_mask_intro; [done|]. iIntros "HE". iPureIntro. by econstructor.
  - rewrite -Hκs. setoid_rewrite wp_unfold at 2.
    iMod ("Hwp" with "[//] Hσ") as "[[? Hwp]|Hwp]". { by iMod "Hwp". }
    iMod ("Hwp" with "[//]") as (? Ht) "Hwp".
    iApply (fupd_mono _ _ ⌜_⌝). { iPureIntro. by apply thas_trace_trans. }
    iIntros (??).
    iMod ("Hwp" with "[//]") as (σi' ?) "[Hstate Hwp]".
    iApply ("IH" with "[//] Hstate Hwp").
  - rewrite -Hκs.
    iApply (fupd_mono _ _ ⌜_⌝). { iPureIntro. apply thas_trace_all. }
    iIntros (?). iApply ("IH" with "Hσ Hwp").
Qed.
