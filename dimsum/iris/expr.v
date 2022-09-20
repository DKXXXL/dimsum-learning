From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From dimsum.core Require Export module trefines.
From dimsum.core Require Import nb_mod.
From dimsum.core.iris Require Export ord_later sim.
Set Default Proof Using "Type".

(** * mod_lang *)
Structure mod_lang EV Σ := ModLang {
  mexpr : Type;
  mectx : Type;
  mstate : Type;
  mfill : mectx → mexpr → mexpr;
  mcomp_ectx : mectx → mectx → mectx;
  mtrans :> mod_trans EV;
  mexpr_rel : mtrans.(m_state) → mexpr → Prop;
  mstate_interp : mtrans.(m_state) → option mstate → iProp Σ;
  mfill_comp K1 K2 e : mfill K1 (mfill K2 e) = mfill (mcomp_ectx K1 K2) e
}.
Global Arguments mexpr {_ _} _.
Global Arguments mstate {_ _} _.
Global Arguments mectx {_ _} _.
Global Arguments mfill {_ _} _.
Global Arguments mcomp_ectx {_ _} _.
Global Arguments mtrans {_ _} _.
Global Arguments mexpr_rel {_ _} _ _ _.
Global Arguments mstate_interp {_ _} _ _.

(** * [sim_tgt_expr] *)
Definition sim_tgt_expr_raw {EV Σ Λ} `{!dimsumGS Σ}
  (e : mexpr Λ) (os : option (mstate Λ)) (Π : option EV → ((m_state Λ → iProp Σ) → iProp Σ) → iProp Σ) : iProp Σ :=
  (∀ σ, ⌜mexpr_rel Λ σ e⌝ -∗ ord_later_ctx -∗ mstate_interp Λ σ os -∗
    σ ≈{ Λ }≈>ₜ Π)%I.

Notation "'TGT' e @ ? os [{ Π }]" := (sim_tgt_expr_raw e os Π%I) (at level 70, Π at level 200,
  format "'[hv' 'TGT'  e  '/' @  ?  os  [{  '[ ' Π  ']' }] ']'") : bi_scope.
Notation "'TGT' e @ s [{ Π }]" := (sim_tgt_expr_raw e (Some s) Π%I) (at level 70, Π at level 200,
  format "'[hv' 'TGT'  e  '/' @  s  [{  '[ ' Π  ']' }] ']'") : bi_scope.
Notation "'TGT' e [{ Π }]" := (sim_tgt_expr_raw e None Π%I) (at level 70, Π at level 200,
  format "'[hv' 'TGT'  e  '/' [{  '[ ' Π  ']' }] ']'") : bi_scope.

Definition sim_tgt_expr {EV Σ Λ} `{!dimsumGS Σ}
  (e : mexpr Λ) (os : option (mstate Λ)) (Π : option EV → ((m_state Λ → iProp Σ) → iProp Σ) → iProp Σ)
  (Φ : mexpr Λ → option (mstate Λ) → (option EV → ((m_state Λ → iProp Σ) → iProp Σ) → iProp Σ) → iProp Σ): iProp Σ :=
  ∀ K, (∀ e' os' Π', Φ e' os' Π' -∗ TGT mfill Λ K e' @ ? os' [{ Π' }]) -∗ TGT mfill Λ K e @ ? os [{ Π }].

Notation "'TGT' e @ ? os [{ Π }] {{ Φ } }" := (sim_tgt_expr e os Π%I Φ%I)
  (at level 70, Π, Φ at level 200, only parsing) : bi_scope.
Notation "'TGT' e @ s [{ Π }] {{ Φ } }" := (sim_tgt_expr e (Some s) Π%I Φ%I)
  (at level 70, Π, Φ at level 200, only parsing) : bi_scope.
Notation "'TGT' e [{ Π }] {{ Φ } }" := (sim_tgt_expr e None Π%I Φ%I)
  (at level 70, Π, Φ at level 200, only parsing) : bi_scope.

Notation "'TGT' e @ ? os [{ Π }] {{ e' , os' , Π' , Φ } }" := (sim_tgt_expr e os Π%I (λ e' os' Π', Φ%I))
  (at level 70, Π, Φ at level 200,
    format "'[hv' 'TGT'  e  '/' @  ?  os  [{  '[ ' Π  ']' }]  {{  '[ ' e' ,  os' ,  Π' ,  '/' Φ  ']' } } ']'") : bi_scope.
Notation "'TGT' e @ s [{ Π }] {{ e' , os' , Π' , Φ } }" := (sim_tgt_expr e (Some s) Π%I (λ e' os' Π', Φ%I))
  (at level 70, Π, Φ at level 200,
    format "'[hv' 'TGT'  e  '/' @  s  [{  '[ ' Π  ']' }]  {{  '[ ' e' ,  os' ,  Π' ,  '/' Φ  ']' } } ']'") : bi_scope.
Notation "'TGT' e [{ Π }] {{ e' , os' , Π' , Φ } }" := (sim_tgt_expr e None Π%I (λ e' os' Π', Φ%I))
  (at level 70, Π, Φ at level 200,
    format "'[hv' 'TGT'  e  '/' [{  '[ ' Π  ']' }]  {{  '[ ' e' ,  os' ,  Π' ,  '/' Φ  ']' } } ']'") : bi_scope.

Section sim_tgt.
Context {EV} {Σ} {Λ : mod_lang EV Σ} `{!dimsumGS Σ}.
Implicit Types (e : mexpr Λ).

Lemma sim_tgt_expr_raw_step e Π os :
  (∀ σ κ Pσ, ⌜mexpr_rel Λ σ e⌝ -∗ ⌜Λ.(m_step) σ κ Pσ⌝ -∗ mstate_interp Λ σ os ={∅}=∗ ▷ₒ
      (Π κ (λ P', ∃ σ', ⌜Pσ σ'⌝ ∗ P' σ') ∨
         ∃ os' σ' e', ⌜κ = None⌝ ∗ ⌜Pσ σ'⌝ ∗ ⌜mexpr_rel Λ σ' e'⌝ ∗ mstate_interp Λ σ' os' ∗ TGT e' @ ? os' [{ Π }])) -∗
  TGT e @ ? os [{ Π }].
Proof.
  iIntros "HΠ" (σ ?) "#??".
  iApply sim_tgt_step. iIntros (???). iMod ("HΠ" with "[//] [//] [$]") as "Hsim". do 2 iModIntro.
  iDestruct "Hsim" as "[$|(%&%&%&%&%&%&?&Hsim)]". iRight. iExists _. iSplit; [done|]. iSplit; [done|].
  by iApply "Hsim".
Qed.

Lemma sim_tgt_expr_raw_elim e Π σ os :
  mexpr_rel Λ σ e →
  mstate_interp Λ σ os -∗
  TGT e @ ? os [{ Π }] -∗
  σ ≈{Λ}≈>ₜ Π.
Proof. iIntros (?) "Hσ He". iApply sim_tgt_ctx. iIntros "#?". by iApply "He". Qed.

Lemma sim_tgt_expr_ctx e Π Φ os :
  (ord_later_ctx -∗ TGT e @ ? os [{ Π }] {{ Φ }}) -∗
  TGT e @ ? os [{ Π }] {{ Φ }}.
Proof.
  iIntros "Hsim" (?) "HΦ". iIntros (??) "#?". iApply ("Hsim" with "[$] [$] [//] [$]").
Qed.

Lemma fupd_sim_tgt_expr e Π Φ os :
  (|={∅}=> TGT e @ ? os [{ Π }] {{ Φ }}) -∗
  TGT e @ ? os [{ Π }] {{ Φ }}.
Proof.
  iIntros "Hsim" (?) "HΦ". iIntros (??) "#??". iApply fupd_sim_tgt. iApply ("Hsim" with "[$] [//] [//] [$]").
Qed.

Lemma sim_tgt_expr_bi_mono e Π Φ os :
  (TGT e @ ? os [{ λ κ, bi_mono1 (Π κ) }] {{ Φ }}) -∗
  TGT e @ ? os [{ Π }] {{ Φ }}.
Proof.
  iIntros "Hsim" (?) "HΦ". iIntros (??) "#??". iApply sim_tgt_bi_mono1.
  iApply ("Hsim" with "[$] [//] [//] [$]").
Qed.

Lemma sim_tgt_expr_bind K e Π Φ os :
  TGT e @ ? os [{ Π }] {{ e', os', Π', TGT mfill Λ K e' @ ? os' [{ Π' }] {{ Φ }} }} -∗
  TGT mfill Λ K e @ ? os [{ Π }] {{ Φ }}.
Proof.
  iIntros "Hsim" (?) "HΦ". rewrite mfill_comp. iApply "Hsim".
  iIntros (???) "Htgt". rewrite -mfill_comp. by iApply "Htgt".
Qed.

Lemma sim_tgt_expr_wand1 e Π Π' Φ os :
  TGT e @ ? os [{ Π' }] {{ Φ }} -∗
  (∀ κ P, Π' κ P -∗ Π κ P) -∗
  TGT e @ ? os [{ Π }] {{ Φ }}.
Proof.
  iIntros "Hsim Hwand" (?) "HΦ".
  iIntros (??) "#? Hσ".
  iApply (sim_tgt_wand with "[Hσ HΦ Hsim] Hwand").
  iApply ("Hsim" with "[$] [//] [$] [$]").
Qed.

Lemma sim_tgt_expr_wand e Π Φ Φ' os :
  TGT e @ ? os [{ Π }] {{ Φ' }} -∗
  (∀ e' os' Π', Φ' e' os' Π' -∗ Φ e' os' Π') -∗
  TGT e @ ? os [{ Π }] {{ Φ }}.
Proof. iIntros "Hsim Hwand" (?) "HΦ". iApply "Hsim". iIntros (???) "Hsim". iApply "HΦ". by iApply "Hwand". Qed.

Lemma sim_tgt_expr_stop1 e Π Φ os :
  (∀ σ, σ ⤇ₜ (λ Π', TGT e @ ? os [{ Π' }] {{ Φ }}) -∗ Π None (λ P, P σ)) -∗
  TGT e @ ? os [{ Π }] {{ Φ }}.
Proof.
  iIntros "HΦ" (?) "HF". iIntros (??) "??".
  iApply sim_tgt_stop. iApply "HΦ". iIntros (?) "Hsim".
  iApply ("Hsim" with "[$] [//] [$] [$]").
Qed.

Lemma sim_tgt_expr_stop2 e Π Φ os :
  Φ e os Π -∗ TGT e @ ? os [{ Π }] {{ Φ }}.
Proof. iIntros "HΦ" (?) "HF". by iApply "HF". Qed.

Lemma sim_tgt_expr_elim os K e Π σ :
  mexpr_rel Λ σ (mfill Λ K e) →
  mstate_interp Λ σ os -∗
  TGT e @ ? os [{ Π }] {{ _, _, _, False }} -∗
  σ ≈{Λ}≈>ₜ Π.
Proof.
  iIntros (?) "Hσ He". iApply (sim_tgt_expr_raw_elim with "[$]"); [done|].
  iApply "He". by iIntros (???) "?".
Qed.

Lemma sim_tgt_expr_step_None e Π Φ os :
  (∀ K σ κ Pσ, ⌜mexpr_rel Λ σ (mfill Λ K e)⌝ -∗ ⌜Λ.(m_step) σ κ Pσ⌝ -∗ mstate_interp Λ σ os ={∅}=∗ ▷ₒ
      (∃ os' σ' e', ⌜κ = None⌝ ∗ ⌜Pσ σ'⌝ ∗ ⌜mexpr_rel Λ σ' (mfill Λ K e')⌝ ∗ mstate_interp Λ σ' os' ∗ TGT e' @ ? os' [{ Π }] {{Φ}})) -∗
  TGT e @ ? os [{ Π }] {{ Φ }}.
Proof.
  iIntros "Hs" (?) "HΦ". iApply sim_tgt_expr_raw_step. iIntros (?????) "?".
  iMod ("Hs" with "[//] [//] [$]") as "Hs". do 2 iModIntro. iRight.
  iDestruct "Hs" as (??????) "[? Hsim]". iExists _, _, _. iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
  iFrame. by iApply "Hsim".
Qed.

Lemma sim_tgt_expr_step e Φ Π os :
  (∀ K σ κ Pσ, ⌜mexpr_rel Λ σ (mfill Λ K e)⌝ -∗ ⌜m_step Λ σ κ Pσ⌝ -∗ mstate_interp Λ σ os ={∅}=∗ ▷ₒ
     Π κ (λ P, ∃ σ', ⌜Pσ σ'⌝ ∗
       ((∀ os' e',
           ⌜mexpr_rel Λ σ' (mfill Λ K e')⌝ -∗
           mstate_interp Λ σ' os' -∗
           σ' ⤇ₜ λ Π', TGT e' @ ? os' [{ Π' }] {{ Φ }}) -∗
          P σ'))) -∗
  TGT e @ ? os [{ Π }] {{ Φ }}.
Proof.
  iIntros "Hsim" (?). iIntros "HΦ" (??) "#? Hσ".
  iApply sim_tgt_bi_mono1. iApply sim_tgt_step_end. iIntros (???). iMod ("Hsim" with "[//] [//] [$]") as "Hsim".
  do 2 iModIntro. iApply (bi_mono1_intro with "Hsim"). iIntros (?) "[% [% Hsim]]".
  iExists _. iSplit; [done|]. iApply "Hsim".
  iIntros (???) "?". iIntros (?) "Hsim". iApply (sim_tgt_expr_raw_elim with "[$]"); [done|].
  by iApply "Hsim".
Qed.

End sim_tgt.

(** * [sim_src_expr] *)
Definition sim_src_expr_raw {EV Σ Λ} `{!dimsumGS Σ}
  (e : mexpr Λ) (os : option (mstate Λ)) (Π : option EV → m_state Λ → iProp Σ) : iProp Σ :=
  (∀ σ, ⌜mexpr_rel Λ σ e⌝ -∗ ord_later_ctx -∗ mstate_interp Λ σ os -∗
    σ ≈{ Λ }≈>ₛ Π)%I.

Notation "'SRC' e @ ? os [{ Π }]" := (sim_src_expr_raw e os Π%I) (at level 70, Π at level 200,
  format "'[hv' 'SRC'  e  '/' @  ?  os  [{  '[ ' Π  ']' }] ']'") : bi_scope.
Notation "'SRC' e @ s [{ Π }]" := (sim_src_expr_raw e (Some s) Π%I) (at level 70, Π at level 200,
  format "'[hv' 'SRC'  e  '/' @  s  [{  '[ ' Π  ']' }] ']'") : bi_scope.
Notation "'SRC' e [{ Π }]" := (sim_src_expr_raw e None Π%I) (at level 70, Π at level 200,
  format "'[hv' 'SRC'  e  '/' [{  '[ ' Π  ']' }] ']'") : bi_scope.

Definition sim_src_expr {EV Σ Λ} `{!dimsumGS Σ}
  (e : mexpr Λ) (os : option (mstate Λ)) (Π : option EV → m_state Λ → iProp Σ)
  (Φ : mexpr Λ → option (mstate Λ) → (option EV → m_state Λ → iProp Σ) → iProp Σ): iProp Σ :=
  ∀ K, (∀ e' os' Π', Φ e' os' Π' -∗ SRC mfill Λ K e' @ ? os' [{ Π' }]) -∗ SRC mfill Λ K e @ ? os [{ Π }].

Notation "'SRC' e @ ? os [{ Π }] {{ Φ } }" := (sim_src_expr e os Π%I Φ%I)
  (at level 70, Π, Φ at level 200, only parsing) : bi_scope.
Notation "'SRC' e @ s [{ Π }] {{ Φ } }" := (sim_src_expr e (Some s) Π%I Φ%I)
  (at level 70, Π, Φ at level 200, only parsing) : bi_scope.
Notation "'SRC' e [{ Π }] {{ Φ } }" := (sim_src_expr e None Π%I Φ%I)
  (at level 70, Π, Φ at level 200, only parsing) : bi_scope.

Notation "'SRC' e @ ? os [{ Π }] {{ e' , os' , Π' , Φ } }" := (sim_src_expr e os Π%I (λ e' os' Π', Φ%I)) (at level 70, Π, Φ at level 200,
  format "'[hv' 'SRC'  e  '/' @  ?  os  [{  '[ ' Π  ']' }]  {{  '[ ' e' ,  os' ,  Π' ,  '/' Φ  ']' } } ']'") : bi_scope.
Notation "'SRC' e @ s [{ Π }] {{ e' , os' , Π' , Φ } }" := (sim_src_expr e (Some s) Π%I (λ e' os' Π', Φ%I)) (at level 70, Π, Φ at level 200,
  format "'[hv' 'SRC'  e  '/' @  s  [{  '[ ' Π  ']' }]  {{  '[ ' e' ,  os' ,  Π' ,  '/' Φ  ']' } } ']'") : bi_scope.
Notation "'SRC' e [{ Π }] {{ e' , os' , Π' , Φ } }" := (sim_src_expr e None Π%I (λ e' os' Π', Φ%I)) (at level 70, Π, Φ at level 200,
  format "'[hv' 'SRC'  e  '/' [{  '[ ' Π  ']' }]  {{  '[ ' e' ,  os' ,  Π' ,  '/' Φ  ']' } } ']'") : bi_scope.

Section sim_src.
Context {EV} {Σ} {Λ : mod_lang EV Σ} `{!dimsumGS Σ}.
Implicit Types (e : mexpr Λ).

Lemma sim_src_expr_raw_step e Π os :
  (∀ σ, ⌜mexpr_rel Λ σ e⌝ -∗ mstate_interp Λ σ os ==∗
    ∃ κ Pσ, ⌜m_step Λ σ κ Pσ⌝ ∗
     ∀ σ', ⌜Pσ σ'⌝ ={∅}=∗ if κ is Some _ then Π κ σ' else
       ∃ os' e', ⌜mexpr_rel Λ σ' e'⌝ ∗ mstate_interp Λ σ' os' ∗ SRC e' @ ? os' [{ Π }]) -∗
  SRC e @ ? os [{ Π }].
Proof.
  iIntros "HΠ" (σ ?) "#??". iApply fupd_sim_src.
  iMod ("HΠ" with "[//] [$]") as (???) "HΠ". iModIntro.
  iApply sim_src_step; [done..|]. iIntros (??).
  iMod ("HΠ" with "[//]") as "HΠ". case_match; [done|]. iModIntro.
  iDestruct ("HΠ") as (???) "[? Hsim]".
  by iApply "Hsim".
Qed.

Lemma sim_src_expr_raw_elim e Π σ os :
  mexpr_rel Λ σ e →
  mstate_interp Λ σ os -∗
  SRC e @ ? os [{ Π }] -∗
  σ ≈{Λ}≈>ₛ Π.
Proof. iIntros (?) "Hσ He". iApply sim_src_ctx. iIntros "#?". by iApply "He". Qed.

Lemma fupd_sim_src_expr e Π Φ os :
  (|={∅}=> SRC e @ ? os [{ Π }] {{ Φ }}) -∗
  SRC e @ ? os [{ Π }] {{ Φ }}.
Proof.
  iIntros "Hsim" (?) "HΦ". iIntros (??) "#??". iApply fupd_sim_src. iApply ("Hsim" with "[$] [//] [//] [$]").
Qed.

Lemma sim_src_expr_ctx e Π Φ os :
  (ord_later_ctx -∗ SRC e @ ? os [{ Π }] {{ Φ }}) -∗
  SRC e @ ? os [{ Π }] {{ Φ }}.
Proof.
  iIntros "Hsim" (?) "HΦ". iIntros (??) "#?". iApply ("Hsim" with "[$] [$] [//] [$]").
Qed.

Lemma sim_src_expr_bind e Π Φ K os :
  SRC e @ ? os [{ Π }] {{ e', os', Π', SRC mfill Λ K e' @ ? os' [{ Π' }] {{ Φ }} }} -∗
  SRC mfill Λ K e @ ? os [{ Π }] {{ Φ }}.
Proof.
  iIntros "Hsim" (?) "HΦ". rewrite mfill_comp. iApply "Hsim".
  iIntros (???) "Htgt". rewrite -mfill_comp. by iApply "Htgt".
Qed.

Lemma sim_src_expr_wand1 e Π Π' Φ os :
  SRC e @ ? os [{ Π' }] {{ Φ }} -∗
  (∀ κ P, Π' κ P -∗ Π κ P) -∗
  SRC e @ ? os [{ Π }] {{ Φ }}.
Proof.
  iIntros "Hsim Hwand" (?) "HΦ".
  iIntros (??) "#? Hσ".
  iApply (sim_src_wand with "[Hσ HΦ Hsim] Hwand").
  iApply ("Hsim" with "[$] [//] [$] [$]").
Qed.

Lemma sim_src_expr_wand e Π Φ Φ' os :
  SRC e @ ? os [{ Π }] {{ Φ' }} -∗
  (∀ e' os' Π', Φ' e' os' Π' -∗ Φ e' os' Π') -∗
  SRC e @ ? os [{ Π }] {{ Φ }}.
Proof. iIntros "Hsim Hwand" (?) "HΦ". iApply "Hsim". iIntros (???) "Hsim". iApply "HΦ". by iApply "Hwand". Qed.

Lemma sim_src_expr_stop1 e Π Φ os :
  (∀ σ, σ ⤇ₛ (λ Π', SRC e @ ? os [{ Π' }] {{ Φ }}) -∗ Π None σ) -∗
  SRC e @ ? os [{ Π }] {{ Φ }}.
Proof.
  iIntros "HΦ" (?) "HF". iIntros (??) "??".
  iApply sim_src_stop. iApply "HΦ". iIntros (?) "Hsim".
  iApply ("Hsim" with "[$] [//] [$] [$]").
Qed.

Lemma sim_src_expr_stop2 e Π Φ os :
  Φ e os Π -∗ SRC e @ ? os [{ Π }] {{ Φ }}.
Proof. iIntros "HΦ" (?) "HF". by iApply "HF". Qed.

Lemma sim_src_expr_elim os e Π σ K :
  mexpr_rel Λ σ (mfill Λ K e) →
  mstate_interp Λ σ os -∗
  SRC e @ ? os [{ Π }] {{ _, _, _, False }} -∗
  σ ≈{Λ}≈>ₛ Π.
Proof.
  iIntros (?) "Hσ He". iApply (sim_src_expr_raw_elim with "[$]"); [done|].
  iApply "He". by iIntros (???) "?".
Qed.

Lemma sim_src_expr_step_None e Π Φ os :
  (∀ K σ, ⌜mexpr_rel Λ σ (mfill Λ K e)⌝ -∗ mstate_interp Λ σ os ==∗
    ∃ Pσ, ⌜m_step Λ σ None Pσ⌝ ∗
     ∀ σ', ⌜Pσ σ'⌝ ={∅}=∗ ∃ os' e', ⌜mexpr_rel Λ σ' (mfill Λ K e')⌝ ∗
       mstate_interp Λ σ' os' ∗ SRC e' @ ? os' [{ Π }] {{ Φ }}) -∗
  SRC e @ ? os [{ Π }] {{ Φ }}.
Proof.
  iIntros "Hs" (?) "HΦ". iApply sim_src_expr_raw_step. iIntros (??) "?".
  iMod ("Hs" with "[//] [$]") as (??) "Hs". iModIntro. iExists _, _. iSplit; [done|].
  iIntros (??). iMod ("Hs" with "[//]") as (???) "[? Hs]". iModIntro. iExists _, _. iFrame. iSplit; [done|].
  by iApply "Hs".
Qed.

Lemma sim_src_expr_step e Φ Π os :
  (∀ K σ, ⌜mexpr_rel Λ σ (mfill Λ K e)⌝ -∗ mstate_interp Λ σ os ==∗
     ∃ κ' Pσ_s, ⌜m_step Λ σ κ' Pσ_s⌝ ∗
       ∀ σ', ⌜Pσ_s σ'⌝ ={∅}=∗
          ((∀ os' e',
              ⌜mexpr_rel Λ σ' (mfill Λ K e')⌝ -∗
              mstate_interp Λ σ' os' -∗
              σ' ⤇ₛ λ Π', SRC e' @ ? os' [{ Π' }] {{ Φ }}) -∗
          Π κ' σ')) -∗
  SRC e @ ? os [{ Π }] {{ Φ }}.
Proof.
  iIntros "He" (?). iIntros "HΦ" (??) "#? Hσ". iApply fupd_sim_src.
  iMod ("He" with "[//] [$]") as (???) "Hsim". iModIntro.
  iApply sim_src_step_end; [done|]. iIntros (??). iMod ("Hsim" with "[//]") as "Hsim".
  iModIntro. iApply "Hsim". iIntros (???) "?". iIntros (?) "Hsim".
  iApply (sim_src_expr_raw_elim with "[$]"); [done|].
  by iApply "Hsim".
Qed.

End sim_src.

Global Typeclasses Opaque sim_tgt_expr sim_src_expr.
Global Opaque sim_tgt_expr sim_src_expr.

(* (** * [sim_expr_s] *) *)
(* Definition sim_expr_s `{!dimsumGS EV Σ Λ_t Λ_s} (q : Qp) (e : mexpr Λ_s) : iProp Σ := *)
(*   ghost_var dimsum_ghost_var_s_name q e. *)

(* Notation "'⤇{' q } e" := (sim_expr_s q e) *)
(*   (at level 20, format "'⤇{' q }  e") : bi_scope. *)
(* Notation "'⤇' e" := (sim_expr_s (1/2) e) *)
(*   (at level 20, format "'⤇'  e") : bi_scope. *)
(* Notation "'⤇?' e" := (if e is Some e' then sim_expr_s (1/2) e' else True)%I *)
(*   (at level 20, format "'⤇?'  e") : bi_scope. *)

(* Section sim_expr. *)
(*   Context `{!dimsumGS EV Σ Λ_t Λ_s}. *)

(*   Lemma sim_expr_s_agree e1 e2 : *)
(*     ⤇ e1 -∗ ⤇ e2 -∗ ⌜e1 = e2⌝. *)
(*   Proof. iIntros "??". by iDestruct (ghost_var_agree with "[$] [$]") as %->. Qed. *)

(*   Lemma sim_expr_s_update e' e1 e2 : *)
(*     ⤇ e1 -∗ ⤇ e2 ==∗ ⤇ e' ∗ ⤇ e'. *)
(*   Proof. iApply ghost_var_update_halves. Qed. *)
(* End sim_expr. *)


(*

TGT e init [{ λ κ, if κ in locle then locle ≈>ₜ ... else src ≈>ₛ λ κ', κ = κ' ... }]
----------------------------------------
memmove ≈>ₜ λ κ, if κ in locle then locle ≈>ₜ ... else src ≈>ₛ λ κ', κ = κ' ...
-----------------------
memmove + locle ≈>ₜ λ κ, src ≈>ₛ λ κ', κ = κ' ...
-----------------------
memmove + locle <= src


TGT Call locle [{ Π }] {{ λ e' Π', ∃ b, e' = ValBool b ∗ Π' = Π }}


TGT if b then ... else [{ Π }] {{ Φ }}
---------------------------------------------------
TGT Call locle [{ Π }] {{ λ e Π', TGT if e then ... else [{ Π' }] {{ Φ }} }}
---------------------------------------------------
TGT if Call locle then... else ... [{ Π }] {{ Φ }}


Left, (Call main vs, h), locle_prog ⪯ main_spec_prog
---------------------------------------------
None, (Waiting, ∅), locle_prog ⪯ main_spec_prog
----------------------------------------------
[main ∪r memmove]r +r [locle]s <= [main_spec]s



*)
