From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From dimsum.core Require Export module trefines.
From dimsum.core Require Import nb_mod.
From dimsum.core.iris Require Export ord_later sim.
Set Default Proof Using "Type".

(** * mod_lang *)
Structure mod_lang EV Σ := ModLang {
  mexpr : Type;
  mtrans :> mod_trans EV;
  mexpr_rel : mtrans.(m_state) → mexpr → Prop;
  mstate_interp : mtrans.(m_state) → iProp Σ;
}.
Global Arguments mexpr {_ _} _.
Global Arguments mtrans {_ _} _.
Global Arguments mexpr_rel {_ _} _ _ _.
Global Arguments mstate_interp {_ _} _ _.

Definition mexprO {Σ EV} {Λ : mod_lang Σ EV} := leibnizO (mexpr Λ).

Canonical Structure nb_mod_lang EV Σ : mod_lang EV Σ := {|
  mexpr := unit;
  mtrans := nb_trans EV;
  mexpr_rel _ _ := True;
  mstate_interp _ := True%I;
|}.

(** * [sim_tgt_expr] *)
Definition sim_tgt_expr_raw {EV Σ Λ} `{!dimsumGS Σ}
  (e : mexpr Λ) (Π : option EV → ((m_state Λ → iProp Σ) → iProp Σ) → iProp Σ) : iProp Σ :=
  (∀ σ, ⌜mexpr_rel Λ σ e⌝ -∗ ord_later_ctx -∗ mstate_interp Λ σ -∗
    σ ≈{ Λ }≈>ₜ Π)%I.

Notation "'TGT' e [{ Π }]" := (sim_tgt_expr_raw e Π%I) (at level 70, Π at level 200,
  format "'[hv' 'TGT'  e  '/' [{  '[ ' Π  ']' }] ']'") : bi_scope.

Definition sim_tgt_expr {EV Σ Λ} `{!dimsumGS Σ}
  (e : mexpr Λ) (Π : option EV → ((m_state Λ → iProp Σ) → iProp Σ) → iProp Σ)
  (Φ : mexpr Λ → (option EV → ((m_state Λ → iProp Σ) → iProp Σ) → iProp Σ) → iProp Σ): iProp Σ :=
  (∀ e' Π', Φ e' Π' -∗ TGT e' [{ Π' }]) -∗ TGT e [{ Π }].

Notation "'TGT' e [{ Π }] {{ Φ } }" := (sim_tgt_expr e Π%I Φ%I) (at level 70, Π, Φ at level 200,
  format "'[hv' 'TGT'  e  '/' [{  '[ ' Π  ']' }]  {{  '[ ' Φ  ']' } } ']'") : bi_scope.

Section sim_tgt.
Context {EV} {Σ} {Λ : mod_lang EV Σ} `{!dimsumGS Σ}.
Implicit Types (e : mexpr Λ).

Lemma sim_tgt_expr_raw_step e Π:
  (∀ σ κ Pσ, ⌜mexpr_rel Λ σ e⌝ -∗ ⌜Λ.(m_step) σ κ Pσ⌝ -∗ mstate_interp Λ σ ={∅}=∗ ▷ₒ
      ((∃ P, Π κ P ∗ ∀ P', P P' -∗ ∃ σ', ⌜Pσ σ'⌝ ∗ P' σ') ∨
         ∃ σ' e', ⌜κ = None⌝ ∗ ⌜Pσ σ'⌝ ∗ ⌜mexpr_rel Λ σ' e'⌝ ∗ mstate_interp Λ σ' ∗ TGT e' [{ Π }])) -∗
  TGT e [{ Π }].
Proof.
  iIntros "HΠ" (σ ?) "#??".
  iApply sim_tgt_step. iIntros (???). iMod ("HΠ" with "[//] [//] [$]") as "Hsim". do 2 iModIntro.
  iDestruct "Hsim" as "[$|(%&%&%&%&%&?&Hsim)]". iRight. iExists _. iSplit; [done|]. iSplit; [done|].
  by iApply "Hsim".
Qed.

Lemma sim_tgt_expr_raw_elim e Π σ :
  mexpr_rel Λ σ e →
  mstate_interp Λ σ -∗
  TGT e [{ Π }] -∗
  σ ≈{Λ}≈>ₜ Π.
Proof. iIntros (?) "Hσ He". iApply sim_tgt_ctx. iIntros "#?". by iApply "He". Qed.

Lemma sim_tgt_expr_bind e Π Φ :
  TGT e [{ Π }] {{ λ e' Π', TGT e' [{ Π' }] {{ Φ }} }} -∗
  TGT e [{ Π }] {{ Φ }}.
Proof. iIntros "Hsim HΦ". iApply "Hsim". iIntros (??) "Hsim". by iApply "Hsim". Qed.

Lemma sim_tgt_expr_wand e Π Φ Φ' :
  TGT e [{ Π }] {{ Φ' }} -∗
  (∀ e' Π', Φ' e' Π' -∗ Φ e' Π') -∗
  TGT e [{ Π }] {{ Φ }}.
Proof. iIntros "Hsim Hwand HΦ". iApply "Hsim". iIntros (??) "Hsim". iApply "HΦ". by iApply "Hwand". Qed.

Lemma sim_tgt_expr_stop e Π Φ :
  Φ e Π -∗ TGT e [{ Π }] {{ Φ }}.
Proof. iIntros "HΦ HF". by iApply "HF". Qed.

Lemma sim_tgt_expr_step_None e Π Φ :
  (∀ σ κ Pσ, ⌜mexpr_rel Λ σ e⌝ -∗ ⌜Λ.(m_step) σ κ Pσ⌝ -∗ mstate_interp Λ σ ={∅}=∗ ▷ₒ
      (∃ σ' e', ⌜κ = None⌝ ∗ ⌜Pσ σ'⌝ ∗ ⌜mexpr_rel Λ σ' e'⌝ ∗ mstate_interp Λ σ' ∗ TGT e' [{ Π }] {{Φ}})) -∗
  TGT e [{ Π }] {{ Φ }}.
Proof.
  iIntros "Hs HΦ". iApply sim_tgt_expr_raw_step. iIntros (?????) "?".
  iMod ("Hs" with "[//] [//] [$]") as "Hs". do 2 iModIntro. iRight.
  iDestruct "Hs" as (?????) "[? Hsim]". iExists _, _. iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
  iFrame. by iApply "Hsim".
Qed.

Lemma sim_tgt_expr_step e Φ Π :
  (∀ σ κ Pσ, ⌜mexpr_rel Λ σ e⌝ -∗ ⌜Λ.(m_step) σ κ Pσ⌝ -∗ mstate_interp Λ σ ={∅}=∗ ▷ₒ
     Π κ (λ P, ∃ σ', ⌜Pσ σ'⌝ ∗
       ((∀ Π' e',
           ⌜mexpr_rel Λ σ' e'⌝ -∗
           mstate_interp Λ σ' -∗
           TGT e' [{ Π' }] {{ Φ }} -∗
           σ' ≈{Λ}≈>ₜ Π') -∗
          P σ'))) -∗
  TGT e [{ Π }] {{ Φ }}.
Proof.
  iIntros "Hsim HΦ" (??) "#? Hσ".
  iApply sim_tgt_step_end. iIntros (???). iMod ("Hsim" with "[//] [//] [$]") as "Hsim".
  do 2 iModIntro. iExists _. iFrame. iIntros (?) "[% [% Hsim]]".
  iExists _. iSplit; [done|]. iApply "Hsim".
  iIntros (???) "? Hsim". iApply (sim_tgt_expr_raw_elim with "[$]"); [done|].
  by iApply "Hsim".
Qed.

End sim_tgt.

(** * [sim_src_expr] *)
Definition sim_src_expr_raw {EV Σ Λ} `{!dimsumGS Σ}
  (e : mexpr Λ) (Π : option EV → m_state Λ → iProp Σ) : iProp Σ :=
  (∀ σ, ⌜mexpr_rel Λ σ e⌝ -∗ ord_later_ctx -∗ mstate_interp Λ σ -∗
    σ ≈{ Λ }≈>ₛ Π)%I.

Notation "'SRC' e [{ Π }]" := (sim_src_expr_raw e Π%I) (at level 70, Π at level 200,
  format "'[hv' 'SRC'  e  '/' [{  '[ ' Π  ']' }] ']'") : bi_scope.

Definition sim_src_expr {EV Σ Λ} `{!dimsumGS Σ}
  (e : mexpr Λ) (Π : option EV → m_state Λ → iProp Σ)
  (Φ : mexpr Λ → (option EV → m_state Λ → iProp Σ) → iProp Σ): iProp Σ :=
  (∀ e' Π', Φ e' Π' -∗ SRC e' [{ Π' }]) -∗ SRC e [{ Π }].

Notation "'SRC' e [{ Π }] {{ Φ } }" := (sim_src_expr e Π%I Φ%I) (at level 70, Π, Φ at level 200,
  format "'[hv' 'SRC'  e  '/' [{  '[ ' Π  ']' }]  {{  '[ ' Φ  ']' } } ']'") : bi_scope.

Section sim_src.
Context {EV} {Σ} {Λ : mod_lang EV Σ} `{!dimsumGS Σ}.
Implicit Types (e : mexpr Λ).

Lemma sim_src_expr_raw_step e Π:
  (∀ σ, ⌜mexpr_rel Λ σ e⌝ -∗ mstate_interp Λ σ ==∗
    ∃ κ Pσ, ⌜m_step Λ σ κ Pσ⌝ ∗
     ∀ σ', ⌜Pσ σ'⌝ ={∅}=∗ if κ is Some _ then Π κ σ' else
       ∃ e', ⌜mexpr_rel Λ σ' e'⌝ ∗ mstate_interp Λ σ' ∗ SRC e' [{ Π }]) -∗
  SRC e [{ Π }].
Proof.
  iIntros "HΠ" (σ ?) "#??". iApply fupd_sim_src.
  iMod ("HΠ" with "[//] [$]") as (???) "HΠ". iModIntro.
  iApply sim_src_step; [done..|]. iIntros (??).
  iMod ("HΠ" with "[//]") as "HΠ". case_match; [done|]. iModIntro.
  iDestruct ("HΠ") as (??) "[? Hsim]".
  by iApply "Hsim".
Qed.

Lemma sim_src_expr_raw_elim e Π σ :
  mexpr_rel Λ σ e →
  mstate_interp Λ σ -∗
  SRC e [{ Π }] -∗
  σ ≈{Λ}≈>ₛ Π.
Proof. iIntros (?) "Hσ He". iApply sim_src_ctx. iIntros "#?". by iApply "He". Qed.

Lemma sim_src_expr_bind e Π Φ :
  SRC e [{ Π }] {{ λ e' Π', SRC e' [{ Π' }] {{ Φ }} }} -∗
  SRC e [{ Π }] {{ Φ }}.
Proof. iIntros "Hsim HΦ". iApply "Hsim". iIntros (??) "Hsim". by iApply "Hsim". Qed.

Lemma sim_src_expr_wand e Π Φ Φ' :
  SRC e [{ Π }] {{ Φ' }} -∗
  (∀ e' Π', Φ' e' Π' -∗ Φ e' Π') -∗
  SRC e [{ Π }] {{ Φ }}.
Proof. iIntros "Hsim Hwand HΦ". iApply "Hsim". iIntros (??) "Hsim". iApply "HΦ". by iApply "Hwand". Qed.

Lemma sim_src_expr_stop e Π Φ :
  Φ e Π -∗ SRC e [{ Π }] {{ Φ }}.
Proof. iIntros "HΦ HF". by iApply "HF". Qed.

Lemma sim_src_expr_step_None e Π Φ :
  (∀ σ, ⌜mexpr_rel Λ σ e⌝ -∗ mstate_interp Λ σ ==∗
    ∃ Pσ, ⌜m_step Λ σ None Pσ⌝ ∗
     ∀ σ', ⌜Pσ σ'⌝ ={∅}=∗ ∃ e', ⌜mexpr_rel Λ σ' e'⌝ ∗
       mstate_interp Λ σ' ∗ SRC e' [{ Π }] {{ Φ }}) -∗
  SRC e [{ Π }] {{ Φ }}.
Proof.
  iIntros "Hs HΦ". iApply sim_src_expr_raw_step. iIntros (??) "?".
  iMod ("Hs" with "[//] [$]") as (??) "Hs". iModIntro. iExists _, _. iSplit; [done|].
  iIntros (??). iMod ("Hs" with "[//]") as (??) "[$ Hs]". iModIntro. iExists _. iSplit; [done|].
  by iApply "Hs".
Qed.

Lemma sim_src_expr_step e Φ Π :
  (∀ σ, ⌜mexpr_rel Λ σ e⌝ -∗ mstate_interp Λ σ ==∗
     ∃ κ' Pσ_s, ⌜m_step Λ σ κ' Pσ_s⌝ ∗
       ∀ σ', ⌜Pσ_s σ'⌝ ={∅}=∗
          ((∀ Π' e',
              ⌜mexpr_rel Λ σ' e'⌝ -∗
              mstate_interp Λ σ' -∗
              SRC e' [{ Π' }] {{ Φ }} -∗
              σ' ≈{Λ}≈>ₛ Π') -∗
          Π κ' σ')) -∗
  SRC e [{ Π }] {{ Φ }}.
Proof.
  iIntros "He HΦ" (??) "#? Hσ". iApply fupd_sim_src.
  iMod ("He" with "[//] [$]") as (???) "Hsim". iModIntro.
  iApply sim_src_step_end; [done|]. iIntros (??). iMod ("Hsim" with "[//]") as "Hsim".
  iModIntro. iApply "Hsim". iIntros (???) "? Hsim".
  iApply (sim_src_expr_raw_elim with "[$]"); [done|].
  by iApply "Hsim".
Qed.

End sim_src.

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
