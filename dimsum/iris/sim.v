From iris.bi Require Import bi fixpoint.
From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.base_logic.lib Require Export ghost_var.
From iris.bi Require Export weakestpre.
From dimsum.core Require Export module trefines.
From dimsum.core Require Import nb_mod.
From dimsum.core.iris Require Export ord_later sim_steps.
Set Default Proof Using "Type".


(** * mod_lang *)
Structure mod_lang EV Σ := ModLang {
  mexpr : Type;
  mtrans : mod_trans EV;
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

(** * dimsumGS *)
Class dimsumPreG (Σ : gFunctors) (E_s : Type) := RefirisPreG {
  dimsum_pre_invG :> invGpreS Σ;
  dimsum_pre_ord_laterG :> ord_laterPreG Σ;
  dimsum_pre_ghost_varG_s :> ghost_varG Σ E_s;
}.

Class dimsumGS (EV : Type) (Σ : gFunctors) (Λ_t Λ_s : mod_lang EV Σ) := DimsumGS {
  dimsum_invGS :> invGS_gen HasNoLc Σ;
  dimsum_ord_laterGS :> ord_laterGS Σ;
  dimsum_ghost_varG_s :> ghost_varG Σ (mexpr Λ_s);
  dimsum_ghost_var_s_name : gname;
}.
Global Opaque dimsum_invGS.

(** * [sim_expr_s] *)
Definition sim_expr_s `{!dimsumGS EV Σ Λ_t Λ_s} (q : Qp) (e : mexpr Λ_s) : iProp Σ :=
  ghost_var dimsum_ghost_var_s_name q e.

Notation "'⤇{' q } e" := (sim_expr_s q e)
  (at level 20, format "'⤇{' q }  e") : bi_scope.
Notation "'⤇' e" := (sim_expr_s (1/2) e)
  (at level 20, format "'⤇'  e") : bi_scope.
Notation "'⤇?' e" := (if e is Some e' then sim_expr_s (1/2) e' else True)%I
  (at level 20, format "'⤇?'  e") : bi_scope.

Section sim_expr.
  Context `{!dimsumGS EV Σ Λ_t Λ_s}.

  Lemma sim_expr_s_agree e1 e2 :
    ⤇ e1 -∗ ⤇ e2 -∗ ⌜e1 = e2⌝.
  Proof. iIntros "??". by iDestruct (ghost_var_agree with "[$] [$]") as %->. Qed.

  Lemma sim_expr_s_update e' e1 e2 :
    ⤇ e1 -∗ ⤇ e2 ==∗ ⤇ e' ∗ ⤇ e'.
  Proof. iApply ghost_var_update_halves. Qed.
End sim_expr.

(** * [sim_pre] *)
Definition sim_pre `{!dimsumGS EV Σ Λ_t Λ_s}
    (sim : leibnizO coPset -d> mexprO -d> (mexprO -d> iPropO Σ) -d> iPropO Σ) :
    leibnizO coPset -d> mexprO -d> (mexprO -d> iPropO Σ) -d> iPropO Σ := λ E e_t Φ,
  (∀ σ_t σ_s e_s, ⌜mexpr_rel Λ_t σ_t e_t⌝ -∗ ⌜mexpr_rel Λ_s σ_s e_s⌝ -∗ ord_later_ctx -∗
              ⤇ e_s -∗ mstate_interp Λ_t σ_t -∗ mstate_interp Λ_s σ_s ={E}=∗
      (⤇ e_s ∗ mstate_interp Λ_t σ_t ∗
         mstate_interp Λ_s σ_s ∗ Φ e_t) ∨
      (∀ κ Pσ_t, ⌜(mtrans Λ_t).(m_step) σ_t κ Pσ_t⌝ ={E,∅}=∗ ▷ₒ
         (σ_s ≈{ mtrans Λ_s, κ }≈> (λ σ_s', ∃ σ_t' e_t' e_s', ⌜Pσ_t σ_t'⌝ ∗
            ⌜mexpr_rel Λ_t σ_t' e_t'⌝ ∗ ⌜mexpr_rel Λ_s σ_s' e_s'⌝ ∗ ⤇ e_s' ∗
            |={∅, E}=> mstate_interp Λ_t σ_t' ∗ mstate_interp Λ_s σ_s' ∗ sim E e_t' Φ)))
      ∨ |={E,∅}=> σ_s ≈{ mtrans Λ_s, None }≈> (λ σ_s', ∃ e_s', ⌜mexpr_rel Λ_s σ_s' e_s'⌝ ∗ ⤇ e_s' ∗
            |={∅, E}=> mstate_interp Λ_t σ_t ∗ mstate_interp Λ_s σ_s' ∗ sim E e_t Φ))%I.

Global Instance sim_pre_ne `{!dimsumGS EV Λ_t Λ_s Σ} n:
  Proper ((dist n ==> dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n ==> dist n) sim_pre.
Proof.
  move => ?? Hsim ?? -> ?? -> ?? HΦ. rewrite /sim_pre.
  repeat (f_equiv || eapply Hsim || eapply HΦ || reflexivity || intros ?? ->).
Qed.

Lemma sim_pre_mono `{!dimsumGS EV Λ_t Λ_s Σ} sim1 sim2:
  ⊢ □ (∀ E e_t Φ, sim1 E e_t Φ -∗ sim2 E e_t Φ )
  → ∀ E e_t Φ , sim_pre sim1 E e_t Φ -∗ sim_pre sim2 E e_t Φ.
Proof.
  iIntros "#Hinner" (E e_t Φ) "Hsim".
  iIntros (σ_t σ_s e_s ??) "#? ? Hσ_t Hσ_s".
  iMod ("Hsim" with "[//] [//] [//] [$] Hσ_t Hσ_s") as "[Hsim|[Hsim|Hsim]]";
    [by iLeft|iRight; iLeft| iRight; iRight].
  - iModIntro. iIntros (κ Pσ_t ?). iMod ("Hsim" with "[//]") as "Hsim". do 2 iModIntro.
    iApply (sim_steps_wand with "Hsim"). iIntros (?) "(%&%&%&%&%&%&?&Hsim)".
    iSplit!; [done..|]. iFrame. iMod "Hsim" as "[? [??]]". iModIntro. iFrame. by iApply "Hinner".
  - iModIntro. iMod "Hsim" as "Hsim". iModIntro.
    iApply (sim_steps_wand with "Hsim"). iIntros (?) "(%&%&?&Hsim)".
    iExists _. iSplit; [done|]. iFrame. iMod "Hsim" as "[? [??]]". iModIntro. iFrame. by iApply "Hinner".
Qed.

Local Instance sim_pre_monotone `{!dimsumGS EV Σ Λ_t Λ_s} :
  BiMonoPred (λ sim : prodO (prodO (leibnizO coPset) mexprO) (mexprO -d> iPropO Σ) -d> iPropO Σ, uncurry3 (sim_pre (curry3 sim))).
Proof.
  constructor.
  - iIntros (Φ Ψ ??) "#Hinner". iIntros ([[??]?]) "Hsim" => /=. iApply sim_pre_mono; [|done].
    iIntros "!>" (???) "HΦ". by iApply ("Hinner" $! (_, _, _)).
  - move => sim Hsim n [[E1 e_t1] Φ1] [[E2 e_t2] Φ2] /= [[/=??]?].
    apply sim_pre_ne; eauto. move => ????????? /=. by apply: Hsim.
Qed.

Definition sim_def `{!dimsumGS EV Σ Λ_t Λ_s} : coPset → mexpr Λ_t → (mexpr Λ_t → iProp Σ) → iProp Σ :=
  curry3 (bi_least_fixpoint (λ sim : prodO (prodO (leibnizO coPset) mexprO) (mexprO -d> iPropO Σ) -d> iPropO Σ, uncurry3 (sim_pre (curry3 sim)))).
Definition sim_aux : seal (@sim_def). Proof. by eexists. Qed.
Definition sim := sim_aux.(unseal).
Global Arguments sim {EV Σ Λ_t Λ_s _}.
Lemma sim_eq `{!dimsumGS EV Σ Λ_t Λ_s} : sim = @sim_def EV Σ Λ_t Λ_s _.
Proof. rewrite -sim_aux.(seal_eq) //. Qed.

Notation "'TGT' et @ E {{ Φ } }" := (sim E et Φ%I) (at level 70, Φ at level 200,
  format "'[hv' 'TGT'  et  '/' @  E  {{  '[ ' Φ  ']' } } ']'") : bi_scope.

(** * [sim_both] *)
Definition sim_both `{!dimsumGS EV Σ Λ_t Λ_s} (E : coPset) (e_t : mexpr Λ_t) (e_s : mexpr Λ_s) (Φ : mexpr Λ_t → mexpr Λ_s → iProp Σ) : iProp Σ :=
  ⤇ e_s -∗ TGT e_t @ E {{ λ e_t', ∃ e_s', ⤇ e_s' ∗ Φ e_t' e_s' }}.
Notation "et '⪯{' E '}' es {{ Φ } }" := (sim_both E et es Φ%I) (at level 70, Φ at level 200,
  format "'[hv' et  '/' '⪯{' E '}'  '/' es  '/' {{  '[ ' Φ  ']' } } ']'") : bi_scope.

(** * [sim_src] *)
Definition sim_src `{!dimsumGS EV Σ Λ_t Λ_s}
  (E : coPset) (κ : option EV) (e_s : mexpr Λ_s) (Φ : mexpr Λ_s → iProp Σ) : iProp Σ :=
  ∀ σ_s, ⌜mexpr_rel Λ_s σ_s e_s⌝ -∗ ord_later_ctx -∗ mstate_interp Λ_s σ_s ={E,∅}=∗
    σ_s ≈{ mtrans Λ_s, κ }≈> (λ σ_s', ∃ e_s', ⌜mexpr_rel Λ_s σ_s' e_s'⌝ ∗
       |={∅, E}=> mstate_interp Λ_s σ_s' ∗ Φ e_s').

Notation "'SRC' e @ κ ; E {{ Φ } }" := (sim_src E κ e Φ%I) (at level 70, Φ at level 200,
  format "'[hv' 'SRC'  e  '/' @  κ ;  E  {{  '[ ' Φ  ']' } } ']'") : bi_scope.

Notation "'SRC' e @ E {{ Φ } }" := (sim_src E None e Φ%I) (at level 70, Φ at level 200,
  format "'[hv' 'SRC'  e  '/' @  E  {{  '[ ' Φ  ']' } } ']'") : bi_scope.


Section sim.
Context `{!dimsumGS EV Σ Λ_t Λ_s}.
Implicit Types P : iProp Σ.

(** * Lemmas about [sim] *)
Lemma sim_unfold E e_t Φ:
  TGT e_t @ E {{ Φ }} ⊣⊢ sim_pre sim E e_t Φ.
Proof. rewrite sim_eq /sim_def /curry3. apply: least_fixpoint_unfold. Qed.

Lemma sim_strong_ind (R: leibnizO coPset -d> mexprO -d> (mexprO -d> iPropO Σ) -d> iPropO Σ):
  NonExpansive3 R →
  ⊢ (□ ∀ E e_t Φ, sim_pre (λ E e_t Ψ, R E e_t Ψ ∧ TGT e_t @ E {{ Ψ }}) E e_t Φ -∗ R E e_t Φ)
    -∗ ∀ E e_t Φ, TGT e_t @ E {{ Φ }} -∗ R E e_t Φ.
Proof.
  iIntros (Hne) "#HPre". iIntros (E e_t Φ) "Hsim".
  rewrite sim_eq {2}/sim_def {1}/curry3.
  iApply (least_fixpoint_ind _ (uncurry3 R) with "[] Hsim").
  iIntros "!>" ([[??]?]) "Hsim" => /=. by iApply "HPre".
Qed.

Lemma sim_ind (R: leibnizO coPset -d> mexprO -d> (mexprO -d> iPropO Σ) -d> iPropO Σ):
  NonExpansive3 R →
  ⊢ (□ ∀ E e_t Φ, sim_pre R E e_t Φ -∗ R E e_t Φ)
    -∗ ∀ E e_t Φ, TGT e_t @ E {{ Φ }} -∗ R E e_t Φ .
Proof.
  iIntros (Hne) "#HPre". iApply sim_strong_ind. iIntros "!>" (E e_t Φ) "Hsim".
  iApply "HPre". iApply (sim_pre_mono with "[] Hsim").
  iIntros "!>" (???) "[? _]". by iFrame.
Qed.

Lemma sim_wand e_t E Φ Ψ:
  TGT e_t @ E {{ Φ }} -∗
  (∀ e_t, Φ e_t -∗ Ψ e_t) -∗
  TGT e_t @ E {{ Ψ }}.
Proof.
  iIntros "Hsim Hwand".
  pose (F := (λ E e_t Ψ, ∀ Φ, (∀ e_t', Ψ e_t' -∗ Φ e_t') -∗ TGT e_t @ E {{ Φ }})%I).
  iAssert (∀ Φ, TGT e_t @ E {{ Φ }} -∗ F E e_t Φ)%I as "Hgen"; last first.
  { iApply ("Hgen" with "Hsim"). done. }
  iIntros (?) "Hsim".
  iApply (sim_ind with "[] Hsim"). { solve_proper. }
  iIntros "!>" (?? ?) "Hsim". iIntros (?) "Hc".
  rewrite sim_unfold. iIntros (?????) "#? ? Hσ_t Hσ_s".
  iMod ("Hsim" with "[//] [//] [$] [$] Hσ_t Hσ_s") as "[[?[?[??]]]|[Hsim|Hsim]]".
  - iModIntro. iLeft. iFrame. by iApply "Hc".
  - iModIntro. iRight. iLeft. iIntros (???). iMod ("Hsim" with "[//]") as "Hsim". do 2 iModIntro.
    iApply (sim_steps_wand with "Hsim"). iIntros (?) "(%&%&%&%&%&%&?&Hsim)".
    iSplit!; [done..|]. iFrame. iMod "Hsim" as "[? [?Hsim]]". iModIntro. iFrame. by iApply "Hsim".
  - iModIntro. iRight. iRight. iMod "Hsim" as "Hsim". iModIntro.
    iApply (sim_steps_wand with "Hsim"). iIntros (?) "(%&%&?&Hsim)".
    iExists _. iSplit; [done|]. iFrame. iMod "Hsim" as "[? [?Hsim]]". iModIntro. iFrame. by iApply "Hsim".
Qed.

Lemma sim_bind e_t E Φ:
  TGT e_t @ E {{ λ e_t', TGT e_t' @ E {{ Φ }} }} -∗
  TGT e_t @ E {{ Φ }}.
Proof.
  iIntros "Hsim".
  pose (F := (λ E e_t Ψ, ∀ Φ, (∀ e_t', Ψ e_t' -∗ TGT e_t' @ E {{ Φ }}) -∗ TGT e_t @ E {{ Φ }})%I).
  iAssert (∀ Φ, TGT e_t @ E {{ Φ }} -∗ F E e_t Φ)%I as "Hgen"; last first.
  { iApply ("Hgen" with "Hsim"). iIntros (?) "?". done. }
  iIntros (?) "Hsim".
  iApply (sim_ind with "[] Hsim"). { solve_proper. }
  iIntros "!>" (?? ?) "Hsim". iIntros (?) "Hc".
  rewrite sim_unfold. iIntros (?????) "#? ? Hσ_t Hσ_s".
  iMod ("Hsim" with "[//] [//] [$] [$] Hσ_t Hσ_s") as "[[?[?[??]]]|[Hsim|Hsim]]".
  - iDestruct ("Hc" with "[$]") as "Hc". rewrite {1}sim_unfold.
    iApply ("Hc" with "[//] [//] [$] [$] [$] [$]").
  - iModIntro. iRight. iLeft. iIntros (???). iMod ("Hsim" with "[//]") as "Hsim". do 2 iModIntro.
    iApply (sim_steps_wand with "Hsim"). iIntros (?) "(%&%&%&%&%&%&?&Hsim)".
    iSplit!; [done..|]. iFrame. iMod "Hsim" as "[? [?Hsim]]". iModIntro. iFrame. by iApply "Hsim".
  - iModIntro. iRight. iRight. iMod "Hsim" as "Hsim". iModIntro.
    iApply (sim_steps_wand with "Hsim"). iIntros (?) "(%&%&?&Hsim)".
    iExists _. iSplit; [done|]. iFrame. iMod "Hsim" as "[? [?Hsim]]". iModIntro. iFrame. by iApply "Hsim".
Qed.

Lemma sim_stop E e_t Φ:
  Φ e_t -∗ TGT e_t @ E {{ Φ }}.
Proof. rewrite sim_unfold. iIntros "HΦ" (σ_t σ_s e_s' ??) "? ? Hσ_t Hσ_s". iLeft. by iFrame. Qed.

(** * Lemmas about [sim_both] *)
Lemma sim_both_to_tgt E e_t e_s Φ:
  (⤇ e_s -∗ TGT e_t @ E {{ λ e_t', ∃ e_s', ⤇ e_s' ∗ Φ e_t' e_s' }}) -∗ e_t ⪯{E} e_s {{ Φ }}.
Proof. done. Qed.

Lemma sim_tgt_to_both E e_t e_s Φ:
  ⤇ e_s -∗
  e_t ⪯{E} e_s {{ λ e_t' e_s', ⤇ e_s' -∗ Φ e_t' }} -∗
  TGT e_t @ E {{ Φ }}.
Proof.
  iIntros "He Hsim".
  iDestruct ("Hsim" with "He") as "Hsim".
  iApply (sim_wand with "Hsim"). iIntros (?) "[%[? Hsim]]".
  by iApply "Hsim".
Qed.

Lemma sim_both_stop E e_t e_s Φ:
  Φ e_t e_s -∗ e_t ⪯{E} e_s {{ Φ }}.
Proof. iIntros "HΦ ?". iApply sim_stop. iExists _. iFrame. Qed.

(** * Lemmas about [sim_src] *)
Lemma sim_tgt_to_src E e_t e_s Φ:
  ⤇ e_s -∗
  SRC e_s @ E {{ λ e_s', ⤇ e_s' -∗ TGT e_t @ E {{ Φ }} }} -∗
  TGT e_t @ E {{ Φ }}.
Proof.
  iIntros "He Hsim".
  rewrite {2}sim_unfold. iIntros (?????) "#? ???". iModIntro.
  iDestruct (sim_expr_s_agree with "[$] [$]") as %->.
  iRight. iRight. iMod ("Hsim" with "[//] [$] [$]") as "Hsim".
  iModIntro. iApply (sim_steps_wand_strong with "Hsim"). iIntros (?) "(%&%&Hsim)".
  iMod (sim_expr_s_update with "[$] [$]") as "[? ?]". iModIntro.
  iExists _. iSplit; [done|]. iFrame.
  iMod "Hsim" as "[$ Hsim]". iModIntro. by iApply "Hsim".
Qed.

Lemma sim_src_bind E e_s Φ κ:
  SRC e_s @ E {{ λ e_s', SRC e_s' @ κ; E {{ Φ }} }} -∗
  SRC e_s @ κ; E {{ Φ }}.
Proof.
  iIntros "Hsim" (σ_s ?) "#??".
  iMod ("Hsim" with "[//] [$] [$]"). iModIntro.
  iApply sim_steps_bind. iApply (sim_steps_wand_strong with "[$]").
  iIntros (?) "[% [% >[? Hsim]]]". by iApply ("Hsim" with "[//] [$] [$]").
Qed.

Lemma sim_src_stop E e_s Φ:
  Φ e_s -∗ SRC e_s @ E {{ Φ }}.
Proof.
  iIntros "HΦ" (σ_s ?) "??".
  iApply fupd_mask_intro; [set_solver|]. iIntros "He".
  iApply sim_steps_stop. iExists _. iSplit; [done|].
  iMod "He". by iFrame.
Qed.

Lemma sim_src_step E e_s Φ κ:
  (∀ σ_s, ⌜mexpr_rel Λ_s σ_s e_s⌝ -∗ mstate_interp Λ_s σ_s ==∗
    ∃ κ' Pσ_s, ⌜σ_s ~{mtrans Λ_s, option_trace κ'}~>ₜ Pσ_s⌝ ∗ ⌜option_prefix κ' κ⌝ ∗
     ∀ σ_s', ⌜Pσ_s σ_s'⌝ ={E}=∗ ∃ e_s', ⌜mexpr_rel Λ_s σ_s' e_s'⌝ ∗
       mstate_interp Λ_s σ_s' ∗ SRC e_s' @ option_drop κ' κ; E {{ Φ }}) -∗
  SRC e_s @ κ; E {{ Φ }}.
Proof.
  iIntros "HΦ" (σ_s ?) "??".
  iMod ("HΦ" with "[//] [$]") as (????) "HΦ".
  iApply fupd_mask_intro; [set_solver|]. iIntros "He".
  iApply sim_steps_step; [done..|]. iIntros (??).
  iMod "He" as "_". iMod ("HΦ" with "[//]") as (??) "[? HΦ]".
  iMod ("HΦ" with "[//] [$] [$]") as "HΦ". by iModIntro.
Qed.

End sim.

Theorem sim_adequacy Σ EV m_t m_s expr_t expr_s `{!dimsumPreG Σ expr_s} `{!Inhabited (expr_s)} :
  (∀ `{Hinv : !invGS_gen HasNoLc Σ} `{Hord : !ord_laterGS Σ} γ_s,
    ⊢ |={⊤}=>
     ∃ (expr_rel_t : (m_trans m_t).(m_state) → expr_t → Prop),
     ∃ (expr_rel_s : (m_trans m_s).(m_state) → expr_s → Prop),
     ∃ (stateI_t : (m_trans m_t).(m_state) → iProp Σ),
     ∃ (stateI_s : (m_trans m_s).(m_state) → iProp Σ),
       let Λ_t := ModLang EV Σ expr_t (m_trans m_t) expr_rel_t stateI_t in
       let Λ_s := ModLang EV Σ expr_s (m_trans m_s) expr_rel_s stateI_s in
       let _ : dimsumGS EV Σ Λ_t Λ_s := DimsumGS _ _ _ _ _ _ _ γ_s
       in
       ∃ e_t e_s,
       ⌜mexpr_rel Λ_t m_t.(m_init) e_t⌝ ∗ ⌜mexpr_rel Λ_s m_s.(m_init) e_s⌝ ∗
       stateI_t m_t.(m_init) ∗ stateI_s m_s.(m_init) ∗
       e_t ⪯{⊤} e_s {{ λ _ _, |={⊤, ∅}=> False }}) →
  trefines m_t m_s.
Proof.
  intros Hsim. constructor => κs /thas_trace_n [n Htrace].
  apply (step_fupdN_soundness_no_lc _ 0 0) => ? /=. simpl in *. iIntros "_".
  iMod (ord_later_alloc n) as (?) "Ha". iDestruct (ord_later_ctx_alloc with "Ha") as "#?".
  iMod (ghost_var_alloc inhabitant) as (γ_s) "Hs".
  iMod Hsim as "(% & % & %stateI_t & %stateI_s & % & % & %He_t & %He_s & Hσ_t & Hσ_s & Hsim)".
  clear Hsim.
  set (Λ_t := ModLang EV Σ expr_t (m_trans m_t) expr_rel_t stateI_t).
  set (Λ_s := ModLang EV Σ expr_s (m_trans m_s) expr_rel_s stateI_s).
  set (X := DimsumGS _ _ _ _ _ _ _ γ_s : dimsumGS EV Σ Λ_t Λ_s).
  iAssert (|==> ⤇ (e_s : mexpr Λ_s) ∗ ⤇ (e_s : mexpr Λ_s))%I with "[Hs]" as ">[He1 He2]".
  { by iMod (ghost_var_update e_s with "Hs") as "[$ $]". }
  pose (F := (λ E e_t Ψ,
               ∀ n κs σ_s σ_t e_s,
               ⌜σ_t ~{ m_trans m_t, κs, n }~>ₜ -⌝ -∗
               ⌜expr_rel_t σ_t e_t⌝ -∗
               ⌜expr_rel_s σ_s e_s⌝ -∗
               ⌜E = ⊤⌝ -∗
               ord_later_auth n -∗
               ⤇ (e_s : mexpr Λ_s) -∗
               stateI_t σ_t -∗
               stateI_s σ_s -∗
               (∀ e_t' : mexpr Λ_t, Ψ e_t' ={⊤,∅}=∗ False) -∗
               |={⊤,∅}=> ⌜σ_s ~{ m_trans m_s, κs }~>ₜ -⌝)%I
          : coPset → mexpr Λ_t → _ → iProp Σ ).
  iAssert (∀ Φ, TGT (e_t : mexpr Λ_t) @ ⊤ {{ Φ }} -∗ F ⊤ e_t Φ)%I as "Hgen"; last first. {
    iApply ("Hgen" with "[He1 Hsim] [//] [//] [//] [//] [$] [$] [$] [$]").
    - by iApply "Hsim".
    - iIntros (?) "[% [?$]]".
  }
  clear n κs Htrace e_s He_s He_t. iIntros (?) "Hsim".
  iApply (sim_ind with "[] Hsim"). { solve_proper. }
  iIntros "!>" (?? ?) "Hsim". iIntros (n κs σ_s σ_t e_s Htrace He_t He_s ->) "Ha He Hσ_t Hσ_s Hc".
  iMod ("Hsim" with "[//] [//] [$] [$] Hσ_t Hσ_s") as "[[?[?[??]]]|[Hsim|Hsim]]".
  - by iMod ("Hc" with "[$]").
  - move: Htrace => /tnhas_trace_inv Htrace.
    iApply (fupd_mono _ _ ⌜_⌝). { iPureIntro. by apply: thas_trace_under_tall. }
    iIntros (?[[??]|[?[?[?[?[?[?[<- ?]]]]]]]]).
    { iApply fupd_mask_intro; [done|]. iIntros "_". iPureIntro. tend. }
    iMod ("Hsim" with "[//]") as "Hsim" => /=.
    iMod (ord_later_elim with "Hsim Ha [-]"); [|done]. iIntros "Ha".
    iMod (ord_later_update with "Ha"); [shelve|].
    iModIntro. iExists _. iFrame. iSplit; [done|]. iIntros "Ha Hsteps". iModIntro.
    iApply (sim_steps_elim with "Hsteps"). iIntros (?) "(%&%&%&%&%&%&?&>[? [? Hsim]])".
    iMod (ord_later_update with "Ha") as "Ha"; [by apply: o_le_choice_r|].
    iApply ("Hsim" with "[//] [//] [//] [//] Ha [$] [$] [$] [$]").
  - iMod "Hsim" as "Hsteps".
    iApply (sim_steps_elim with "Hsteps"). iIntros (?) "(%&%&?&>[? [? Hsim]])".
    iApply ("Hsim" with "[//] [//] [//] [//] [$] [$] [$] [$] [$]").
  Unshelve.
  + apply _.
  + etrans; [|done]. apply o_le_S.
  + done.
Qed.
