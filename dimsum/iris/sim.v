From iris.bi Require Import bi fixpoint.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From dimsum.core Require Export module.
From dimsum.core Require Import trefines.
From dimsum.core.iris Require Export ord_later.
Set Default Proof Using "Type".

Class Sim (PROP : bi) (E1 E2 : Type) :=
  sim : coPset → E1 → E2 → (E1 → E2 → PROP) → PROP.
(* We assume only one instance is ever in scope, hence no mode *)

(* FIXME what are good levels for et, es? *)
Notation "et '⪯{' E '}' es {{ Φ } }" := (sim E et es Φ) (at level 70, Φ at level 200,
  format "'[hv' et  '/' '⪯{' E '}'  '/' es  '/' {{  '[ ' Φ  ']' } } ']'") : bi_scope.

Structure mod_lang EV := ModLang {
  mexpr : Type;
  mtrans : mod_trans EV;
  mexpr_rel : mtrans.(m_state) → mexpr → Prop;
}.
Global Arguments mexpr {_} _.
Global Arguments mtrans {_} _.
Global Arguments mexpr_rel {_} _ _ _.

Definition mexprO {EV} {Λ : mod_lang EV} := leibnizO (mexpr Λ).

Class dimsumPreG (Σ : gFunctors) := RefirisPreG {
  dimsum_pre_invG :> invGpreS Σ;
  dimsum_pre_ord_laterG :> ord_laterPreG Σ;
}.

Class dimsumGS (EV : Type) (Λ_t Λ_s : mod_lang EV) (Σ : gFunctors) := DimsumGS {
  dimsum_invGS :> invGS_gen HasNoLc Σ;
  dimsum_ord_laterGS :> ord_laterGS Σ;
  state_interp : (mtrans Λ_t).(m_state) → (mtrans Λ_s).(m_state) → iProp Σ;
}.
Global Opaque dimsum_invGS.

Definition sim_pre `{!dimsumGS EV Λ_t Λ_s Σ}
    (sim : leibnizO coPset -d> mexprO -d> mexprO -d> (mexprO -d> mexprO -d> iPropO Σ) -d> iPropO Σ) :
    leibnizO coPset -d> mexprO -d> mexprO -d> (mexprO -d> mexprO -d> iPropO Σ) -d> iPropO Σ := λ E e_t e_s Φ,
  (∀ σ_t σ_s, ⌜mexpr_rel Λ_t σ_t e_t⌝ -∗ ⌜mexpr_rel Λ_s σ_s e_s⌝ -∗
    ord_later_ctx -∗ state_interp σ_t σ_s ={E}=∗
      (state_interp σ_t σ_s ∗ Φ e_t e_s) ∨
      ∀ κ Pσ_t, ⌜(mtrans Λ_t).(m_step) σ_t κ Pσ_t⌝ ={E,∅}=∗ ▷ₒ
        ∃ Pσ_s, ⌜σ_s ~{mtrans Λ_s, option_trace κ}~>ₜ Pσ_s⌝ ∗
          ∀ σ_s', ⌜Pσ_s σ_s'⌝ ={∅, E}=∗
            ∃ σ_t' e_t' e_s', ⌜Pσ_t σ_t'⌝ ∗ ⌜mexpr_rel Λ_t σ_t' e_t'⌝ ∗ ⌜mexpr_rel Λ_s σ_s' e_s'⌝ ∗
              (state_interp σ_t' σ_s' ∗ sim E e_t' e_s' Φ))%I.

Global Instance sim_pre_ne `{!dimsumGS EV Λ_t Λ_s Σ} n:
  Proper ((dist n ==> dist n ==> dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n ==> dist n ==> dist n) sim_pre.
Proof.
  move => ?? Hsim ?? -> ?? -> ?? -> ?? HΦ. rewrite /sim_pre.
  repeat (f_equiv || eapply Hsim || eapply HΦ || reflexivity).
Qed.

Lemma sim_pre_mono `{!dimsumGS EV Λ_t Λ_s Σ} sim1 sim2:
  ⊢ □ (∀ E e_t e_s Φ, sim1 E e_t e_s Φ -∗ sim2 E e_t e_s Φ )
  → ∀ E e_t e_s Φ , sim_pre sim1 E e_t e_s Φ -∗ sim_pre sim2 E e_t e_s Φ.
Proof.
  iIntros "#Hinner" (E e_t e_s Φ) "Hsim".
  iIntros (σ_t σ_s ??) "#? Hσ".
  iMod ("Hsim" with "[//] [//] [//] Hσ") as "[Hsim|Hsim]"; [by iLeft|iRight]. iModIntro.
  iIntros (κ P_tσ ?). iMod ("Hsim" with "[//]") as "Hsim". iModIntro. iMod "Hsim" as (??) "Hsim".
  iExists _. iSplit; [done|].
  iIntros (??). iMod ("Hsim" with "[//]") as (??????) "[? ?]". iModIntro.
  iSplit!; [done..|]. iFrame. by iApply "Hinner".
Qed.

Local Instance sim_pre_monotone `{!dimsumGS EV Λ_t Λ_s Σ} :
  BiMonoPred (λ sim : prodO (prodO (prodO (leibnizO coPset) mexprO) mexprO) (mexprO -d> mexprO -d> iPropO Σ) -d> iPropO Σ, uncurry4 (sim_pre (curry4 sim))).
Proof.
  constructor.
  - iIntros (Φ Ψ ??) "#Hinner". iIntros ([[[??]?]?]) "Hsim" => /=. iApply sim_pre_mono; [|done].
    iIntros "!>" (????) "HΦ". by iApply ("Hinner" $! (_, _, _, _)).
  - move => sim Hsim n [[[E1 e_t1] e_s1] Φ1] [[[E2 e_t2] e_s2] Φ2] /= [[/=[/=??]?]?].
    apply sim_pre_ne; eauto. move => ???????????? /=. by apply: Hsim.
Qed.

Definition sim_def `{!dimsumGS EV Λ_t Λ_s Σ} : Sim (iPropI Σ) (mexpr Λ_t) (mexpr Λ_s) :=
  curry4 (bi_least_fixpoint (λ sim : prodO (prodO (prodO (leibnizO coPset) mexprO) mexprO) (mexprO -d> mexprO -d> iPropO Σ) -d> iPropO Σ, uncurry4 (sim_pre (curry4 sim)))).
Definition sim_aux : seal (@sim_def). Proof. by eexists. Qed.
Definition sim' := sim_aux.(unseal).
Global Arguments sim' {EV Λ_t Λ_s Σ _}.
Global Existing Instance sim'.
Lemma sim_eq `{!dimsumGS EV Λ_t Λ_s Σ} : sim = @sim_def EV Λ_t Λ_s Σ _.
Proof. rewrite -sim_aux.(seal_eq) //. Qed.

Section sim.
Context `{!dimsumGS EV Λ_t Λ_s Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : mexpr Λ_t → mexpr Λ_s → iProp Σ.

(* Weakest pre *)
Lemma sim_unfold E e_t e_s Φ:
  e_t ⪯{E} e_s {{ Φ }} ⊣⊢ sim_pre (sim (PROP:=iPropI Σ)) E e_t e_s Φ.
Proof. rewrite sim_eq /sim_def /curry3. apply: least_fixpoint_unfold. Qed.

Lemma sim_strong_ind (R: leibnizO coPset -d> mexprO -d> mexprO -d> (mexprO -d> mexprO -d> iPropO Σ) -d> iPropO Σ):
  NonExpansive4 R →
  ⊢ (□ ∀ E e_t e_s Φ, sim_pre (λ E e_t e_s Ψ, R E e_t e_s Ψ ∧ e_t ⪯{E} e_s {{ Ψ }}) E e_t e_s Φ -∗ R E e_t e_s Φ)
    -∗ ∀ E e_t e_s Φ, e_t ⪯{E} e_s {{ Φ }} -∗ R E e_t e_s Φ.
Proof.
  iIntros (Hne) "#HPre". iIntros (E e_t e_s Φ) "Hsim".
  rewrite sim_eq {2}/sim_def {1}/curry4.
  iApply (least_fixpoint_ind _ (uncurry4 R) with "[] Hsim").
  iIntros "!>" ([[[??]?]?]) "Hsim" => /=. by iApply "HPre".
Qed.

Lemma sim_ind (R: leibnizO coPset -d> mexprO -d> mexprO -d> (mexprO -d> mexprO -d> iPropO Σ) -d> iPropO Σ):
  NonExpansive4 R →
  ⊢ (□ ∀ E e_t e_s Φ, sim_pre R E e_t e_s Φ -∗ R E e_t e_s Φ)
    -∗ ∀ E e_t e_s Φ, e_t ⪯{E} e_s {{ Φ }} -∗ R E e_t e_s Φ .
Proof.
  iIntros (Hne) "#HPre". iApply sim_strong_ind. iIntros "!>" (E e_t e_s Φ) "Hsim".
  iApply "HPre". iApply (sim_pre_mono with "[] Hsim").
  iIntros "!>" (????) "[? _]". by iFrame.
Qed.

Lemma sim_stop' E e_t e_s Φ:
  (|={E}=> Φ e_t e_s) -∗ e_t ⪯{E} e_s {{ Φ }}.
Proof. rewrite sim_unfold. iIntros "HΦ" (σ_t σ_s ??) "? Hσ". iLeft. iFrame. Qed.
Lemma sim_stop E e_t e_s Φ:
  Φ e_t e_s -∗ e_t ⪯{E} e_s {{ Φ }}.
Proof. iIntros "HΦ". iApply sim_stop'. by iFrame. Qed.


Lemma sim_step E e_t e_s Φ:
  (∀ σ_t σ_s κ Pσ_t, ⌜mexpr_rel Λ_t σ_t e_t⌝ -∗ ⌜mexpr_rel Λ_s σ_s e_s⌝ -∗
    ⌜(mtrans Λ_t).(m_step) σ_t κ Pσ_t⌝ -∗ state_interp σ_t σ_s ={E,∅}=∗ ▷ₒ
      ∃ Pσ_s, ⌜σ_s ~{mtrans Λ_s, option_trace κ}~>ₜ Pσ_s⌝ ∗
         ∀ σ_s', ⌜Pσ_s σ_s'⌝ ={∅, E}=∗
           ∃ σ_t' e_t' e_s', ⌜Pσ_t σ_t'⌝ ∗ ⌜mexpr_rel Λ_t σ_t' e_t'⌝ ∗ ⌜mexpr_rel Λ_s σ_s' e_s'⌝ ∗
              (state_interp σ_t' σ_s' ∗ e_t' ⪯{E} e_s' {{ Φ }})) -∗
  e_t ⪯{E} e_s {{ Φ }}.
Proof.
  iIntros "Hsim".
  rewrite sim_unfold. iIntros (????) "#? Hσ !>". iRight. iIntros (???).
  iMod ("Hsim" with "[//] [//] [//] [$]") as "Hsim". do 2 iModIntro.
  iDestruct "Hsim" as (??) "Hsim". iExists _. iSplit; [done|].
  iIntros (??). iMod ("Hsim" with "[//]") as (??????) "[? Hsim]".
  iModIntro. iSplit!; [done..|]. iFrame.
Qed.

Lemma sim_bind E e_t e_s Φ:
  e_t ⪯{E} e_s {{ λ e_t' e_s', e_t' ⪯{E} e_s' {{ Φ }} }} -∗ e_t ⪯{E} e_s {{ Φ }}.
Proof.
  iIntros "HΦ".
  pose (F := (λ E e_t e_s Ψ, ∀ Φ, (∀ e_t e_s, Ψ e_t e_s -∗ e_t ⪯{E} e_s {{ Φ }}) -∗ e_t ⪯{E} e_s {{ Φ }})%I).
  iAssert (∀ Φ, e_t ⪯{E} e_s {{ Φ }} -∗ F E e_t e_s Φ)%I as "Hgen"; last first.
  { iApply ("Hgen" with "HΦ"). iIntros (??) "$". }
  iIntros (?) "Hsim".
  iApply (sim_ind with "[] Hsim"). { solve_proper. }
  iIntros "!>" (????) "Hsim". iIntros (?) "Hc".
  rewrite sim_unfold. iIntros (????) "#? Hσ".
  iMod ("Hsim" with "[//] [//] [//] Hσ") as "[[? ?]|Hsim]".
  - iDestruct ("Hc" with "[$]") as "Hc". rewrite sim_unfold. by iApply "Hc".
  - iModIntro. iRight. iIntros (???). iMod ("Hsim" with "[//]") as "Hsim". do 2 iModIntro.
    iDestruct "Hsim" as (??) "Hsim".
    iExists _. iSplit; [done|]. iIntros (??). iMod ("Hsim" with "[//]") as (??????) "[? HF]". iModIntro.
    iSplit!; [done..|]. iFrame. by iApply "HF".
Qed.

(* TODO *)
Definition sim_src (E : coPset) (κ : option EV) (e_s : mexpr Λ_s) (Φ : mexpr Λ_s → iProp Σ) :=
  ∀ σ_t σ_s, ⌜mexpr_rel Λ_s σ_s e_s⌝ -∗ state_interp σ_t σ_s ={E,∅}=∗
    ∃ Pσ_s, ⌜σ_s ~{mtrans Λ_s, option_trace κ}~>ₜ Pσ_s⌝ ∗
       ∀ σ_s', ⌜Pσ_s σ_s'⌝ ={∅, E}=∗
            ∃ e_s', ⌜mexpr_rel Λ_s σ_s' e_s'⌝ ∗
              (state_interp σ_t σ_s' ∗ Φ e_s').

End sim.

Theorem sim_adequacy Σ EV Λ_t Λ_s `{!dimsumPreG Σ} σ_t σ_s :
  (∀ `{Hinv : !invGS_gen HasNoLc Σ} `{Hord : !ord_laterGS Σ},
    ⊢ |={⊤}=> ∃ (stateI : (mtrans Λ_t).(m_state) → (mtrans Λ_s).(m_state) → iProp Σ),
       let _ : dimsumGS EV Λ_t Λ_s Σ := DimsumGS _ _ _ _ _ _ stateI
       in
       ∃ e_t e_s,
       ⌜mexpr_rel Λ_t σ_t e_t⌝ ∗ ⌜mexpr_rel Λ_s σ_s e_s⌝ ∗
       stateI σ_t σ_s ∗
       e_t ⪯{⊤} e_s {{ λ _ _, |={⊤, ∅}=> False }}) →
  trefines (Mod (mtrans Λ_t) σ_t) (Mod (mtrans Λ_s) σ_s).
Proof.
  intros Hsim. constructor => κs /thas_trace_n [n Htrace].
  apply (step_fupdN_soundness_no_lc _ 0 0) => ? /=. simpl in *. iIntros "_".
  iMod (ord_later_alloc n) as (?) "Ha". iDestruct (ord_later_ctx_alloc with "Ha") as "#?".
  iMod Hsim as (stateI ?? Het Hes) "(Hσ & Hsim)". clear Hsim.
  iInduction Htrace as [????? Hκs|???????? Hstep ?? Hlt Hκs|????????? Hκs Hle] "IH" forall (σ_s e_t e_s Het Hes).
  - rewrite -Hκs. iApply fupd_mask_intro; [done|]. iIntros "HE". iPureIntro. by econstructor.
  - rewrite -Hκs. setoid_rewrite sim_unfold at 2.
    iMod ("Hsim" with "[//] [//] [//] Hσ") as "[[? Hsim]|Hsim]". { by iMod "Hsim". }
    iMod ("Hsim" with "[//]") as "Hsim".
    iMod (ord_later_elim with "Hsim Ha [-]"); [|done]. iIntros "Ha".
    iMod (ord_later_update with "Ha"); [shelve|].
    iModIntro. iExists _. iFrame. iSplit; [done|]. iIntros "Ha".
    iDestruct 1 as (? Ht) "Hsim".
    iApply (fupd_mono _ _ ⌜_⌝). { iPureIntro. by apply thas_trace_trans. }
    iModIntro. iIntros (??).
    iMod ("Hsim" with "[//]") as (σ_t' ???? ?) "[Hstate Hsim]".
    iMod (ord_later_update with "Ha") as "Ha"; [by apply: o_le_choice_r|].
    iApply ("IH" with "[//] [//] Ha Hstate Hsim").
    Unshelve. { by apply o_lt_impl_le. } { done. }
  - rewrite -Hκs. iApply (fupd_mono _ _ ⌜_⌝). { iPureIntro. apply thas_trace_all. }
    iIntros (?). iMod (ord_later_update with "Ha") as "Ha". { etrans; [|done]. by apply: o_le_choice_r. }
    iApply ("IH" with "[//] [//] Ha Hσ Hsim").
Qed.
