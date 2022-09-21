From iris.bi Require Import fixpoint.
From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From dimsum.core Require Export module trefines.
From dimsum.core.iris Require Export ord_later.
Set Default Proof Using "Type".

(* TODO: rename to limo or lin_mon? for linear monotonicity *)
Definition bi_mono1 {Σ A} (P : (A → iProp Σ) → iProp Σ) : (A → iProp Σ) → iProp Σ :=
  λ Q, (∃ Q', P Q' ∗ (∀ a, Q' a -∗ Q a))%I.

Section bi_mono1.
  Context {Σ : gFunctors} {A : Type}.
  Implicit Types (P : (A → iProp Σ) → iProp Σ).

  Lemma bi_mono1_intro0 P Q :
    P Q -∗
    bi_mono1 P Q.
  Proof. iIntros "?". iExists _. iFrame. iIntros (?) "$". Qed.

  Lemma bi_mono1_mono P Q1 Q2 :
    bi_mono1 P Q1 -∗
    (∀ x, Q1 x -∗ Q2 x) -∗
    bi_mono1 P Q2.
  Proof.
    iIntros "[% [HP HQ1]] HQ". iExists _. iFrame "HP". iIntros (?) "?".
    iApply "HQ". by iApply "HQ1".
  Qed.

  Lemma bi_mono1_mono_l P1 P2 Q :
    bi_mono1 P1 Q -∗
    (∀ Q, P1 Q -∗ P2 Q) -∗
    bi_mono1 P2 Q.
  Proof.
    iIntros "[% [HP HQ1]] HQ". iExists _. iFrame "HQ1". by iApply "HQ".
  Qed.

  Lemma bi_mono1_elim P Q :
    bi_mono1 P Q -∗
    (∀ Q', (∀ x, Q' x -∗ Q x) -∗ P Q' -∗ P Q) -∗
    P Q.
  Proof. iIntros "[% [??]] HP". iApply ("HP" with "[$] [$]"). Qed.

  (** Derived laws *)
  Lemma bi_mono1_dup P Q :
    bi_mono1 (bi_mono1 P) Q -∗
    bi_mono1 P Q.
  Proof.
    iIntros "?".
    iApply (bi_mono1_elim with "[$] []").
    iIntros (?) "??". by iApply (bi_mono1_mono with "[$]").
  Qed.

  Lemma bi_mono1_intro P Q Q' :
    P Q' -∗
    (∀ x, Q' x -∗ Q x) -∗
    bi_mono1 P Q.
  Proof.
    iIntros "HP HQ".
    iApply (bi_mono1_mono with "[HP] HQ").
    by iApply bi_mono1_intro0.
  Qed.

End bi_mono1.

(* TODO: enable this and prevent clients from unfolding bi_mono1 *)
(* Global Typeclasses Opaque bi_mono1. *)

(** * dimsumGS *)
Class dimsumPreG (Σ : gFunctors) := DimsumPreG {
  dimsum_pre_invG :> invGpreS Σ;
  dimsum_pre_ord_laterG :> ord_laterPreG Σ;
}.

Class dimsumGS (Σ : gFunctors) := DimsumGS {
  dimsum_invGS :> invGS_gen HasNoLc Σ;
  dimsum_ord_laterGS :> ord_laterGS Σ;
}.
Global Opaque dimsum_invGS.

Definition dimsumΣ : gFunctors :=
  #[ ord_laterΣ; invΣ ].

Global Instance subG_dimsumΣ Σ :
  subG (dimsumΣ) Σ → dimsumPreG Σ.
Proof. solve_inG. Qed.

(** * [sim_tgt] *)
Section sim_tgt.
  Context {Σ : gFunctors} {EV : Type} `{!dimsumGS Σ}.
  Context (m : mod_trans EV).

  Definition sim_tgt_pre
    (sim_tgt : leibnizO (m.(m_state)) -d>
                   (leibnizO (option EV) -d> ((leibnizO (m.(m_state)) -d> iPropO Σ) -d> iPropO Σ) -d> iPropO Σ) -d> iPropO Σ) :
    leibnizO (m.(m_state)) -d>
      (leibnizO (option EV) -d> ((leibnizO (m.(m_state)) -d> iPropO Σ) -d> iPropO Σ) -d> iPropO Σ) -d> iPropO Σ := λ σ Π,
  (ord_later_ctx -∗ |={∅}=> (bi_mono1 (Π None) (λ P', P' σ)) ∨
        ∀ κ Pσ, ⌜m.(m_step) σ κ Pσ⌝ ={∅}=∗ ▷ₒ
           ((bi_mono1 (Π κ) (λ P', ∃ σ', ⌜Pσ σ'⌝ ∗ P' σ')) ∨ ∃ σ', ⌜κ = None⌝ ∗ ⌜Pσ σ'⌝ ∗ sim_tgt σ' Π))%I.

  Global Instance sim_tgt_pre_ne n:
    Proper ((dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n) sim_tgt_pre.
  Proof.
    move => ?? Hsim ?? -> ?? HΠ. rewrite /sim_tgt_pre/bi_mono1.
    repeat (f_equiv || eapply Hsim || eapply HΠ || reflexivity).
  Qed.

  Lemma sim_tgt_pre_mono sim1 sim2:
    ⊢ □ (∀ σ Π, sim1 σ Π -∗ sim2 σ Π)
    → ∀ σ Π , sim_tgt_pre sim1 σ Π -∗ sim_tgt_pre sim2 σ Π.
  Proof.
    iIntros "#Hinner" (σ Π) "Hsim ?".
    iMod ("Hsim" with "[$]") as "[?|Hsim]"; [by iLeft; iFrame| iRight].
    iIntros "!>" (???). iMod ("Hsim" with "[//]") as "Hsim". do 2 iModIntro.
    iDestruct "Hsim" as "[?|[% [% [% ?]]]]"; [by iLeft| iRight].
    iExists _. iSplit; [done|]. iSplit; [done|]. by iApply "Hinner".
  Qed.

  Local Instance sim_tgt_pre_monotone :
    BiMonoPred (λ sim_tgt : prodO (leibnizO (m.(m_state))) ((leibnizO (option EV)) -d> ((leibnizO (m.(m_state)) -d> iPropO Σ) -d> iPropO Σ) -d> iPropO Σ) -d> iPropO Σ, uncurry (sim_tgt_pre (curry sim_tgt))).
  Proof.
    constructor.
    - iIntros (Π Ψ ??) "#Hinner". iIntros ([??]) "Hsim" => /=. iApply sim_tgt_pre_mono; [|done].
      iIntros "!>" (??) "HΠ". by iApply ("Hinner" $! (_, _)).
    - move => sim_tgt Hsim n [σ1 Π1] [σ2 Π2] /= [/=??].
      apply sim_tgt_pre_ne; eauto. move => ?????? /=. by apply: Hsim.
  Qed.

  Definition sim_tgt : m.(m_state) → (option EV → ((m.(m_state) → iProp Σ) → iProp Σ) → iProp Σ) → iProp Σ :=
    curry (bi_least_fixpoint (λ sim_tgt : prodO (leibnizO (m.(m_state))) ((leibnizO (option EV)) -d> ((leibnizO (m.(m_state)) -d> iPropO Σ) -d> iPropO Σ) -d> iPropO Σ) -d> iPropO Σ, uncurry (sim_tgt_pre (curry sim_tgt)))).

  Global Instance sim_tgt_ne n:
    Proper ((=) ==> ((=) ==> (=) ==> dist n) ==> dist n) sim_tgt.
  Proof. move => ?? -> ?? HΠ. unfold sim_tgt. f_equiv. intros ??. by apply HΠ. Qed.
End sim_tgt.

Notation " σ '≈{' m '}≈>ₜ' P " := (sim_tgt m σ P)
  (at level 70, format "σ  '≈{'  m  '}≈>ₜ'  P") : bi_scope.

Definition sim_tgt_mapsto `{!dimsumGS Σ} {EV} (m : mod_trans EV) (σ : m_state m)
  (H_s : (option EV → ((m_state m → iProp Σ) → iProp Σ) → iProp Σ) → iProp Σ) : iProp Σ :=
  ∀ Π, H_s Π -∗ σ ≈{m}≈>ₜ Π.

Notation "σ '⤇ₜ{' m } P " := (sim_tgt_mapsto m σ P)
  (at level 20, only parsing) : bi_scope.
Notation "σ '⤇ₜ' P " := (sim_tgt_mapsto _ σ P)
  (at level 20, format "σ  '⤇ₜ'  P") : bi_scope.

Section sim_tgt.
  Context {Σ : gFunctors} {EV : Type} `{!dimsumGS Σ}.
  Context (m : mod_trans EV).
  Implicit Types Π : option EV → ((m.(m_state) → iProp Σ) → iProp Σ) → iProp Σ.

  Local Existing Instance sim_tgt_pre_monotone.
  Lemma sim_tgt_unfold σ Π:
    σ ≈{ m }≈>ₜ Π ⊣⊢ sim_tgt_pre m (sim_tgt m) σ Π.
  Proof. rewrite /sim_tgt /curry. apply: least_fixpoint_unfold. Qed.

  Lemma sim_tgt_strong_ind (R: leibnizO (m.(m_state)) -d> (leibnizO (option EV) -d> ((leibnizO (m.(m_state)) -d> iPropO Σ) -d> iPropO Σ) -d> iPropO Σ) -d> iPropO Σ):
    NonExpansive2 R →
    ⊢ (□ ∀ σ Π, sim_tgt_pre m (λ σ Ψ, R σ Ψ ∧ σ ≈{ m }≈>ₜ Ψ) σ Π -∗ R σ Π)
      -∗ ∀ σ Π, σ ≈{ m }≈>ₜ Π -∗ R σ Π.
  Proof.
    iIntros (Hne) "#HPre". iIntros (σ Π) "Hsim".
    rewrite {2}/sim_tgt {1}/curry.
    iApply (least_fixpoint_ind _ (uncurry R) with "[] Hsim").
    iIntros "!>" ([??]) "Hsim" => /=. by iApply "HPre".
  Qed.

  Lemma sim_tgt_ind (R: leibnizO (m.(m_state)) -d> (leibnizO (option EV) -d> ((leibnizO (m.(m_state)) -d> iPropO Σ) -d> iPropO Σ) -d> iPropO Σ) -d> iPropO Σ) :
    NonExpansive2 R →
    ⊢ (□ ∀ σ Π, sim_tgt_pre m R σ Π -∗ R σ Π)
      -∗ ∀ σ Π, σ ≈{ m }≈>ₜ Π -∗ R σ Π.
  Proof.
    iIntros (Hne) "#HPre". iApply sim_tgt_strong_ind. iIntros "!>" (σ Π) "Hsim".
    iApply "HPre". iApply (sim_tgt_pre_mono with "[] Hsim").
    iIntros "!>" (??) "[? _]". by iFrame.
  Qed.

  Lemma sim_tgt_wand_strong σ Π Ψ:
    σ ≈{ m }≈>ₜ Π -∗
    (∀ κ Pσ, Π κ Pσ -∗ bi_mono1 (Ψ κ) (λ P, bi_mono1 Pσ P)) -∗
    σ ≈{ m }≈>ₜ Ψ.
  Proof.
    iIntros "Hsim Hwand".
    pose (F := (λ σ Ψ, ∀ Π, (∀ κ Pσ, Ψ κ Pσ -∗ bi_mono1 (Π κ) (λ P, bi_mono1 Pσ P)) -∗ σ ≈{ m }≈>ₜ Π)%I).
    iAssert (∀ Π, σ ≈{ m }≈>ₜ Π -∗ F σ Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"). done. }
    iIntros (?) "Hsim".
    iApply (sim_tgt_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros (?) "Hc".
    rewrite sim_tgt_unfold. iIntros "#?".
    iMod ("Hsim" with "[$]") as "[HΠ|Hsim]"; [iLeft| iRight].
    - iModIntro.
      iDestruct (bi_mono1_mono_l with "[$] Hc") as "?".
      iDestruct (bi_mono1_elim with "[$] []") as "?".
      { iIntros (?) "Hsub ?". iApply (bi_mono1_mono with "[$]"). iIntros (?) "?".
        by iDestruct (bi_mono1_mono_l with "[$] Hsub") as "?". }
      iApply (bi_mono1_mono with "[$]").
      iIntros (?) "?".
      iDestruct (bi_mono1_elim with "[$] []") as "$".
      by iIntros (?) "?".
    - iIntros "!>" (???). iMod ("Hsim" with "[//]") as "Hsim". do 2 iModIntro.
      iDestruct "Hsim" as "[HΠ|[% [% [% Hsim]]]]"; [iLeft|iRight].
      + iDestruct "HΠ" as (?) "[? HP1]".
        iDestruct ("Hc" with "[$]") as (?) "[? HP2]".
        iExists _. iFrame. iIntros (?) "?".
        iDestruct ("HP2" with "[$]") as (?) "[? HP3]".
        iDestruct ("HP1" with "[$]") as (??) "?". iExists _. iSplit; [done|].
        by iApply "HP3".
      + iExists _. iSplit; [done|]. iSplit; [done|]. by iApply "Hsim".
  Qed.

  Lemma sim_tgt_wand σ Π Ψ:
    σ ≈{ m }≈>ₜ Π -∗
    (∀ κ Pσ, Π κ Pσ -∗ Ψ κ Pσ) -∗
    σ ≈{ m }≈>ₜ Ψ.
  Proof.
    iIntros "Hsim Hwand".
    iApply (sim_tgt_wand_strong with "Hsim"). iIntros (??) "?".
    iApply (bi_mono1_intro with "[-]"); [by iApply "Hwand"|].
    iIntros (?) "?". by iApply bi_mono1_intro0.
  Qed.

  Lemma sim_tgt_bind σ Π :
    σ ≈{ m }≈>ₜ (λ κ Pσ', Π κ Pσ' ∨ ⌜κ = None⌝ ∗ Pσ' (λ σ', σ' ≈{ m }≈>ₜ Π)) -∗
    σ ≈{ m }≈>ₜ Π.
  Proof.
    iIntros "HΠ".
    pose (F := (λ σ Ψ, ∀ Π, (∀ κ Pσ, Ψ κ Pσ -∗ Π κ Pσ ∨ ⌜κ = @None EV⌝ ∗ Pσ (λ σ', σ' ≈{ m }≈>ₜ Π)) -∗ σ ≈{ m }≈>ₜ Π)%I).
    iAssert (∀ Π, σ ≈{ m }≈>ₜ Π -∗ F σ Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "HΠ"). iIntros (??) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_tgt_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros (?) "Hc".
    rewrite sim_tgt_unfold. iIntros "#?".
    iMod ("Hsim" with "[$]") as "[HΠ|Hsim]".
    - iDestruct "HΠ" as (?) "[? HP1]".
      iDestruct ("Hc" with "[$]") as "[HΠ | [% HP2]]".
      { iModIntro. iLeft. by iApply (bi_mono1_intro with "HΠ"). }
      iDestruct ("HP1" with "[$]") as "Hsim".
      rewrite sim_tgt_unfold. by iApply "Hsim".
    - iRight. iIntros "!>" (???). iMod ("Hsim" with "[//]") as "Hsim". do 2 iModIntro.
      iDestruct "Hsim" as "[[% [? HP1]]|[% [% [% Hsim]]]]".
      + iDestruct ("Hc" with "[$]") as "[HΠ | [% HP2]]".
        { iLeft. by iApply (bi_mono1_intro with "HΠ"). }
        iDestruct ("HP1" with "[$]") as (??) "?". iRight. by iSplit!.
      + iRight. iSplit!; [done|]. by iApply "Hsim".
  Qed.

  Lemma sim_tgt_bi_mono σ Π:
    σ ≈{ m }≈>ₜ (λ κ Pσ, bi_mono1 (Π κ) (λ P, bi_mono1 Pσ P)) -∗
    σ ≈{ m }≈>ₜ Π.
  Proof. iIntros "Hsim". iApply (sim_tgt_wand_strong with "Hsim"). by iIntros (??) "?". Qed.

  Lemma sim_tgt_bi_mono1 σ Π:
    σ ≈{ m }≈>ₜ (λ κ, bi_mono1 (Π κ)) -∗
    σ ≈{ m }≈>ₜ Π.
  Proof.
    iIntros "Hsim". iApply (sim_tgt_wand_strong with "Hsim").
    iIntros (??) "?". iApply (bi_mono1_mono with "[$]").
    iIntros (?) "?". by iApply bi_mono1_intro0.
  Qed.

  Lemma sim_tgt_bi_mono2 σ Π:
    σ ≈{ m }≈>ₜ (λ κ Pσ, Π κ (λ P, bi_mono1 Pσ P)) -∗
    σ ≈{ m }≈>ₜ Π.
  Proof.
    iIntros "Hsim". iApply (sim_tgt_wand_strong with "Hsim").
    iIntros (??) "?". by iApply bi_mono1_intro0.
  Qed.

  Lemma fupd_sim_tgt σ Π :
    (|={∅}=> σ ≈{ m }≈>ₜ Π) -∗
    σ ≈{ m }≈>ₜ Π.
  Proof. iIntros "Hsim". rewrite sim_tgt_unfold. iMod "Hsim". iApply "Hsim". Qed.

  Lemma sim_tgt_ctx σ Π :
    (ord_later_ctx -∗ σ ≈{ m }≈>ₜ Π) -∗
    σ ≈{ m }≈>ₜ Π.
  Proof. iIntros "Hsim". rewrite sim_tgt_unfold. iIntros "#?". by iApply "Hsim". Qed.

  Lemma sim_tgt_stop σ Π :
    Π None (λ P', P' σ) -∗
    σ ≈{ m }≈>ₜ Π.
  Proof.
    iIntros "?". rewrite sim_tgt_unfold. iIntros "?". iModIntro. iLeft. by iApply bi_mono1_intro0.
  Qed.

  Lemma sim_tgt_step σ Π :
    (∀ κ Pσ, ⌜m.(m_step) σ κ Pσ⌝ ={∅}=∗ ▷ₒ
        ((Π κ (λ P', ∃ σ', ⌜Pσ σ'⌝ ∗ P' σ')) ∨ ∃ σ', ⌜κ = None⌝ ∗ ⌜Pσ σ'⌝ ∗ σ' ≈{m}≈>ₜ Π)) -∗
    σ ≈{ m }≈>ₜ Π.
  Proof.
    iIntros "Hsim". rewrite sim_tgt_unfold. iIntros "#?". iModIntro. iRight.
    iIntros (???). iMod ("Hsim" with "[//]") as "Hsim". do 2 iModIntro.
    iDestruct "Hsim" as "[?|?]"; [iLeft|by iRight].
    by iApply bi_mono1_intro0.
  Qed.

  Lemma sim_tgt_step_end σ Π :
    (∀ κ Pσ, ⌜m.(m_step) σ κ Pσ⌝ ={∅}=∗ ▷ₒ Π κ (λ P', ∃ σ', ⌜Pσ σ'⌝ ∗ P' σ')) -∗
    σ ≈{ m }≈>ₜ Π.
  Proof.
    iIntros "Hsim". iApply sim_tgt_step. iIntros (???). iMod ("Hsim" with "[//]") as "Hsim".
    do 2 iModIntro. by iLeft.
  Qed.

  Lemma sim_tgt_elim E σ Π κs n m_s σ_s :
    σ ~{m, κs, n}~>ₜ - →
    σ ≈{ m }≈>ₜ Π -∗
    ord_later_auth n -∗
    (∀ κ n' κs', bi_mono1 (Π κ) (λ P', ∃ σ', P' σ' ∗ ⌜σ' ~{m, κs', n'}~>ₜ -⌝ ∗ ord_later_auth n') -∗
           |={E}=> ⌜σ_s ~{m_s, tapp (option_trace κ) κs'}~>ₜ -⌝) -∗
    |={E}=> ⌜σ_s ~{m_s, κs}~>ₜ -⌝.
  Proof.
    iIntros (?) "Hsim Ha Hc".
    iDestruct (ord_later_ctx_alloc with "[$]") as "#?".
    pose (F := (λ σ Π,
      ∀ n κs,
        ⌜σ ~{m, κs, n}~>ₜ -⌝ -∗
        ord_later_auth n -∗
        (∀ κ n' κs', bi_mono1 (Π κ) (λ P', ∃ σ', P' σ' ∗ ⌜σ' ~{m, κs', n'}~>ₜ -⌝ ∗ ord_later_auth n') -∗
           |={E}=> ⌜σ_s ~{m_s, tapp (option_trace κ) κs'}~>ₜ -⌝) -∗
        |={E}=> ⌜σ_s ~{m_s, κs}~>ₜ -⌝)%I).
    iAssert (∀ Π, σ ≈{ m }≈>ₜ Π -∗ F σ Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim [//] [$] Hc"). }
    iIntros (?) "Hsim".
    iApply (sim_tgt_ind with "[] Hsim"). { unfold F, bi_mono1. solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros (?? Htrace) "Ha Hc".
    iMod (fupd_mask_subseteq ∅) as "He"; [set_solver|].
    iMod ("Hsim" with "[$]") as "[HΠ|Hsim]"; iMod "He" as "_".
    { iApply ("Hc" $! None with "[-]"). iApply (bi_mono1_mono with "[$]"). iIntros (?) "?". iExists _. by iFrame. }
    move: Htrace => /tnhas_trace_inv Htrace.
    iApply (fupd_mono _ _ ⌜_⌝). { iPureIntro. by apply: thas_trace_under_tall. }
    iIntros (κs' [[??]|(?&?&?&?&?&?&?&?)]). { iPureIntro. tend. }
    iMod (fupd_mask_subseteq ∅) as "He"; [set_solver|].
    iMod ("Hsim" with "[//]") as "Hsim". iMod "He" as "_".
    iMod (ord_later_elim with "Hsim Ha [-]"); [|done]. iIntros "Ha".
    iMod (ord_later_update with "Ha"); [shelve|].
    iModIntro. iExists _. iFrame. iSplit; [done|]. iIntros "Ha [HΠ|[% [% [% Hsim]]]]". iModIntro.
    + iMod ("Hc" with "[-]") as %?. 2: { iPureIntro. by apply: thas_trace_mono. }
      iApply (bi_mono1_mono with "[$]"). iIntros (?) "[% [% ?]]".
      iExists _. iFrame. iPureIntro.
      apply: tnhas_trace_mono; [naive_solver|done|by econs|done].
    + iModIntro. iApply ("Hsim" with "[%] [$] [$]"). simplify_eq/=.
      apply: tnhas_trace_mono; [naive_solver|done|by econs|done].
    Unshelve.
    * etrans; [|done]. apply o_le_S.
    * done.
    * done.
  Qed.

End sim_tgt.

(** * [sim_src] *)
Section sim_src.
  Context {Σ : gFunctors} {EV : Type} `{!dimsumGS Σ}.
  Context (m : mod_trans EV).

  Definition sim_src_pre
    (sim_src : leibnizO (m.(m_state)) -d>
                   (leibnizO (option EV) -d> leibnizO (m.(m_state)) -d> iPropO Σ) -d> iPropO Σ) :
    leibnizO (m.(m_state)) -d>
      (leibnizO (option EV) -d> leibnizO (m.(m_state)) -d> iPropO Σ) -d> iPropO Σ := λ σ Π,
  (ord_later_ctx -∗ |={∅}=> (Π None σ) ∨
        ∃ κ Pσ, ⌜m.(m_step) σ κ Pσ⌝ ∗ ∀ σ', ⌜Pσ σ'⌝ ={∅}=∗
          if κ is Some _ then Π κ σ' else sim_src σ' Π)%I.

  Global Instance sim_src_pre_ne n:
    Proper ((dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n) sim_src_pre.
  Proof.
    move => ?? Hsim ?? -> ?? HΠ. rewrite /sim_src_pre.
    repeat (f_equiv || eapply Hsim || eapply HΠ || reflexivity).
  Qed.

  Lemma sim_src_pre_mono sim1 sim2:
    ⊢ □ (∀ σ Π, sim1 σ Π -∗ sim2 σ Π)
    → ∀ σ Π , sim_src_pre sim1 σ Π -∗ sim_src_pre sim2 σ Π.
  Proof.
    iIntros "#Hinner" (σ Π) "Hsim ?".
    iMod ("Hsim" with "[$]") as "[?|[% [% [% Hsim]]]]"; [by iLeft; iFrame| iRight].
    iModIntro. iExists _, _. iSplit; [done|]. iIntros (??).
    iMod ("Hsim" with "[//]"). case_match => //. iModIntro. by iApply "Hinner".
  Qed.

  Local Instance sim_src_pre_monotone :
    BiMonoPred (λ sim_src : prodO (leibnizO (m.(m_state))) ((leibnizO (option EV)) -d> (leibnizO (m.(m_state))) -d> iPropO Σ) -d> iPropO Σ, uncurry (sim_src_pre (curry sim_src))).
  Proof.
    constructor.
    - iIntros (Π Ψ ??) "#Hinner". iIntros ([??]) "Hsim" => /=. iApply sim_src_pre_mono; [|done].
      iIntros "!>" (??) "HΠ". by iApply ("Hinner" $! (_, _)).
    - move => sim_src Hsim n [σ1 Π1] [σ2 Π2] /= [/=??].
      apply sim_src_pre_ne; eauto. move => ?????? /=. by apply: Hsim.
  Qed.

  Definition sim_src : m.(m_state) → (option EV → m.(m_state) → iProp Σ) → iProp Σ :=
    curry (bi_least_fixpoint (λ sim_src : prodO (leibnizO (m.(m_state))) ((leibnizO (option EV)) -d> (leibnizO (m.(m_state))) -d>  iPropO Σ) -d> iPropO Σ, uncurry (sim_src_pre (curry sim_src)))).

  Global Instance sim_src_ne n:
    Proper ((=) ==> ((=) ==> (=) ==> dist n) ==> dist n) sim_src.
  Proof. move => ?? -> ?? HΠ. unfold sim_src. f_equiv. intros ??. by apply HΠ. Qed.
End sim_src.

Notation " σ '≈{' m '}≈>ₛ' P " := (sim_src m σ P)
  (at level 70, format "σ  '≈{'  m  '}≈>ₛ'  P") : bi_scope.

Definition sim_src_mapsto `{!dimsumGS Σ} {EV} (m : mod_trans EV) (σ : m_state m)
  (H_s : (option EV → m_state m → iProp Σ) → iProp Σ) : iProp Σ :=
  ∀ Π, H_s Π -∗ σ ≈{m}≈>ₛ Π.

Notation "σ '⤇ₛ{' m } P " := (sim_src_mapsto m σ P)
  (at level 20, only parsing) : bi_scope.
Notation "σ '⤇ₛ' P " := (sim_src_mapsto _ σ P)
  (at level 20, format "σ  '⤇ₛ'  P") : bi_scope.

Section sim_src.
  Context {Σ : gFunctors} {EV : Type} `{!dimsumGS Σ}.
  Context (m : mod_trans EV).
  Implicit Types Π : option EV → m.(m_state) → iProp Σ.

  Local Existing Instance sim_src_pre_monotone.
  Lemma sim_src_unfold σ Π:
    σ ≈{ m }≈>ₛ Π ⊣⊢ sim_src_pre m (sim_src m) σ Π.
  Proof. rewrite /sim_src /curry. apply: least_fixpoint_unfold. Qed.

  Lemma sim_src_strong_ind (R: leibnizO (m.(m_state)) -d> (leibnizO (option EV) -d> leibnizO (m.(m_state)) -d> iPropO Σ) -d> iPropO Σ):
    NonExpansive2 R →
    ⊢ (□ ∀ σ Π, sim_src_pre m (λ σ Ψ, R σ Ψ ∧ σ ≈{ m }≈>ₛ Ψ) σ Π -∗ R σ Π)
      -∗ ∀ σ Π, σ ≈{ m }≈>ₛ Π -∗ R σ Π.
  Proof.
    iIntros (Hne) "#HPre". iIntros (σ Π) "Hsim".
    rewrite {2}/sim_src {1}/curry.
    iApply (least_fixpoint_ind _ (uncurry R) with "[] Hsim").
    iIntros "!>" ([??]) "Hsim" => /=. by iApply "HPre".
  Qed.

  Lemma sim_src_ind (R: leibnizO (m.(m_state)) -d> (leibnizO (option EV) -d> leibnizO (m.(m_state)) -d> iPropO Σ) -d> iPropO Σ) :
    NonExpansive2 R →
    ⊢ (□ ∀ σ Π, sim_src_pre m R σ Π -∗ R σ Π)
      -∗ ∀ σ Π, σ ≈{ m }≈>ₛ Π -∗ R σ Π.
  Proof.
    iIntros (Hne) "#HPre". iApply sim_src_strong_ind. iIntros "!>" (σ Π) "Hsim".
    iApply "HPre". iApply (sim_src_pre_mono with "[] Hsim").
    iIntros "!>" (??) "[? _]". by iFrame.
  Qed.

  Lemma sim_src_wand_strong σ Π Ψ:
    σ ≈{ m }≈>ₛ Π -∗
    (∀ κ σ, Π κ σ ={∅}=∗ Ψ κ σ) -∗
    σ ≈{ m }≈>ₛ Ψ.
  Proof.
    iIntros "Hsim Hwand".
    pose (F := (λ σ Ψ, ∀ Π, (∀ κ σ', Ψ κ σ' ={∅}=∗ Π κ σ') -∗ σ ≈{ m }≈>ₛ Π)%I).
    iAssert (∀ Π, σ ≈{ m }≈>ₛ Π -∗ F σ Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"). done. }
    iIntros (?) "Hsim".
    iApply (sim_src_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros (?) "Hc".
    rewrite sim_src_unfold. iIntros "?".
    iMod ("Hsim" with "[$]") as "[?|[% [% [% Hsim]]]]"; [iLeft| iRight].
    - iMod ("Hc" with "[$]") as "$". done.
    - iModIntro. iExists _, _. iSplit; [done|].
      iIntros (??). iMod ("Hsim" with "[//]") as "Hsim".
      case_match.
      + by iMod ("Hc" with "[$]").
      + iModIntro. by iApply "Hsim".
  Qed.

  Lemma sim_src_wand σ Π Ψ:
    σ ≈{ m }≈>ₛ Π -∗
    (∀ κ σ, Π κ σ -∗ Ψ κ σ) -∗
    σ ≈{ m }≈>ₛ Ψ.
  Proof.
    iIntros "Hsim Hwand".
    iApply (sim_src_wand_strong with "Hsim"). iIntros (??) "?". iModIntro. by iApply "Hwand".
  Qed.

  Lemma sim_src_bind σ Π :
    σ ≈{ m }≈>ₛ (λ κ σ', Π κ σ' ∨ ⌜κ = None⌝ ∗ σ' ≈{ m }≈>ₛ Π) -∗
    σ ≈{ m }≈>ₛ Π.
  Proof.
    iIntros "HΠ".
    pose (F := (λ σ Ψ, ∀ Π, (∀ κ (σ' : m_state m), Ψ κ σ' -∗ Π κ σ' ∨ ⌜κ = @None EV⌝ ∗ σ' ≈{ m }≈>ₛ Π) -∗ σ ≈{ m }≈>ₛ Π)%I).
    iAssert (∀ Π, σ ≈{ m }≈>ₛ Π -∗ F σ Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "HΠ"). iIntros (??) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_src_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros (?) "Hc".
    rewrite sim_src_unfold. iIntros "#?".
    iMod ("Hsim" with "[$]") as "[?|[% [% [% Hsim]]]]".
    - iSpecialize ("Hc" with "[$]"). iDestruct "Hc" as "[$|[_ Hc]]"; [done|].
      rewrite sim_src_unfold. by iApply "Hc".
    - iModIntro. iRight. iExists _, _. iSplit; [done|]. iIntros (??). iMod ("Hsim" with "[//]") as "Hsim".
      case_match.
      + by iDestruct ("Hc" with "[$]") as "[$|[% ?]]".
      + iModIntro. by iApply "Hsim".
  Qed.

  Lemma fupd_sim_src σ Π :
    (|={∅}=> σ ≈{ m }≈>ₛ Π) -∗
    σ ≈{ m }≈>ₛ Π.
  Proof. iIntros "Hsim". rewrite sim_src_unfold. iMod "Hsim". iApply "Hsim". Qed.

  Lemma sim_src_ctx σ Π :
    (ord_later_ctx -∗ σ ≈{ m }≈>ₛ Π) -∗
    σ ≈{ m }≈>ₛ Π.
  Proof. iIntros "Hsim". rewrite sim_src_unfold. iIntros "#?". by iApply "Hsim". Qed.

  Lemma sim_src_stop σ Π :
    Π None σ -∗
    σ ≈{ m }≈>ₛ Π.
  Proof. iIntros "?". rewrite sim_src_unfold. iIntros "?". iLeft. by iFrame. Qed.

  Lemma sim_src_step Pσ κ σ Π :
    m_step m σ κ Pσ →
    (∀ σ', ⌜Pσ σ'⌝ ={∅}=∗ if κ is Some _ then Π κ σ' else σ' ≈{ m }≈>ₛ Π) -∗
    σ ≈{ m }≈>ₛ Π.
  Proof.
    iIntros (?) "HΠ". rewrite sim_src_unfold.
    iIntros "?". iRight. iModIntro. iExists _, _. iSplit; [done|].
    iIntros (??). by iMod ("HΠ" with "[//]").
  Qed.

  Lemma sim_src_step_end Pσ κ σ Π :
    m_step m σ κ Pσ →
    (∀ σ', ⌜Pσ σ'⌝ ={∅}=∗ Π κ σ') -∗
    σ ≈{ m }≈>ₛ Π.
  Proof.
    iIntros (?) "HΠ". iApply sim_src_step; [done|].
    iIntros (??). iMod ("HΠ" with "[//]"). iModIntro. case_match; [done|].
    by iApply sim_src_stop.
  Qed.

  (* One should be able to get rid of the [HasNoLc] if one uses classical logic. *)
  (* TODO: Is it possible to get a stronger adequacy lemma? *)
  Lemma sim_src_elim E Pσ σ Π κs `{!VisNoAng m} :
    ord_later_ctx -∗
    σ ≈{ m }≈>ₛ Π -∗
    (∀ κ σ', Π κ σ' -∗ ∃ κs', ⌜κs = tapp (option_trace κ) κs'⌝ ∗ |={E}=> ⌜σ' ~{m, κs'}~>ₜ Pσ⌝ ) -∗
    |={E}=> ⌜σ ~{m, κs}~>ₜ Pσ⌝.
  Proof.
    iIntros "#? Hsim HΠ".
    pose (F := (λ σ Π,
      (∀ κ σ', Π κ σ' -∗ ∃ κs', ⌜κs = tapp (option_trace κ) κs'⌝ ∗ |={E}=> ⌜σ' ~{m, κs'}~>ₜ Pσ⌝ ) -∗
        |={E}=> ⌜σ ~{m, κs}~>ₜ Pσ⌝)%I).
    iAssert (∀ Π, σ ≈{ m }≈>ₛ Π -∗ F σ Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"). done. }
    iIntros (?) "Hsim".
    iApply (sim_src_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros "Hc".
    iMod (fupd_mask_subseteq ∅) as "He"; [set_solver|].
    iMod ("Hsim" with "[$]") as "[?|[% [% [% Hsim]]]]"; iMod "He" as "_".
    { iDestruct ("Hc" with "[$]") as (??) "?". subst. done. }
    destruct κ; last first.
    - iApply (fupd_mono _ _ ⌜_⌝). { iPureIntro. by apply TTraceStepNone. }
      iIntros (??).
      iMod (fupd_mask_subseteq ∅) as "He"; [set_solver|].
      iMod ("Hsim" with "[//]") as "Hsim". iMod "He" as "_".
      by iApply "Hsim".
    - exploit vis_no_all; [done|] => -[??].
      iMod (fupd_mask_subseteq ∅) as "He"; [set_solver|].
      iMod ("Hsim" with "[%]"); [naive_solver|]. iMod "He" as "_".
      iDestruct ("Hc" with "[$]") as (?->) ">%". iPureIntro. tstep; [done| |done]. naive_solver.
  Qed.
End sim_src.

(** * [sim] *)
Section sim.
  Context {Σ : gFunctors} {EV : Type} `{!dimsumGS Σ}.
  Context (m_t m_s : mod_trans EV).

  Definition sim_pre
    (sim : leibnizO (m_t.(m_state)) -d> leibnizO (m_s.(m_state)) -d> iPropO Σ) :
    leibnizO (m_t.(m_state)) -d> leibnizO (m_s.(m_state)) -d> iPropO Σ := λ σ_t σ_s,
      (σ_t ≈{ m_t }≈>ₜ λ κ Pσ, σ_s ≈{ m_s }≈>ₛ λ κ' σ_s', ⌜κ = κ'⌝ ∗ bi_mono1 Pσ (λ σ_t', sim σ_t' σ_s'))%I.

  Global Instance sim_pre_ne n:
    Proper ((dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n) sim_pre.
  Proof.
    move => ?? Hsim ?? -> ?? ->. rewrite /sim_pre/bi_mono1.
    f_equiv. move => ?? -> ?? ->.
    f_equiv. move => ?? -> ?? ->.
    repeat (f_equiv || eapply Hsim || eapply HΠ || reflexivity).
  Qed.

  Lemma sim_pre_mono sim1 sim2:
    ⊢ □ (∀ σ_t σ_s, sim1 σ_t σ_s -∗ sim2 σ_t σ_s)
    → ∀ σ_t σ_s , sim_pre sim1 σ_t σ_s -∗ sim_pre sim2 σ_t σ_s.
  Proof.
    iIntros "#Hinner" (σ_t σ_s) "Hsim".
    iApply (sim_tgt_wand with "Hsim"). iIntros (??) "Hsim".
    iApply (sim_src_wand with "Hsim"). iIntros (??) "[% Hsim]".
    iSplit; [done|]. iApply (bi_mono1_mono with "Hsim"). iIntros (?) "?". by iApply "Hinner".
  Qed.

  Local Instance sim_pre_monotone :
    BiMonoPred (λ sim : prodO (leibnizO (m_t.(m_state))) (leibnizO (m_s.(m_state))) -d> iPropO Σ, uncurry (sim_pre (curry sim))).
  Proof.
    constructor.
    - iIntros (Π Ψ ??) "#Hinner". iIntros ([??]) "Hsim" => /=. iApply sim_pre_mono; [|done].
      iIntros "!>" (??) "HΠ". by iApply ("Hinner" $! (_, _)).
    - move => sim_src Hsim n [σ_t1 σ_s1] [σ_t2 σ_s2] /= [/=??].
      apply sim_pre_ne; eauto. move => ?????? /=. by apply: Hsim.
  Qed.

  Definition sim : m_t.(m_state) → m_s.(m_state) → iProp Σ :=
    curry (bi_least_fixpoint (λ sim : prodO (leibnizO (m_t.(m_state))) (leibnizO (m_s.(m_state))) -d> iPropO Σ, uncurry (sim_pre (curry sim)))).

  Global Instance sim_ne n:
    Proper ((=) ==> (=) ==> dist n) sim.
  Proof. move => ?? -> ?? ->. unfold sim. f_equiv. Qed.
End sim.

Notation "σ_t ⪯{ m_t , m_s } σ_s" := (sim m_t m_s σ_t σ_s) (at level 70,
    format "σ_t  ⪯{ m_t ,  m_s }  σ_s") : bi_scope.

Section sim.
  Context {Σ : gFunctors} {EV : Type} `{!dimsumGS Σ}.
  Context (m_t m_s : mod_trans EV).

  Local Existing Instance sim_pre_monotone.
  Lemma sim_unfold σ_t σ_s :
    σ_t ⪯{m_t, m_s} σ_s ⊣⊢ sim_pre m_t m_s (sim m_t m_s) σ_t σ_s.
  Proof. rewrite /sim /curry. apply: least_fixpoint_unfold. Qed.

  Lemma sim_strong_ind (R: leibnizO (m_t.(m_state)) -d> leibnizO (m_s.(m_state)) -d> iPropO Σ):
    NonExpansive2 R →
    ⊢ (□ ∀ σ_t σ_s, sim_pre m_t m_s (λ σ_t σ_s, R σ_t σ_s ∧ σ_t ⪯{m_t, m_s} σ_s) σ_t σ_s -∗ R σ_t σ_s)
      -∗ ∀ σ_t σ_s, σ_t ⪯{m_t, m_s} σ_s -∗ R σ_t σ_s.
  Proof.
    iIntros (Hne) "#HPre". iIntros (σ_t σ_s) "Hsim".
    rewrite {2}/sim {1}/curry.
    iApply (least_fixpoint_ind _ (uncurry R) with "[] Hsim").
    iIntros "!>" ([??]) "Hsim" => /=. by iApply "HPre".
  Qed.

  Lemma sim_ind (R: leibnizO (m_t.(m_state)) -d> leibnizO (m_s.(m_state)) -d> iPropO Σ) :
    NonExpansive2 R →
    ⊢ (□ ∀ σ_t σ_s, sim_pre m_t m_s R σ_t σ_s -∗ R σ_t σ_s)
      -∗ ∀ σ_t σ_s, σ_t ⪯{m_t, m_s} σ_s -∗ R σ_t σ_s.
  Proof.
    iIntros (Hne) "#HPre". iApply sim_strong_ind. iIntros "!>" (σ_t σ_s) "Hsim".
    iApply "HPre". iApply (sim_pre_mono with "[] Hsim").
    iIntros "!>" (??) "[? _]". by iFrame.
  Qed.

  Lemma fupd_sim σ_t σ_s :
    (|={∅}=> σ_t ⪯{m_t, m_s} σ_s) -∗
    σ_t ⪯{m_t, m_s} σ_s.
  Proof. iIntros "Hsim". rewrite sim_unfold. by iApply fupd_sim_tgt. Qed.

  Lemma sim_ctx σ_t σ_s :
    (ord_later_ctx -∗ σ_t ⪯{m_t, m_s} σ_s) -∗
    σ_t ⪯{m_t, m_s} σ_s.
  Proof. iIntros "Hsim". rewrite sim_unfold. by iApply sim_tgt_ctx. Qed.

End sim.

Theorem sim_adequacy Σ EV (m_t m_s : module EV) `{!dimsumPreG Σ} `{!VisNoAng (m_trans m_s)} :
  (∀ `{Hinv : !invGS_gen HasNoLc Σ} `{Hord : !ord_laterGS Σ},
    ⊢ |={⊤}=>
       let _ : dimsumGS Σ := DimsumGS _ _ _
       in
       m_init m_t ⪯{m_trans m_t, m_trans m_s} m_init m_s ) →
  trefines m_t m_s.
Proof.
  intros Hsim. constructor => κs /thas_trace_n [n Htrace].
  apply (step_fupdN_soundness_no_lc _ 0 0) => ? /=. simpl in *. iIntros "_".
  iMod (ord_later_alloc n) as (?) "Ha". iDestruct (ord_later_ctx_alloc with "Ha") as "#?".
  iMod Hsim as "Hsim".
  clear Hsim. set (X := DimsumGS _ _ _ : dimsumGS Σ).
  pose (F := (λ σ_t σ_s,
               ∀ n κs,
               ⌜σ_t ~{ m_trans m_t, κs, n }~>ₜ -⌝ -∗
               ord_later_auth n -∗
               |={⊤,∅}=> ⌜σ_s ~{ m_trans m_s, κs }~>ₜ -⌝)%I
          : _ → _ → iProp Σ ).
  iAssert (∀ σ_t σ_s, σ_t ⪯{m_trans m_t, m_trans m_s} σ_s -∗ F σ_t σ_s)%I as "Hgen"; last first. {
    by iApply ("Hgen" with "Hsim").
  }
  clear n κs Htrace. iIntros (σ_t σ_s) "Hsim".
  iApply (sim_ind with "[] Hsim").
  iIntros "!>" (??) "Hsim". iIntros (n κs Htrace) "Ha".
  iApply (fupd_mask_weaken ∅); [set_solver|]. iIntros "He".
  iApply (sim_tgt_elim with "Hsim Ha"); [done|].
  iIntros (???) "Hsim".
  iDestruct (bi_mono1_elim with "Hsim []") as "Hsim".
  { iIntros (?) "Hwand ?". iApply (sim_src_wand with "[$]"). iIntros (??) "[$ ?]".
    iApply (bi_mono1_mono_l with "[$] [$]"). }
  iApply (sim_src_elim with "[$] Hsim"). iIntros (??) "[% Hsim]". subst.
  iDestruct (bi_mono1_elim with "Hsim []") as (?) "[Hsim [% ?]]".
  { iIntros (?) "Hwand [% [??]]". iExists _. iFrame. by iApply "Hwand". }
  iExists _. iSplit; [done|].
  iMod "He" as "_". iApply ("Hsim" with "[//] [$]").
Qed.
