From iris.bi Require Import fixpoint.
From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From dimsum.core Require Export module trefines.
From dimsum.core.iris Require Export ord_later.
Set Default Proof Using "Type".

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

(** * [sim_tgt] *)
Section sim_tgt.
  Context {Σ : gFunctors} {EV : Type} `{!dimsumGS Σ}.
  Context (m : mod_trans EV).

  Definition sim_tgt_pre
    (sim_tgt : leibnizO (m.(m_state)) -d>
                   (leibnizO (option EV) -d> ((leibnizO (m.(m_state)) -d> iPropO Σ) -d> iPropO Σ) -d> iPropO Σ) -d> iPropO Σ) :
    leibnizO (m.(m_state)) -d>
      (leibnizO (option EV) -d> ((leibnizO (m.(m_state)) -d> iPropO Σ) -d> iPropO Σ) -d> iPropO Σ) -d> iPropO Σ := λ σ Π,
  (ord_later_ctx -∗ |={∅}=> (∃ P, Π None P ∗ ∀ P', P P' -∗ P' σ) ∨
        ∀ κ Pσ, ⌜m.(m_step) σ κ Pσ⌝ ={∅}=∗ ▷ₒ
           ((∃ P, Π κ P ∗ ∀ P', P P' -∗ ∃ σ', ⌜Pσ σ'⌝ ∗ P' σ') ∨ ∃ σ', ⌜κ = None⌝ ∗ ⌜Pσ σ'⌝ ∗ sim_tgt σ' Π))%I.

  Global Instance sim_tgt_pre_ne n:
    Proper ((dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n) sim_tgt_pre.
  Proof.
    move => ?? Hsim ?? -> ?? HΠ. rewrite /sim_tgt_pre.
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

  Lemma sim_tgt_wand σ Π Ψ:
    σ ≈{ m }≈>ₜ Π -∗
    (∀ κ Pσ, Π κ Pσ -∗ Ψ κ Pσ) -∗
    σ ≈{ m }≈>ₜ Ψ.
  Proof.
    iIntros "Hsim Hwand".
    pose (F := (λ σ Ψ, ∀ Π, (∀ σ' κ, Ψ σ' κ -∗ Π σ' κ) -∗ σ ≈{ m }≈>ₜ Π)%I).
    iAssert (∀ Π, σ ≈{ m }≈>ₜ Π -∗ F σ Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"). done. }
    iIntros (?) "Hsim".
    iApply (sim_tgt_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros (?) "Hc".
    rewrite sim_tgt_unfold. iIntros "#?".
    iMod ("Hsim" with "[$]") as "[[% [??]]|Hsim]"; [iLeft| iRight].
    - iModIntro. iExists _. iFrame. by iApply "Hc".
    - iIntros "!>" (???). iMod ("Hsim" with "[//]") as "Hsim". do 2 iModIntro.
      iDestruct "Hsim" as "[[% [??]]|[% [% [% Hsim]]]]"; [iLeft; iExists _; iFrame; by iApply "Hc"| iRight].
      iExists _. iSplit; [done|]. iSplit; [done|]. by iApply "Hsim".
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
    Π None (λ P, P σ) -∗
    σ ≈{ m }≈>ₜ Π.
  Proof.
    iIntros "?". rewrite sim_tgt_unfold. iIntros "?". iModIntro.
    iLeft. iExists _. iFrame. by iIntros.
  Qed.

  Lemma sim_tgt_step σ Π :
    (∀ κ Pσ, ⌜m.(m_step) σ κ Pσ⌝ ={∅}=∗ ▷ₒ
        ((∃ P, Π κ P ∗ ∀ P', P P' -∗ ∃ σ', ⌜Pσ σ'⌝ ∗ P' σ') ∨ ∃ σ', ⌜κ = None⌝ ∗ ⌜Pσ σ'⌝ ∗ σ' ≈{m}≈>ₜ Π)) -∗
    σ ≈{ m }≈>ₜ Π.
  Proof.
    iIntros "Hsim". rewrite sim_tgt_unfold. iIntros "#?". iModIntro. iRight.
    iIntros (???). iMod ("Hsim" with "[//]") as "Hsim". do 2 iModIntro. done.
  Qed.

  Lemma sim_tgt_step_end σ Π :
    (∀ κ Pσ, ⌜m.(m_step) σ κ Pσ⌝ ={∅}=∗ ▷ₒ ∃ P, Π κ P ∗ ∀ P', P P' -∗ ∃ σ', ⌜Pσ σ'⌝ ∗ P' σ') -∗
    σ ≈{ m }≈>ₜ Π.
  Proof.
    iIntros "Hsim". iApply sim_tgt_step. iIntros (???). iMod ("Hsim" with "[//]") as "Hsim".
    do 2 iModIntro. by iLeft.
  Qed.

  Lemma sim_tgt_elim E σ Π κs n m_s σ_s :
    σ ~{m, κs, n}~>ₜ - →
    σ ≈{ m }≈>ₜ Π -∗
    ord_later_auth n -∗
    (∀ κ P n' κs', Π κ P -∗
       (∀ P', P P' -∗ ∃ σ', P' σ' ∗ ⌜σ' ~{m, κs', n'}~>ₜ -⌝ ∗ ord_later_auth n') -∗
           |={E}=> ⌜σ_s ~{m_s, tapp (option_trace κ) κs'}~>ₜ -⌝) -∗
    |={E}=> ⌜σ_s ~{m_s, κs}~>ₜ -⌝.
  Proof.
    iIntros (?) "Hsim Ha Hc".
    iDestruct (ord_later_ctx_alloc with "[$]") as "#?".
    pose (F := (λ σ Π,
      ∀ n κs,
        ⌜σ ~{m, κs, n}~>ₜ -⌝ -∗
        ord_later_auth n -∗
        (∀ κ P n' κs', Π κ P -∗
          (∀ P', P P' -∗ ∃ σ', P' σ' ∗ ⌜σ' ~{m, κs', n'}~>ₜ -⌝ ∗ ord_later_auth n') -∗
           |={E}=> ⌜σ_s ~{m_s, tapp (option_trace κ) κs'}~>ₜ -⌝) -∗
        |={E}=> ⌜σ_s ~{m_s, κs}~>ₜ -⌝)%I).
    iAssert (∀ Π, σ ≈{ m }≈>ₜ Π -∗ F σ Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim [//] [$] Hc"). }
    iIntros (?) "Hsim".
    iApply (sim_tgt_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros (?? Htrace) "Ha Hc".
    iMod (fupd_mask_subseteq ∅) as "He"; [set_solver|].
    iMod ("Hsim" with "[$]") as "[[% [? HP]]|Hsim]"; iMod "He" as "_".
    { iApply ("Hc" $! None with "[$]"). iIntros (?) "?". iExists _. iFrame. iSplit; [|done]. by iApply "HP". }
    move: Htrace => /tnhas_trace_inv Htrace.
    iApply (fupd_mono _ _ ⌜_⌝). { iPureIntro. by apply: thas_trace_under_tall. }
    iIntros (κs' [[??]|(?&?&?&?&?&?&?&?)]). { iPureIntro. tend. }
    iMod (fupd_mask_subseteq ∅) as "He"; [set_solver|].
    iMod ("Hsim" with "[//]") as "Hsim". iMod "He" as "_".
    iMod (ord_later_elim with "Hsim Ha [-]"); [|done]. iIntros "Ha".
    iMod (ord_later_update with "Ha"); [shelve|].
    iModIntro. iExists _. iFrame. iSplit; [done|]. iIntros "Ha [[% [? HP]]|[% [% [% Hsim]]]]". iModIntro.
    + iMod ("Hc" with "[$] [Ha HP]") as %?. 2: { iPureIntro. by apply: thas_trace_mono. }
      iIntros (?) "?". iDestruct ("HP" with "[$]") as (??) "?".
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
    σ ≈{ m }≈>ₛ (λ κ σ', ⌜κ = None⌝ ∗ σ' ≈{ m }≈>ₛ Π) -∗
    σ ≈{ m }≈>ₛ Π.
  Proof.
    iIntros "HΠ".
    pose (F := (λ σ Ψ, ∀ Π, (∀ κ (σ' : m_state m), Ψ κ σ' -∗ ⌜κ = @None EV⌝ ∗ σ' ≈{ m }≈>ₛ Π) -∗ σ ≈{ m }≈>ₛ Π)%I).
    iAssert (∀ Π, σ ≈{ m }≈>ₛ Π -∗ F σ Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "HΠ"). iIntros (??) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_src_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros (?) "Hc".
    rewrite sim_src_unfold. iIntros "#?".
    iMod ("Hsim" with "[$]") as "[?|[% [% [% Hsim]]]]".
    - iSpecialize ("Hc" with "[$]"). iDestruct "Hc" as "[_ Hc]". rewrite sim_src_unfold. by iApply "Hc".
    - iModIntro. iRight. iExists _, _. iSplit; [done|]. iIntros (??). iMod ("Hsim" with "[//]") as "Hsim".
      case_match.
      + by iDestruct ("Hc" with "[$]") as "[% ?]".
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
      (σ_t ≈{ m_t }≈>ₜ λ κ Pσ, σ_s ≈{ m_s }≈>ₛ λ κ' σ_s', ∃ P, ⌜κ = κ'⌝ ∗ Pσ P ∗
          (∀ σ_t', P σ_t' -∗ sim σ_t' σ_s'))%I.

  Global Instance sim_pre_ne n:
    Proper ((dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n) sim_pre.
  Proof.
    move => ?? Hsim ?? -> ?? ->. rewrite /sim_pre.
    apply sim_tgt_ne; [done|]. move => ?? -> ?? ->.
    apply sim_src_ne; [done|]. move => ?? -> ?? ->.
    repeat (f_equiv || eapply Hsim || eapply HΠ || reflexivity).
  Qed.

  Lemma sim_pre_mono sim1 sim2:
    ⊢ □ (∀ σ_t σ_s, sim1 σ_t σ_s -∗ sim2 σ_t σ_s)
    → ∀ σ_t σ_s , sim_pre sim1 σ_t σ_s -∗ sim_pre sim2 σ_t σ_s.
  Proof.
    iIntros "#Hinner" (σ_t σ_s) "Hsim".
    iApply (sim_tgt_wand with "Hsim"). iIntros (??) "Hsim".
    iApply (sim_src_wand with "Hsim"). iIntros (??) "[% [% [? Hsim]]]".
    iExists _. iFrame. iSplit; [done|]. iIntros (?) "?". iApply "Hinner". by iApply "Hsim".
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
  iIntros (????) "Hsim HP".
  iApply (sim_src_elim with "[$] Hsim"). iIntros (??) "[% [% [? Hsim]]]". subst.
  iDestruct ("HP" with "[$]") as (?) "[? [% ?]]".
  iExists _. iSplit; [done|].
  iMod "He" as "_". iApply ("Hsim" with "[$] [//] [$]").
Qed.
