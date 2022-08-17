From iris.bi Require Import fixpoint.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From dimsum.core Require Export module trefines.
Set Default Proof Using "Type".

(** * [sim_steps] *)
Section sim_steps.
  Context {Σ : gFunctors} {EV : Type} `{!invGS_gen HasNoLc Σ}.
  Context (m : mod_trans EV).

  Definition sim_steps_pre
    (sim_steps : leibnizO (m.(m_state)) -d> leibnizO (option EV) -d>
                   (leibnizO (m.(m_state)) -d> iPropO Σ) -d> iPropO Σ) :
    leibnizO (m.(m_state)) -d> leibnizO (option EV) -d>
      (leibnizO (m.(m_state)) -d> iPropO Σ) -d> iPropO Σ := λ σ κ Φ,
  (|={∅}=> (⌜κ = None⌝ ∗ Φ σ) ∨
        ∃ κ' Pσ, ⌜σ ~{m, option_trace κ'}~>ₜ Pσ⌝ ∗ ⌜option_prefix κ' κ⌝ ∗
         ∀ σ', ⌜Pσ σ'⌝ ={∅}=∗ sim_steps σ' (option_drop κ' κ) Φ)%I.

  Global Instance sim_steps_pre_ne n:
    Proper ((dist n ==> dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n ==> dist n) sim_steps_pre.
  Proof.
    move => ?? Hsim ?? -> ?? -> ?? HΦ. rewrite /sim_steps_pre.
    repeat (f_equiv || eapply Hsim || eapply HΦ || reflexivity).
  Qed.

  Lemma sim_steps_pre_mono sim1 sim2:
    ⊢ □ (∀ σ κ Φ, sim1 σ κ Φ -∗ sim2 σ κ Φ)
    → ∀ σ κ Φ , sim_steps_pre sim1 σ κ Φ -∗ sim_steps_pre sim2 σ κ Φ.
  Proof.
    iIntros "#Hinner" (σ κ Φ) "Hsim".
    iMod "Hsim" as "[[% ?]|[% [% [% [% Hsim]]]]]"; [by iLeft; iFrame| iRight].
    iModIntro. iExists _, _. iSplit; [done|]. iSplit; [done|].
    iIntros (??). iMod ("Hsim" with "[//]"). iModIntro. by iApply "Hinner".
  Qed.

  Local Instance sim_steps_pre_monotone :
    BiMonoPred (λ sim_steps : prodO (prodO (leibnizO (m.(m_state))) (leibnizO (option EV))) ((leibnizO (m.(m_state))) -d> iPropO Σ) -d> iPropO Σ, uncurry3 (sim_steps_pre (curry3 sim_steps))).
  Proof.
    constructor.
    - iIntros (Φ Ψ ??) "#Hinner". iIntros ([[??]?]) "Hsim" => /=. iApply sim_steps_pre_mono; [|done].
      iIntros "!>" (???) "HΦ". by iApply ("Hinner" $! (_, _, _)).
    - move => sim_steps Hsim n [[σ1 κ1] Φ1] [[σ2 κ2] Φ2] /= [[/=??]?].
      apply sim_steps_pre_ne; eauto. move => ????????? /=. by apply: Hsim.
  Qed.

  Definition sim_steps : m.(m_state) → option EV → (m.(m_state) → iProp Σ) → iProp Σ :=
    curry3 (bi_least_fixpoint (λ sim_steps : prodO (prodO (leibnizO (m.(m_state))) (leibnizO (option EV))) ((leibnizO (m.(m_state))) -d> iPropO Σ) -d> iPropO Σ, uncurry3 (sim_steps_pre (curry3 sim_steps)))).

  Global Instance sim_steps_ne n:
    Proper ((=) ==> (=) ==> ((=) ==> dist n) ==> dist n) sim_steps.
  Proof. move => ?? -> ?? -> ?? HΦ. unfold sim_steps. f_equiv. intros ?. by apply HΦ. Qed.
End sim_steps.

Notation " σ '≈{' m , κ '}≈>' P " := (sim_steps m σ κ P)
  (at level 70, format "σ  '≈{'  m ,  κ  '}≈>'  P") : bi_scope.

Section sim_steps.
  Context {Σ : gFunctors} {EV : Type} `{!invGS_gen HasNoLc Σ}.
  Context (m : mod_trans EV).
  Implicit Types Φ : m.(m_state) → iProp Σ.

  Local Existing Instance sim_steps_pre_monotone.
  Lemma sim_steps_unfold σ κ Φ:
    σ ≈{ m, κ }≈> Φ ⊣⊢ sim_steps_pre m (sim_steps m) σ κ Φ.
  Proof. rewrite /sim_steps /curry3. apply: least_fixpoint_unfold. Qed.

  Lemma sim_steps_strong_ind (R: leibnizO (m.(m_state)) -d> leibnizO (option EV) -d> (leibnizO (m.(m_state)) -d> iPropO Σ) -d> iPropO Σ):
    NonExpansive3 R →
    ⊢ (□ ∀ σ κ Φ, sim_steps_pre m (λ σ κ Ψ, R σ κ Ψ ∧ σ ≈{ m, κ }≈> Ψ) σ κ Φ -∗ R σ κ Φ)
      -∗ ∀ σ κ Φ, σ ≈{ m, κ }≈> Φ -∗ R σ κ Φ.
  Proof.
    iIntros (Hne) "#HPre". iIntros (σ κ Φ) "Hsim".
    rewrite {2}/sim_steps {1}/curry3.
    iApply (least_fixpoint_ind _ (uncurry3 R) with "[] Hsim").
    iIntros "!>" ([[??]?]) "Hsim" => /=. by iApply "HPre".
  Qed.

  Lemma sim_steps_ind (R: leibnizO (m.(m_state)) -d> leibnizO (option EV) -d> (leibnizO (m.(m_state)) -d> iPropO Σ) -d> iPropO Σ) :
    NonExpansive3 R →
    ⊢ (□ ∀ σ κ Φ, sim_steps_pre m R σ κ Φ -∗ R σ κ Φ)
      -∗ ∀ σ κ Φ, σ ≈{ m, κ }≈> Φ -∗ R σ κ Φ.
  Proof.
    iIntros (Hne) "#HPre". iApply sim_steps_strong_ind. iIntros "!>" (σ κ Φ) "Hsim".
    iApply "HPre". iApply (sim_steps_pre_mono with "[] Hsim").
    iIntros "!>" (???) "[? _]". by iFrame.
  Qed.

  Lemma sim_steps_wand_strong σ κ Φ Ψ:
    σ ≈{ m, κ }≈> Φ -∗
    (∀ σ, Φ σ ={∅}=∗ Ψ σ) -∗
    σ ≈{ m, κ }≈> Ψ.
  Proof.
    iIntros "Hsim Hwand".
    pose (F := (λ σ κ Ψ, ∀ Φ, (∀ σ', Ψ σ' ={∅}=∗ Φ σ') -∗ σ ≈{ m, κ }≈> Φ)%I).
    iAssert (∀ Φ, σ ≈{ m, κ }≈> Φ -∗ F σ κ Φ)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"). done. }
    iIntros (?) "Hsim".
    iApply (sim_steps_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (?? ?) "Hsim". iIntros (?) "Hc".
    rewrite sim_steps_unfold. iMod "Hsim" as "[[% ?]|[% [% [% [% Hsim]]]]]"; [iLeft| iRight].
    - iMod ("Hc" with "[$]") as "$". done.
    - iModIntro. iExists _, _. iSplit; [done|]. iSplit; [done|].
      iIntros (??). iMod ("Hsim" with "[//]") as "Hsim". iModIntro. by iApply "Hsim".
  Qed.

  Lemma sim_steps_wand σ κ Φ Ψ:
    σ ≈{ m, κ }≈> Φ -∗
    (∀ σ, Φ σ -∗ Ψ σ) -∗
    σ ≈{ m, κ }≈> Ψ.
  Proof.
    iIntros "Hsim Hwand".
    iApply (sim_steps_wand_strong with "Hsim"). iIntros (?) "?". iModIntro. by iApply "Hwand".
  Qed.

  Lemma sim_steps_bind κ σ Φ :
    σ ≈{ m, None }≈> (λ σ', σ' ≈{ m, κ }≈> Φ) -∗
    σ ≈{ m, κ }≈> Φ.
  Proof.
    iIntros "HΦ".
    pose (F := (λ σ κ' Ψ, ∀ Φ, ⌜κ' = @None EV⌝ -∗ (∀ σ' : m_state m, Ψ σ' -∗ σ' ≈{ m, κ }≈> Φ) -∗ σ ≈{ m, κ }≈> Φ)%I).
    iAssert (∀ Φ, σ ≈{ m, None }≈> Φ -∗ F σ None Φ)%I as "Hgen"; last first.
    { iApply ("Hgen" with "HΦ"); [done|]. iIntros (?) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_steps_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (?? ?) "Hsim". iIntros (?->) "Hc".
    rewrite sim_steps_unfold. iMod "Hsim" as "[[% ?]|[% [% [% [% Hsim]]]]]".
    - iSpecialize ("Hc" with "[$]"). rewrite sim_steps_unfold. iApply "Hc".
    - iModIntro. iRight. iExists _, _. iSplit; [done|]. destruct κ' => //. iSplit; [done|].
      iIntros (??). iMod ("Hsim" with "[//]") as "Hsim". iModIntro. by iApply "Hsim".
  Qed.

  Lemma sim_steps_stop σ Φ :
    Φ σ -∗
    σ ≈{ m, None }≈> Φ.
  Proof. iIntros "?". rewrite sim_steps_unfold. iLeft. by iFrame. Qed.

  Lemma sim_steps_step κ' Pσ κ σ Φ :
    σ ~{m, option_trace κ'}~>ₜ Pσ →
    option_prefix κ' κ →
    (∀ σ', ⌜Pσ σ'⌝ ={∅}=∗ σ' ≈{ m, option_drop κ' κ }≈> Φ) -∗
    σ ≈{ m, κ }≈> Φ.
  Proof.
    iIntros (??) "HΦ". rewrite sim_steps_unfold.
    iRight. iModIntro. iExists _, _. iSplit; [done|]. iSplit; [done|].
    iIntros (??). by iMod ("HΦ" with "[//]").
  Qed.

  (* One should be able to get rid of the [HasNoLc] if one uses classical logic. *)
  (* TODO: Is it possible to get a stronger adequacy lemma? *)
  Lemma sim_steps_elim E Pσ κ σ Φ κs :
    σ ≈{ m, κ }≈> Φ -∗
    (∀ σ', Φ σ' -∗ |={E}=> ⌜σ' ~{m, κs}~>ₜ Pσ⌝ ) -∗
    |={E}=> ⌜σ ~{m, tapp (option_trace κ) κs}~>ₜ Pσ⌝.
  Proof.
    iIntros "Hsim HΦ".
    pose (F := (λ σ κ Φ,
      (∀ σ', Φ σ' -∗ |={E}=> ⌜σ' ~{m, κs}~>ₜ Pσ⌝ ) -∗
        |={E}=> ⌜σ ~{m, tapp (option_trace κ) κs}~>ₜ Pσ⌝)%I).
    iAssert (∀ Φ, σ ≈{ m, κ }≈> Φ -∗ F σ κ Φ)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"). done. }
    iIntros (?) "Hsim".
    iApply (sim_steps_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (?? ?) "Hsim". iIntros "Hc".
    iMod (fupd_mask_subseteq ∅) as "He"; [set_solver|].
    iMod "Hsim" as "[[% ?]|[% [% [% [% Hsim]]]]]"; iMod "He" as "_".
    { subst. by iApply "Hc". }
    erewrite option_prefix_option_trace; [|done]. rewrite -assoc_L.
    iApply (fupd_mono _ _ ⌜_⌝). { iPureIntro. by apply thas_trace_trans. }
    iIntros (??).
    iMod (fupd_mask_subseteq ∅) as "He"; [set_solver|].
    iMod ("Hsim" with "[//]") as "Hsim". iMod "He" as "_".
    by iApply "Hsim".
  Qed.
End sim_steps.
