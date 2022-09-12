From iris.algebra Require Import big_op gmap frac agree dfrac_agree.
From iris.base_logic.lib Require Import ghost_map.
From dimsum.core.iris Require Export iris.
From dimsum.examples Require Export rec.
From dimsum.core Require Import spec_mod.
From dimsum.examples Require Import memmove.
Set Default Proof Using "Type".

Local Open Scope Z_scope.

  Lemma loc_eq (l1 l2 : loc) :
    l1 = l2 ↔ l1.1 = l2.1 ∧ l1.2 = l2.2.
  Proof. destruct l1, l2; naive_solver. Qed.

Section sim.
  Context {Σ : gFunctors} {EV : Type} `{!dimsumGS Σ}.

  Definition sim_tgt_handler {m_t m_s : mod_trans EV}
    (σ : m_state m_s) :
    option EV → ((m_state m_t → iProp Σ) → iProp Σ) → iProp Σ :=
    λ κ Pσ, (σ ≈{m_s}≈>ₛ (λ κ' σ_s', ⌜κ = κ'⌝ ∗ bi_mono1 Pσ (λ σ_t', σ_t' ⪯{m_t, m_s} σ_s')))%I.

  Lemma sim_tgt_handler_intro m_t m_s σ_t σ_s :
    σ_t ≈{m_t}≈>ₜ sim_tgt_handler σ_s -∗ σ_t ⪯{m_t, m_s} σ_s.
  Proof. iIntros "?". by rewrite sim_unfold. Qed.

End sim.

Section link.
  Context {Σ : gFunctors} {EV : Type} {S : Type} `{!dimsumGS Σ}.
  Implicit Types (R : seq_product_case → S → EV → seq_product_case → S → EV → bool → Prop).

  Lemma sim_tgt_link_None R m1 m2 s σ1 σ2 Π :
    ▷ₒ (∀ e p' s' e' ok,
        ⌜R SPNone s e p' s' e' ok⌝ -∗
        Π (Some (Incoming, e')) (λ P, P (link_to_case ok p' e', s', σ1, σ2))) -∗
    (MLFNone, s, σ1, σ2) ≈{link_trans R m1 m2}≈>ₜ Π.
  Proof.
    iIntros "HΠ".
    iApply (sim_tgt_bi_mono1 with "[-]").
    iApply sim_tgt_state_transform; [done|] => /=.
    iApply (sim_tgt_map with "[-]").
    iApply sim_tgt_seq_product_None. iIntros (p) "!>". iIntros (????).
    inv_all @link_filter.
    iApply (bi_mono1_intro with "[HΠ]"); [by iApply "HΠ"|] => /=.
    iIntros (?) "?". iIntros ([[[??]?]?] ?); simplify_eq/=. by repeat case_match; simplify_eq/=.
  Qed.

  Definition link_tgt_left_handler R {m1 m2 : mod_trans (io_event EV)}
    (Π : option (io_event EV) → ((link_case EV * S * m_state m1 * m_state m2 → iProp Σ) → iProp Σ) → iProp Σ)
    (s : S) (σ2 : m_state m2)
    : option (io_event EV) → ((m_state m1 → iProp Σ) → iProp Σ) → iProp Σ :=
    λ κ Pσ,
      match κ with
            | None => Π None (λ P, Pσ (λ σ1', P (MLFLeft, s, σ1', σ2)))
            | Some e => ∀ p' s' e' ok, ⌜R SPLeft s e.2 p' s' e' ok⌝ -∗ ⌜e.1 = Outgoing⌝ -∗
                 Π (if p' is SPNone then Some (Outgoing, e') else None)
                 (λ P, Pσ (λ σ1', P (link_to_case ok p' e', s', σ1', σ2)))
            end%I.

  Lemma sim_tgt_link_left R m1 m2 s σ1 σ2 Π :
    σ1 ≈{m1}≈>ₜ link_tgt_left_handler R Π s σ2 -∗
    (MLFLeft, s, σ1, σ2) ≈{link_trans R m1 m2}≈>ₜ Π.
  Proof.
    iIntros "Hsim".
    iApply (sim_tgt_bi_mono1 with "[-]").
    iApply sim_tgt_state_transform; [done|] => /=.
    iApply (sim_tgt_map with "[-]").
    iApply sim_tgt_seq_product_left.
    iApply (sim_tgt_bi_mono2 with "[-]").
    iApply (sim_tgt_wand with "Hsim").
    iIntros (κ ?) "Hsim". iIntros (??????). destruct κ; destruct!/=.
    - inv_all @link_filter.
      iApply (bi_mono1_intro with "[Hsim]"); [by iApply "Hsim"|].
      iIntros (?) "HP". iApply (bi_mono1_intro with "HP").
      iIntros (?) "?". iIntros ([[[??]?]?]?). simplify_eq/=. by repeat case_match; simplify_eq/=.
    - iApply (bi_mono1_intro with "[Hsim]"); [by iApply "Hsim"|].
      iIntros (?) "HP". iApply (bi_mono1_intro with "HP").
      iIntros (?) "?". iIntros ([[[??]?]?]?). simplify_eq/=. done.
  Qed.

  Lemma sim_tgt_link_left_recv R m1 m2 s σ1 σ2 Π e :
    (σ1 ≈{m1}≈>ₜ λ κ Pσ,
      match κ with
      | None => Π None (λ P, Pσ (λ σ1', P (MLFRecvL e, s, σ1', σ2)))
      | Some e' => ⌜e' = (Incoming, e)⌝ -∗ Π None (λ P, Pσ (λ σ1', P (MLFLeft, s, σ1', σ2)))
      end%I) -∗
    (MLFRecvL e, s, σ1, σ2) ≈{link_trans R m1 m2}≈>ₜ Π.
  Proof.
    iIntros "Hsim".
    iApply (sim_tgt_bi_mono1 with "[-]").
    iApply sim_tgt_state_transform; [done|] => /=.
    iApply (sim_tgt_map with "[-]").
    iApply sim_tgt_seq_product_left.
    iApply (sim_tgt_bi_mono2 with "[-]").
    iApply (sim_tgt_wand with "Hsim").
    iIntros (κ ?) "Hsim". iIntros (??????). destruct κ; destruct!/=.
    - inv_all @link_filter.
      iApply (bi_mono1_intro with "[Hsim]"); [by iApply "Hsim"|].
      iIntros (?) "HP". iApply (bi_mono1_intro with "HP").
      iIntros (?) "?". iIntros ([[[??]?]?]?). by simplify_eq/=.
    - iApply (bi_mono1_intro with "[Hsim]"); [by iApply "Hsim"|].
      iIntros (?) "HP". iApply (bi_mono1_intro with "HP").
      iIntros (?) "?". iIntros ([[[??]?]?]?). simplify_eq/=. done.
  Qed.

  Definition link_tgt_right_handler R {m1 m2 : mod_trans (io_event EV)}
    (Π : option (io_event EV) → ((link_case EV * S * m_state m1 * m_state m2 → iProp Σ) → iProp Σ) → iProp Σ)
    (s : S) (σ1 : m_state m1)
    : option (io_event EV) → ((m_state m2 → iProp Σ) → iProp Σ) → iProp Σ :=
    λ κ Pσ,
      match κ with
            | None => Π None (λ P, Pσ (λ σ2', P (MLFRight, s, σ1, σ2')))
            | Some e => ∀ p' s' e' ok, ⌜R SPRight s e.2 p' s' e' ok⌝ -∗ ⌜e.1 = Outgoing⌝ -∗
                 Π (if p' is SPNone then Some (Outgoing, e') else None)
                 (λ P, Pσ (λ σ2', P (link_to_case ok p' e', s', σ1, σ2')))
            end%I.

  Lemma sim_tgt_link_right R m1 m2 s σ1 σ2 Π :
    σ2 ≈{m2}≈>ₜ link_tgt_right_handler R Π s σ1 -∗
    (MLFRight, s, σ1, σ2) ≈{link_trans R m1 m2}≈>ₜ Π.
  Proof.
    iIntros "Hsim".
    iApply (sim_tgt_bi_mono1 with "[-]").
    iApply sim_tgt_state_transform; [done|] => /=.
    iApply (sim_tgt_map with "[-]").
    iApply sim_tgt_seq_product_right.
    iApply (sim_tgt_bi_mono2 with "[-]").
    iApply (sim_tgt_wand with "Hsim").
    iIntros (κ ?) "Hsim". iIntros (??????). destruct κ; destruct!/=.
    - inv_all @link_filter.
      iApply (bi_mono1_intro with "[Hsim]"); [by iApply "Hsim"|].
      iIntros (?) "HP". iApply (bi_mono1_intro with "HP").
      iIntros (?) "?". iIntros ([[[??]?]?]?). simplify_eq/=. by repeat case_match; simplify_eq/=.
    - iApply (bi_mono1_intro with "[Hsim]"); [by iApply "Hsim"|].
      iIntros (?) "HP". iApply (bi_mono1_intro with "HP").
      iIntros (?) "?". iIntros ([[[??]?]?]?). simplify_eq/=. done.
  Qed.

  Lemma sim_tgt_link_right_recv R m1 m2 s σ1 σ2 Π e :
    (σ2 ≈{m2}≈>ₜ λ κ Pσ,
      match κ with
      | None => Π None (λ P, Pσ (λ σ2', P (MLFRecvR e, s, σ1, σ2')))
      | Some e' => ⌜e' = (Incoming, e)⌝ -∗ Π None (λ P, Pσ (λ σ2', P (MLFRight, s, σ1, σ2')))
      end%I) -∗
    (MLFRecvR e, s, σ1, σ2) ≈{link_trans R m1 m2}≈>ₜ Π.
  Proof.
    iIntros "Hsim".
    iApply (sim_tgt_bi_mono1 with "[-]").
    iApply sim_tgt_state_transform; [done|] => /=.
    iApply (sim_tgt_map with "[-]").
    iApply sim_tgt_seq_product_right.
    iApply (sim_tgt_bi_mono2 with "[-]").
    iApply (sim_tgt_wand with "Hsim").
    iIntros (κ ?) "Hsim". iIntros (??????). destruct κ; destruct!/=.
    - inv_all @link_filter.
      iApply (bi_mono1_intro with "[Hsim]"); [by iApply "Hsim"|].
      iIntros (?) "HP". iApply (bi_mono1_intro with "HP").
      iIntros (?) "?". iIntros ([[[??]?]?]?). by simplify_eq/=.
    - iApply (bi_mono1_intro with "[Hsim]"); [by iApply "Hsim"|].
      iIntros (?) "HP". iApply (bi_mono1_intro with "HP").
      iIntros (?) "?". iIntros ([[[??]?]?]?). simplify_eq/=. done.
  Qed.
End link.

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
           ∀ x', sat_closed γ x' -∗ Π None (λ P, P (SMProgRecv r.1, σ, (PPInside, r.2, uPred_shrink x')))) -∗
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

  Lemma sim_tgt_prepost_Inside i o m s σ x Π e γ :
    (sat_closed γ x ∗ ∀ r y x', ⌜pp_to_ex (o e s) (λ r' y', r' = r ∧ y' = y)⌝ -∗
       sat_open γ -∗ sat γ y -∗ sat γ x' -∗
        ▷ₒ Π (Some r.1) (λ P, P (SMFilter, σ, (PPOutside, r.2, uPred_shrink x')))) -∗
    (SMFilterRecv e, σ, (PPInside, s, uPred_shrink x)) ≈{prepost_trans i o m}≈>ₜ Π.
  Proof using Type*.
    iIntros "[Hclosed HΠ]".
    iApply (sim_tgt_bi_mono1 with "[-]").
    iApply sim_tgt_bind.
    iApply (sim_tgt_seq_map_filter_recv with "[-]").
    iApply (sim_tgt_step_end with "[-]"). iIntros (???). inv_all @m_step.
    do 2 iModIntro. iIntros (?). iSplit!.
    iApply (sim_tgt_seq_map_filter with "[-]").
    iApply (sim_tgt_step with "[-]"). iIntros (???). inv_all @m_step.
    revert select (satisfiable _). rewrite uPred_expand_shrink assoc => ?.
    iMod ("Hclosed" with "[//]") as "[Ha [??]]".
    iSpecialize ("HΠ" with "[//] [$] [$] [$]").
    do 2 iModIntro. iRight. iSplit!.
    iApply (sim_tgt_step with "[-]"). iIntros (???). inv_all @m_step.
    do 2 iModIntro. iLeft.
    iApply (bi_mono1_intro with "HΠ").
    iIntros (?) "?". iSplit!.
  Qed.
End prepost.

Definition spec_state_interp {Σ EV S} (state_interp : S → iProp Σ) : (spec EV S void * S) → option S → iProp Σ :=
  λ s os, if os is Some s' then ⌜s.2 = s'⌝%I else state_interp s.2.

Arguments spec_state_interp _ _ _ _ _ !_ /.

Program Definition spec_mod_lang {Σ} (EV S : Type) (state_interp : S → iProp Σ)  : mod_lang EV Σ := {|
  mexpr := spec EV S void;
  mectx := unit;
  mstate := S;
  mfill _ := id;
  mcomp_ectx _ _:= tt;
  mtrans := spec_trans EV S;
  mexpr_rel σ t := σ.1 ≡ t;
  mstate_interp := spec_state_interp state_interp;
|}.
Next Obligation. done. Qed.

Definition spec_mod_lang_unit {Σ} (EV : Type) : mod_lang EV Σ :=
  spec_mod_lang EV unit (λ _, True%I).

Section spec.
  Context `{!dimsumGS Σ} {EV S : Type} {state_interp : S → iProp Σ}.

  Global Instance sim_tgt_expr_spec_proper :
    Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (⊣⊢)) (sim_tgt_expr (Λ:=spec_mod_lang EV S state_interp)).
  Proof.
    move => ?? ? ?? -> ?? -> ?? ->.
    Local Transparent sim_tgt_expr.
    Local Typeclasses Transparent sim_tgt_expr.
    iSplit; iIntros "HP" (?) "?"; iIntros (??); destruct!/=; iApply ("HP" with "[$]"); iPureIntro; split!.
    all: by etrans; [done|].
    Unshelve. all: exact tt.
  Qed.

  Global Instance sim_src_expr_spec_proper :
    Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (⊣⊢)) (sim_src_expr (Λ:=spec_mod_lang EV S state_interp)).
  Proof.
    move => ?? ? ?? -> ?? -> ?? ->.
    Local Transparent sim_src_expr.
    Local Typeclasses Transparent sim_src_expr.
    iSplit; iIntros "HP" (?) "?"; iIntros (??); destruct!/=; iApply ("HP" with "[$]"); iPureIntro; split!.
    all: by etrans; [done|].
    Unshelve. all: exact tt.
  Qed.

  Let X := (spec_mod_lang EV _ state_interp).
  Local Canonical Structure X.

  Lemma sim_tgt_TVis k Π Φ e os :
    (▷ₒ Π (Some e) (λ P, (∀ σ, σ ⤇ₜ (λ Π, TGT k tt @ ? os [{ Π }] {{ Φ }}) -∗ P σ))) -∗
    TGT (Spec.bind (TVis e) k) @ ? os [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_tgt_expr_bi_mono.
    iApply sim_tgt_expr_step. iIntros (?[??]?? Heq Hstep) "Hs". simplify_eq/=. iModIntro.
    inv/= Hstep.
    all: revert select (_ ≡ _); rewrite {1}Heq; try by move => /spec_equiv_inv.
    move => /spec_equiv_inv //= [? Heq2]. simplify_eq/=.
    iModIntro. iApply (bi_mono1_intro with "Hsim"). iIntros (?) "Hσ".
    iSplit!. iIntros "Htgt". iApply "Hσ". by iApply "Htgt".
  Qed.

  Lemma sim_src_TVis k Π Φ e os :
    (∀ σ, σ ⤇ₛ (λ Π, SRC k tt @ ? os [{ Π }] {{ Φ }}) -∗ Π (Some e) σ) -∗
    SRC (Spec.bind (TVis e) k) @ ? os [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_src_expr_step. iIntros (?[??]?) "?". simplify_eq/=. iModIntro.
    iExists _, _. iSplit. { iPureIntro. by econs. }
    iIntros ([??] ?) "!> HΦ". simplify_eq.
    iApply "Hsim". iIntros (?) "?". by iApply ("HΦ" with "[//] [$]").
  Qed.

  Lemma sim_tgt_TGet k Π Φ s :
    (▷ₒ TGT (k s) @ s [{ Π }] {{ Φ }}) -∗
    TGT (Spec.bind TGet k) @ s [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_tgt_expr_step_None. iIntros (?[??]?? Heq Hstep ?). simplify_eq/=. iModIntro.
    inv/= Hstep.
    all: revert select (_ ≡ _); rewrite {1}Heq; try by move => /spec_equiv_inv.
    move => /spec_equiv_inv //= Heq2. simplify_eq/=.
    iModIntro. rewrite Heq2. iSplit!. by iFrame.
  Qed.

  Lemma sim_src_TGet k Π Φ s :
    SRC (k s) @ s [{ Π }] {{ Φ }} -∗
    SRC (Spec.bind TGet k) @ s [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_src_expr_step_None. iIntros (?[??]? ?). simplify_eq/=. iModIntro.
    iExists _. iSplit. { iPureIntro. by econs. }
    iIntros ([??] ?) "!>". simplify_eq. iSplit!. by iFrame.
  Qed.

  Lemma sim_tgt_TPut k Π Φ s s' :
    (▷ₒ TGT (k tt) @ s' [{ Π }] {{ Φ }}) -∗
    TGT (Spec.bind (TPut s') k) @ s [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_tgt_expr_step_None. iIntros (?[??]?? Heq Hstep ?). simplify_eq/=. iModIntro.
    inv/= Hstep.
    all: revert select (_ ≡ _); rewrite {1}Heq; try by move => /spec_equiv_inv.
    move => /spec_equiv_inv //= [? Heq2]. simplify_eq/=.
    iModIntro. rewrite Heq2. iSplit!. by iFrame.
  Qed.

  Lemma sim_src_TPut k Π Φ s s' :
    SRC (k tt) @ s' [{ Π }] {{ Φ }} -∗
    SRC (Spec.bind (TPut s') k) @ s [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_src_expr_step_None. iIntros (?[??]? ?). simplify_eq/=. iModIntro.
    iExists _. iSplit. { iPureIntro. by econs. }
    iIntros ([??] ?) "!>". simplify_eq. iSplit!. by iFrame.
  Qed.

  Lemma sim_tgt_TAll {T} x k Π Φ os :
    (▷ₒ TGT (k x) @ ? os [{ Π }] {{ Φ }}) -∗
    TGT (Spec.bind (TAll T) k) @ ? os [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_tgt_expr_step_None. iIntros (?[??]?? Heq Hstep) "Hs". simplify_eq/=. iModIntro.
    inv/= Hstep.
    all: revert select (_ ≡ _); rewrite {1}Heq; try by move => /spec_equiv_inv.
    move => /spec_equiv_inv //= [? Heq2]. simplify_eq/=.
    iModIntro. rewrite Heq2. iSplit!. iFrame.
  Qed.

  Lemma sim_src_TAll {T} k Π Φ os :
    (∀ x, SRC (k x) @ ? os [{ Π }] {{ Φ }}) -∗
    SRC (Spec.bind (TAll T) k) @ ? os [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_src_expr_step_None. iIntros (?[??]?) "?". simplify_eq/=. iModIntro.
    iExists _. iSplit. { iPureIntro. by econs. }
    iIntros ([??] [??]) "!>". simplify_eq. iSplit!. iFrame. iApply "Hsim".
  Qed.

  Lemma sim_tgt_TExist {T} k Π Φ os :
    (∀ x, ▷ₒ TGT (k x) @ ? os [{ Π }] {{ Φ }}) -∗
    TGT (Spec.bind (TExist T) k) @ ? os [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_tgt_expr_step_None. iIntros (?[??]?? Heq Hstep) "Hs". simplify_eq/=. iModIntro.
    inv/= Hstep.
    all: revert select (_ ≡ _); rewrite {1}Heq; try by move => /spec_equiv_inv.
    move => /spec_equiv_inv //= [? Heq2]. simplify_eq/=. iSpecialize ("Hsim" $! _).
    iModIntro. rewrite Heq2. iSplit!. iFrame.
  Qed.

  Lemma sim_src_TExist {T} x k Π Φ os :
    SRC (k x) @ ? os [{ Π }] {{ Φ }} -∗
    SRC (Spec.bind (TExist T) k) @ ? os [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_src_expr_step_None. iIntros (?[??]?) "?". simplify_eq/=. iModIntro.
    iExists _. iSplit. { iPureIntro. by econs. }
    iIntros ([??] ?) "!>". simplify_eq. iSplit!. iFrame.
  Qed.

  (* TODO: Can these proofs be derived from the proofs before? *)
  Lemma sim_tgt_TNb T (k : T → _) Π Φ os :
    ⊢ TGT (Spec.bind TNb k) @ ? os [{ Π }] {{ Φ }}.
  Proof.
    rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_tgt_expr_step_None. iIntros (?[??]?? Heq Hstep) "Hs". simplify_eq/=. iModIntro.
    inv/= Hstep.
    all: revert select (_ ≡ _); rewrite {1}Heq; try by move => /spec_equiv_inv.
    move => /spec_equiv_inv //= [? Heq2]. simplify_eq/=. destruct_all void.
  Qed.

  Lemma sim_tgt_TNb_end Π Φ os :
    ⊢ TGT TNb @ ? os [{ Π }] {{ Φ }}.
  Proof.
    iApply sim_tgt_expr_step_None. iIntros (?[??]?? Heq Hstep) "Hs". simplify_eq/=. iModIntro.
    inv/= Hstep.
    all: revert select (_ ≡ _); rewrite {1}Heq; try by move => /spec_equiv_inv.
    move => /spec_equiv_inv //= [? Heq2]. simplify_eq/=. destruct_all void.
  Qed.

  Lemma sim_src_TUb T (k : T → _) Π Φ os :
    ⊢ SRC (Spec.bind TUb k) @ ? os [{ Π }] {{ Φ }}.
  Proof.
    rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_src_expr_step_None. iIntros (?[??]?) "?". simplify_eq/=. iModIntro.
    iExists _. iSplit. { iPureIntro. by econs. }
    iIntros ([??] [??]) "!>". destruct_all void.
  Qed.

  Lemma sim_src_TUb_end Π Φ os :
    ⊢ SRC TUb @ ? os [{ Π }] {{ Φ }}.
  Proof.
    iApply sim_src_expr_step_None. iIntros (?[??]?) "?". simplify_eq/=. iModIntro.
    iExists _. iSplit. { iPureIntro. by econs. }
    iIntros ([??] [??]) "!>". destruct_all void.
  Qed.

  Lemma sim_tgt_TAssume k Π Φ (P : Prop) os :
    P →
    (▷ₒ TGT (k tt) @ ? os [{ Π }] {{ Φ }}) -∗
    TGT (Spec.bind (TAssume P) k) @ ? os [{ Π }] {{ Φ }}.
  Proof.
    iIntros (?) "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_tgt_expr_step_None. iIntros (?[??]?? Heq Hstep) "Hs". simplify_eq/=. iModIntro.
    inv/= Hstep.
    all: revert select (_ ≡ _); rewrite {1}Heq; try by move => /spec_equiv_inv.
    move => /spec_equiv_inv //= [? Heq2]. simplify_eq/=.
    iModIntro. rewrite Heq2. iSplit!. iFrame.
    Unshelve. done.
  Qed.

  Lemma sim_src_TAssume k Π Φ P os :
    (⌜P⌝ -∗ SRC (k tt) @ ? os [{ Π }] {{ Φ }}) -∗
    SRC (Spec.bind (TAssume P) k) @ ? os [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_src_expr_step_None. iIntros (?[??]?) "?". simplify_eq/=. iModIntro.
    iExists _. iSplit. { iPureIntro. by econs. }
    iIntros ([??] [??]) "!>". simplify_eq. iSplit!. iFrame. by iApply "Hsim".
  Qed.

  Lemma sim_tgt_TAssert k Π Φ (P : Prop) os :
    (⌜P⌝ -∗ ▷ₒ TGT (k tt) @ ? os [{ Π }] {{ Φ }}) -∗
    TGT (Spec.bind (TAssert P) k) @ ? os [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_tgt_expr_step_None. iIntros (?[??]?? Heq Hstep) "Hs". simplify_eq/=. iModIntro.
    inv/= Hstep.
    all: revert select (_ ≡ _); rewrite {1}Heq; try by move => /spec_equiv_inv.
    move => /spec_equiv_inv //= [? Heq2]. simplify_eq/=. iSpecialize ("Hsim" with "[//]").
    iModIntro. rewrite Heq2. iSplit!. iFrame.
  Qed.

  Lemma sim_src_TAssert k Π Φ (P : Prop) os :
    P →
    SRC (k tt) @ ? os [{ Π }] {{ Φ }} -∗
    SRC (Spec.bind (TAssert P) k) @ ? os [{ Π }] {{ Φ }}.
  Proof.
    iIntros (?) "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_src_expr_step_None. iIntros (?[??]?) "?". simplify_eq/=. iModIntro.
    iExists _. iSplit. { iPureIntro. by econs. }
    iIntros ([??] ?) "!>". simplify_eq. iSplit!. iFrame.
    Unshelve. done.
  Qed.

  Lemma sim_tgt_TAssumeOpt {T} o (x : T) k Π Φ os :
    o = Some x →
    TGT k x @ ? os [{ Π }] {{ Φ }} -∗
    TGT (Spec.bind (TAssumeOpt o) k) @ ? os [{ Π }] {{ Φ }}.
  Proof. iIntros (->) "Hsim". simpl. by rewrite unfold_bind/=. Qed.

  Lemma sim_src_TAssumeOpt {T} (o : option T) k Π Φ os :
    (∀ x, ⌜o = Some x⌝ -∗ SRC k x @ ? os [{ Π }] {{ Φ }}) -∗
    SRC (Spec.bind (TAssumeOpt o) k) @ ? os [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim".
    destruct o => /=.
    - rewrite unfold_bind/=. by iApply "Hsim".
    - iApply sim_src_TUb.
  Qed.

  Lemma sim_tgt_TAssertOpt {T} (o : option T) k Π Φ os :
    (∀ x, ⌜o = Some x⌝ -∗ TGT k x @ ? os [{ Π }] {{ Φ }}) -∗
    TGT (Spec.bind (TAssertOpt o) k) @ ? os [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim".
    destruct o => /=.
    - rewrite unfold_bind/=. by iApply "Hsim".
    - iApply sim_tgt_TNb.
  Qed.

  Lemma sim_src_TAssertOpt {T} o (x : T) k Π Φ os :
    o = Some x →
    SRC k x @ ? os [{ Π }] {{ Φ }} -∗
    SRC (Spec.bind (TAssertOpt o) k) @ ? os [{ Π }] {{ Φ }}.
  Proof. iIntros (->) "Hsim". simpl. by rewrite unfold_bind/=. Qed.
End spec.


Definition array (l : loc) (vs : list val) : gmap loc val :=
  (kmap (λ i, l +ₗ i) (map_seqZ 0 vs)).

Section array.
  Lemma array_nil l :
    array l [] = ∅.
  Proof. rewrite /array/=. apply kmap_empty. Qed.
  Lemma array_cons l v vs :
    array l (v::vs) = <[l:=v]> $ array (l +ₗ 1) vs.
  Proof.
    rewrite /array/= kmap_insert offset_loc_0. f_equal.
    apply map_eq => ?. apply option_eq => ?.
    rewrite !lookup_kmap_Some. setoid_rewrite lookup_map_seqZ_Some.
    split => -[i [? [? <-]]]; simplify_eq.
    - eexists (Z.pred i). split!; [|lia|f_equal; lia].
      unfold offset_loc. destruct l => /=. f_equal. lia.
    - eexists (Z.succ i). split!; [|lia|f_equal; lia].
      unfold offset_loc. destruct l => /=. f_equal. lia.
  Qed.

  Lemma array_app l vs1 vs2 :
    array l (vs1 ++ vs2) = array l vs1 ∪ array (l +ₗ length vs1) vs2.
  Proof.
    elim: vs1 l. { move => ?/=. by rewrite array_nil offset_loc_0 left_id_L. }
    move => v vs1 IH l /=. rewrite !array_cons -insert_union_l.
    rewrite IH. do 3 f_equal. apply loc_eq. split!. lia.
  Qed.

  Lemma array_insert l1 l2 v vs :
    l1.1 = l2.1 →
    l2.2 ≤ l1.2 < l2.2 + length vs →
    <[l1:=v]> $ array l2 vs = array l2 (<[Z.to_nat (l1.2 - l2.2):=v]>vs).
  Proof.
    move => ??. have {1} -> : l1 = l2 +ₗ Z.to_nat (l1.2 - l2.2).
    { unfold offset_loc. destruct l1, l2; simplify_eq/=. f_equal. lia. }
    rewrite /array/= map_seqZ_insert. 2: lia.
    by rewrite kmap_insert.
  Qed.

  Lemma array_lookup_None l l' vs :
    array l vs !! l' = None ↔ (l.1 = l'.1 → l'.2 < l.2 ∨ l.2 + length vs ≤ l'.2).
  Proof.
    rewrite /array.
    rewrite lookup_kmap_None.
    setoid_rewrite lookup_map_seqZ_None.
    split.
    - move => Hi Heq.
      exploit (Hi (l'.2 - l.2)). { unfold offset_loc. destruct l, l'; simplify_eq/=. f_equal. lia. }
      lia.
    - move => Hi ??. simplify_eq/=. lia.
  Qed.

  Lemma array_lookup_is_Some l l' vs :
    is_Some (array l vs !! l') ↔ l.1 = l'.1 ∧ l.2 ≤ l'.2 < l.2 + length vs.
  Proof. rewrite -not_eq_None_Some array_lookup_None. naive_solver lia. Qed.
End array.

Definition fnsUR : cmra :=
  agreeR (gmapO string (leibnizO fndef)).

Definition to_fns : gmap string fndef → fnsUR :=
  to_agree.


Class recPreGS (Σ : gFunctors) := RecPreGS {
  rec_mapsto_ghost_map_preG :> ghost_mapG Σ loc val;
  rec_alloc_ghost_map_preG :> ghost_mapG Σ prov Z;
  rec_fn_preG :> inG Σ fnsUR;
}.

Class recGS (Σ : gFunctors) := RecGS {
  rec_mapsto_ghost_mapG :> ghost_mapG Σ loc val;
  rec_alloc_ghost_mapG :> ghost_mapG Σ prov Z;
  rec_fnG :> inG Σ fnsUR;
  rec_mapsto_name : gname;
  rec_alloc_name : gname;
  rec_fn_name : gname;
}.

Definition recΣ : gFunctors :=
  #[ ghost_mapΣ loc val; ghost_mapΣ prov Z; GFunctor fnsUR ].

Global Instance subG_recΣ Σ :
  subG recΣ Σ → recPreGS Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{!recGS Σ}.

  Definition rec_mapsto_def (l : loc) (q : dfrac) (v : val) : iProp Σ :=
    ghost_map_elem rec_mapsto_name l q v.
  Local Definition rec_mapsto_aux : seal (@rec_mapsto_def).
  Proof. by eexists. Qed.
  Definition rec_mapsto := rec_mapsto_aux.(unseal).
  Local Definition rec_mapsto_unseal :
    @rec_mapsto = @rec_mapsto_def := rec_mapsto_aux.(seal_eq).

  Definition rec_mapsto_auth (h : gmap loc val) : iProp Σ :=
    ghost_map_auth rec_mapsto_name 1 h.

  Definition rec_alloc_def (l : loc) (sz : Z) : iProp Σ :=
    ⌜l.2 = 0⌝ ∗ ghost_map_elem rec_alloc_name l.1 (DfracOwn 1) sz.
  Local Definition rec_alloc_aux : seal (@rec_alloc_def).
  Proof. by eexists. Qed.
  Definition rec_alloc := rec_alloc_aux.(unseal).
  Local Definition rec_alloc_unseal :
    @rec_alloc = @rec_alloc_def := rec_alloc_aux.(seal_eq).

  Definition rec_alloc_auth (h : gset loc) : iProp Σ :=
    ∃ m,
    ⌜∀ p sz, m !! p = Some sz → sz > 0⌝ ∗
    ⌜∀ p sz, m !! p = Some sz → ∀ l', l'.1 = p → l' ∈ h ↔ 0 ≤ l'.2 < sz⌝ ∗
    ghost_map_auth rec_alloc_name 1 m.

  Definition rec_fn_auth (fns : gmap string fndef) : iProp Σ :=
    own rec_fn_name (to_fns fns).
  Definition rec_fn_mapsto_def (f : string) (fn : option fndef) : iProp Σ :=
    ∃ fns, ⌜fns !! f = fn⌝ ∗ rec_fn_auth fns.
  Local Definition rec_fn_mapsto_aux : seal (@rec_fn_mapsto_def).
  Proof. by eexists. Qed.
  Definition rec_fn_mapsto := rec_fn_mapsto_aux.(unseal).
  Local Definition rec_fn_mapsto_unseal :
    @rec_fn_mapsto = @rec_fn_mapsto_def := rec_fn_mapsto_aux.(seal_eq).

  Definition rec_state_interp (σ : rec_state) (os : option heap_state) : iProp Σ :=
    rec_fn_auth (st_fns σ) ∗
    if os is Some h then
      ⌜st_heap σ = h⌝
    else
      rec_mapsto_auth (h_heap (st_heap σ)) ∗ rec_alloc_auth (dom (h_heap (st_heap σ))).
End definitions.

Notation "l ↦ v" := (rec_mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.
Notation "f ↪ fn" := (rec_fn_mapsto f fn)
  (at level 20, format "f  ↪  fn") : bi_scope.

Local Ltac unseal := rewrite
  ?rec_mapsto_unseal /rec_mapsto_def /rec_mapsto_auth
  ?rec_alloc_unseal /rec_alloc_def /rec_alloc_auth
  ?rec_fn_mapsto_unseal /rec_fn_mapsto_def /rec_fn_auth.

Section lemmas.
  Context `{!recGS Σ}.

  (** mapsto ghost state  *)
  Lemma rec_mapsto_lookup h l v :
    rec_mapsto_auth h -∗ l ↦ v -∗ ⌜h !! l = Some v⌝.
  Proof. unseal. apply ghost_map_lookup. Qed.

  Lemma rec_mapsto_update h l v v' :
    rec_mapsto_auth h -∗ l ↦ v ==∗ rec_mapsto_auth (alter (λ _, v') l h) ∗ l ↦ v'.
  Proof.
    iIntros "Hh Hl".
    iDestruct (rec_mapsto_lookup with "Hh Hl") as %?.
    unseal.
    iMod (ghost_map_update with "Hh Hl") as "[? $]".
    have -> : (<[l:=v']> h) = (alter (λ _ : val, v') l h); [|done].
    apply partial_alter_ext => ??. by simplify_map_eq.
  Qed.

  Lemma rec_mapsto_alloc_big h' h :
    h' ##ₘ h →
    rec_mapsto_auth h ==∗
    rec_mapsto_auth (h' ∪ h) ∗ [∗ map] l↦v∈h', l ↦ v.
  Proof. unseal. apply ghost_map_insert_big. Qed.

  Local Transparent heap_alloc_h.
  Lemma rec_mapsto_alloc h l sz :
    heap_is_fresh h l →
    rec_mapsto_auth (h_heap h) ==∗
    rec_mapsto_auth (h_heap (heap_alloc h l sz)) ∗ [∗ list] o∈seqZ 0 sz, (l +ₗ o) ↦ 0.
  Proof.
    iIntros (Ha) "Hh".
    iMod (rec_mapsto_alloc_big with "Hh") as "[$ ?]".
    { apply map_disjoint_list_to_map_l. apply Forall_forall => -[??] /= /elem_of_list_fmap[?[??]].
      simplify_eq. apply eq_None_not_Some => /heap_wf. unfold heap_is_fresh in *. naive_solver. }
    rewrite big_sepM_list_to_map. 2: {
      apply NoDup_alt => ???. do 2 setoid_rewrite list_lookup_fmap_Some.
      setoid_rewrite lookup_seqZ => ??. naive_solver lia. }
    by rewrite big_sepL_fmap.
  Qed.
  Local Opaque heap_alloc_h.

  Lemma rec_mapsto_alloc_list h ls h' szs :
    heap_alloc_list szs ls h h' →
    rec_mapsto_auth (h_heap h) ==∗
    rec_mapsto_auth (h_heap h') ∗ ([∗ list] l;n∈ls; szs, [∗ list] o∈seqZ 0 n, (l +ₗ o) ↦ 0).
  Proof.
    iIntros (Ha) "Hh".
    iInduction (szs) as [|sz szs] "IH" forall (ls h h' Ha); destruct!/=. { by iFrame. }
    iMod (rec_mapsto_alloc with "Hh") as "[Hh $]"; [done|].
    iApply ("IH" with "[//] Hh").
  Qed.

  Lemma seqZ_succ m i :
    0 ≤ i →
    seqZ m (Z.succ i) = seqZ m i ++ [m + i].
  Proof. intros ?. by rewrite -(Z2Nat.id i) // -Nat2Z.inj_succ seqZ_S. Qed.

  Lemma rec_mapsto_free h l sz :
    heap_range h l sz →
    0 ≤ sz →
    rec_mapsto_auth (h_heap h) -∗
    ([∗ list] o∈seqZ 0 sz, ∃ v, (l +ₗ o) ↦ v) ==∗
    rec_mapsto_auth (h_heap (heap_free h l)).
  Proof.
    iIntros (Hr Hsz) "Ha Hl".
    iAssert (∃ vs, ⌜sz = length vs⌝ ∗ [∗ map] l↦v∈array l vs, l↦v)%I with "[Hl]" as (vs ?) "Hl".
    { clear Hr.
      iInduction sz as [|sz|sz] "IH" using (Z.succ_pred_induction 0) forall (Hsz).
      { iExists []. iSplit!. } 2: { lia. }
      rewrite seqZ_succ // big_sepL_app /=. iDestruct "Hl" as "[Hl [[%v Hv] _]]". rewrite Z.add_0_l.
      iDestruct ("IH" with "[//] [$]") as (vs ?) "?". subst.
      iExists (vs ++ [v]). iSplit; [iPureIntro; rewrite app_length /=; lia|].
      rewrite array_app array_cons array_nil. iApply (big_sepM_union_2 with "[$]").
      by iApply (big_sepM_insert_2 with "[Hv]").
    }
    unseal.
    iMod (ghost_map_delete_big with "Ha [$]") => /=.
    have -> : (h_heap h ∖ array l vs = (filter (λ '(l', _), l'.1 ≠ l.1) (h_heap h))); [|done].
    apply map_eq => i. apply option_eq => v.
    rewrite map_filter_lookup_Some lookup_difference_Some.
    rewrite array_lookup_None.
    unfold heap_range in Hr. split; [|naive_solver lia].
    move => [Hh ?]. split!. move => ?. have := Hr i. rewrite Hh /is_Some. naive_solver lia.
  Qed.

  (** alloc ghost state  *)
  Lemma rec_alloc_fake h :
    rec_alloc_auth ∅ -∗ rec_alloc_auth h.
  Proof.
    unseal. iDestruct 1 as (m Hsz Hl) "?".
    have -> : m = ∅. {
      apply map_empty => i. apply eq_None_ne_Some_2 => ??.
      have := Hl _ _ ltac:(done) (i, 0). set_unfold. naive_solver lia. }
    iExists ∅. iFrame. iPureIntro. naive_solver.
  Qed.

  Local Transparent heap_alloc_h.
  Lemma rec_alloc_alloc h l sz :
    heap_is_fresh h l →
    0 < sz →
    rec_alloc_auth (dom (h_heap h)) ==∗
    rec_alloc_auth (dom (h_heap (heap_alloc h l sz))) ∗ rec_alloc l sz.
  Proof.
    iIntros ([Hn Hl0] ?) "Ha". unseal.
    iDestruct "Ha" as (m Hsz Hin) "Ha".
    iMod (ghost_map_insert l.1 sz with "Ha") as "[Ha ?]". {
      apply eq_None_not_Some => -[??].
      have [//|_ Hdom]:= Hin _ _ ltac:(done) (l.1, 0).
      apply Hn. apply (heap_wf _ (l.1, 0)). apply elem_of_dom. naive_solver lia.
    }
    iModIntro. iFrame. iSplit!; [..|done].
    - move => ?? /lookup_insert_Some. naive_solver lia.
    - move => ?? /lookup_insert_Some[[??]|[??]] l' ?; simplify_eq.
      + rewrite dom_union_L elem_of_union dom_list_to_map_L.
        set_unfold. setoid_rewrite elem_of_seq.
        split; move => ?; destruct!/=.
        * lia.
        * revert select (_ ∈ _) => /elem_of_dom/heap_wf. congruence.
        * left.  eexists (l +ₗ l'.2, _) => /=. split. { apply loc_eq. split!. lia. }
          eexists _. split; [done|]. eexists (Z.to_nat l'.2). lia.
      + rewrite dom_union_L elem_of_union dom_list_to_map_L.
        split; move => ?; destruct!/=. 1: set_solver. all: naive_solver lia.
  Qed.
  Local Opaque heap_alloc_h.

  Lemma rec_alloc_alloc_list szs h h' ls :
    heap_alloc_list szs ls h h' →
    Forall (λ sz, 0 < sz) szs →
    rec_alloc_auth (dom (h_heap h)) ==∗
    rec_alloc_auth (dom (h_heap h')) ∗ [∗ list] l;sz∈ls;szs, rec_alloc l sz.
  Proof.
    iIntros (Ha Hall) "Ha".
    iInduction (szs) as [|sz szs] "IH" forall (ls h h' Ha Hall); destruct!/=. { by iFrame. }
    decompose_Forall.
    iMod (rec_alloc_alloc with "Ha") as "[Ha $]"; [done..|].
    iApply ("IH" with "[//] [//] Ha").
  Qed.

  Lemma rec_alloc_range h l sz :
    rec_alloc_auth (dom (h_heap h)) -∗
    rec_alloc l sz -∗
    ⌜heap_range h l sz⌝.
  Proof.
    unseal. iDestruct 1 as (p Hsz Hl) "?". iIntros "[% ?]".
    iDestruct (ghost_map_lookup with "[$] [$]") as %?.
    iPureIntro. setoid_rewrite elem_of_dom in Hl.
    move => ??. rewrite Hl //. lia.
  Qed.

  Lemma rec_alloc_size h l sz :
    rec_alloc_auth (dom (h_heap h)) -∗
    rec_alloc l sz -∗
    ⌜0 < sz⌝.
    unseal. iDestruct 1 as (p Hsz Hl) "?". iIntros "[% ?]".
    iDestruct (ghost_map_lookup with "[$] [$]") as %?.
    iPureIntro. naive_solver lia.
  Qed.

  Lemma rec_alloc_free h l sz :
    rec_alloc_auth (dom (h_heap h)) -∗
    rec_alloc l sz ==∗
    rec_alloc_auth (dom (h_heap (heap_free h l))).
  Proof.
    unseal. iDestruct 1 as (p Hsz Hl) "?". iIntros "[% ?]".
    iMod (ghost_map_delete with "[$] [$]"). iModIntro. iExists _. iFrame.
    iPureIntro. split => ?? /lookup_delete_Some. 1: naive_solver.
    move => [??] ?? /=. rewrite -Hl //.
    rewrite !elem_of_dom map_filter_lookup_true //. naive_solver.
  Qed.

  Lemma rec_alloc_free_list h ls szs :
    rec_mapsto_auth (h_heap h) -∗
    rec_alloc_auth (dom (h_heap h)) -∗
    ([∗ list] l;sz ∈ ls;szs, rec_alloc l sz) -∗
    ([∗ list] l;n ∈ ls;szs, [∗ list] o ∈ seqZ 0 n, ∃ v0 : val, (l +ₗ o) ↦ v0) ==∗
    ∃ h', ⌜heap_free_list (zip ls szs) h h'⌝ ∗ rec_mapsto_auth (h_heap h') ∗ rec_alloc_auth (dom (h_heap h')).
  Proof.
    iIntros "Hh Ha Has Hls".
    iInduction (szs) as [|sz szs] "IH" forall (h ls).
    { iModIntro. iDestruct (big_sepL2_nil_inv_r with "Has") as %?. simplify_eq/=. iSplit!. iFrame. }
    iDestruct (big_sepL2_cons_inv_r with "Has") as (???) "[??]".
    iDestruct (big_sepL2_cons_inv_r with "Hls") as (???) "[??]". simplify_eq/=.
    iDestruct (rec_alloc_range with "[$] [$]") as %?.
    iDestruct (rec_alloc_size with "[$] [$]") as %?.
    iMod (rec_mapsto_free with "Hh [$]") as "Hh"; [done|lia|].
    iMod (rec_alloc_free with "Ha [$]") as "Ha".
    iMod ("IH" with "Hh Ha [$] [$]") as (??) "[??]". iModIntro. iSplit!; [done|]. iFrame.
  Qed.

  (** fn ghost state  *)
  Global Instance rec_fn_auth_pers fns : Persistent (rec_fn_auth fns).
  Proof. unseal. apply _. Qed.

  Global Instance rec_fn_mapsto_pers f fn : Persistent (f ↪ fn).
  Proof. unseal. apply _. Qed.

  Lemma rec_fn_auth_agree fns1 fns2 :
    rec_fn_auth fns1 -∗ rec_fn_auth fns2 -∗ ⌜fns1 = fns2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    move: Hvalid => /to_agree_op_valid.
    by fold_leibniz.
  Qed.

  Lemma rec_fn_intro f fn fns :
    fns !! f = fn → rec_fn_auth fns -∗ f ↪ fn.
  Proof. unseal. iIntros (?) "Htbl". iExists _. by iFrame. Qed.

  Lemma rec_fn_lookup f fn fns :
    rec_fn_auth fns -∗ f ↪ fn -∗ ⌜fns !! f = fn⌝.
  Proof.
    unseal. iIntros "Htbl Hf".
    iDestruct "Hf" as (fns2 ?) "Hf".
    by iDestruct (rec_fn_auth_agree with "Htbl Hf") as %->.
  Qed.

End lemmas.

Lemma recgs_alloc `{!recPreGS Σ} fns :
  ⊢ |==> ∃ H : recGS Σ, rec_mapsto_auth ∅ ∗ rec_alloc_auth ∅ ∗ rec_fn_auth fns.
Proof.
  iMod (own_alloc (to_fns fns)) as (γf) "#Hfns" => //.
  iMod (ghost_map_alloc (V:=val)) as (γh) "[??]".
  iMod (ghost_map_alloc (V:=Z)) as (γa) "[??]".

  iModIntro. iExists (RecGS _ _ _ _ γh γa γf). iFrame "#∗".
  iExists ∅. iFrame. iPureIntro; split!.
Qed.

Program Canonical Structure rec_mod_lang {Σ} `{!recGS Σ} := {|
  mexpr := expr;
  mectx := list expr_ectx;
  mstate := heap_state;
  mfill := expr_fill;
  mcomp_ectx := flip app;
  mtrans := rec_trans;
  mexpr_rel σ e := st_expr σ = e;
  mstate_interp := rec_state_interp;
|}.
Next Obligation. move => ?????/=. by rewrite expr_fill_app. Qed.

Section lifting.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Lemma sim_tgt_rec_Waiting fns Π Φ (b : bool) h :
    rec_fn_auth fns -∗
    ((∀ f fn vs h', ⌜fns !! f = Some fn⌝ -∗
       ▷ₒ Π (Some (Incoming, ERCall f vs h')) (λ P,
         ∀ σ,
           (rec_mapsto_auth (h_heap h') -∗
            rec_alloc_auth (dom (h_heap h')) -∗
            σ ⤇ₜ λ Π', TGT ReturnExt b (Call f (Val <$> vs)) [{ Π' }] {{ Φ }}) -∗
           P σ)) ∧
      ∀ v h', ⌜b⌝ -∗
       ▷ₒ Π (Some (Incoming, ERReturn v h')) (λ P, ∀ σ,
           (rec_mapsto_auth (h_heap h') -∗
            rec_alloc_auth (dom (h_heap h')) -∗
            σ ⤇ₜ λ Π', TGT Val v [{ Π' }] {{ Φ }}) -∗
           P σ)) -∗
    TGT Waiting b @ h [{ Π }] {{ Φ }}.
  Proof.
    iIntros "#Hfns HΦ".
    iApply sim_tgt_expr_bi_mono.
    iApply sim_tgt_expr_step => /=. iIntros (? [e h0 fns0] ?? ? Hp) "[Hfns' %]". simplify_eq/=.
    iDestruct (rec_fn_auth_agree with "Hfns' Hfns") as %?. subst.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    - iDestruct "HΦ" as "[HΦ _]". iDestruct ("HΦ" with "[//]") as "HΦ".
      do 2 iModIntro. iApply (bi_mono1_intro with "HΦ"). iIntros (?) "Htgt".
      iSplit!. iIntros "Hc". iApply "Htgt". iIntros "??".
      iApply "Hc"; [done|]. iFrame.
    - iDestruct "HΦ" as "[_ HΦ]". iDestruct ("HΦ" with "[//]") as "HΦ".
      do 2 iModIntro. iApply (bi_mono1_intro with "HΦ"). iIntros (?) "Htgt".
      iSplit!. iIntros "Hc". iApply "Htgt". iIntros "??".
      iApply "Hc"; [done|]. iFrame.
  Qed.

  Lemma sim_tgt_rec_ReturnExt v Π Φ (b : bool) :
    (∀ h,
      rec_mapsto_auth (h_heap h) -∗
      rec_alloc_auth (dom (h_heap h)) -∗
     ▷ₒ Π (Some (Outgoing, ERReturn v h)) (λ P,
         ∀ σ,
           (σ ⤇ₜ λ Π', TGT Waiting b @ h [{ Π' }] {{ Φ }}) -∗
           P σ)) -∗
    TGT ReturnExt b (Val v) [{ Π }] {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply sim_tgt_expr_bi_mono.
    iApply sim_tgt_expr_step => /=. iIntros (? [e h0 fns0] ?? ? Hp) "[Hfns' [Hh Ha]]". simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iSpecialize ("HΦ" $! _ with "[$] [$]"). do 2 iModIntro. iApply (bi_mono1_intro with "HΦ").
    iIntros (?) "Htgt". iSplit!. iIntros "Hc". iApply "Htgt".
    iApply "Hc"; [done|]. by iFrame.
  Qed.

  Lemma sim_tgt_rec_Call_internal f fn es Π Φ vs `{!AsVals es vs None} :
    length vs = length (fd_args fn) →
    f ↪ Some fn -∗
    (▷ₒ TGT AllocA fn.(fd_vars) (subst_l fn.(fd_args) vs fn.(fd_body)) [{ Π }] {{ Φ }}) -∗
    TGT Call f es [{ Π }] {{ Φ }}.
  Proof.
    destruct AsVals0. iIntros (?) "Hfn HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e h fns] ?? ? Hp) "[Hfns [Hh Ha]]". simplify_eq/=.
    iDestruct (rec_fn_lookup with "[$] [$]") as %?.
    rewrite right_id_L in Hp.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; try naive_solver.
      move => /= ??? e' [_ Heq]. by apply: list_expr_val_inv. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    do 2 iModIntro. iExists None, _, _. iSplit!. iFrame.
  Qed.

  Lemma sim_tgt_rec_Call_external f es Π Φ vs `{!AsVals es vs None} :
    f ↪ None -∗
    (∀ h,
      rec_mapsto_auth (h_heap h) -∗
      rec_alloc_auth (dom (h_heap h)) -∗
     ▷ₒ Π (Some (Outgoing, ERCall f vs h)) (λ P,
         ∀ σ,
           (σ ⤇ₜ λ Π', TGT Waiting true @ h [{ Π' }] {{ Φ }}) -∗
           P σ)) -∗
    TGT Call f es [{ Π }] {{ Φ }}.
  Proof.
    destruct AsVals0. iIntros "Hfn HΦ".
    iApply sim_tgt_expr_bi_mono.
    iApply sim_tgt_expr_step => /=. iIntros (? [e h0 fns0] ?? ? Hp) "[Hfns' [Hh Ha]]". simplify_eq/=.
    iDestruct (rec_fn_lookup with "[$] [$]") as %?.
    rewrite right_id_L in Hp.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; try naive_solver.
      move => /= ??? e' [_ Heq]. by apply: list_expr_val_inv. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iSpecialize ("HΦ" $! _ with "[$] [$]"). do 2 iModIntro. iApply (bi_mono1_intro with "HΦ").
    iIntros (?) "Htgt". iSplit!. iIntros "Hc". iApply "Htgt".
    iApply "Hc"; [done|]. by iFrame.
  Qed.

  Lemma sim_tgt_rec_BinOp Π Φ v1 v2 v3 op :
    eval_binop op v1 v2 = Some v3 →
    (▷ₒ Φ (Val v3) None Π) -∗
    TGT BinOp (Val v1) op (Val v2) [{ Π }] {{ Φ }}.
  Proof.
    iIntros (Hop) "HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e' h fns] ?? ? Hp) "[Hfns [Hh Ha]]". simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    do 2 iModIntro. iExists None, _, _. iSplit!. iFrame.
    by iApply sim_tgt_expr_stop2.
  Qed.

  Lemma sim_tgt_rec_Load Π Φ l v :
    l ↦ v -∗
    (l ↦ v -∗ ▷ₒ Φ (Val v) None Π) -∗
    TGT Load (Val (ValLoc l)) [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e' h fns] ???  Hp) "[Hfns [Hh Ha]]". simplify_eq/=.
    iDestruct (rec_mapsto_lookup with "[$] [$]") as %?.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iSpecialize ("HΦ" with "[$]").
    do 2 iModIntro. iExists None, _, _. iSplit!.
    iFrame. by iApply sim_tgt_expr_stop2.
  Qed.

  Lemma sim_tgt_rec_Store Π Φ l v v' :
    l ↦ v -∗
    (l ↦ v' -∗ ▷ₒ Φ (Val v') None Π) -∗
    TGT Store (Val (ValLoc l)) (Val v') [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e' h fns] ?? ? Hp) "[Hfns [Hh Ha]]". simplify_eq/=.
    iDestruct (rec_mapsto_lookup with "[$] [$]") as %?.
    iMod (rec_mapsto_update with "[$] [$]") as "[??]".
    iSpecialize ("HΦ" with "[$]").
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    do 2 iModIntro. iExists None, _, _. iSplit!. { by eexists. }
    iFrame => /=. rewrite dom_alter_L. iFrame. by iApply sim_tgt_expr_stop2.
  Qed.

  Lemma sim_tgt_rec_AllocA e Π Φ vs :
    Forall (λ z, 0 < z) vs.*2 →
    (∀ ls, ([∗ list] l;n∈ls; vs.*2, [∗ list] o∈seqZ 0 n, (l +ₗ o) ↦ 0) -∗
     ▷ₒ TGT subst_l vs.*1 (ValLoc <$> ls) e [{ Π }] {{ e', os', Π',
     ∃ v, ⌜e' = Val v⌝ ∗ ⌜os' = None⌝ ∗ ([∗ list] l;n∈ls; vs.*2, [∗ list] o∈seqZ 0 n, ∃ v, (l +ₗ o) ↦ v) ∗ Φ e' None Π' }}) -∗
    TGT AllocA vs e [{ Π }] {{ Φ }}.
  Proof.
    iIntros (Hall) "HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e' h fns] ?? ? Hp) "[Hfns [Hh Ha]]". simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iMod (rec_mapsto_alloc_list with "Hh") as "[Hh ?]"; [done|].
    iMod (rec_alloc_alloc_list with "Ha") as "[Ha Has]"; [done..|].
    iSpecialize ("HΦ" with "[$]").
    do 2 iModIntro. iExists None, _, _. iSplit!. iFrame => /=.
    iApply (sim_tgt_expr_bind [FreeACtx _] _ with "[-]") => /=.
    iApply (sim_tgt_expr_wand with "HΦ") => /=.
    iIntros (? ? ?) "[% [% [% [Hl HΦ]]]]" => /=. simplify_eq/=.

    iApply sim_tgt_expr_step_None => /=. iIntros (? [e' h'' fns'] ?? ? Hp') "[Hfns [Hh Ha]]". simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iMod (rec_alloc_free_list with "Hh Ha [$] [$]") as (??) "[??]".
    do 2 iModIntro. iExists None, _, _. iSplit!; [done|]. iFrame => /=.
    by iApply sim_tgt_expr_stop2.
  Qed.

  Lemma sim_tgt_rec_LetE Π Φ s v e :
    (▷ₒ TGT (subst s v e) [{ Π }] {{ Φ }}) -∗
    TGT LetE s (Val v) e [{ Π }] {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e' h fns] ?? ? Hp) "[Hfns [Hh Ha]]". simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    do 2 iModIntro. iExists None, _, _. iSplit!. iFrame.
  Qed.

  Lemma sim_tgt_rec_If Π Φ (b : bool) e1 e2 :
    (▷ₒ TGT (if b then e1 else e2) [{ Π }] {{ Φ }}) -∗
    TGT If (Val (ValBool b)) e1 e2 [{ Π }] {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e' h fns] ?? ? Hp) "[Hfns [Hh Ha]]". simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    do 2 iModIntro. iExists None, _, _. iSplit!. iFrame.
  Qed.

End lifting.

Section memmove.
  Context `{!dimsumGS Σ} `{!recGS Σ}.


  (* TODO: create a version of the target triple where the Π stays unchanged *)
  Lemma sim_memcpy Π Φ d d' s' s n o hvss hvsd :
    n = Z.of_nat (length hvss) →
    length hvss = length hvsd →
    o = 1 ∨ o = -1 →
    d' = (if bool_decide (o = 1) then d else d +ₗ (- n + 1)) →
    s' = (if bool_decide (o = 1) then s else s +ₗ (- n + 1)) →
    (if bool_decide (o = 1) then d.1 = s.1 → d.2 ≤ s.2 else d.1 = s.1 → s.2 ≤ d.2) →
    "memcpy" ↪ Some memcpy_rec -∗
    ([∗ map] l↦v∈array s' hvss ∪ array d' hvsd, l ↦ v) -∗
    (([∗ map] l↦v∈array d' hvss ∪ array s' hvss, l ↦ v) -∗
     Φ (Val 0) None Π) -∗
    TGT Call "memcpy" [Val (ValLoc d); Val $ ValLoc s; Val $ ValNum n; Val $ ValNum o] [{ Π }] {{ Φ }}.
  Proof.
    iIntros (Hn Hlen Ho Hd' Hs' Hle) "#Hf Hm HΦ".
    iApply sim_tgt_expr_ctx. iIntros "#?".
    iRevert (hvss hvsd d d' s s' n Φ Hn Hlen Hd' Hs' Hle) "Hm HΦ".
    iApply ord_loeb; [done|].
    iIntros "!> #IH" (hvss hvsd d d' s s' n Φ Hn Hlen Hd' Hs' Hle) "Hm HΦ". simplify_eq.
    iApply (sim_tgt_rec_Call_internal with "Hf"); [done|]. iModIntro => /=.
    iApply sim_tgt_rec_AllocA; [econs|] => /=. iIntros (?) "?". destruct ls => //. iModIntro.
    iApply (sim_tgt_expr_bind [IfCtx _ _] _ with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply sim_tgt_rec_If. iModIntro => /=. case_bool_decide (0 < _).
    2: { destruct hvss, hvsd => //. iApply sim_tgt_expr_stop2. iSplit!. iApply "HΦ".
         by rewrite /array !kmap_empty. }
    iApply (sim_tgt_expr_bind [LetECtx _ _] with "[-]") => /=.
    iApply (sim_tgt_expr_bind [StoreRCtx _] with "[-]") => /=.
    destruct Ho; simplify_eq; case_bool_decide => //.
    - destruct hvss as [|v hvss]; [done|] => /=.
      destruct hvsd as [|vd hvsd]; [done|] => /=.
      rewrite !array_cons.
      iDestruct (big_sepM_lookup_acc _ _ s v with "[$]") as "[Hsv Hm]". { by simplify_map_eq. }
      iApply (sim_tgt_rec_Load with "Hsv"). iIntros "Hsv !>" => /=.
      iDestruct ("Hm" with "[$]") as "Hm".
      have [? Hx]: is_Some ((<[s:=v]> (array (s +ₗ 1) hvss) ∪ <[d:=vd]> (array (d +ₗ 1) hvsd)) !! d).
      { apply lookup_union_is_Some. simplify_map_eq. naive_solver. }
      rewrite (big_sepM_delete _ _ _ _ Hx).
      iDestruct "Hm" as "[Hdv Hm]".
      iApply (sim_tgt_rec_Store with "Hdv"). iIntros "Hdv !>" => /=.
      iApply (sim_tgt_rec_LetE). iIntros "!>" => /=.
      iApply (sim_tgt_expr_bind [CallCtx _ [] _] with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply (sim_tgt_expr_bind [CallCtx _ [_] _] with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply (sim_tgt_expr_bind [CallCtx _ [_; _] _] with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      destruct (decide (d.1 = s.1 ∧ s.2 ≤ d.2 + length hvss)) as [[??]|Hn]; simplify_eq.
      + rewrite -(insert_union_l _ _ s) insert_union_r. 2: { apply array_lookup_None => /=. lia. }
        rewrite delete_union. rewrite delete_notin. 2: { apply array_lookup_None => /=. lia. }
        destruct (decide (d = s)); simplify_eq.
        * rewrite delete_insert_delete delete_insert. 2: { apply array_lookup_None => /=. lia. }
          iApply ("IH" with "[%] [%] [//] [//] [%] Hm"). { lia. } { done. } { simpl. lia. }
          iIntros "?". iSplit!. iApply ("HΦ" with "[-]").
          rewrite -insert_union_l -insert_union_r. 2: { apply array_lookup_None => /=. lia. }
          rewrite insert_insert. by iApply (big_sepM_insert_2 with "[Hdv]"); [done|].
        * rewrite delete_insert_ne // delete_insert. 2: { apply array_lookup_None => /=. lia. }
          have ?: d.2 ≠ s.2. { destruct d, s; naive_solver. }
          rewrite (array_insert s ( d+ₗ1)) //=; [|lia].
          iApply ("IH" with "[%] [%] [//] [//] [%] Hm"). { lia. } { rewrite insert_length. done. } { simpl. lia. }
          iIntros "?". iSplit!. iApply ("HΦ" with "[-]").
          rewrite -insert_union_l. iApply (big_sepM_insert_2 with "[Hdv]"); [done|].
          rewrite -insert_union_r_Some //. apply array_lookup_is_Some. split!; lia.
      + rewrite delete_union delete_insert. 2: { apply array_lookup_None => /=. lia. }
        rewrite delete_insert_ne. 2: { move => ?. subst. lia. }
        rewrite delete_notin. 2: { apply array_lookup_None => /=. lia. }
        rewrite -!insert_union_l (big_sepM_delete _ (<[s:=_]>_) s v). 2: by simplify_map_eq.
        iDestruct "Hm" as "[Hsv Hm]".
        rewrite delete_insert. 2: { apply lookup_union_None. rewrite !array_lookup_None => /=. lia. }
        iApply ("IH" with "[%] [%] [//] [//] [%] Hm"). { lia. } { done. } { simpl. lia. }
        iIntros "?". iSplit!. iApply ("HΦ" with "[-]").
        rewrite -insert_union_r. 2: { apply array_lookup_None => /=. lia. }
        iApply (big_sepM_insert_2 with "[Hdv]"); [done|].
        iApply (big_sepM_insert_2 with "[Hsv]"); [done|].
        done.
    - destruct hvss as [|v hvss _] using rev_ind; [done|] => /=.
      destruct hvsd as [|vd hvsd _] using rev_ind; [simplify_eq/=; lia|] => /=.
      rewrite app_length/=. rewrite !app_length/= in Hlen.
      have -> : (- (length hvss + 1)%nat + 1) = - Z.of_nat (length hvss) by lia.
      rewrite !array_app /= !array_cons !array_nil.
      have -> : s +ₗ - length hvss +ₗ length hvss = s by apply loc_eq; split!; lia.
      have -> : d +ₗ - length hvss +ₗ length hvss = d by apply loc_eq; split!; lia.
      have -> : d +ₗ - length hvss +ₗ length hvsd = d by apply loc_eq; split!; lia.
      rewrite -insert_union_r. 2: { apply array_lookup_None => /=. lia. }
      rewrite -insert_union_r. 2: { apply array_lookup_None => /=. lia. }
      rewrite !right_id_L.
      iDestruct (big_sepM_lookup_acc _ _ s v with "[$]") as "[Hsv Hm]". { by simplify_map_eq. }
      iApply (sim_tgt_rec_Load with "Hsv"). iIntros "Hsv !>" => /=.
      iDestruct ("Hm" with "[$]") as "Hm".
      have [? Hx]: is_Some ((<[s:=v]> (array (s +ₗ - length hvss) hvss) ∪ <[d:=vd]> (array (d +ₗ - length hvss) hvsd)) !! d).
      { apply lookup_union_is_Some. simplify_map_eq. naive_solver. }
      rewrite (big_sepM_delete _ _ _ _ Hx).
      iDestruct "Hm" as "[Hdv Hm]".
      iApply (sim_tgt_rec_Store with "Hdv"). iIntros "Hdv !>" => /=.
      iApply (sim_tgt_rec_LetE). iIntros "!>" => /=.
      iApply (sim_tgt_expr_bind [CallCtx _ [] _] with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply (sim_tgt_expr_bind [CallCtx _ [_] _] with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply (sim_tgt_expr_bind [CallCtx _ [_; _] _] with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      destruct (decide (d.1 = s.1 ∧ d.2 ≤ s.2 + length hvss)) as [[??]|Hn]; simplify_eq.
      + rewrite -(insert_union_l _ _ s) insert_union_r. 2: { apply array_lookup_None => /=. lia. }
        rewrite delete_union. rewrite delete_notin. 2: { apply array_lookup_None => /=. lia. }
        destruct (decide (d = s)); simplify_eq.
        * rewrite delete_insert_delete delete_insert. 2: { apply array_lookup_None => /=. lia. }
          iApply ("IH" with "[%] [%] [%] [%] [%] Hm"). { lia. } { lia. }
          { apply loc_eq; split!; lia. } { apply loc_eq; split!; lia. } { simpl. lia. }
          iIntros "?". iSplit!. iApply ("HΦ" with "[-]").
          rewrite -(insert_union_r _ ∅). 2: { apply array_lookup_None => /=. lia. }
          rewrite -insert_union_l right_id_L -insert_union_r. 2: { apply array_lookup_None => /=. lia. }
          rewrite insert_insert. by iApply (big_sepM_insert_2 with "[Hdv]"); [done|].
        * rewrite delete_insert_ne // delete_insert. 2: { apply array_lookup_None => /=. lia. }
          have ?: d.2 ≠ s.2. { destruct d, s; naive_solver. }
          rewrite (array_insert s (d +ₗ - length hvss)) //=; [|lia].
          iApply ("IH" with "[%] [%] [%] [%] [%] Hm"). { lia. } { rewrite insert_length. lia. }
          { apply loc_eq; split!; lia. } { apply loc_eq; split!; lia. } { simpl. lia. }
          iIntros "?". iSplit!. iApply ("HΦ" with "[-]").
          rewrite -(insert_union_r _ ∅). 2: { apply array_lookup_None => /=. lia. }
          rewrite right_id_L -insert_union_l. iApply (big_sepM_insert_2 with "[Hdv]"); [done|].
          rewrite -insert_union_r_Some //. apply array_lookup_is_Some. split!; lia.
      + rewrite delete_union delete_insert. 2: { apply array_lookup_None => /=. lia. }
        rewrite delete_insert_ne. 2: { move => ?. subst. lia. }
        rewrite delete_notin. 2: { apply array_lookup_None => /=. lia. }
        rewrite -!insert_union_l (big_sepM_delete _ (<[s:=_]>_) s v). 2: by simplify_map_eq.
        iDestruct "Hm" as "[Hsv Hm]".
        rewrite delete_insert. 2: { apply lookup_union_None. rewrite !array_lookup_None => /=. lia. }
        iApply ("IH" $! hvss hvsd with "[%] [%] [%] [%] [%] Hm"). { lia. } { lia. }
        { apply loc_eq; split!; lia. } { apply loc_eq; split!; lia. } { simpl. lia. }
        iIntros "?". iSplit!. iApply ("HΦ" with "[-]").
        rewrite -(insert_union_r _ _ d). 2: { apply array_lookup_None => /=. lia. }
        rewrite -insert_union_l right_id_L -insert_union_r. 2: { apply array_lookup_None => /=. lia. }
        iApply (big_sepM_insert_2 with "[Hdv]"); [done|].
        iApply (big_sepM_insert_2 with "[Hsv]"); [done|].
        done.
  Qed.

  Lemma sim_memmove hvss hvsd Π Φ d s n :
    n = Z.of_nat (length hvss) →
    length hvss = length hvsd →
    "memmove" ↪ Some memmove_rec -∗
    "memcpy" ↪ Some memcpy_rec -∗
    □ (∀ l1 l2 Φ,
        (∀ b, ⌜l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2)⌝ -∗ Φ (Val (ValBool b)) None Π) -∗
          TGT Call "locle" [Val (ValLoc l1); Val $ ValLoc l2] [{ Π }] {{ Φ }}) -∗
    ([∗ map] l↦v∈array s hvss ∪ array d hvsd, l ↦ v) -∗
    (([∗ map] l↦v∈array d hvss ∪ array s hvss, l ↦ v) -∗ Φ (Val 0) None Π) -∗
    TGT Call "memmove" [Val (ValLoc d); Val $ ValLoc s; Val $ ValNum n] [{ Π }] {{ Φ }}.
  Proof.
    iIntros (-> ?) "#Hmemmove #Hmemcpy #Hlocle Hs HΦ".
    iApply (sim_tgt_expr_bind []).
    iApply (sim_tgt_rec_Call_internal with "Hmemmove"); [done|]. iModIntro => /=.
    iApply sim_tgt_rec_AllocA; [econs|] => /=. iIntros (?) "?". destruct ls => //. iModIntro.
    iApply (sim_tgt_expr_bind [IfCtx _ _] with "[-]") => /=.
    iApply "Hlocle". iIntros (b Hb) => /=.
    iApply sim_tgt_rec_If. iModIntro => /=. destruct b.
    - iApply (sim_memcpy with "[//] Hs"). { done. } { done. } { by left. } { by rewrite bool_decide_true. }
      { by rewrite bool_decide_true. } {
        rewrite bool_decide_true // => /Hb Hx. symmetry in Hx. by rewrite bool_decide_eq_true in Hx.
      }
      iIntros "?". iSplit!. iApply sim_tgt_expr_stop2. iApply ("HΦ" with "[$]").
    - iApply (sim_tgt_expr_bind [CallCtx _ [] _] with "[-]") => /=.
      iApply (sim_tgt_expr_bind [BinOpRCtx _ _] with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply (sim_tgt_expr_bind [CallCtx _ [_] _] with "[-]") => /=.
      iApply (sim_tgt_expr_bind [BinOpRCtx _ _] with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply (sim_memcpy with "[//] Hs"). { done. } { done. } { by right. }
      { rewrite bool_decide_false; [|done]. rewrite offset_loc_assoc.
        have -> : (length hvss + -1 + (- length hvss + 1)) = 0 by lia.
        rewrite offset_loc_0. done. }
      { rewrite bool_decide_false; [|done]. rewrite offset_loc_assoc.
        have -> : (length hvss + -1 + (- length hvss + 1)) = 0 by lia.
        rewrite offset_loc_0. done. } {
        rewrite bool_decide_false // => /Hb Hx. symmetry in Hx. rewrite bool_decide_eq_false in Hx.
        simpl. lia.
      }
      iIntros "?". iSplit!. iApply sim_tgt_expr_stop2. iApply ("HΦ" with "[$]").
  Qed.

  Local Canonical Structure spec_mod_lang_unit.
  Lemma sim_locle s fns fns1 Φ l1 l2 Π_s :
    (* TODO: remove this by using sim_tgt_bind *)
    (∀ P, P (λ σ', σ' ≈{rec_link_trans fns1 {["locle"]} _ _}≈>ₜ Π_s) -∗ Π_s None P) →
    let Π := λ κ P, (∀ σl, (σl ⤇ₜ λ Π, TGT locle_spec [{Π}] {{_, _, _, False}}) -∗
              link_tgt_left_handler (rec_link_filter fns1 {["locle"]}) Π_s s σl κ P)%I in
    rec_fn_auth fns -∗
    "locle" ↪ None -∗
    (∀ b, ⌜l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2)⌝ -∗ Φ (Val (ValBool b)) None Π) -∗
    TGT Call "locle" [Val (ValLoc l1); Val $ ValLoc l2] [{ Π }] {{ Φ }}.
  Proof.
    iIntros (HΠ_s Π) "#Hfns #Hf HΦ".
    iApply (sim_tgt_rec_Call_external with "[$]"). iIntros (?) "?? !>". iIntros (σl) "Hσl".
    iIntros (??????). destruct!/=. case_bool_decide => //. rewrite (bool_decide_true (_ ∈ _)) //.
    iApply HΠ_s. iIntros (σ') "Hσ'".
    iApply (sim_tgt_link_right_recv with "[-]"). iApply "Hσl".
    rewrite /locle_spec unfold_forever -/locle_spec.
    rewrite /TReceive bind_bind bind_bind.
    iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>".
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply (sim_tgt_TVis with "[-]"). iIntros "!>" (?). simplify_eq/=.
    iApply HΠ_s. iIntros (?) "Hσl".
    iApply (sim_tgt_link_right with "[-]"). iApply "Hσl".
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAll with "[-]"). iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAll with "[-]"). iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TExist with "[-]"). iIntros (b) "!>".
    rewrite bind_bind. iApply (sim_tgt_TAssert with "[-]"). iIntros (?) "!>".
    iApply (sim_tgt_TVis with "[-]"). iIntros "!>" (??????). destruct!/=.
    iApply HΠ_s. iIntros (?) "Hσl".
    iApply (sim_tgt_link_left_recv with "[-]"). iApply "Hσ'".
    iApply (sim_tgt_rec_Waiting with "[$]").
    iSplit. { iIntros. iModIntro. iIntros. simplify_eq. }
    iIntros (???) "!>". iIntros (?). simplify_eq.
    iApply HΠ_s. iIntros (?) "Hσ'".
    iApply (sim_tgt_link_left with "[-]"). iApply ("Hσ'" with "[$] [$]").
    iApply (sim_tgt_expr_wand1 with "[HΦ]").
    { iApply sim_tgt_expr_stop2. by iApply "HΦ". }
    iIntros (??) "HΠ". by iApply "HΠ".
  Qed.

End memmove.

Section memmove.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Local Canonical Structure spec_mod_lang_unit.

  Lemma memmove_sim  :
    rec_state_interp (rec_init (main_prog ∪ memmove_prog ∪ memcpy_prog)) None -∗
    (MLFNone, [], rec_init (main_prog ∪ memmove_prog ∪ memcpy_prog), (locle_spec, ())) ⪯{
      rec_link_trans {["main"; "memmove"; "memcpy"]} {["locle"]} rec_trans (spec_trans rec_event ()),
      spec_trans rec_event ()} (main_spec, ()).
  Proof.
    iIntros "[#Hfns [Hh Ha]] /=". iApply (sim_tgt_handler_intro with "[-]").
    iApply (sim_tgt_link_None with "[-]").
    iIntros "!>" (??????). destruct!/=. case_match; destruct!/=.
    unfold sim_tgt_handler.
    iApply (sim_src_expr_elim None with "[] [-]"); [simpl; done..|].
    rewrite /main_spec/TReceive bind_bind.
    iApply (sim_src_TExist (_, _, _)).
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply sim_src_TVis. iIntros (?) "Hsrc". iSplit!.
    iApply bi_mono1_intro0.
    iApply (sim_tgt_handler_intro with "[-]"). iApply sim_tgt_stop.
    iApply "Hsrc".
    iApply sim_src_TAssume. iIntros (?).
    iApply sim_src_TAssume. iIntros (?). simplify_eq.
    rewrite bool_decide_true; [|done].
    iApply sim_src_expr_stop1. iIntros (?) "Hsrc". iSplit!.
    iApply bi_mono1_intro0.
    iApply (sim_tgt_handler_intro with "[-]").
    iApply (sim_tgt_link_left_recv with "[-]").
    iApply (sim_tgt_expr_elim (Some _) [] with "[] [-]"); [done| by iSplit |] => /=.
    iApply (sim_tgt_rec_Waiting with "[$]").
    iSplit; [|by iIntros].
    iIntros (???? Hin) "!>". iIntros (?). simplify_map_eq.
    iApply sim_src_stop. iSplit!. iApply bi_mono1_intro0. iIntros (?) "Htgt".
    iApply (sim_tgt_handler_intro with "[-]").
    iApply (sim_tgt_link_left with "[-]").
    iApply fupd_sim_tgt.
    iMod (rec_mapsto_alloc_big (h_heap h) with "Hh") as "[Hh _]". { apply map_disjoint_empty_r. } iModIntro.
    iApply ("Htgt" with "[Hh] [Ha]"). { by rewrite right_id_L. }
    { rewrite dom_empty_L. by iApply rec_alloc_fake. }
    iApply (sim_tgt_expr_bind [ReturnExtCtx _]).
    iApply sim_tgt_rec_Call_internal. 2: { by iApply (rec_fn_intro with "[$]"). } { done. }
    iModIntro => /=.
    iApply sim_tgt_rec_AllocA; [by econs|] => /=. iIntros (?) "Hl".
    destruct ls as [|l []] => //=. 2: by iDestruct!.
    have -> : (0%nat + 0) = 0 by []. have -> : (1%nat + 0) = 1 by []. have -> : (2%nat + 0) = 2 by [].
    iDestruct "Hl" as "[[Hl0 [Hl1 [Hl2 _]]] _]". iModIntro.
    iApply (sim_tgt_expr_bind [LetECtx _ _] with "[-]") => /=.
    iApply (sim_tgt_expr_bind [StoreLCtx _] with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply (sim_tgt_rec_Store with "Hl0"). iIntros "Hl0 !>" => /=.
    iApply sim_tgt_rec_LetE. iIntros "!>" => /=.
    iApply (sim_tgt_expr_bind [LetECtx _ _] with "[-]") => /=.
    iApply (sim_tgt_expr_bind [StoreLCtx _] with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply (sim_tgt_rec_Store with "Hl1"). iIntros "Hl1 !>" => /=.
    iApply sim_tgt_rec_LetE. iIntros "!>" => /=.
    iApply (sim_tgt_expr_bind [LetECtx _ _] with "[-]") => /=.
    iApply (sim_tgt_expr_bind [CallCtx _ [] _] with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply (sim_tgt_expr_bind [CallCtx _ [_] _] with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply (sim_tgt_expr_wand1 with "[-]"). 2: shelve.
    iApply (sim_memmove [ValNum 1; ValNum 2] [ValNum 2; ValNum 0] with "[] [] [] [Hl0 Hl1 Hl2]").
    { done. } { done. }
    { by iApply (rec_fn_intro with "[$]"). }
    { by iApply (rec_fn_intro with "[$]"). }
    { iIntros "!>" (???) "HΦ".
      iApply sim_locle. 2: done. 2: { by iApply (rec_fn_intro with "[$]"). } 2: done.
      Unshelve. all: shelve_unifiable. 2: exact tt. 2: {
        iIntros (??) "HΦ". iApply "HΦ". iIntros (?) "?".
        by iApply (sim_tgt_expr_elim None with "[] [-]"); [simpl; done..|].
      }
      iIntros (?) "HP". unfold sim_tgt_handler.
      iApply (sim_src_stop with "[-]"). iSplit!.
      iApply (bi_mono1_intro with "HP"). iIntros (?) "?".
      by iApply (sim_tgt_handler_intro with "[-]").
    }
    { rewrite !array_cons !array_nil -!insert_union_l !left_id_L.
      rewrite !offset_loc_assoc insert_insert.
      iApply (big_sepM_insert_2 with "[Hl0]"); [done|].
      iApply (big_sepM_insert_2 with "[Hl1]"); [done|].
      iApply (big_sepM_insert_2 with "[Hl2]"); [done|].
      done. }
    iIntros "Hl" => /=. rewrite !array_cons !array_nil -!insert_union_l !left_id_L.
    rewrite !offset_loc_assoc.
    rewrite (big_sepM_delete _ _ (l +ₗ 1)). 2: { by simplify_map_eq. }
    rewrite delete_insert_delete.
    rewrite delete_insert_ne //. 2: apply/loc_eq; split!; lia.
    rewrite delete_insert_ne //. 2: apply/loc_eq; split!; lia.
    rewrite delete_insert //.
    rewrite big_sepM_insert. 2: { rewrite lookup_insert_ne //. apply/loc_eq; split!; lia. }
    rewrite big_sepM_insert. 2: done.
    iDestruct "Hl" as "[Hl1 [Hl2 [Hl0 _]]]".
    iApply sim_tgt_rec_LetE. iModIntro => /=.
    iApply (sim_tgt_expr_bind [LetECtx _ _] with "[-]") => /=.
    iApply (sim_tgt_expr_bind [CallCtx _ [] _] with "[-]") => /=.
    iApply (sim_tgt_expr_bind [LoadCtx] with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply (sim_tgt_rec_Load with "Hl1"). iIntros "Hl1 !>" => /=.
    iApply (sim_tgt_rec_Call_external). { by iApply (rec_fn_intro with "[$]"). }
    iIntros (?) "Hh Ha !>". iIntros (σ') "Hlocle".
    iIntros (??????). destruct!/=. rewrite bool_decide_false//.
    iApply "Hsrc". iApply sim_src_TExist. iApply sim_src_TVis.
    iIntros (?) "Hsrc". iSplit!. iApply bi_mono1_intro0.
    iIntros (?) "Htgt". iApply (sim_tgt_handler_intro with "[-]").
    iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????). destruct!/=.
    iApply "Hsrc". iApply sim_src_TExist. iApply sim_src_TVis.
    iIntros (?) "Hsrc". iSplit!. iApply bi_mono1_intro0.
    iApply (sim_tgt_handler_intro with "[-]"). iApply sim_tgt_stop.
    iApply "Hsrc". iApply sim_src_TAssume. iIntros (?). iApply sim_src_expr_stop1.
    iIntros (?) "Hsrc". iSplit!. iApply bi_mono1_intro0. case_match; destruct!/=.
    iApply (sim_tgt_handler_intro with "[-]").
    iApply (sim_tgt_link_left_recv with "[-]").
    iApply "Htgt".
    iApply (sim_tgt_rec_Waiting with "[$]").
    iSplit; [iIntros; iModIntro; by iIntros|].
    iIntros (???) "!>". iIntros (?). simplify_eq.
    iApply sim_src_stop. iSplit!. iApply bi_mono1_intro0.
    iIntros (?) "Htgt".
    iApply (sim_tgt_handler_intro with "[-]").
    iApply (sim_tgt_link_left with "[-]").
    iApply ("Htgt" with "[$] [$]").
    iApply sim_tgt_expr_stop2 => /=.
    iApply (sim_tgt_rec_LetE with "[-]"). iIntros "!>" => /=.
    iApply (sim_tgt_expr_bind [LetECtx _ _] with "[-]") => /=.
    iApply (sim_tgt_expr_bind [CallCtx _ [] _] with "[-]") => /=.
    iApply (sim_tgt_expr_bind [LoadCtx] with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply (sim_tgt_rec_Load with "Hl2"). iIntros "Hl2 !>" => /=.
    iApply (sim_tgt_rec_Call_external). { by iApply (rec_fn_intro with "[$]"). }
    iIntros (?) "Hh Ha !>". iIntros (??????). destruct!/=. rewrite bool_decide_false//.
    iApply "Hsrc". iApply sim_src_TExist. iApply sim_src_TVis.
    iIntros (?) "Hsrc". iSplit!. iApply bi_mono1_intro0.
    iIntros (?) "Htgt". iApply (sim_tgt_handler_intro with "[-]").
    iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????). destruct!/=.
    iApply "Hsrc". iApply sim_src_TExist. iApply sim_src_TVis.
    iIntros (?) "Hsrc". iSplit!. iApply bi_mono1_intro0.
    iApply (sim_tgt_handler_intro with "[-]"). iApply sim_tgt_stop.
    iApply "Hsrc". iApply sim_src_TAssume. iIntros (?). iApply sim_src_expr_stop1.
    iIntros (?) "Hsrc". iSplit!. iApply bi_mono1_intro0. case_match; destruct!/=.
    iApply (sim_tgt_handler_intro with "[-]").
    iApply (sim_tgt_link_left_recv with "[-]").
    iApply "Htgt".
    iApply (sim_tgt_rec_Waiting with "[$]").
    iSplit; [iIntros; iModIntro; by iIntros|].
    iIntros (???) "!>". iIntros (?). simplify_eq.
    iApply sim_src_stop. iSplit!. iApply bi_mono1_intro0.
    iIntros (?) "Htgt".
    iApply (sim_tgt_handler_intro with "[-]").
    iApply (sim_tgt_link_left with "[-]").
    iApply ("Htgt" with "[$] [$]").
    iApply sim_tgt_expr_stop2 => /=.
    iApply (sim_tgt_rec_LetE with "[-]"). iIntros "!>" => /=.
    iApply sim_tgt_expr_stop2 => /=. iSplit!.
    iSplitL "Hl0 Hl1 Hl2".
    { iSplit!. iSplitL "Hl0"; eauto with iFrame. iSplitL "Hl1"; eauto with iFrame. }
    iApply sim_tgt_rec_ReturnExt. iIntros (?) "Hh Ha !>".
    iIntros (??????). destruct!/=.
    iApply "Hsrc". iApply sim_src_TUb_end.
    Unshelve. exact: tt.
  Qed.
End memmove.

Lemma memmove_refines_spec :
  trefines (rec_link {["main"; "memmove"; "memcpy"]} {["locle"]}
              (rec_mod (main_prog ∪ memmove_prog ∪ memcpy_prog))
              (spec_mod locle_spec tt))
    (spec_mod main_spec tt).
Proof.
  apply (sim_adequacy #[dimsumΣ; recΣ]); [apply _..|].
  iIntros (??) "!>". simpl.
  iApply (fupd_sim with "[-]").
  iMod recgs_alloc as (?) "[?[??]]". iModIntro.
  iApply memmove_sim. iFrame.
Qed.

(* Idea: construct PI for source level proof from pre and
postconditions of all the external functions instead of constructing
it directly from the used combinators. Maybe one can do the texan
triple trick to force monotonicity of the Π. *)
