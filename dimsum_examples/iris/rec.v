From iris.algebra Require Import big_op gmap frac agree dfrac_agree.
From iris.base_logic.lib Require Import ghost_map.
From dimsum.core.iris Require Export iris.
From dimsum.examples Require Export rec.
From dimsum.core Require Import spec_mod.
From dimsum.examples Require Import memmove.
Set Default Proof Using "Type".

Local Open Scope Z_scope.


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


Program Definition spec_mod_lang {Σ} (EV S : Type) (state_interp : S → iProp Σ)  : mod_lang EV Σ := {|
  mexpr := spec EV S void;
  mectx := unit;
  mfill _ := id;
  mcomp_ectx _ _:= tt;
  mtrans := spec_trans EV S;
  mexpr_rel σ t := σ.1 ≡ t;
  mstate_interp σ := state_interp σ.2;
|}.
Next Obligation. done. Qed.

Definition spec_mod_lang_unit {Σ} (EV : Type) : mod_lang EV Σ :=
  spec_mod_lang EV unit (λ _, True%I).

Section spec.
  Context `{!dimsumGS Σ} {EV S : Type} {state_interp : S → iProp Σ}.

  Global Instance sim_tgt_expr_spec_proper :
    Proper ((≡) ==> (=) ==> (=) ==> (⊣⊢)) (sim_tgt_expr (Λ:=spec_mod_lang EV S state_interp)).
  Proof.
    move => ?? ? ?? -> ?? ->.
    Local Transparent sim_tgt_expr.
    Local Typeclasses Transparent sim_tgt_expr.
    iSplit; iIntros "HP" (?) "?"; iIntros (??); simplify_eq/=; iApply ("HP" with "[$]"); iPureIntro => /=.
    all: by etrans; [done|].
    Unshelve. all: exact tt.
  Qed.

  Global Instance sim_src_expr_spec_proper :
    Proper ((≡) ==> (=) ==> (=) ==> (⊣⊢)) (sim_src_expr (Λ:=spec_mod_lang EV S state_interp)).
  Proof.
    move => ?? ? ?? -> ?? ->.
    Local Transparent sim_src_expr.
    Local Typeclasses Transparent sim_src_expr.
    iSplit; iIntros "HP" (?) "?"; iIntros (??); simplify_eq/=; iApply ("HP" with "[$]"); iPureIntro => /=.
    all: by etrans; [done|].
    Unshelve. all: exact tt.
  Qed.

  Let X := (spec_mod_lang EV _ state_interp).
  Local Canonical Structure X.

  Lemma sim_tgt_TVis k Π Φ e :
    (▷ₒ Π (Some e) (λ P, (∀ σ, σ ⤇ₜ (λ Π, TGT k tt [{ Π }] {{ Φ }}) -∗ P σ))) -∗
    TGT (Spec.bind (TVis e) k) [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_tgt_expr_bi_mono.
    iApply sim_tgt_expr_step. iIntros (?[??]?? Heq Hstep) "Hs". simplify_eq/=. iModIntro.
    inv/= Hstep.
    all: revert select (_ ≡ _); rewrite Heq; try by move => /spec_equiv_inv.
    move => /spec_equiv_inv //= [? Heq2]. simplify_eq/=.
    iModIntro. iApply (bi_mono1_intro with "Hsim"). iIntros (?) "Hσ".
    iSplit!. iIntros "Htgt". iApply "Hσ". by iApply "Htgt".
  Qed.

  Lemma sim_src_TVis k Π Φ e :
    (∀ σ, σ ⤇ₛ (λ Π, SRC k tt [{ Π }] {{ Φ }}) -∗ Π (Some e) σ) -∗
    SRC (Spec.bind (TVis e) k) [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_src_expr_step. iIntros (?[??]?) "?". simplify_eq/=. iModIntro.
    iExists _, _. iSplit. { iPureIntro. by econs. }
    iIntros ([??] ?) "!> HΦ". simplify_eq.
    iApply "Hsim". iIntros (?) "?". by iApply ("HΦ" with "[//] [$]").
  Qed.

  Lemma sim_tgt_TAll {T} x k Π Φ :
    (▷ₒ TGT (k x) [{ Π }] {{ Φ }}) -∗
    TGT (Spec.bind (TAll T) k) [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_tgt_expr_step_None. iIntros (?[??]?? Heq Hstep) "Hs". simplify_eq/=. iModIntro.
    inv/= Hstep.
    all: revert select (_ ≡ _); rewrite Heq; try by move => /spec_equiv_inv.
    move => /spec_equiv_inv //= [? Heq2]. simplify_eq/=.
    iModIntro. rewrite Heq2. iSplit!. iFrame.
  Qed.

  Lemma sim_src_TAll {T} k Π Φ :
    (∀ x, SRC (k x) [{ Π }] {{ Φ }}) -∗
    SRC (Spec.bind (TAll T) k) [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_src_expr_step_None. iIntros (?[??]?) "?". simplify_eq/=. iModIntro.
    iExists _. iSplit. { iPureIntro. by econs. }
    iIntros ([??] [??]) "!>". simplify_eq. iSplit!. iFrame. iApply "Hsim".
  Qed.

  Lemma sim_tgt_TExist {T} k Π Φ :
    (∀ x, ▷ₒ TGT (k x) [{ Π }] {{ Φ }}) -∗
    TGT (Spec.bind (TExist T) k) [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_tgt_expr_step_None. iIntros (?[??]?? Heq Hstep) "Hs". simplify_eq/=. iModIntro.
    inv/= Hstep.
    all: revert select (_ ≡ _); rewrite Heq; try by move => /spec_equiv_inv.
    move => /spec_equiv_inv //= [? Heq2]. simplify_eq/=. iSpecialize ("Hsim" $! _).
    iModIntro. rewrite Heq2. iSplit!. iFrame.
  Qed.

  Lemma sim_src_TExist {T} x k Π Φ :
    SRC (k x) [{ Π }] {{ Φ }} -∗
    SRC (Spec.bind (TExist T) k) [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_src_expr_step_None. iIntros (?[??]?) "?". simplify_eq/=. iModIntro.
    iExists _. iSplit. { iPureIntro. by econs. }
    iIntros ([??] ?) "!>". simplify_eq. iSplit!. iFrame.
  Qed.

  Lemma sim_tgt_TNb T (k : T → _) Π Φ :
    ⊢ TGT (Spec.bind TNb k) [{ Π }] {{ Φ }}.
  Proof.
    rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_tgt_expr_step_None. iIntros (?[??]?? Heq Hstep) "Hs". simplify_eq/=. iModIntro.
    inv/= Hstep.
    all: revert select (_ ≡ _); rewrite Heq; try by move => /spec_equiv_inv.
    move => /spec_equiv_inv //= [? Heq2]. simplify_eq/=. destruct_all void.
  Qed.

  Lemma sim_tgt_TNb_end Π Φ :
    ⊢ TGT TNb [{ Π }] {{ Φ }}.
  Proof.
    iApply sim_tgt_expr_step_None. iIntros (?[??]?? Heq Hstep) "Hs". simplify_eq/=. iModIntro.
    inv/= Hstep.
    all: revert select (_ ≡ _); rewrite Heq; try by move => /spec_equiv_inv.
    move => /spec_equiv_inv //= [? Heq2]. simplify_eq/=. destruct_all void.
  Qed.

  Lemma sim_src_TUb T (k : T → _) Π Φ :
    ⊢ SRC (Spec.bind TUb k) [{ Π }] {{ Φ }}.
  Proof.
    rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_src_expr_step_None. iIntros (?[??]?) "?". simplify_eq/=. iModIntro.
    iExists _. iSplit. { iPureIntro. by econs. }
    iIntros ([??] [??]) "!>". destruct_all void.
  Qed.

  Lemma sim_src_TUb_end Π Φ :
    ⊢ SRC (TUb) [{ Π }] {{ Φ }}.
  Proof.
    iApply sim_src_expr_step_None. iIntros (?[??]?) "?". simplify_eq/=. iModIntro.
    iExists _. iSplit. { iPureIntro. by econs. }
    iIntros ([??] [??]) "!>". destruct_all void.
  Qed.

  Lemma sim_tgt_TAssume k Π Φ (P : Prop) :
    P →
    (▷ₒ TGT (k tt) [{ Π }] {{ Φ }}) -∗
    TGT (Spec.bind (TAssume P) k) [{ Π }] {{ Φ }}.
  Proof.
    iIntros (?) "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_tgt_expr_step_None. iIntros (?[??]?? Heq Hstep) "Hs". simplify_eq/=. iModIntro.
    inv/= Hstep.
    all: revert select (_ ≡ _); rewrite Heq; try by move => /spec_equiv_inv.
    move => /spec_equiv_inv //= [? Heq2]. simplify_eq/=.
    iModIntro. rewrite Heq2. iSplit!. iFrame.
    Unshelve. done.
  Qed.

  Lemma sim_src_TAssume k Π Φ P :
    (⌜P⌝ -∗ SRC (k tt) [{ Π }] {{ Φ }}) -∗
    SRC (Spec.bind (TAssume P) k) [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_src_expr_step_None. iIntros (?[??]?) "?". simplify_eq/=. iModIntro.
    iExists _. iSplit. { iPureIntro. by econs. }
    iIntros ([??] [??]) "!>". simplify_eq. iSplit!. iFrame. by iApply "Hsim".
  Qed.

  Lemma sim_tgt_TAssert k Π Φ (P : Prop) :
    (⌜P⌝ -∗ ▷ₒ TGT (k tt) [{ Π }] {{ Φ }}) -∗
    TGT (Spec.bind (TAssert P) k) [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_tgt_expr_step_None. iIntros (?[??]?? Heq Hstep) "Hs". simplify_eq/=. iModIntro.
    inv/= Hstep.
    all: revert select (_ ≡ _); rewrite Heq; try by move => /spec_equiv_inv.
    move => /spec_equiv_inv //= [? Heq2]. simplify_eq/=. iSpecialize ("Hsim" with "[//]").
    iModIntro. rewrite Heq2. iSplit!. iFrame.
  Qed.

  Lemma sim_src_TAssert k Π Φ (P : Prop) :
    P →
    SRC (k tt) [{ Π }] {{ Φ }} -∗
    SRC (Spec.bind (TAssert P) k) [{ Π }] {{ Φ }}.
  Proof.
    iIntros (?) "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_src_expr_step_None. iIntros (?[??]?) "?". simplify_eq/=. iModIntro.
    iExists _. iSplit. { iPureIntro. by econs. }
    iIntros ([??] ?) "!>". simplify_eq. iSplit!. iFrame.
    Unshelve. done.
  Qed.

  Lemma sim_tgt_TAssumeOpt {T} o (x : T) k Π Φ :
    o = Some x →
    TGT k x [{ Π }] {{ Φ }} -∗
    TGT (Spec.bind (TAssumeOpt o) k) [{ Π }] {{ Φ }}.
  Proof. iIntros (->) "Hsim". simpl. by rewrite unfold_bind/=. Qed.

  Lemma sim_src_TAssumeOpt {T} (o : option T) k Π Φ :
    (∀ x, ⌜o = Some x⌝ -∗ SRC k x [{ Π }] {{ Φ }}) -∗
    SRC (Spec.bind (TAssumeOpt o) k) [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim".
    destruct o => /=.
    - rewrite unfold_bind/=. by iApply "Hsim".
    - iApply sim_src_TUb.
  Qed.

  Lemma sim_tgt_TAssertOpt {T} (o : option T) k Π Φ :
    (∀ x, ⌜o = Some x⌝ -∗ TGT k x [{ Π }] {{ Φ }}) -∗
    TGT (Spec.bind (TAssertOpt o) k) [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim".
    destruct o => /=.
    - rewrite unfold_bind/=. by iApply "Hsim".
    - iApply sim_tgt_TNb.
  Qed.

  Lemma sim_src_TAssertOpt {T} o (x : T) k Π Φ :
    o = Some x →
    SRC k x [{ Π }] {{ Φ }} -∗
    SRC (Spec.bind (TAssertOpt o) k) [{ Π }] {{ Φ }}.
  Proof. iIntros (->) "Hsim". simpl. by rewrite unfold_bind/=. Qed.
End spec.


Definition fnsUR : cmra :=
  agreeR (gmapO string (leibnizO fndef)).

Definition to_fns : gmap string fndef → fnsUR :=
  to_agree.


Class recPreGS (Σ : gFunctors) := RecPreGS {
  rec_mapsto_ghost_map_preG :> ghost_mapG Σ loc val;
  rec_alloc_ghost_map_preG :> ghost_mapG Σ loc Z;
  rec_fn_preG :> inG Σ fnsUR;
}.

Class recGS (Σ : gFunctors) := RecGS {
  rec_mapsto_ghost_mapG :> ghost_mapG Σ loc val;
  rec_alloc_ghost_mapG :> ghost_mapG Σ loc Z;
  rec_fnG :> inG Σ fnsUR;
  rec_mapsto_name : gname;
  rec_alloc_name : gname;
  rec_fn_name : gname;
}.

Definition recΣ : gFunctors :=
  #[ ghost_mapΣ loc val; ghost_mapΣ loc Z; GFunctor fnsUR ].

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
    ghost_map_elem rec_alloc_name l (DfracOwn 1) sz.
  Local Definition rec_alloc_aux : seal (@rec_alloc_def).
  Proof. by eexists. Qed.
  Definition rec_alloc := rec_alloc_aux.(unseal).
  Local Definition rec_alloc_unseal :
    @rec_alloc = @rec_alloc_def := rec_alloc_aux.(seal_eq).

  Definition rec_alloc_auth (h : gset loc) : iProp Σ :=
    ∃ p,
    ⌜∀ l sz, p !! l = Some sz → sz > 0⌝ ∗
    ⌜∀ l sz, p !! l = Some sz → ∀ l', l'.1 = l.1 → l' ∈ h ↔ l.2 ≤ l'.2 < l.2 + sz⌝ ∗
    ghost_map_auth rec_alloc_name 1 p.

  Definition rec_fn_auth (fns : gmap string fndef) : iProp Σ :=
    own rec_fn_name (to_fns fns).
  Definition rec_fn_mapsto_def (f : string) (fn : option fndef) : iProp Σ :=
    ∃ fns, ⌜fns !! f = fn⌝ ∗ rec_fn_auth fns.
  Local Definition rec_fn_mapsto_aux : seal (@rec_fn_mapsto_def).
  Proof. by eexists. Qed.
  Definition rec_fn_mapsto := rec_fn_mapsto_aux.(unseal).
  Local Definition rec_fn_mapsto_unseal :
    @rec_fn_mapsto = @rec_fn_mapsto_def := rec_fn_mapsto_aux.(seal_eq).

  Definition rec_state_interp (σ : rec_state) : iProp Σ :=
    rec_mapsto_auth (h_heap (st_heap σ)) ∗ rec_alloc_auth (dom (h_heap (st_heap σ))) ∗ rec_fn_auth (st_fns σ).
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

Record expr_heap := ExprHeap {
 eh_expr : expr;
 eh_heap : option heap_state;
}.
Add Printing Constructor expr_heap.

Definition expr_heap_fill (K : list expr_ectx) (e : expr_heap) : expr_heap :=
  ExprHeap (expr_fill K (eh_expr e)) (eh_heap e).

Arguments expr_heap_fill !_ _ /.

Notation "e @ h" := (ExprHeap e (Some h)) (at level 14) : stdpp_scope.
Notation "e @ -" := (ExprHeap e None) (at level 14) : stdpp_scope.

Program Canonical Structure rec_mod_lang {Σ} `{!recGS Σ} := {|
  mexpr := expr_heap;
  mectx := list expr_ectx;
  mfill := expr_heap_fill;
  mcomp_ectx := flip app;
  mtrans := rec_trans;
  mexpr_rel σ e := st_expr σ = eh_expr e ∧ if eh_heap e is Some h then st_heap σ = h else True;
  mstate_interp := rec_state_interp;
|}.
Next Obligation. move => ???? [??]/=. by rewrite /expr_heap_fill/= expr_fill_app. Qed.

Section lifting.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Lemma sim_tgt_rec_Waiting fns h Π Φ (b : bool) :
    rec_fn_auth fns -∗
    (rec_mapsto_auth (h_heap h) -∗
     rec_alloc_auth (dom (h_heap h)) -∗
     (∀ f fn vs h', ⌜fns !! f = Some fn⌝ -∗
       ▷ₒ Π (Some (Incoming, ERCall f vs h')) (λ P,
         ∀ σ,
           (rec_mapsto_auth (h_heap h') -∗
            rec_alloc_auth (dom (h_heap h')) -∗
            σ ⤇ₜ λ Π', TGT ReturnExt b (Call f (Val <$> vs)) @ - [{ Π' }] {{ Φ }}) -∗
           P σ)) ∧
      ∀ v h', ⌜b⌝ -∗
       ▷ₒ Π (Some (Incoming, ERReturn v h')) (λ P, ∀ σ,
           (rec_mapsto_auth (h_heap h') -∗
            rec_alloc_auth (dom (h_heap h')) -∗
            σ ⤇ₜ λ Π', TGT Val v @ - [{ Π' }] {{ Φ }}) -∗
           P σ)) -∗
    TGT Waiting b @ h [{ Π }] {{ Φ }}.
  Proof.
    iIntros "#Hfns HΦ".
    iApply sim_tgt_expr_bi_mono.
    iApply sim_tgt_expr_step => /=. iIntros (? [e h0 fns0] ?? [??] Hp) "[Hh [Ha Hfns']]". simplify_eq/=.
    iDestruct (rec_fn_auth_agree with "Hfns' Hfns") as %?. subst.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    - iDestruct ("HΦ" with "[$] [$]") as "[HΦ _]". iDestruct ("HΦ" with "[//]") as "HΦ".
      do 2 iModIntro. iApply (bi_mono1_intro with "HΦ"). iIntros (?) "Htgt".
      iSplit!. iIntros "Hc". iApply "Htgt". iIntros "??".
      iApply "Hc"; [done|]. iFrame.
    - iDestruct ("HΦ" with "[$] [$]") as "[_ HΦ]". iDestruct ("HΦ" with "[//]") as "HΦ".
      do 2 iModIntro. iApply (bi_mono1_intro with "HΦ"). iIntros (?) "Htgt".
      iSplit!. iIntros "Hc". iApply "Htgt". iIntros "??".
      iApply "Hc"; [done|]. iFrame.
  Qed.

  Lemma sim_tgt_rec_ReturnExt v Π Φ (b : bool) :
    (∀ h,
     ▷ₒ Π (Some (Outgoing, ERReturn v h)) (λ P,
         ∀ σ,
           (σ ⤇ₜ λ Π', TGT Waiting b @ h [{ Π' }] {{ Φ }}) -∗
           P σ)) -∗
    TGT ReturnExt b (Val v) @ - [{ Π }] {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply sim_tgt_expr_bi_mono.
    iApply sim_tgt_expr_step => /=. iIntros (? [e h0 fns0] ?? [??] Hp) "[Hh [Ha Hfns']]". simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iSpecialize ("HΦ" $! _). do 2 iModIntro. iApply (bi_mono1_intro with "HΦ").
    iIntros (?) "Htgt". iSplit!. iIntros "Hc". iApply "Htgt".
    iApply "Hc"; [done|]. iFrame.
  Qed.

  Lemma sim_tgt_rec_Call_internal f fn es Π Φ vs `{!AsVals es vs None} :
    length vs = length (fd_args fn) →
    f ↪ Some fn -∗
    (▷ₒ TGT AllocA fn.(fd_vars) (subst_l fn.(fd_args) vs fn.(fd_body)) @ - [{ Π }] {{ Φ }}) -∗
    TGT Call f es @ - [{ Π }] {{ Φ }}.
  Proof.
    destruct AsVals0. iIntros (?) "Hfn HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e h fns] ?? [??] Hp) "[Hh [Ha Hfns]]". simplify_eq/=.
    iDestruct (rec_fn_lookup with "[$] [$]") as %?.
    rewrite right_id_L in Hp.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; try naive_solver.
      move => /= ??? e' [_ Heq]. by apply: list_expr_val_inv. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    do 2 iModIntro. iExists _, (_ @ -). iSplit!. iFrame.
  Qed.

  Lemma sim_tgt_rec_Call_external f es Π Φ vs `{!AsVals es vs None} :
    f ↪ None -∗
    (∀ h,
     ▷ₒ Π (Some (Outgoing, ERCall f vs h)) (λ P,
         ∀ σ,
           (σ ⤇ₜ λ Π', TGT Waiting true @ h [{ Π' }] {{ Φ }}) -∗
           P σ)) -∗
    TGT Call f es @ - [{ Π }] {{ Φ }}.
  Proof.
    destruct AsVals0. iIntros "Hfn HΦ".
    iApply sim_tgt_expr_bi_mono.
    iApply sim_tgt_expr_step => /=. iIntros (? [e h0 fns0] ?? [??] Hp) "[Hh [Ha Hfns']]". simplify_eq/=.
    iDestruct (rec_fn_lookup with "[$] [$]") as %?.
    rewrite right_id_L in Hp.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; try naive_solver.
      move => /= ??? e' [_ Heq]. by apply: list_expr_val_inv. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iSpecialize ("HΦ" $! _). do 2 iModIntro. iApply (bi_mono1_intro with "HΦ").
    iIntros (?) "Htgt". iSplit!. iIntros "Hc". iApply "Htgt".
    iApply "Hc"; [done|]. iFrame.
  Qed.

  Lemma sim_tgt_rec_BinOp Π Φ v1 v2 v3 op :
    eval_binop op v1 v2 = Some v3 →
    (▷ₒ Φ (Val v3 @ -) Π) -∗
    TGT BinOp (Val v1) op (Val v2) @ - [{ Π }] {{ Φ }}.
  Proof.
    iIntros (Hop) "HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e' h fns] ?? [??] Hp) "[Hh [Ha Hfns]]". simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    do 2 iModIntro. iExists _, (_ @ -). iSplit!. iFrame.
    by iApply sim_tgt_expr_stop2.
  Qed.

  Lemma sim_tgt_rec_Load Π Φ l v :
    l ↦ v -∗
    (l ↦ v -∗ ▷ₒ Φ (Val v @ -) Π) -∗
    TGT Load (Val (ValLoc l)) @ - [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e' h fns] ?? [??] Hp) "[Hh [Ha Hfns]]". simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iSpecialize ("HΦ" with "[$]").
    do 2 iModIntro. iExists _, (_ @ -). iSplit!. admit.
    iFrame. by iApply sim_tgt_expr_stop2.
  Admitted.

  Lemma sim_tgt_rec_Store Π Φ l v v' :
    l ↦ v -∗
    (l ↦ v' -∗ ▷ₒ Φ (Val 0 @ -) Π) -∗
    TGT Store (Val (ValLoc l)) (Val v') @ - [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e' h fns] ?? [??] Hp) "[Hh [Ha Hfns]]". simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    do 2 iModIntro. iExists _, (_ @ -). iSplit!. admit.
    iFrame => /=.
  Admitted.

  Lemma sim_tgt_rec_AllocA e Π Φ vs :
    Forall (λ z, 0 < z) vs.*2 →
    (∀ ls, ([∗ list] l;n∈ls; vs.*2, [∗ list] o∈seqZ 0 n, (l +ₗ o) ↦ 0) -∗
     ▷ₒ TGT subst_l vs.*1 (ValLoc <$> ls) e @ - [{ Π }] {{ e', Π',
     ∃ v, ⌜e' = Val v @ -⌝ ∗ ([∗ list] l;n∈ls; vs.*2, [∗ list] o∈seqZ 0 n, ∃ v, (l +ₗ o) ↦ v) ∗ Φ e' Π' }}) -∗
    TGT AllocA vs e @ - [{ Π }] {{ Φ }}.
  Proof.
    iIntros (Hall) "HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e' h fns] ?? [??] Hp) "[Hh [Ha Hfns]]". simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    do 2 iModIntro. iExists _, (_ @ -). iSplit!. iFrame. simpl.
  Admitted.

  Lemma sim_tgt_rec_LetE Π Φ s v e :
    (▷ₒ TGT (subst s v e) @ - [{ Π }] {{ Φ }}) -∗
    TGT LetE s (Val v) e @ - [{ Π }] {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e' h fns] ?? [??] Hp) "[Hh [Ha Hfns]]". simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    do 2 iModIntro. iExists _, (_ @ -). iSplit!. iFrame.
  Qed.

  Lemma sim_tgt_rec_If Π Φ (b : bool) e1 e2 :
    (▷ₒ TGT (if b then e1 else e2) @ - [{ Π }] {{ Φ }}) -∗
    TGT If (Val (ValBool b)) e1 e2 @ - [{ Π }] {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e' h fns] ?? [??] Hp) "[Hh [Ha Hfns]]". simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    do 2 iModIntro. iExists _, (_ @ -). iSplit!. iFrame.
  Qed.

End lifting.

Section memmove.
  Context `{!dimsumGS Σ} `{!recGS Σ}.


  Local Definition array (l : loc) (vs : list val) : gmap loc val :=
    (kmap (λ i, l +ₗ i) (map_seqZ 0 vs)).

  Lemma loc_eq (l1 l2 : loc) :
    l1 = l2 ↔ l1.1 = l2.1 ∧ l1.2 = l2.2.
  Proof. destruct l1, l2; naive_solver. Qed.

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
     Φ (Val 0 @ -) Π) -∗
    TGT Call "memcpy" [Val (ValLoc d); Val $ ValLoc s; Val $ ValNum n; Val $ ValNum o] @ - [{ Π }] {{ Φ }}.
  Proof.
    iIntros (Hn Hlen Ho Hd' Hs' Hle) "#Hf Hm HΦ".
    iApply sim_tgt_expr_ctx. iIntros "#?".
    iRevert (hvss hvsd d d' s s' n Φ Hn Hlen Hd' Hs' Hle) "Hm HΦ".
    iApply ord_loeb; [done|].
    iIntros "!> #IH" (hvss hvsd d d' s s' n Φ Hn Hlen Hd' Hs' Hle) "Hm HΦ". simplify_eq.
    iApply (sim_tgt_rec_Call_internal with "Hf"); [done|]. iModIntro => /=.
    iApply sim_tgt_rec_AllocA; [econs|] => /=. iIntros (?) "?". destruct ls => //. iModIntro.
    iApply (sim_tgt_expr_bind [IfCtx _ _] (_ @ -) with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply sim_tgt_rec_If. iModIntro => /=. case_bool_decide (0 < _).
    2: { destruct hvss, hvsd => //. iApply sim_tgt_expr_stop2. iSplit!. iApply "HΦ".
         by rewrite /array !kmap_empty. }
    iApply (sim_tgt_expr_bind [LetECtx _ _] (_ @ -) with "[-]") => /=.
    iApply (sim_tgt_expr_bind [StoreRCtx _] (_ @ -) with "[-]") => /=.
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
      iApply (sim_tgt_expr_bind [CallCtx _ [] _] (_ @ -) with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply (sim_tgt_expr_bind [CallCtx _ [_] _] (_ @ -) with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply (sim_tgt_expr_bind [CallCtx _ [_; _] _] (_ @ -) with "[-]") => /=.
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
      iApply (sim_tgt_expr_bind [CallCtx _ [] _] (_ @ -) with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply (sim_tgt_expr_bind [CallCtx _ [_] _] (_ @ -) with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply (sim_tgt_expr_bind [CallCtx _ [_; _] _] (_ @ -) with "[-]") => /=.
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
        (∀ b, ⌜l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2)⌝ -∗ Φ (Val (ValBool b) @ -) Π) -∗
          TGT Call "locle" [Val (ValLoc l1); Val $ ValLoc l2] @ - [{ Π }] {{ Φ }}) -∗
    ([∗ map] l↦v∈array s hvss ∪ array d hvsd, l ↦ v) -∗
    (([∗ map] l↦v∈array d hvss ∪ array s hvss, l ↦ v) -∗ Φ (Val 0 @ -) Π) -∗
    TGT Call "memmove" [Val (ValLoc d); Val $ ValLoc s; Val $ ValNum n] @ - [{ Π }] {{ Φ }}.
  Proof.
    iIntros (-> ?) "#Hmemmove #Hmemcpy #Hlocle Hs HΦ".
    iApply (sim_tgt_expr_bind [] (_ @ -)).
    iApply (sim_tgt_rec_Call_internal with "Hmemmove"); [done|]. iModIntro => /=.
    iApply sim_tgt_rec_AllocA; [econs|] => /=. iIntros (?) "?". destruct ls => //. iModIntro.
    iApply (sim_tgt_expr_bind [IfCtx _ _] (_ @ -) with "[-]") => /=.
    iApply "Hlocle". iIntros (b Hb) => /=.
    iApply sim_tgt_rec_If. iModIntro => /=. destruct b.
    - iApply (sim_memcpy with "[//] Hs"). { done. } { done. } { by left. } { by rewrite bool_decide_true. }
      { by rewrite bool_decide_true. } {
        rewrite bool_decide_true // => /Hb Hx. symmetry in Hx. by rewrite bool_decide_eq_true in Hx.
      }
      iIntros "?". iSplit!. iApply sim_tgt_expr_stop2. iApply ("HΦ" with "[$]").
    - iApply (sim_tgt_expr_bind [CallCtx _ [] _] (_ @ -) with "[-]") => /=.
      iApply (sim_tgt_expr_bind [BinOpRCtx _ _] (_ @ -) with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply (sim_tgt_expr_bind [CallCtx _ [_] _] (_ @ -) with "[-]") => /=.
      iApply (sim_tgt_expr_bind [BinOpRCtx _ _] (_ @ -) with "[-]") => /=.
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
    (∀ P, P (λ σ', σ' ≈{rec_link_trans fns1 {["locle"]} _ _}≈>ₜ Π_s) -∗ Π_s None P) →
    let Π := λ κ P, (∀ σl, (σl ⤇ₜ λ Π, TGT locle_spec [{Π}] {{_, _, False}}) -∗
              link_tgt_left_handler (rec_link_filter fns1 {["locle"]}) Π_s s σl κ P)%I in
    rec_fn_auth fns -∗
    "locle" ↪ None -∗
    (∀ b, ⌜l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2)⌝ -∗ Φ (Val (ValBool b) @ -) Π) -∗
    TGT Call "locle" [Val (ValLoc l1); Val $ ValLoc l2] @ - [{ Π }] {{ Φ }}.
  Proof.
    iIntros (HΠ_s Π) "#Hfns #Hf HΦ".
    iApply (sim_tgt_rec_Call_external with "[$]"). iIntros (?) "!>". iIntros (σl) "Hσl".
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
    iApply (sim_tgt_rec_Waiting with "[$]"). iIntros "??".
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

  Context `{!dimsumGS Σ} `{!recGS Σ}.
  Lemma memmove_sim  :
    rec_state_interp (rec_init (main_prog ∪ memmove_prog ∪ memcpy_prog)) -∗
    (MLFNone, [], rec_init (main_prog ∪ memmove_prog ∪ memcpy_prog), (locle_spec, ())) ⪯{
      rec_link_trans {["main"; "memmove"; "memcpy"]} {["locle"]} rec_trans (spec_trans rec_event ()),
      spec_trans rec_event ()} (main_spec, ()).
  Proof.
    iIntros "[Hh [Ha #Hfns]]". iApply (sim_tgt_handler_intro with "[-]").
    iApply (sim_tgt_link_None with "[-]").
    iIntros "!>" (??????). destruct!/=. case_match; destruct!/=.
    unfold sim_tgt_handler.
    iApply (sim_src_expr_elim with "[] [-]"); [simpl; done..|].
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
    iApply (sim_tgt_expr_elim [] (_ @ _) with "[Ha Hh] [-]"); [done| by iFrame |] => /=.
    iApply (sim_tgt_rec_Waiting with "[$]"). iIntros "Hh Ha".
    iSplit; [|by iIntros].
    iIntros (???? Hin) "!>". iIntros (?). simplify_map_eq.
    iApply sim_src_stop. iSplit!. iApply bi_mono1_intro0. iIntros (?) "Htgt".
    iApply (sim_tgt_handler_intro with "[-]").
    iApply (sim_tgt_link_left with "[-]").
    iApply ("Htgt" with "[Hh] [Ha]"). admit. admit.
    iApply (sim_tgt_expr_bind [ReturnExtCtx _] (_ @ -)).
    iApply sim_tgt_rec_Call_internal. 2: { by iApply (rec_fn_intro with "[$]"). } { done. }
    iModIntro => /=.
    iApply sim_tgt_rec_AllocA; [by econs|] => /=. iIntros (?) "Hl".
    destruct ls as [|l []] => //=. 2: by iDestruct!.
    have -> : (0%nat + 0) = 0 by []. have -> : (1%nat + 0) = 1 by []. have -> : (2%nat + 0) = 2 by [].
    iDestruct "Hl" as "[[Hl0 [Hl1 [Hl2 _]]] _]". iModIntro.
    iApply (sim_tgt_expr_bind [LetECtx _ _] (_ @ -) with "[-]") => /=.
    iApply (sim_tgt_expr_bind [StoreLCtx _] (_ @ -) with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply (sim_tgt_rec_Store with "Hl0"). iIntros "Hl0 !>" => /=.
    iApply sim_tgt_rec_LetE. iIntros "!>" => /=.
    iApply (sim_tgt_expr_bind [LetECtx _ _] (_ @ -) with "[-]") => /=.
    iApply (sim_tgt_expr_bind [StoreLCtx _] (_ @ -) with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply (sim_tgt_rec_Store with "Hl1"). iIntros "Hl1 !>" => /=.
    iApply sim_tgt_rec_LetE. iIntros "!>" => /=.
    iApply (sim_tgt_expr_bind [LetECtx _ _] (_ @ -) with "[-]") => /=.
    iApply (sim_tgt_expr_bind [CallCtx _ [] _] (_ @ -) with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply (sim_tgt_expr_bind [CallCtx _ [_] _] (_ @ -) with "[-]") => /=.
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
        by iApply (sim_tgt_expr_elim with "[] [-]"); [simpl; done..|].
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
      iApply (sim_tgt_expr_bind [LetECtx _ _] (_ @ -) with "[-]") => /=.
      iApply (sim_tgt_expr_bind [CallCtx _ [] _] (_ @ -) with "[-]") => /=.
      iApply (sim_tgt_expr_bind [LoadCtx] (_ @ -) with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply (sim_tgt_rec_Load with "Hl1"). iIntros "Hl1 !>" => /=.
      iApply (sim_tgt_rec_Call_external). { by iApply (rec_fn_intro with "[$]"). }
      iIntros (?) "!>". iIntros (σ') "Hlocle".
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
      iApply (sim_tgt_rec_Waiting with "[$]"). iIntros "Hh Ha".
      iSplit; [iIntros; iModIntro; by iIntros|].
      iIntros (???) "!>". iIntros (?). simplify_eq.
      iApply sim_src_stop. iSplit!. iApply bi_mono1_intro0.
      iIntros (?) "Htgt".
      iApply (sim_tgt_handler_intro with "[-]").
      iApply (sim_tgt_link_left with "[-]").
      iApply ("Htgt" with "[$] [$]").
      iApply sim_tgt_expr_stop2 => /=.
      iApply (sim_tgt_rec_LetE with "[-]"). iIntros "!>" => /=.
      iApply (sim_tgt_expr_bind [LetECtx _ _] (_ @ -) with "[-]") => /=.
      iApply (sim_tgt_expr_bind [CallCtx _ [] _] (_ @ -) with "[-]") => /=.
      iApply (sim_tgt_expr_bind [LoadCtx] (_ @ -) with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply (sim_tgt_rec_Load with "Hl2"). iIntros "Hl2 !>" => /=.
      iApply (sim_tgt_rec_Call_external). { by iApply (rec_fn_intro with "[$]"). }
      iIntros (?) "!>". iIntros (??????). destruct!/=. rewrite bool_decide_false//.
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
      iApply (sim_tgt_rec_Waiting with "[$]"). iIntros "Hh Ha".
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
      iApply sim_tgt_rec_ReturnExt. iIntros (?) "!>".
      iIntros (??????). destruct!/=.
      iApply "Hsrc". iApply sim_src_TUb_end.
    Unshelve. exact: tt.
  Admitted.
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
