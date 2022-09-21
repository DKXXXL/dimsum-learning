From dimsum.core Require Export spec_mod.
From dimsum.core.iris Require Export sim expr.
Set Default Proof Using "Type".

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

  (* TODO: This is missing lemmas for going from @ ? None to @ ? Some and back. *)
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
