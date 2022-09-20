From iris.algebra Require Export cmra local_updates proofmode_classes auth.
From iris.algebra Require Import updates.
From iris.base_logic.lib Require Export own.
From iris.algebra.lib Require Import gmap_view.
From iris.proofmode Require Export proofmode.
From dimsum.core Require Export satisfiable.
From dimsum.core Require Import axioms.
From iris.prelude Require Import options.

(** * upstream *)
Section cmra.
  Context {A B} (rel : view_rel A B).
  Implicit Types a : A.
  Implicit Types ag : option (dfrac * agree A).
  Implicit Types b : B.
  Implicit Types x y : view rel.
  Implicit Types q : frac.
  Implicit Types dq : dfrac.

  Lemma view_updateP a b P :
    (∀ n bf, rel n a (b ⋅ bf) → ∃ a' b', P (●V a' ⋅ ◯V b') ∧ rel n a' (b' ⋅ bf)) →
    view_auth (rel:=rel) (DfracOwn 1) a ⋅ ◯V b ~~>: P.
  Proof.
    intros Hup; apply cmra_total_updateP=> n [[[dq ag]|] bf] [/=].
    { by intros []%(exclusiveN_l _ _). }
    intros _ (a0 & <-%(inj to_agree) & Hrel).
    rewrite left_id in Hrel. edestruct Hup as [a' [b'[??]]]; [done|].
    eexists _. split; [done|].
    split; simpl; [done|].
    exists a'; split; [done|]. rewrite !left_id. done.
  Qed.
End cmra.

  Lemma cmra_opM_op_assoc {A : cmra} (x1 : A) x2 x3 :
    x1 ⋅? (x2 ⋅ x3) ≡ x1 ⋅? x2 ⋅? x3.
  Proof. destruct x2, x3 => //=. by rewrite -assoc. Qed.

(** * CoreCancelable *)
Class CoreCancelable {A : cmra} (x : A) :=
  core_cancelableN n y z : ✓{n}(x ⋅ y) → x ⋅ y ≡{n}≡ x ⋅ z → y ⋅? pcore x ≡{n}≡ z ⋅? pcore x
.
Global Arguments core_cancelableN {_} _ {_} _ _ _ _.
Global Hint Mode CoreCancelable + ! : typeclass_instances.
Global Instance: Params (@CoreCancelable) 1 := {}.

Section cmra.
Context {A : cmra}.
Implicit Types x y z : A.

Global Instance CoreCancelable_proper : Proper ((≡) ==> iff) (@CoreCancelable A).
Proof. intros x y Hxy. rewrite /CoreCancelable. by setoid_rewrite Hxy. Qed.

Lemma core_cancelable x `{!CoreCancelable x} y z : ✓(x ⋅ y) → x ⋅ y ≡ x ⋅ z → y ⋅? pcore x ≡ z ⋅? pcore x.
Proof. rewrite !equiv_dist cmra_valid_validN. intros. by apply (core_cancelableN x). Qed.
Lemma discrete_core_cancelable x `{CmraDiscrete A}:
  (∀ y z, ✓(x ⋅ y) → x ⋅ y ≡ x ⋅ z → y ⋅? pcore x ≡ z ⋅? pcore x) → CoreCancelable x.
Proof. intros ????. rewrite -!discrete_iff -cmra_discrete_valid_iff. auto. Qed.

Lemma core_cancelableN_total x `{!CoreCancelable x} `{!CmraTotal A} n y z :
  ✓{n}(x ⋅ y) → x ⋅ y ≡{n}≡ x ⋅ z → y ⋅ core x ≡{n}≡ z ⋅ core x.
Proof. move => ??. efeed generalize (core_cancelableN x); [done..|]. by rewrite cmra_pcore_core. Qed.

Global Instance cancelable_core_cancelable x `{!Cancelable x} : CoreCancelable x.
Proof.
  rewrite /CoreCancelable => n y z Hvalid Hz. efeed generalize @cancelableN; [done..|]. move => ->. done.
Qed.

Global Instance coreid_core_cancelable x `{!CoreId x} : CoreCancelable x.
Proof. rewrite /CoreCancelable => n y z Hvalid Heq. by rewrite core_id /= comm Heq comm. Qed.

Lemma core_cancelable_op x1 x2 :
  CoreCancelable x1 →
  CoreCancelable x2 →
  (* TODO: Does this hold in general? *)
  pcore (x1 ⋅ x2) ≡ pcore x1 ⋅ pcore x2 →
  CoreCancelable (x1 ⋅ x2).
Proof.
  move => Hx1 Hx2 Hcore. rewrite /CoreCancelable => n y z Hvalid Hz.
  rewrite Hcore !cmra_opM_op_assoc.
  apply Hx2. {
    apply: cmra_validN_includedN; [done|].
    rewrite (comm _ x1) -!assoc. apply: cmra_monoN_l.
    rewrite comm. destruct (pcore x1) eqn:? => /=.
    + apply: cmra_monoN_l. apply cmra_included_includedN. by apply cmra_included_pcore.
    + apply cmra_includedN_l.
  }
  efeed pose proof (Hx1 n (x2 ⋅ y) (x2 ⋅ z)).
  - by rewrite assoc.
  - by rewrite !assoc.
  - by rewrite -!cmra_op_opM_assoc.
Qed.
End cmra.

Section instances.
Global Instance dfrac_core_cancelable (dq : dfracR) : CoreCancelable dq.
Proof.
  destruct dq as [q| |q]; [apply _..|].
  have -> : DfracBoth q = DfracOwn q ⋅ DfracDiscarded by done.
  by apply: core_cancelable_op.
Qed.

Lemma prod_core_cancelable {A B : cmra} (x1 : A) (x2 : B) :
  CoreCancelable x1 →
  CoreCancelable x2 →
  is_Some (pcore x1) →
  is_Some (pcore x2) →
  CoreCancelable (x1, x2).
Proof.
  move => Hx1 Hx2 [? Hp1] [? Hp2].
  move => n [y1 y2] [z1 z2] /=. rewrite -!pair_op => /pair_validN[/=??] [/= ??].
  efeed specialize Hx1; [done..|].
  efeed specialize Hx2; [done..|].
  rewrite pair_pcore /= Hp1 Hp2 /=.
  rewrite Hp1/= in Hx1. rewrite Hp2/= in Hx2.
  done.
Qed.

Global Instance prod_total_core_cancelable {A B : cmra} (x : A * B) `{!CmraTotal A} `{!CmraTotal B} :
  CoreCancelable x.1 →
  CoreCancelable x.2 →
  CoreCancelable x.
Proof. move => ??. apply: prod_core_cancelable; by rewrite cmra_pcore_core. Qed.

Global Instance core_cancelable_Some {A : cmra} (a : A) :
  IdFree a → CoreCancelable a → CoreCancelable (Some a).
Proof.
  intros Hirr ? n [b|] [c|] ? EQ; inversion_clear EQ => /=.
  - rewrite ?Some_op_opM. constructor. by apply (core_cancelableN a).
  - destruct (Hirr b); [|eauto using dist_le with lia].
    by eapply (cmra_validN_op_l 0 a b), (cmra_validN_le n); last lia.
  - destruct (Hirr c); [|symmetry; eauto using dist_le with lia].
    by eapply (cmra_validN_le n); last lia.
  - done.
Qed.

Global Instance option_core_cancelable {A : cmra} (x : optionR A) :
  (∀ a : A, IdFree a) →
  (∀ a : A, CoreCancelable a) →
  CoreCancelable x.
Proof. destruct x; apply _. Qed.

Global Instance gmap_core_cancelable `{Countable K} {A : cmra} (m : gmap K A) :
  (∀ x : option A, CoreCancelable x) → CoreCancelable m.
Proof.
  intros ? n m1 m2 ?? i.
  rewrite !lookup_opM !cmra_pcore_core /= lookup_core.
  apply (core_cancelableN (m !! i)); by rewrite -!lookup_op.
Qed.


Global Instance prod_dfrac_agree_core_cancelable {A : ofe} (x : prodR dfracR (agreeR A)) :
  CoreCancelable x.
Proof. destruct x as [[q| |q]?]. 1: apply _. all: apply prod_core_cancelable => //; by apply _. Qed.

Global Instance option_prod_dfrac_agree_core_cancelable {A : ofe} (x : optionR (prodR dfracR (agreeR A))) :
  CoreCancelable x.
Proof.
  destruct x as [[[q| |q] a]|]; try apply _.
  have -> : (Some (DfracBoth q, a)) ≡ (Some (DfracOwn q, a)) ⋅ (Some (DfracDiscarded, a)).
  { by rewrite -Some_op -pair_op agree_idemp. }
  apply: core_cancelable_op.
  rewrite /pcore/cmra_pcore/=/option_pcore_instance/=.
  rewrite /pcore/cmra_pcore/=/prod_pcore_instance/=.
  by rewrite agree_idemp.
Qed.

Global Instance view_core_cancelable {A B} (rel : view_rel A B) (x : viewR rel) :
  CoreCancelable (view_frag_proj x) →
  CoreCancelable x.
Proof.
  move => Hfrag n y z Hvalid [Heqa Heqf].
  have ? : ✓{n} view_auth_proj (x ⋅ y). {
    destruct x as [[[??]|]?], y as [[[??]|]?] => //; simplify_eq/=.
    all: move: Hvalid => [? [? [Heq ?]]]; split; try done; simpl in *; by rewrite Heq.
  }
  have ? : ✓{n} view_frag_proj (x ⋅ y). {
    destruct x as [[[??]|]?], y as [[[??]|]?] => //; simplify_eq/=.
    1,2,3: move: Hvalid => [? [? [_ /view_rel_validN ?]]]; done.
    1: move: Hvalid => [? /view_rel_validN ?]; done.
  }
  split.
  - eapply (core_cancelableN (A:=optionUR (prodR (dfracR) (agreeR _)))); try apply _; done.
  - eapply core_cancelableN_total; try apply _; done.
Qed.

Global Instance gmap_view_core_cancelable {A} `{Countable K} (x : gmap_viewR K A) :
  CoreCancelable x.
Proof. apply _. Abort.

End instances.

(** * sat *)
Class satG Σ (M : ucmra) := SatG {
  sat_inG : inG Σ (authR M);
}.
Local Existing Instance sat_inG.

Definition sat {Σ M} `{!satG Σ M} : gname → uPred M → iProp Σ :=
  λ γ P, (∃ m, ⌜uPred_holds P 0 m⌝ ∗ own γ (auth_frag m))%I.

Definition sat_open {Σ M} `{!satG Σ M} : gname → iProp Σ :=
  λ γ, (∃ m, own γ (auth_auth (DfracOwn 1) m))%I.

Definition sat_closed {Σ M} `{!satG Σ M} : gname → bool → uPred M → iProp Σ :=
  λ γ b F, (∀ P', ⌜satisfiable (P' ∗ F)⌝ ==∗ sat_open γ ∗ sat γ (if b then P' ∗ F else P'))%I.

Global Instance: Params (@sat) 4 := {}.
Global Instance: Params (@sat_open) 4 := {}.
Global Instance: Params (@sat_closed) 5 := {}.

Section sat.
  Context {Σ : gFunctors} {M : ucmra}.
  Context `{!satG Σ M} {Hdiscrete : CmraDiscrete M}.
  Implicit Types (P : uPred M).

  Global Instance sat_proper γ : Proper ((≡) ==> (≡)) (sat γ).
  Proof.
    move => P1 P2 [Heq].
    iSplit; iIntros "[%x [% Hx]]".
    all: iDestruct (own_valid with "Hx") as "#Hvalid"; rewrite auth_frag_validI.
    (* TODO: Is this use of excluded middle necessary? *)
    all: destruct (AxClassic (✓{0} x)); [|by iDestruct (uPred.cmra_valid_elim with "Hvalid") as %[]].
    all: iExists _; iFrame; iPureIntro; by apply Heq.
  Qed.

  (** ** Commuting connectives with [sat] *)
  Lemma sat_mono γ P1 P2 :
    (P1 -∗ P2) →
    sat γ P1 -∗ sat γ P2.
  Proof.
    iIntros ([Hwand]) "[%m [%Hholds Hm]]".
    iDestruct (own_valid with "Hm") as "#Hvalid". rewrite auth_frag_validI.
    iExists _. iFrame.
    (* TODO: Is this use of excluded middle necessary? *)
    destruct (AxClassic (✓{0} m)); [iPureIntro; naive_solver|].
    by iDestruct (uPred.cmra_valid_elim with "Hvalid") as %[].
  Qed.

  Lemma sat_bupd γ P :
    sat_open γ -∗
    sat γ (|==> P) ==∗
    sat_open γ ∗ sat γ P.
  Proof using Hdiscrete.
    iIntros "[%ma Ha] [%mf [%Hholds Hf]]".
    iCombine "Ha Hf" as "H".
    do [uPred.unseal] in Hholds.
    iMod (own_updateP (λ x, ∃ ma' mf', x ≡ ● ma' ⋅ ◯ mf' ∧ uPred_holds P 0 mf')  with "H")
      as (?[?[?[-> ?]]]) "[Ha Hf]".
    2: { iModIntro. iSplitL "Ha"; iExists _; by iFrame. }
    apply view_updateP. move => ? f [/cmra_discrete_included_iff [i Heq] /cmra_discrete_valid_iff Hvalid].
    feed destruct (Hholds 0 (f ⋅ i)) as [x [?%cmra_discrete_valid_iff ?]].
    { done. } { rewrite assoc -Heq. by apply cmra_valid_validN. }
    eexists (x ⋅ f ⋅ i), x.
    split; [by eexists (x ⋅ f ⋅ i), x|].
    split.
    - apply cmra_includedN_l.
    - apply cmra_valid_validN. by rewrite -assoc.
  Qed.

  Lemma sat_sep γ P1 P2 :
    sat γ (P1 ∗ P2) ⊣⊢ sat γ P1 ∗ sat γ P2.
  Proof using Hdiscrete.
    iSplit.
    - iIntros "[%m [%Hholds H]]".
      do [uPred.unseal] in Hholds. destruct Hholds as [m1 [m2 [Heq%discrete_iff [??]]]]. 2: apply _.
      rewrite Heq auth_frag_op own_op. iDestruct "H" as "[H1 H2]".
      iSplitL "H1"; iExists _; by iFrame.
    - iIntros "[[%m1 [%Hholds1 H1]] [%m2 [%Hholds2 H2]]]".
      iExists (m1 ⋅ m2).
      iCombine "H1 H2" as "$".
      iPureIntro. uPred.unseal. eexists _, _. eauto.
  Qed.

  Lemma sat_exist A γ (P : A → _) :
    sat γ (∃ x : A, P x) ⊣⊢ ∃ x, sat γ (P x).
  Proof.
    iSplit.
    - iIntros "[%m [%Hholds H]]".
      do [uPred.unseal] in Hholds. destruct Hholds as [??].
      iExists _, _. by iFrame.
    - iIntros "[% ?]". iApply (sat_mono with "[$]").
      iIntros. by iExists _.
  Qed.

  Lemma sat_pure γ Φ :
    sat γ ⌜Φ⌝ -∗ ⌜Φ⌝.
  Proof. iIntros "[%m [%Hholds H]]". do [uPred.unseal] in Hholds. done. Qed.

  Lemma sat_persistently_1 γ P :
    sat γ (<pers> P) -∗ <pers> sat γ P.
  Proof.
    iIntros "[%m1 [%Hholds1 H1]]".
    iExists (core m1).
    iDestruct (own_mono with "H1") as "H1". { apply cmra_included_core. }
    iDestruct "H1" as "#H1".
    iModIntro. iSplit; [|done].
    iPureIntro. move: Hholds1. uPred.unseal. done.
  Qed.

  Lemma sat_affinely γ P :
    sat γ (<affine> P) ⊣⊢ <affine> sat γ P.
  Proof. by rewrite !bi.affine_affinely. Qed.

  Lemma sat_intuitionistically_1 γ P :
    sat γ (□ P) -∗ □ sat γ P.
  Proof.
    rewrite sat_affinely /bi_intuitionistically. f_equiv.
    apply sat_persistently_1.
  Qed.

  (** ** proof mode instances *)
  Global Instance sat_persistent γ P `{!Persistent P} : Persistent (sat γ P).
  Proof.
    rewrite /Persistent.
    iIntros "P". iApply sat_persistently_1.
    by iApply sat_mono.
  Qed.

  Global Instance sat_into_sep γ P Q : IntoSep (sat γ (P ∗ Q)) (sat γ P) (sat γ Q).
  Proof using Hdiscrete. by rewrite /IntoSep sat_sep. Qed.

  Global Instance sat_into_exist {A} γ (Φ : A → uPred M) name :
    AsIdentName Φ name →
    IntoExist (sat γ (∃ x, Φ x)) (λ x, sat γ (Φ x)) name | 1.
  Proof. move => ?. by rewrite /IntoExist sat_exist. Qed.

  Global Instance sat_into_pure γ Φ :
    IntoPure (sat γ ⌜Φ⌝) Φ.
  Proof. by rewrite /IntoPure sat_pure. Qed.

  (** ** rules for interacting with [sat] *)
  Lemma sat_alloc_open P :
    satisfiable P →
    ⊢ |==> ∃ γ, sat_open γ ∗ sat γ P.
  Proof using Hdiscrete.
    move => [x [/cmra_discrete_valid_iff Hvalid ?]].
    iMod (own_alloc (● x ⋅ ◯ x)) as (γ) "[Ha Hf]". { by apply auth_both_valid_discrete. }
    iModIntro. iExists _. iSplitL "Ha"; iExists _; by iFrame.
  Qed.

  Lemma sat_alloc_closed F :
    ⊢ |==> ∃ γ, sat_closed γ true F.
  Proof using Hdiscrete.
    iMod (own_alloc (● ε)) as (γ) "Ha". { by apply auth_auth_valid, ucmra_unit_valid. }
    iModIntro. iExists γ. iIntros (P [x [?%cmra_discrete_valid_iff ?]]).
    iMod (own_update with "Ha") as "[Ha Hf]".
    - apply auth_update_alloc. apply (op_local_update_discrete _ _ x).
      move => _. by rewrite right_id.
    - rewrite right_id. iModIntro. iSplitL "Ha"; iExists _; by iFrame.
  Qed.

  Lemma sat_switch γ P Q G :
    (P -∗ ∃ P', P' ∗ ⌜sat γ P' ∗ Q -∗ G⌝) →
    sat γ P ∗ Q -∗ G.
  Proof using Hdiscrete.
    iIntros (Himpl) "[Hsat HQ]".
    iDestruct (sat_mono with "Hsat") as "Hsat"; [done|].
    iDestruct "Hsat" as (P') "[Hsat1 %HG]".
    iApply HG. iFrame.
  Qed.

  Lemma sat_switch_sep γ P Q G1 G2 :
    (P -∗ ∃ P', G1 ∗ P' ∗ ⌜sat γ P' ∗ Q -∗ G2⌝) →
    sat γ P ∗ Q -∗ sat γ G1 ∗ G2.
  Proof using Hdiscrete.
    iIntros (Himpl). iApply sat_switch.
    iIntros "HP". iDestruct (Himpl with "HP") as (P') "[? [? %HG]]".
    iExists _. iSplit; [iAccu|iPureIntro].
    iIntros "[[??] ?]". iFrame. iApply HG. iFrame.
  Qed.

  Lemma sat_switch_bupd γ P Q G :
    (P ==∗ ∃ P', P' ∗ ⌜sat_open γ ∗ sat γ P' ∗ Q -∗ G⌝) →
    sat_open γ ∗ sat γ P ∗ Q ==∗ G.
  Proof using Hdiscrete.
    iIntros (Himpl) "[Hauth [Hsat HQ]]".
    iDestruct (sat_mono with "Hsat") as "Hsat"; [done|].
    iMod (sat_bupd with "Hauth Hsat") as "[Hauth Hsat]".
    iDestruct "Hsat" as (P') "[Hsat1 %HG]".
    iApply HG. by iFrame.
  Qed.

  Lemma sat_close γ P `{!∀ x : M, CoreCancelable x} :
    sat γ P -∗
    sat_open γ -∗
    ∃ F, ⌜satisfiable (P ∗ F)⌝ ∗ sat_closed γ false F.
  Proof using Hdiscrete.
    iIntros "[%m [%Hholds Hm]] [%a Ha]".
    iDestruct (own_valid_2 with "Ha Hm") as %[[f Heq] Hvalid]%auth_both_valid_discrete.
    setoid_subst.
    iExists (uPred_ownM (core m ⋅ f)). iSplit.
    - iPureIntro. eexists (m ⋅ core m ⋅ f).
      rewrite cmra_core_r. split; [by apply cmra_discrete_valid_iff|].
      uPred.unseal. eexists m, (core m ⋅ f). split_and!.
      + by rewrite assoc cmra_core_r.
      + done.
      + eexists ε. by rewrite right_id.
    - iIntros (P' [x [Hxvalid Hx]]).
      do [uPred.unseal] in Hx.
      destruct Hx as [a1 [a2 [Ha%discrete_iff [Ha1 [a2' Ha2']%cmra_discrete_included_r]]]].
      2, 3: apply _.
      iMod (own_update_2 _ _ _ (● x ⋅ ◯ (a1 ⋅ core m ⋅ a2')) with "Ha Hm") as "[Ha Hf]".
      + rewrite Ha Ha2'. apply auth_update.
        apply local_update_unital_discrete.
        move => z Hz Heq2. split.
        * rewrite -Ha2' -Ha. by apply/cmra_discrete_valid_iff.
        * efeed pose proof @core_cancelable as Heq; [done..|].
          rewrite cmra_pcore_core/= comm in Heq.
          rewrite Heq -!assoc. f_equiv.
          by rewrite (comm _ z) assoc.
      + iModIntro. iSplitL "Ha".
        * iExists _. iFrame.
        * iExists _. iFrame. iPureIntro.
          apply: uPred_mono; [done| |done].
          etrans; [|apply cmra_includedN_l].
          apply cmra_includedN_l.
  Qed.
End sat.
