From Paco Require Import paco.
From dimsum.core.itree Require Export upstream events small_itree.
From dimsum.core Require Export proof_techniques.
From dimsum.core Require Import axioms.

Export ITreeStdppNotations.

(* TODOs:
- Why do we need %itree so often? Why does Bind Scope itree_scope with itree. not work?
- Why does the destructuring pattern syntax print so weirdly?
 *)

(* important TODOs:
- define instances that lift ITreeTStep under bind
- add a step to clear_itree that simplifies using ITreeTStep
 *)

(** * Module semantics for spec *)

Inductive itree_step EV S : (SmallITree.itree (moduleE EV S) void * S) → option EV → ((SmallITree.itree (moduleE EV S) void * S) → Prop) → Prop :=
| ITauS t t' s:
  t ≡ ↓ᵢ (Tau t') →
  itree_step EV S (t, s) None (λ σ', σ' = (↓ᵢ t', s))
| IAngelicS T t t' s:
  t ≡ ↓ᵢ (Vis (inl1 (EAngelic T)) t') →
  itree_step EV S (t, s) None (λ σ', ∃ x, σ' = (↓ᵢ (t' x), s))
| IDemonicS T x t t' s:
  t ≡ ↓ᵢ (Vis (inl1 (EDemonic T)) t') →
  itree_step EV S (t, s) None (λ σ', σ' = (↓ᵢ (t' x), s))
| IVisS t t' s e:
  t ≡ ↓ᵢ (Vis (inr1 (inl1 (EVisible e))) t') →
  itree_step EV S (t, s) (Some e) (λ σ', σ' = (↓ᵢ (t' tt), s))
| IGetS t t' s:
  t ≡ ↓ᵢ (Vis (inr1 (inr1 EGetState)) t') →
  itree_step EV S (t, s) None (λ σ', σ' = (↓ᵢ (t' s), s))
| ISetS t t' s s':
  t ≡ ↓ᵢ (Vis (inr1 (inr1 (ESetState s'))) t') →
  itree_step EV S (t, s) None (λ σ', σ' = (↓ᵢ (t' tt), s'))
| IYieldS t t' s:
  t ≡ ↓ᵢ (Vis (inr1 (inr1 EYield)) t') →
  itree_step EV S (t, s) None (λ σ', σ' = (↓ᵢ (t' tt), s))
.

Definition itree_trans EV S := ModTrans (itree_step EV S).

Global Instance itree_vis_no_all EV S: VisNoAng (itree_trans EV S).
Proof. move => *. inv_all @m_step; naive_solver. Qed.

Definition itree_mod {EV S} (t : itree (moduleE EV S) void) (s : S) :=
  Mod (itree_trans EV S) (↓ᵢ t, s).

(** * Proper instances *)
Lemma itree_step_mono {EV S} σ1 σ2 e Pσ :
  itree_step EV S σ1 e Pσ →
  σ1.1 ≡ σ2.1 →
  σ1.2 = σ2.2 →
  itree_step EV S σ2 e Pσ.
Proof.
  destruct σ1, σ2 => /= Hs Heq ?.
  inv Hs. all: by econs; rewrite -Heq.
Qed.

(* Lemma supseteq_to_thas_trace EV S t1 t2 σ : *)
(*   t1 ⊒ t2 → *)
(*   (t1, σ) ~{ itree_trans EV S, tnil }~>ₜ (λ σ1, *)
(*   ∀ e Pσ2, m_step (itree_trans EV S) (t2, σ) e Pσ2 → ∃ Pσ1, *)
(*         m_step (itree_trans EV S) σ1 e Pσ1 ∧ *)
(*           (∀ σ1', Pσ1 σ1' → ∃ σ2, Pσ2 σ2 ∧ σ1'.1 ⊒ σ2.1 ∧ σ1'.2 = σ2.2)). *)
(* Proof. *)
(*   unfold sqsupseteq, SmallITree.SmallITree_supseteq. *)
(*   move => Hsup. *)
(*   have : ↑ᵢ t2 ≅ ↑ᵢ t2 by []. *)
(*   have : ↑ᵢ t1 ≅ ↑ᵢ t1 by []. *)
(*   move: Hsup. move: {1 2}(↑ᵢ t1) => t1'. move: {1 2}(↑ᵢ t2) => t2'. *)
(*   move => Hsup. punfold Hsup. unfold eqit_ in Hsup. *)
(*   rewrite (itree_eta t1') (itree_eta t2'). *)
(*   elim: Hsup t1 t2 => //. *)
(*   - move => t1 t2 [Hp|//] ?? Ht1 Ht2. *)
(*     tend => /= ?? ?. inv_all itree_step; simplify_eq/=; setoid_subst. *)
(*     all: rewrite SmallITree.from_to_itree in Ht2. *)
(*     all: move: Ht2 => /moduleE_eq_itree_inv//= Heq. *)
(*     eexists _. split. { econstructor. unfold equiv, SmallITree.SmallITree_equiv. rewrite -Ht1. *)
(*                         rewrite SmallITree.from_to_itree. done. } *)
(*     move => /= ? ->. split!. *)
(*     rewrite !SmallITree.from_to_itree -Heq. *)
(*     punfold Hp. *)
(*     pfold. *)
(*     eapply eqit__mono; [|done|]. move => ?. naive_solver. done. *)
(*   - move => /=. admit. *)
(*   - move => t1 t2 _ ? IH ?? Ht1 Ht2. *)
(*     tstep. { econstructor. unfold equiv, SmallITree.SmallITree_equiv. rewrite -Ht1. *)
(*                         rewrite SmallITree.from_to_itree. done. } *)
(*     2: simpl; done. *)
(*     move => ? /= ->. apply: IH; [|done..]. rewrite SmallITree.from_to_itree. by rewrite -itree_eta. *)
(* Admitted. *)

Definition steps_impl_itree_equiv_rel {EV S} :
  relation (bool → option EV → ((SmallITree.itree (moduleE EV S) void * S → Prop) → Prop)) := λ Pσ Pσ',
  ∀ (b b' : bool) κ (P1 P2 : _ → Prop),
    (∀ t s, P1 (t, s) → ∃ t', t' ⊒ t ∧ P2 (t', s)) →
    (b → b') →
    Pσ b κ P1 → Pσ' b' κ P2.

Lemma steps_impl_itree_equiv_mono {EV S} t' σ (Pσ Pσ' : _ → _ → _ → Prop) :
  steps_impl_itree_equiv_rel Pσ Pσ' →
  σ -{ itree_trans EV S }-> Pσ →
  t' ⊒ σ.1 →
  (t', σ.2) -{ itree_trans EV S }-> Pσ'.
Proof.
  (* TODO: clean up this horrible proof *)
  move => HP Ht Heq.
  elim/@prop_least_fixpoint_pair_ind_wf: Ht t' Pσ' Heq HP => {}σ {}Pσ IHn t' {}Pσ' Heq HP.
  destruct σ as [t s]; simpl in *.
  punfold Heq. unfold eqit_ in Heq at 1.
  move: Heq. move Hot: (observe (↑ᵢ t)) => ot. move Hot': (observe (↑ᵢ t')) => ot' Heq.
  move: Hot'. have : (↑ᵢ t') ≅ (↑ᵢ t') by [].
  move: {1 3}(↑ᵢ t') => ti Hti Hot'.
  elim: Heq t t' ti s Pσ' Pσ HP IHn Hot Hot' Hti.
  - done.
  - move => m1 m2 [REL|//] t t' ti s Pσ' Pσ HP IHn Hot Hot' Hti.
    rewrite -/(eqit _ _ _) -/(euttge _ _ _) in REL.
    move: IHn => [?| {}IHn]; simplify_eq.
    + apply: steps_impl_end. eapply HP; [|done..]. move => t1 ? [? ?]. subst. eexists _. split; [|done].
      rewrite -SmallITree.euttge_to_itree -Hti (itree_eta (↑ᵢ t1)) Hot (itree_eta ti) Hot'.
      by apply eqit_Tau.
    + apply: steps_impl_step => ???. inv_all @m_step.
      all: revert select (_ ≡ _);
        rewrite -SmallITree.eqit_to_itree SmallITree.from_to_itree -Hti (itree_eta ti) Hot';
        move => /moduleE_eq_itree_inv //= Heq.
      exploit IHn.
      { by econs; rewrite -SmallITree.eqit_to_itree (itree_eta (↑ᵢ t)) Hot SmallITree.from_to_itree. }
      move => [?|[?[?[? Hfix]]]]; simplify_eq.
      * left. eapply HP; [|done..]. move => /= ???. simplify_eq. split!. by rewrite -Heq REL.
      * right. eexists _. split_and!; [done..|].
        move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|/=IH ?].
        { apply wf_pred_mono. apply (steps_impl_rec_mono (itree_trans _ _)). }
        apply IH => //=. { by rewrite -Heq REL. } unfold steps_impl_itree_equiv_rel in *. naive_solver.
  - move => u e k1 k2 Hu t t' ti s Pσ' Pσ HP IHn Hot Hot' Hti.
    move: IHn => [?|{}IHn]. {
      apply: steps_impl_end. eapply HP; [|done..]. move => t1 ? [? ?]. subst. eexists _. split; [|done].
      rewrite -SmallITree.euttge_to_itree -Hti (itree_eta (↑ᵢ t1)) Hot (itree_eta ti) Hot'.
      apply eqit_Vis => v. move: (Hu v) => [|//]. done.
    }
    apply: steps_impl_step => ???.
    inv_all @m_step.
    all: revert select (_ ≡ _);
      rewrite -SmallITree.eqit_to_itree SmallITree.from_to_itree -Hti (itree_eta ti) Hot';
      move => /moduleE_eq_itree_inv //= Heq.
    all: repeat case_match => //; destruct!/=.
    + exploit IHn.
      { by econs; rewrite -SmallITree.eqit_to_itree (itree_eta (↑ᵢ t)) Hot SmallITree.from_to_itree. }
      move => [?|[?[?[? Hfix]]]]; destruct!/=.
      * left. eapply HP; [|done..]. move => t1 ? [? ?]. simplify_eq. split!.
        rewrite SmallITree.supseteq_from_itree -Heq. exploit Hu => -[//|//].
      * right. move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_impl_rec_mono (itree_trans _ _)). }
        split!. apply: IH => /=. 2: unfold steps_impl_itree_equiv_rel in *; naive_solver.
        rewrite SmallITree.supseteq_from_itree -Heq. exploit Hu => -[//|//].
    + exploit IHn.
      { by econs; rewrite -SmallITree.eqit_to_itree (itree_eta (↑ᵢ t)) Hot SmallITree.from_to_itree. }
      move => [?|[?[?[? Hfix]]]]; destruct!/=.
      * left. eapply HP; [|done..]. move => t1 ? [? ?]. simplify_eq. split!.
        rewrite SmallITree.supseteq_from_itree -Heq. exploit Hu => -[//|//].
      * right. move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_impl_rec_mono (itree_trans _ _)). }
        split!. apply: IH => /=. 2: unfold steps_impl_itree_equiv_rel in *; naive_solver.
        rewrite SmallITree.supseteq_from_itree -Heq. exploit Hu => -[//|//].
    + exploit IHn.
      { by econs; rewrite -SmallITree.eqit_to_itree (itree_eta (↑ᵢ t)) Hot SmallITree.from_to_itree. }
      move => [?|[?[?[? Hfix]]]]; destruct!/=.
      left. eapply HP; [|done..]. move => t1 ? [? ?]. simplify_eq. split!.
      rewrite SmallITree.supseteq_from_itree. revert select (_ ≅ _) => <-.
      exploit Hu => -[//|//].
    + exploit IHn.
      { by econs; rewrite -SmallITree.eqit_to_itree (itree_eta (↑ᵢ t)) Hot SmallITree.from_to_itree. }
      move => [?|[?[?[? Hfix]]]]; destruct!/=.
      * left. eapply HP; [|done..]. move => t1 ? [? ?]. simplify_eq. split!.
        rewrite SmallITree.supseteq_from_itree -Heq. exploit Hu => -[//|//].
      * right. move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_impl_rec_mono (itree_trans _ _)). }
        split!. apply: IH => /=. 2: unfold steps_impl_itree_equiv_rel in *; naive_solver.
        rewrite SmallITree.supseteq_from_itree -Heq. exploit Hu => -[//|//].
    + exploit IHn.
      { by econs; rewrite -SmallITree.eqit_to_itree (itree_eta (↑ᵢ t)) Hot SmallITree.from_to_itree. }
      revert select (_ ≅ _) => Heq.
      move => [?|[?[?[? Hfix]]]]; destruct!/=.
      * left. eapply HP; [|done..]. move => t1 ? [? ?]. simplify_eq. split!.
        rewrite SmallITree.supseteq_from_itree -Heq. exploit Hu => -[//|//].
      * right. move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_impl_rec_mono (itree_trans _ _)). }
        split!. apply: IH => /=. 2: unfold steps_impl_itree_equiv_rel in *; naive_solver.
        rewrite SmallITree.supseteq_from_itree -Heq. exploit Hu => -[//|//].
    + exploit IHn.
      { by econs; rewrite -SmallITree.eqit_to_itree (itree_eta (↑ᵢ t)) Hot SmallITree.from_to_itree. }
      revert select (_ ≅ _) => Heq.
      move => [?|[?[?[? Hfix]]]]; destruct!/=.
      * left. eapply HP; [|done..]. move => t1 ? [? ?]. simplify_eq. split!.
        rewrite SmallITree.supseteq_from_itree -Heq. exploit Hu => -[//|//].
      * right. move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_impl_rec_mono (itree_trans _ _)). }
        split!. apply: IH => /=. 2: unfold steps_impl_itree_equiv_rel in *; naive_solver.
        rewrite SmallITree.supseteq_from_itree -Heq. exploit Hu => -[//|//].
  - move => t1 ot2 ? REL IH t t' ti s Pσ' Pσ HP IHn Hot Hot' Hti.
    move: REL => /fold_eqitF REL. specialize (REL _ _ ltac:(done) ltac:(done)). simplify_eq.
    apply: steps_impl_step => ???. inv_all @m_step.
    all: revert select (_ ≡ _);
      rewrite -SmallITree.eqit_to_itree SmallITree.from_to_itree -Hti (itree_eta ti) Hot';
      move => /moduleE_eq_itree_inv //= Heq.
    right. split!. apply: IH. 2: done.
    + move => *. apply: HP; [..|done]; naive_solver.
    + done.
    + done.
    + by rewrite SmallITree.from_to_itree.
  - done.
Qed.

Global Instance steps_impl_itree_proper EV S :
  Proper ((prod_relation (flip (⊒)) (=)) ==> steps_impl_itree_equiv_rel ==> impl) (steps_impl (itree_trans EV S)).
Proof. move => [??] [??] [/= Heq ->] ?? Hf ?. by apply: (steps_impl_itree_equiv_mono _ (_, _)). Qed.

Global Instance steps_impl_itree_proper_flip EV S :
  Proper ((prod_relation (⊒) (=)) ==> flip steps_impl_itree_equiv_rel ==> flip impl) (steps_impl (itree_trans EV S)).
Proof.
  move => [??] [??] [/= Heq ->] ?? Hf ?. apply: (steps_impl_itree_equiv_mono _ (_, _)); [done..|]. done.
Qed.

Lemma steps_spec_itree_equiv_mono {EV S} t' σ κ Pσ Pσ' :
  (prod_relation (flip (⊒)) (=) ==> impl)%signature Pσ Pσ' →
  σ -{ itree_trans EV S, κ }->ₛ Pσ →
  t' ⊒ σ.1 →
  (t', σ.2) -{ itree_trans EV S, κ }->ₛ Pσ'.
Proof.
  (* TODO: clean up this horrible proof *)
  move => HP Ht Heq.
  elim/@prop_least_fixpoint_ind_wf: Ht t' Heq => {}σ IHn t' Heq.
  destruct σ as [t s]; simpl in *.
  punfold Heq. unfold eqit_ in Heq at 1.
  move: Heq. move Hot: (observe (↑ᵢ t)) => ot. move Hot': (observe (↑ᵢ t')) => ot' Heq.
  move: Hot'. have : (↑ᵢ t') ≅ (↑ᵢ t') by [].
  move: {1 3}(↑ᵢ t') => ti Hti Hot'.
  elim: Heq t t' ti s IHn Hot Hot' Hti.
  - done.
  - move => m1 m2 [REL|//] t t' ti s IHn Hot Hot' Hti. rewrite -/(eqit _ _ _) -/(euttge _ _ _) in REL.
    move: IHn => [[??]|[?[?[? [? Ht]]]]]; simplify_eq.
    + apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=.
      rewrite -SmallITree.euttge_to_itree (itree_eta (↑ᵢ t)) Hot -Hti (itree_eta ti) Hot'.
      by apply eqit_Tau.
    + inv_all @m_step.
      all: revert select (_ ≡ _);
        rewrite -SmallITree.eqit_to_itree SmallITree.from_to_itree (itree_eta (↑ᵢ t)) Hot;
        move => /moduleE_eq_itree_inv //= Heq.
      exploit Ht; [done|] => -[[??]|[? Hfix]]; simplify_eq.
      * apply: steps_spec_step_end.
        { by econs; rewrite -SmallITree.eqit_to_itree -Hti (itree_eta ti) Hot' SmallITree.from_to_itree. }
        move => ? ->. eapply HP; [|done]. split; [|done] => /=.
        by rewrite SmallITree.supseteq_from_itree -Heq.
      * apply: steps_spec_step.
        { by econs; rewrite -SmallITree.eqit_to_itree -Hti (itree_eta ti) Hot' SmallITree.from_to_itree. }
        move => ? ->. move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_spec_rec_mono (itree_trans _ _)). }
        apply: IH => /=. by rewrite SmallITree.supseteq_from_itree -Heq.
  - move => u e k1 k2 Hu t t' ti s IHn Hot Hot' Hti.
    move: IHn => [[??]|[?[?[? [? Ht]]]]]. {
      subst. apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=.
      rewrite -SmallITree.euttge_to_itree (itree_eta (↑ᵢ t)) Hot -Hti (itree_eta ti) Hot'.
      apply eqit_Vis => v. move: (Hu v) => [|//]. done.
    }
    inv_all @m_step.
    all: revert select (_ ≡ _);
      rewrite -SmallITree.eqit_to_itree SmallITree.from_to_itree (itree_eta (↑ᵢ t)) Hot;
      move => /moduleE_eq_itree_inv //= Heq.
    all: repeat case_match => //; destruct!/=.
    + apply: steps_spec_step.
      { by econs; rewrite -SmallITree.eqit_to_itree -Hti (itree_eta ti) Hot' SmallITree.from_to_itree. }
      move => ? /= [x ->].
      exploit Ht; [split!|].
      move => -[[??]|[? Hfix]]; subst.
      * apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=.
        rewrite SmallITree.supseteq_from_itree -Heq.
        move: (Hu x) => [|//]. done.
      * move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_spec_rec_mono (itree_trans _ _)). }
        apply: IH => /=. rewrite SmallITree.supseteq_from_itree -Heq.
        move: (Hu x) => [|//]. done.
    + apply: steps_spec_step.
      { by econs; rewrite -SmallITree.eqit_to_itree -Hti (itree_eta ti) Hot' SmallITree.from_to_itree. }
      move => ? /= ?.
      exploit Ht; [split!|].
      move => -[[??]|[? Hfix]]; subst.
      * apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=.
        rewrite SmallITree.supseteq_from_itree -Heq.
        move: (Hu x) => [|//]. done.
      * move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_spec_rec_mono (itree_trans _ _)). }
        apply: IH => /=. rewrite SmallITree.supseteq_from_itree -Heq.
        move: (Hu x) => [|//]. done.
    + apply: steps_spec_step_end.
      { by econs; rewrite -SmallITree.eqit_to_itree -Hti (itree_eta ti) Hot' SmallITree.from_to_itree. }
      revert select (_ ≅ _) => Heq.
      move => ? /= ?. exploit Ht; [split!|].
      move => -[[??]|[? Hfix]]; simplify_eq.
      eapply HP; [|done]. split; [|done] => /=.
      rewrite SmallITree.supseteq_from_itree -Heq.
      move: (Hu tt) => [|//]. done.
    + apply: steps_spec_step.
      { by econs; rewrite -SmallITree.eqit_to_itree -Hti (itree_eta ti) Hot' SmallITree.from_to_itree. }
      move => ? /= ?.
      exploit Ht; [split!|].
      move => -[[??]|[? Hfix]]; subst.
      * apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=.
        rewrite SmallITree.supseteq_from_itree -Heq.
        move: (Hu s) => [|//]. done.
      * move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_spec_rec_mono (itree_trans _ _)). }
        apply: IH => /=. rewrite SmallITree.supseteq_from_itree -Heq.
        move: (Hu s) => [|//]. done.
    + apply: steps_spec_step.
      { by econs; rewrite -SmallITree.eqit_to_itree -Hti (itree_eta ti) Hot' SmallITree.from_to_itree. }
      revert select (_ ≅ _) => Heq.
      move => ? /= ?.
      exploit Ht; [split!|].
      move => -[[??]|[? Hfix]]; subst.
      * apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=.
        rewrite SmallITree.supseteq_from_itree -Heq.
        move: (Hu tt) => [|//]. done.
      * move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_spec_rec_mono (itree_trans _ _)). }
        apply: IH => /=. rewrite SmallITree.supseteq_from_itree -Heq.
        move: (Hu tt) => [|//]. done.
    + apply: steps_spec_step.
      { by econs; rewrite -SmallITree.eqit_to_itree -Hti (itree_eta ti) Hot' SmallITree.from_to_itree. }
      revert select (_ ≅ _) => Heq.
      move => ? /= ?.
      exploit Ht; [split!|].
      move => -[[??]|[? Hfix]]; subst.
      * apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=.
        rewrite SmallITree.supseteq_from_itree -Heq.
        move: (Hu tt) => [|//]. done.
      * move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_spec_rec_mono (itree_trans _ _)). }
        apply: IH => /=. rewrite SmallITree.supseteq_from_itree -Heq.
        move: (Hu tt) => [|//]. done.
  - move => t1 ot2 ? REL IH t t' ti s IHn Hot Hot' Hti.
    move: REL => /fold_eqitF REL. specialize (REL _ _ ltac:(done) ltac:(done)).
    apply: steps_spec_step.
    { by econs; rewrite -SmallITree.eqit_to_itree -Hti (itree_eta ti) Hot' SmallITree.from_to_itree. }
    move => /= ??. simplify_eq.
    apply: IH.
    + done.
    + done.
    + done.
    + by rewrite SmallITree.from_to_itree.
  - done.
Qed.

Global Instance steps_spec_itree_proper EV S :
  Proper ((prod_relation (flip (⊒)) (=)) ==> (=) ==> (prod_relation (flip (⊒)) (=) ==> impl) ==> impl) (steps_spec (itree_trans EV S)).
Proof.
  move => [??] [??] [/= Heq ->] ?? -> ?? Hf ?.
  apply: (steps_spec_itree_equiv_mono _ (_, _)); [done| done |done].
Qed.

Global Instance steps_spec_itree_proper_flip EV S :
  Proper ((prod_relation (⊒) (=)) ==> (=) ==> ((prod_relation (⊒) (=) ==> flip impl)) ==> flip impl) (steps_spec (itree_trans EV S)).
Proof.
  move => [??] [??] [/= Heq ->] ?? -> ?? Hf ?.
  apply: (steps_spec_itree_equiv_mono _ (_, _)); [ | done |done].
  move => ?? [??]. apply Hf. by split.
Qed.

(* The following lemmas should not be necessary. *)
(*
Lemma tnhas_trace_itree_equiv_mono {EV S} t t' s κs Pσ Pσ' n:
  (prod_relation (≡) (=) ==> impl)%signature Pσ Pσ' →
  (t, s) ~{ itree_trans EV S, κs, n }~>ₜ Pσ →
  t ≡ t' →
  (t', s) ~{ itree_trans EV S, κs, n }~>ₜ Pσ'.
Proof.
  move => HP /tnhas_trace_inv Ht Heq.
  apply: tnhas_trace_under_tall; [done..|] => /= ? [[??]|[?[?[?[?[?[?[??]]]]]]]].
  { tend. apply: HP; [|done]. by split. }
  tstep; [| |done..]. { by apply: itree_step_mono. }
  move => ??. apply: tnhas_trace_mono; [by eauto|done|done|].
  move => ??. by apply: HP.
Qed.

Global Instance tnhas_trace_itree_proper EV S :
  Proper ((prod_relation (≡) (=)) ==> (=) ==> (=) ==> (prod_relation (≡) (=) ==> iff) ==> iff) (tnhas_trace (itree_trans EV S)).
Proof.
  move => [??] [??] [/= Heq ->] ?? -> ?? -> ?? Hf.
  split => ?.
  all: apply: tnhas_trace_itree_equiv_mono; [try done| done |].
  - move => ????. by eapply Hf.
  - done.
  - move => [??] [??] [/=? ->] ?. eapply Hf; [|done]. split; [|done] => /=.
    apply eqit_flip. by apply: eqit_mon; [..|done].
  - apply eqit_flip. by apply: eqit_mon; [..|done].
Qed.

Lemma thas_trace_itree_equiv_mono {EV S} t t' s κs Pσ Pσ' :
  (prod_relation (≡) (=) ==> impl)%signature Pσ Pσ' →
  (t, s) ~{ itree_trans EV S, κs }~>ₜ Pσ →
  t ≡ t' →
  (t', s) ~{ itree_trans EV S, κs }~>ₜ Pσ'.
Proof.
  move => HP /thas_trace_inv Ht Heq.
  apply: thas_trace_under_tall; [done..|] => /= ? [[??]|[?[?[?[?[??]]]]]].
  { tend. apply: HP; [|done]. by split. }
  tstep; [| |done..]. { by apply: itree_step_mono. }
  move => ??. apply: thas_trace_mono; [naive_solver|done|].
  move => ??. by apply: HP.
Qed.

Global Instance itree_trans_proper EV S :
  Proper ((prod_relation (≡) (=)) ==> (=) ==> (prod_relation (≡) (=) ==> iff) ==> iff) (thas_trace (itree_trans EV S)).
Proof.
  move => [??] [??] [/= Heq ->] ?? -> ?? Hf.
  split => ?.
  all: apply: thas_trace_itree_equiv_mono; [try done| done |].
  - move => ????. by eapply Hf.
  - done.
  - move => [??] [??] [/=? ->] ?. eapply Hf; [|done]. split; [|done] => /=.
    apply eqit_flip. by apply: eqit_mon; [..|done].
  - apply eqit_flip. by apply: eqit_mon; [..|done].
Qed.
*)

Definition itree_mod_rel {E R S} (P : SmallITree.itree E R * S → Prop) (t : SmallITree.itree E R * S) : Prop :=
  ∀ t', t' ⊒ t.1 → P (t', t.2).

Global Instance itree_mod_rel_proper EV R S P :
  Proper ((prod_relation (flip (⊒)) (=) ==> impl)) (@itree_mod_rel EV R S P).
Proof.
  move => [x ?] [y ?] [Heq ?]. simplify_eq/=. rewrite /itree_mod_rel /=.
  move => ??. rewrite Heq. naive_solver.
Qed.
Global Instance itree_mod_rel_proper_flip EV R S P :
  Proper ((prod_relation (⊒) (=) ==> flip impl)) (@itree_mod_rel EV R S P).
Proof.
  move => [x ?] [y ?] [Heq ?]. simplify_eq/=. rewrite /itree_mod_rel /=.
  move => ??. rewrite Heq. naive_solver.
Qed.
Global Typeclasses Opaque itree_mod_rel.

Lemma itree_mod_rel_intro EV S σ κs P:
  σ ~{itree_trans EV S, κs }~>ₜ itree_mod_rel P →
  σ ~{itree_trans EV S, κs }~>ₜ P.
Proof. move => Ht. apply: thas_trace_mono; [done|done|] => -[??] Hp. by apply: Hp. Qed.

Lemma itree_mod_rel_spec_intro EV S σ κ P:
  σ -{itree_trans EV S, κ }->ₛ itree_mod_rel P →
  σ -{itree_trans EV S, κ }->ₛ P.
Proof. move => ?. apply: steps_spec_mono; [done|]. move => -[??] Hp. by apply Hp. Qed.

Definition itree_mod_impl_rel {EV S} (P : bool → option EV → (SmallITree.itree (moduleE EV S) void * S → Prop) → Prop) :
  bool → option EV → (SmallITree.itree (moduleE EV S) void * S → Prop) → Prop :=
  λ b κ Pσ, ∀ (b' : bool) (Pσ' : _ → Prop),
      (∀ t s, Pσ (t, s) → ∃ t', t' ⊒ t ∧ Pσ' (t', s)) →
      (b → b') →
      P b' κ Pσ'.

Global Instance itree_mod_impl_rel_proper EV S P :
  Proper (steps_impl_itree_equiv_rel) (@itree_mod_impl_rel EV S P).
Proof.
  move => ????? HP1 ? REL ?? HPσ' ?. apply: REL. 2: naive_solver.
  move => ?? /HP1 [? [Ht /HPσ'[?[??]]]]. eexists _. split; [|done]. etrans; [|done].
  by apply: eqit_mon; [..|done].
Qed.
Global Typeclasses Opaque itree_mod_impl_rel.

Lemma itree_mod_impl_rel_intro EV S σ P:
  σ -{itree_trans EV S }-> itree_mod_impl_rel P →
  σ -{itree_trans EV S }-> P.
Proof. move => ?. apply: steps_impl_mono; [done|]. move => ??? Hp. apply Hp; [|done]. naive_solver. Qed.

Ltac clear_itree :=
  try match goal with | |- itree_mod_rel _ _ => move => ?/=? end;
  repeat match goal with
         | H : ?t ⊒@{SmallITree.itree _ _} _ |- _ => clear H; clear t
         | H1 : ?t ⊒@{SmallITree.itree _ _} ?t', H2: ?t' ⊒@{SmallITree.itree _ _} _ |- _ => rewrite -H1 in H2; clear H1; clear t'
         end.

(** * tsim *)
(* The following lemmas should not be necessary. *)
(*
Global Instance tsim_itree_l_proper EV S m1 n b:
  Proper ((prod_relation (≡) (=)) ==> (=) ==> (=) ==> iff) (tsim n b (itree_trans EV S) m1).
Proof.
  move => [??] [??] [/=Heq ->] ?? -> ?? ->.
  split => Hsim ????; (eapply Hsim; [done|]). { by rewrite Heq. } { by rewrite -Heq. }
Qed.

Global Instance tsim_itree_r_proper EV S m1 n b:
  Proper ((=) ==> (=) ==> (prod_relation (≡) (=)) ==> iff) (tsim n b m1 (itree_trans EV S)).
Proof.
  move => ?? -> ?? -> [??] [??] [/=Heq ->].
  split => Hsim ????. { rewrite -Heq. by eapply Hsim. } { rewrite Heq. by eapply Hsim. }
Qed.
*)

(** * tstep *)
(** ** typeclasses and infrastructure *)
Class ITreeModEq {E R} (t : SmallITree.itree E R) (t' : itree E R) := {
  itree_mod_eq_proof : t ⊒ ↓ᵢ t'
}.
Global Hint Mode ITreeModEq + + ! - : typeclass_instances.
Lemma ITreeModEq_refl {E R} (t : itree E R) :
  ITreeModEq (↓ᵢ t) t.
Proof. done. Qed.

Global Hint Extern 5 (ITreeModEq ?t _) => (assert_fails (is_var t); by apply ITreeModEq_refl) : typeclass_instances.
Global Hint Extern 10 (ITreeModEq _ _) => (constructor; eassumption) : typeclass_instances.

Class ITreeTStep {E R} (cont : bool) (t t' : itree E R) := {
  itree_tstep_proof : t ≳ t'
}.
Global Hint Mode ITreeTStep + + + ! - : typeclass_instances.

Class ITreeTStepS {EV S} (t : itree (moduleE EV S) void) (s : S) (κ : option EV)
  (P : (itree (moduleE EV S) void → S → Prop) → Prop) := {
    itree_tsteps_proof G:
    P (λ t' s', itree_mod_rel G (↓ᵢ t', s')) →
    (↓ᵢ t, s) -{ itree_trans EV S, κ }->ₛ itree_mod_rel G
}.
Global Hint Mode ITreeTStepS + + ! ! - - : typeclass_instances.

Lemma itree_step_s_itree_step_cont EV S t t' (s : S) (κ : option EV) P `{!ITreeTStep true t t'}
      `{!ITreeTStepS t' s κ P} :
  ITreeTStepS t s κ P.
Proof. constructor => ??. move: ITreeTStep0 => [->]. by apply itree_tsteps_proof. Qed.
Global Hint Resolve itree_step_s_itree_step_cont | 50 : typeclass_instances.

Lemma itree_step_s_itree_step_no_cont EV S t t' (s : S) `{!ITreeTStep false t t'}:
  ITreeTStepS t s (@None EV) (λ G, G t' s).
Proof. constructor => ??. move: ITreeTStep0 => [->]. by apply steps_spec_end. Qed.
Global Hint Resolve itree_step_s_itree_step_no_cont | 100 : typeclass_instances.

Lemma itree_tstep_s {EV S} s t t' κ `{!ITreeModEq t t'} `{!ITreeTStepS t' s κ P}:
  TStepS (itree_trans EV S) (t, s) (λ G, G κ (λ G', P (λ t'' s', itree_mod_rel G' (↓ᵢ t'', s')))).
Proof.
  constructor => G HG. eexists _, _. split; [done|] => ? /= ?.
  apply itree_mod_rel_spec_intro. move: ITreeModEq0 => [->]. by apply: itree_tsteps_proof.
Qed.
Global Hint Resolve itree_tstep_s : typeclass_instances.

Class ITreeTStepI {EV S} (t : itree (moduleE EV S) void) (s : S)
      (P : (bool → option EV → ((itree (moduleE EV S) void → S → Prop) → Prop) → Prop) → Prop) := {
    itree_tstepi_proof G:
    P G →
    (↓ᵢ t, s) -{ itree_trans EV S }-> (λ b κ Pσ, ∃ (b' : bool) P', G b' κ P' ∧ (b' → b) ∧ ∀ G', P' G' → ∃ t t' s, Pσ (t, s) ∧ t ⊒ ↓ᵢ t' ∧ G' t' s)
}.
Global Hint Mode ITreeTStepI + + ! ! - : typeclass_instances.

Lemma itree_step_i_itree_step_cont EV S t t' (s : S) P `{!ITreeTStep true t t'}
      `{!ITreeTStepI t' s P} :
  ITreeTStepI (EV:=EV) t s P.
Proof.
  constructor => ??. apply itree_mod_impl_rel_intro.
  move: ITreeTStep0 => [->].
  apply: steps_impl_mono; [by apply itree_tstepi_proof|].
  move => /= * ?? HP ?. destruct!. eexists _, _. split_and!; [done|naive_solver|].
  move => ? /H2[?[?[? [/HP[?[??]] [? HG]]]]]. eexists _, _, _. split_and!; [done| |done].
  by etrans.
Qed.
Global Hint Resolve itree_step_i_itree_step_cont | 50 : typeclass_instances.

Lemma itree_step_i_itree_step_no_cont EV S t t' (s : S) `{!ITreeTStep false t t'} :
  ITreeTStepI (EV:=EV) t s (λ G, G false None (λ G', G' t' s)).
Proof.
  constructor => ??. apply steps_impl_end. eexists _, _. split_and!; [done..|].
  move => /=??. eexists _, _, _. split_and!; [done| |done].
  by rewrite [t]itree_tstep_proof.
Qed.
Global Hint Resolve itree_step_i_itree_step_no_cont | 100 : typeclass_instances.

Lemma itree_tstep_i {EV S} s t t' `{!ITreeModEq t t'} `{!ITreeTStepI t' s P}:
  TStepI (itree_trans EV S) (t, s) (λ G, P (λ b κ P', G b κ (λ G', P' (λ t'' s', itree_mod_rel G' (↓ᵢ t'', s'))))).
Proof.
  constructor => ??. apply itree_mod_impl_rel_intro.
  move: ITreeModEq0 => [->].
  apply: steps_impl_mono; [by apply itree_tstepi_proof|].
  move => /= * ?? HP ?. destruct!. eexists _, _. split_and!; [done|naive_solver|].
  move => ? /H2[?[?[? [/HP[?[??]] [? HG]]]]]. eexists (_, _). split; [done|].
  apply HG. by etrans.
Qed.
Global Hint Resolve itree_tstep_i : typeclass_instances.

(** ** instances *)
(** *** ITreeTStep *)
Lemma itree_tstep_bind {E} A B C (h : _ → itree _ C) (k : A → itree E B) (t : itree E A) cont :
  ITreeTStep cont (ITree.bind (ITree.bind t k) h) (ITree.bind t (fun r => ITree.bind (k r) h)).
Proof. constructor. by rewrite bind_bind. Qed.
Global Hint Resolve itree_tstep_bind | 50 : typeclass_instances.

Lemma itree_tstep_bind_rec {E} A C (h : _ → itree _ C) (t t' : itree E A) cont :
  ITreeTStep cont t t' →
  ITreeTStep cont (ITree.bind t h) (ITree.bind t' h).
Proof. move => [Hstep]. constructor. by rewrite Hstep. Qed.
Global Hint Resolve itree_tstep_bind_rec | 10 : typeclass_instances.

Lemma itree_tstep_bind_tau {E R} A h (x : itree _ A) cont:
  ITreeTStep (E:=E) (R:=R) cont (ITree.bind (Tau x) h) (Tau (ITree.bind x h)).
Proof. constructor. by rewrite unfold_bind. Qed.
Global Hint Resolve itree_tstep_bind_tau : typeclass_instances.

Lemma itree_tstep_ret {E R} A h (x : A) cont:
  ITreeTStep (E:=E) (R:=R) cont (ITree.bind (Ret x) h) (h x).
Proof. constructor. by rewrite unfold_bind. Qed.
Global Hint Resolve itree_tstep_ret : typeclass_instances.

Lemma itree_tstep_interp_ret {E} {R A B} f x cont :
  ITreeTStep (E:=E) (R:=R) cont (interp (recursive' (A:=A) (B:=B) f) (Ret x)) (Ret x).
Proof. constructor. by rewrite interp_ret. Qed.
Global Hint Resolve itree_tstep_interp_ret : typeclass_instances.

Lemma itree_tstep_interp_bind {E} {R S A B} f g1 (g2 : S → _) cont:
  ITreeTStep (E:=E) (R:=R) cont
    (interp (recursive' (A:=A) (B:=B) f) (ITree.bind g1 g2))
    (ITree.bind (interp (recursive' f) g1) (λ x,
         interp (recursive' f) (g2 x))).
Proof. constructor. by rewrite interp_bind. Qed.
Global Hint Resolve itree_tstep_interp_bind : typeclass_instances.

Lemma itree_tstep_interp_rec_call {E} {A B} f x:
  ITreeTStep (E:=E) false
    (interp (recursive' (A:=A) (B:=B) f) (call x))
    (Tau (rec' f x)).
Proof.
  constructor. rewrite interp_recursive'_call_eq.
  do 2 f_equiv. setoid_rewrite tau_euttge. by rewrite bind_ret_r.
Qed.
Global Hint Resolve itree_tstep_interp_rec_call : typeclass_instances.

Lemma itree_tstep_interp_rec_inr {E} {R A B} f (g : itree (callE A B +' E) _)
  (g' : itree E R) cont :
  ITreeToTranslate g _ g' →
  ITreeTStep (E:=E) cont (interp (recursive' (A:=A) (B:=B) f) g) g'.
Proof.
  move => [Heq]. constructor.
  by rewrite Heq /= interp_translate /recursive' interp_trigger_h_ge.
Qed.
Global Hint Resolve itree_tstep_interp_rec_inr : typeclass_instances.

Lemma itree_tstep_rec {E} {A B} f x :
  ITreeTStep (E:=E) false (rec' (A:=A) (B:=B) f x) (interp (recursive' f) (f x)).
Proof. constructor. by rewrite rec'_as_interp_eq. Qed.
Global Hint Resolve itree_tstep_rec : typeclass_instances.

Lemma itree_tstep_forever E R R' (t : itree E R) :
  ITreeTStep (R:=R') false (ITree.forever t) (t;; Tau (ITree.forever t)).
Proof. constructor. by rewrite {1}unfold_forever. Qed.
Global Hint Resolve itree_tstep_forever : typeclass_instances.

(** *** ITreeTStepS and ITreeTStepI *)
Lemma itree_step_Tau_s EV S k (s : S) :
  ITreeTStepS (EV:=EV) (Tau k) s None (λ G, G k s).
Proof.
  constructor => ??. apply: steps_spec_step_end. { by econs. } naive_solver.
Qed.
Global Hint Resolve itree_step_Tau_s : typeclass_instances.

Lemma itree_step_Tau_i EV S k s:
  ITreeTStepI (EV:=EV) (S:=S) (Tau k) s (λ G, G true None (λ G', G' k s)).
Proof.
  constructor => ??.
  apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=.
  all: revert select (_ ≡ _) => /SmallITree.equiv_from_itree/moduleE_eq_itree_inv //.
  cbn => Heq. split!; [done..|]. move => /=??. split!; [|done]. by rewrite Heq.
Qed.
Global Hint Resolve itree_step_Tau_i : typeclass_instances.

Lemma itree_step_Tau_maybe_s EV S k (s : S) b :
  ITreeTStepS (EV:=EV) (Tau?b k) s None (λ G, G k s).
Proof.
  destruct b; [by apply itree_step_Tau_s|].
  constructor => ??. by apply: steps_spec_end.
Qed.
Global Hint Resolve itree_step_Tau_maybe_s : typeclass_instances.

Lemma itree_step_Tau_maybe_i EV S k s b:
  ITreeTStepI (EV:=EV) (S:=S) (Tau?b k) s (λ G, G false None (λ G', G' k s)).
Proof.
  constructor => ??.
  destruct b. 2: { apply: steps_impl_end. naive_solver. }
  apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=.
  all: revert select (_ ≡ _) => /SmallITree.equiv_from_itree/moduleE_eq_itree_inv //.
  cbn => Heq. split!; [done..|]. move => /=??. split!; [|done]. by rewrite Heq.
Qed.
Global Hint Resolve itree_step_Tau_maybe_i : typeclass_instances.

Lemma itree_step_Vis_s EV S k (s : S) (e : EV):
  ITreeTStepS (ITree.bind (visible e) k) s (Some e) (λ G, G (k tt) s).
Proof.
  constructor => ??. rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
  apply: steps_spec_step_end. { by econs. } naive_solver.
Qed.
Global Hint Resolve itree_step_Vis_s : typeclass_instances.

Lemma itree_step_Vis_i EV S k s e:
  ITreeTStepI (EV:=EV) (S:=S) (ITree.bind (visible e) k) s (λ G, G true (Some e) (λ G', G' (k tt) s)).
Proof.
  constructor => ??.
  apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=.
  all: revert select (_ ≡ _) => /SmallITree.equiv_from_itree/moduleE_eq_itree_inv //.
  cbn. rewrite -/(ITree.bind _ _) unfold_bind/= => -[<- Heq].
  split!; [done..|]. move => /=??. split!; [|done]. by rewrite Heq.
Qed.
Global Hint Resolve itree_step_Vis_i : typeclass_instances.

Lemma itree_step_All_s EV S T (k : T → _) s:
  ITreeTStepS (EV:=EV) (S:=S) (ITree.bind (angelic T) k) s None (λ G, ∀ x, G (k x) s).
Proof.
  constructor => ??. rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
  apply: steps_spec_step_end. {
    econs; by repeat f_equiv. }
 naive_solver.
Qed.
Global Hint Resolve itree_step_All_s : typeclass_instances.

Lemma itree_step_All_i EV S T (k : T → _) s:
  ITreeTStepI (EV:=EV) (S:=S) (ITree.bind (angelic T) k) s (λ G, G true None (λ G', ∃ x, G' (k x) s)).
Proof.
  constructor => ??.
  apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=.
  all: revert select (_ ≡ _) => /SmallITree.equiv_from_itree/moduleE_eq_itree_inv //.
  cbn. move => [?]. subst => /= Heq.
  split!; [done..|]. move => /=?[??]. split!; [|done]. rewrite -Heq -/(ITree.bind _ _) unfold_bind/=. done.
Qed.
Global Hint Resolve itree_step_All_i : typeclass_instances.

Lemma itree_step_Exist_s EV S T (k : T → _) s:
  ITreeTStepS (EV:=EV) (S:=S) (ITree.bind (demonic T) k) s None (λ G, ∃ x, G (k x) s).
Proof.
  constructor => ? [??]. rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
  apply: steps_spec_step_end. { econs; by repeat f_equiv. } naive_solver.
Qed.
Global Hint Resolve itree_step_Exist_s : typeclass_instances.

Lemma itree_step_Exist_i EV S T (k : T → _) s:
  ITreeTStepI (EV:=EV) (S:=S) (ITree.bind (demonic _) k) s (λ G, ∀ x, G true None (λ G', G' (k x) s)).
Proof.
  constructor => ??.
  apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=.
  all: revert select (_ ≡ _) => /SmallITree.equiv_from_itree/moduleE_eq_itree_inv //.
  cbn. move => [?]. subst => /= Heq.
  split!; [done..|]. move => /=??. split!; [|done]. rewrite -Heq -/(ITree.bind _ _) unfold_bind/=. done.
Qed.
Global Hint Resolve itree_step_Exist_i : typeclass_instances.

Lemma itree_step_Get_s EV S k s:
  ITreeTStepS (EV:=EV) (S:=S) (ITree.bind get_state k) s None (λ G, G (k s) s).
Proof.
  constructor => ? ?. rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
  apply: steps_spec_step_end. { by econs. } naive_solver.
Qed.
Global Hint Resolve itree_step_Get_s : typeclass_instances.

Lemma itree_step_Get_i EV S k s:
  ITreeTStepI (EV:=EV) (S:=S) (ITree.bind get_state k) s (λ G, G true None (λ G', G' (k s) s)).
Proof.
  constructor => ??.
  apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=.
  all: revert select (_ ≡ _) => /SmallITree.equiv_from_itree/moduleE_eq_itree_inv //.
  cbn. move => Heq.
  split!; [done..|]. move => /=??. split!; [|done]. rewrite -Heq -/(ITree.bind _ _) unfold_bind/=. done.
Qed.
Global Hint Resolve itree_step_Get_i : typeclass_instances.

Lemma itree_step_Put_s EV S k s s':
  ITreeTStepS (EV:=EV) (S:=S) (ITree.bind (set_state s') k) s None (λ G, G (k tt) s').
Proof.
  constructor => ? ?. rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
  apply: steps_spec_step_end. { econs; by repeat f_equiv. } naive_solver.
Qed.
Global Hint Resolve itree_step_Put_s : typeclass_instances.

Lemma itree_step_Put_i EV S k s s':
  ITreeTStepI (EV:=EV) (S:=S) (ITree.bind (set_state s') k) s (λ G, G true None (λ G', G' (k tt) s')).
Proof.
  constructor => ??.
  apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=.
  all: revert select (_ ≡ _) => /SmallITree.equiv_from_itree/moduleE_eq_itree_inv //.
  cbn. move => [? Heq]. subst.
  split!; [done..|]. move => /=??. split!; [|done]. rewrite -Heq -/(ITree.bind _ _) unfold_bind/=. done.
Qed.
Global Hint Resolve itree_step_Put_i : typeclass_instances.

Lemma itree_step_Ub_s EV S T (k : T → _) s:
  ITreeTStepS (EV:=EV) (S:=S) (ITree.bind UB k) s None (λ G, True).
Proof.
  constructor => ? ?. rewrite /UB bind_bind.
 rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
  apply: steps_spec_step_end. { econs; by repeat f_equiv. } move => /=? [[]?].
Qed.
Global Hint Resolve itree_step_Ub_s : typeclass_instances.

Lemma itree_step_Ub_end_s EV S s:
  ITreeTStepS (EV:=EV) (S:=S) UB s None (λ G, True).
Proof.
  constructor => ? ?. rewrite /UB unfold_bind/=.
 apply: steps_spec_step_end. { econs; by repeat f_equiv. } move => /= ? [[] ?].
Qed.
Global Hint Resolve itree_step_Ub_end_s : typeclass_instances.

Lemma itree_step_Nb_i EV S T (k : T → _) s:
  ITreeTStepI (EV:=EV) (S:=S) (ITree.bind NB k) s (λ G, G true None (λ G', True)).
Proof.
  constructor => ??.
  apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=.
  all: revert select (_ ≡ _) => /SmallITree.equiv_from_itree/moduleE_eq_itree_inv //.
  cbn. move => [? Heq]. simplify_eq/=. done.
Qed.
Global Hint Resolve itree_step_Nb_i : typeclass_instances.

Lemma itree_step_Nb_end_i EV S s:
  ITreeTStepI (EV:=EV) (S:=S) NB s (λ G, G true None (λ G', True)).
Proof.
  constructor => ??.
  apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=.
  all: revert select (_ ≡ _) => /SmallITree.equiv_from_itree/moduleE_eq_itree_inv //.
  cbn. move => [? Heq]. simplify_eq/=. done.
Qed.
Global Hint Resolve itree_step_Nb_end_i : typeclass_instances.

Lemma itree_step_Assume_s EV S P k s:
  ITreeTStepS (EV:=EV) (S:=S) (ITree.bind (assume P) k) s None (λ G, P → G (k tt) s).
Proof.
  constructor => ? ?. rewrite bind_bind unfold_bind/=. do 2 setoid_rewrite unfold_bind; simpl.
  apply: steps_spec_step_end. { econs; by repeat f_equiv. } naive_solver.
Qed.
Global Hint Resolve itree_step_Assume_s : typeclass_instances.

Lemma itree_step_Assume_i EV S P k s:
  ITreeTStepI (EV:=EV) (S:=S) (ITree.bind (assume P) k) s (λ G, G true None (λ G', P ∧ G' (k tt) s)).
Proof.
  constructor => ??.
  apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=.
  all: revert select (_ ≡ _) => /SmallITree.equiv_from_itree/moduleE_eq_itree_inv //.
  cbn. move => [?]. subst T => /= Heq.
  split!; [done..|]. move => /=?[??]. split!; [|done]. rewrite -Heq -/(ITree.bind _ _) unfold_bind/=. done.
  Unshelve. done.
Qed.
Global Hint Resolve itree_step_Assume_i : typeclass_instances.

Lemma itree_step_Assert_s EV S P k s:
  ITreeTStepS (EV:=EV) (S:=S) (ITree.bind (assert P) k) s None (λ G, P ∧ G (k tt) s).
Proof.
  constructor => ? ?. rewrite bind_bind unfold_bind/=. do 2 setoid_rewrite unfold_bind; simpl.
  apply: steps_spec_step_end. { econs; by repeat f_equiv. } naive_solver.
  Unshelve. naive_solver.
Qed.
Global Hint Resolve itree_step_Assert_s : typeclass_instances.

Lemma itree_step_Assert_i EV S P k s:
  ITreeTStepI (EV:=EV) (S:=S) (ITree.bind (assert P) k) s (λ G, P → G true None (λ G', G' (k tt) s)).
Proof.
  constructor => ??.
  apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=.
  all: revert select (_ ≡ _) => /SmallITree.equiv_from_itree/moduleE_eq_itree_inv //.
  cbn. move => [?]. subst T => /= Heq.
  split!; [naive_solver|done..|]. move => /=??. split!; [|done]. rewrite -Heq -/(ITree.bind _ _) unfold_bind/=. done.
Qed.
Global Hint Resolve itree_step_Assert_i : typeclass_instances.

Lemma itree_step_AssumeOpt_s EV S T (o : option T) k s:
  ITreeTStepS (EV:=EV) (S:=S) (ITree.bind (assume_option o) k) s None (λ G, ∀ x, o = Some x → G (k x) s).
Proof.
  constructor => ??. destruct o => /=.
  - rewrite unfold_bind/=. apply: steps_spec_end. naive_solver.
  - by apply itree_step_Ub_s.
Qed.
Global Hint Resolve itree_step_AssumeOpt_s : typeclass_instances.

Lemma itree_step_AssumeOpt_i EV S T (o : option T) k s:
  ITreeTStepI (EV:=EV) (S:=S) (ITree.bind (assume_option o) k) s (λ G, G false None (λ G', ∃ x, o = Some x ∧ G' (k x) s)).
Proof.
  constructor => ??. destruct o => /=.
  - apply: steps_impl_end. split!; [done..|].
    move => ?[? [[?]?]]. subst. eexists _, _, _. split_and!; [naive_solver| |naive_solver].
    by rewrite unfold_bind/=.
  - apply: steps_impl_step_end => ???.
    inv_all @m_step; simplify_eq/=.
    all: revert select (_ ≡ _) => /SmallITree.equiv_from_itree/moduleE_eq_itree_inv //.
    cbn. move => [??]. split!; [done..|].
    naive_solver.
Qed.
Global Hint Resolve itree_step_AssumeOpt_i : typeclass_instances.

Lemma itree_step_AssertOpt_s EV S T (o : option T) k s:
  ITreeTStepS (EV:=EV) (S:=S) (ITree.bind (assert_option o) k) s None (λ G, ∃ x, o = Some x ∧ G (k x) s).
Proof.
  constructor => ?[?[??]]. simplify_eq/=. rewrite unfold_bind/=. by apply: steps_spec_end.
Qed.
Global Hint Resolve itree_step_AssertOpt_s : typeclass_instances.

Lemma itree_step_AssertOpt_i EV S T (o : option T) k s:
  ITreeTStepI (EV:=EV) (S:=S) (ITree.bind (assert_option o) k) s (λ G, ∀ x, o = Some x → G false None (λ G', G' (k x) s)).
Proof.
  constructor => ??. destruct o => /=.
  - apply: steps_impl_end. split!; [naive_solver|done..|].
    move => ??. eexists _, _, _. split_and!; [naive_solver| |naive_solver].
    by rewrite unfold_bind/=.
  - apply: steps_impl_step_end => ???.
    inv_all @m_step; simplify_eq/=.
    all: revert select (_ ≡ _) => /SmallITree.equiv_from_itree/moduleE_eq_itree_inv //.
    cbn. move => [??]. subst. done.
Qed.
Global Hint Resolve itree_step_AssertOpt_i : typeclass_instances.

(** * itree_step tactic *)
Lemma tac_itree_step {E R} (t t' : itree E R) x:
  x ⊒ ↓ᵢ t →
  ITreeTStep true t t' →
  x ⊒ ↓ᵢ t'.
Proof. move => Hx [Ht]. by rewrite Hx Ht. Qed.

Ltac itree_step_hyp Hx :=
  lazymatch type of Hx with
  | _ ⊒ ↓ᵢ ?x =>
      let H := fresh in
      let e := constr:(_ : ITreeTStep true x _) in
      pose proof (tac_itree_step _ _ _ Hx e) as H;
      clear Hx; rename H into Hx; cbv beta in Hx
  end.
Ltac itree_step :=
  (* match is important that we try all hyps (both impl and spec )*)
  match goal with
  | H : _ ⊒ ↓ᵢ _ |- _ => itree_step_hyp H
  end.


Module itree_test.

Local Definition test_itree : itree (moduleE nat nat) void
  := (s ← get_state; set_state (S s);;
     ((s ← get_state; set_state(S s);; Ret tt);; visible(1);; Ret tt);; NB)%itree.

Goal trefines (itree_mod test_itree 0) (itree_mod test_itree 0).
  apply tsim_implies_trefines => ? /=. rewrite /test_itree.

  tstep_i; clear_itree.
  tstep_i; clear_itree.
  tstep_i; clear_itree.
  tstep_i; clear_itree.
  tstep_i; clear_itree.
  tstep_s; clear_itree.
  tstep_s; clear_itree.
  tstep_s; clear_itree.
  tstep_s; clear_itree.
  tstep_s; clear_itree. split!. clear_itree.
  tstep_s; clear_itree.
  tstep_i; clear_itree.
  done.
Abort.
End itree_test.
