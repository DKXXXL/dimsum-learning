From Paco Require Import paco.
From ITree Require Export ITree ITreeFacts.
From ITree Require Export ITree.
From dimsum.core Require Export proof_techniques.
From dimsum.core Require Import axioms.

Notation "' x ← y ;;; z" := (ITree.bind y (λ x : _, z))
  (at level 20, x pattern, y at level 100, z at level 200) : stdpp_scope.
Notation "x ← y ;;; z" := (ITree.bind y (λ x : _, z))
  (at level 20, y at level 100, z at level 200) : stdpp_scope.
Notation "y ;;;; z" := (ITree.bind y (λ _, z))
  (at level 100, z at level 200, right associativity) : stdpp_scope.
Global Instance eqit_false_true_rewrite {R E} r : RewriteRelation (@eqit E R R r false true) := { }.
Global Instance eqit_true_false_rewrite {R E} r : RewriteRelation (@eqit E R R r true false) := { }.

Inductive moduleE (EV S : Type) : Type → Type :=
| EVis (e : EV) : moduleE EV S unit
| EAll (T : Type) : moduleE EV S T
| EExist (T : Type) : moduleE EV S T
| EGet : moduleE EV S S
| EPut (s : S) : moduleE EV S unit
.
Arguments EVis {_ _}.
Arguments EAll {_ _}.
Arguments EExist {_ _}.
Arguments EGet {_ _}.
Arguments EPut {_ _}.

Inductive itree_step EV S : (itree (moduleE EV S) unit * S) → option EV → ((itree (moduleE EV S) unit * S) → Prop) → Prop :=
| ITauS t t' s:
  observe t = TauF t' →
  itree_step EV S (t, s) None (λ σ', σ' = (t', s))
| IVisS t t' s e:
  observe t = VisF (EVis e) t' →
  itree_step EV S (t, s) (Some e) (λ σ', σ' = (t' tt, s))
| IAllS T t t' s:
  observe t = VisF (EAll T) t' →
  itree_step EV S (t, s) None (λ σ', ∃ x, σ' = (t' x, s))
| IExistS T x t t' s:
  observe t = VisF (EExist T) t' →
  itree_step EV S (t, s) None (λ σ', σ' = (t' x, s))
| IGetS t t' s:
  observe t = VisF (EGet) t' →
  itree_step EV S (t, s) None (λ σ', σ' = (t' s, s))
| IPutS t t' s s':
  observe t = VisF (EPut s') t' →
  itree_step EV S (t, s) None (λ σ', σ' = (t' (), s'))
.

Definition itree_trans EV S := ModTrans (itree_step EV S).

Global Instance itree_vis_no_all EV S: VisNoAng (itree_trans EV S).
Proof. move => *. inv_all @m_step; naive_solver. Qed.

Definition itree_mod {EV S} (t : itree (moduleE EV S) unit) (s : S) :=
  Mod (itree_trans EV S) (t, s).

(** [Tau] *)
(* TODO: Are all these lemmas necessary? *)
Lemma tnhas_trace_Tau' {EV S} t t' n n' Pσ s κs:
  observe t = TauF t' →
  (t', s) ~{itree_trans EV S, κs, n}~>ₜ Pσ →
  oS n ⊆ n' →
  (t, s) ~{itree_trans EV S, κs, n'}~>ₜ Pσ.
Proof.
  move => Htau Ht Hsub. apply: (TNTraceStep _ _ (λ _, n)); [by econs| | |simpl; done].
  - move => /= ? ->. done.
  - etrans; [|done]. econs. by econs.
Qed.
Lemma tnhas_trace_Tau {EV S} t n n' Pσ s κs:
  (t, s) ~{itree_trans EV S, κs, n}~>ₜ Pσ →
  oS n ⊆ n' →
  (Tau t, s) ~{itree_trans EV S, κs, n'}~>ₜ Pσ.
Proof. by apply tnhas_trace_Tau'. Qed.

Lemma thas_trace_Tau' {EV S} t t' Pσ s κs:
  observe t = TauF t' →
  (t', s) ~{itree_trans EV S, κs}~>ₜ Pσ →
  (t, s) ~{itree_trans EV S, κs}~>ₜ Pσ.
Proof. move => Htau Ht. tstep_None; [by econs|]. naive_solver. Qed.
Lemma thas_trace_Tau {EV S} t Pσ s κs:
  (t, s) ~{itree_trans EV S, κs}~>ₜ Pσ →
  (Tau t, s) ~{itree_trans EV S, κs}~>ₜ Pσ.
Proof. by apply thas_trace_Tau'. Qed.

Lemma tnhas_trace_Tau_inv' {EV S} t t' n Pσ s κs:
  observe t' = TauF t →
  (t', s) ~{itree_trans EV S, κs, n}~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ (t', s)) ∨
    ∃ n', oS n' ⊆ n ∧ (t, s) ~{ itree_trans _ _,  κs, n' }~>ₜ Pσ).
Proof.
  move => Htau Ht. thas_trace_inv Ht. { naive_solver. }
  right. inv_all @m_step; rewrite ->Htau in *; simplify_eq.
  eexists _. split; last first.
  - rewrite -H0. naive_solver.
  - etrans; [|done]. econs. by econs.
  Unshelve. done.
Qed.
Lemma tnhas_trace_Tau_inv {EV S} t n Pσ s κs:
  (Tau t, s) ~{itree_trans EV S, κs, n}~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ (Tau t, s)) ∨
    ∃ n', oS n' ⊆ n ∧ (t, s) ~{ itree_trans _ _,  κs, n' }~>ₜ Pσ).
Proof. by apply tnhas_trace_Tau_inv'. Qed.

Lemma thas_trace_Tau_inv' {EV S} t t' Pσ s κs:
  observe t' = TauF t →
  (t', s) ~{itree_trans EV S, κs}~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ (t', s)) ∨ (t, s) ~{ itree_trans _ _,  κs }~>ₜ Pσ).
Proof.
  move => Htau /thas_trace_n[? /(tnhas_trace_Tau_inv' _ _ _ _ _) Ht]. specialize (Ht _ ltac:(done)).
  apply: under_tall_mono'; [done..|] => {Ht} ? [[??]|[?[??]]]. { naive_solver. }
  right. apply thas_trace_n. naive_solver.
Qed.
Lemma thas_trace_Tau_inv {EV S} t Pσ s κs:
  (Tau t, s) ~{itree_trans EV S, κs}~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ (Tau t, s)) ∨ (t, s) ~{ itree_trans _ _,  κs }~>ₜ Pσ).
Proof. by apply thas_trace_Tau_inv'. Qed.

(** [Ret] *)
Lemma tnhas_trace_Ret_inv' {EV S} t x n Pσ s κs:
  observe t = RetF x →
  (t, s) ~{itree_trans EV S, κs, n}~>ₜ Pσ →
  under_tall κs (λ κs, tnil ⊆ κs ∧ Pσ (t, s)).
Proof.
  move => Hret. move => Ht.
  thas_trace_inv Ht; [done|].
  inv_all @m_step; rewrite ->Hret in *; simplify_eq.
Qed.
Lemma tnhas_trace_Ret_inv {EV S} x n Pσ s κs:
  (Ret x, s) ~{itree_trans EV S, κs, n}~>ₜ Pσ →
  under_tall κs (λ κs, tnil ⊆ κs ∧ Pσ (Ret x, s)).
Proof. by apply: tnhas_trace_Ret_inv'. Qed.

Lemma thas_trace_Ret_inv' {EV S} t x Pσ s κs:
  observe t = RetF x →
  (t, s) ~{itree_trans EV S, κs}~>ₜ Pσ →
  under_tall κs (λ κs, tnil ⊆ κs ∧ Pσ (t, s)).
Proof. move => Hret /thas_trace_n [? /(tnhas_trace_Ret_inv' _ _ _ _ _) Ht]. naive_solver. Qed.
Lemma thas_trace_Ret_inv {EV S} x Pσ s κs:
  (Ret x, s) ~{itree_trans EV S, κs}~>ₜ Pσ →
  under_tall κs (λ κs, tnil ⊆ κs ∧ Pσ (Ret x, s)).
Proof. by apply: thas_trace_Ret_inv'. Qed.

(** [Vis] *)
Lemma thas_trace_Vis_inv {EV S} e k Pσ s κs:
  (vis (EVis e) k, s) ~{itree_trans EV S, κs}~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ (vis (EVis e) k, s)) ∨
   ∃ κs', tcons e κs' ⊆ κs ∧ (k (), s) ~{ itree_trans EV S, κs' }~>ₜ Pσ ).
Proof.
  move => Ht. thas_trace_inv Ht; [naive_solver|].
  inv_all @m_step; simpl in *; simplify_eq; simplify_K.
  naive_solver.
Qed.

Lemma thas_trace_Vis {EV S} e k Pσ s κs:
  (k tt, s) ~{itree_trans EV S, κs}~>ₜ Pσ →
  (vis (EVis e) k, s) ~{itree_trans EV S, tcons e κs}~>ₜ Pσ.
Proof. move => Ht. tstep_Some; [by econs|] => ? ->. done. Qed.

(** [All] *)
Lemma thas_trace_All_inv {EV S} T k Pσ s κs:
  (vis (EAll T) k, s) ~{itree_trans EV S, κs}~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ (vis (EAll T) k, s)) ∨
   ∀ x, (k x, s) ~{ itree_trans EV S, κs }~>ₜ Pσ ).
Proof.
  move => Ht. thas_trace_inv Ht; [naive_solver|].
  inv_all @m_step; simpl in *; simplify_eq; simplify_K.
  right => ?. revert select (_ ⊆ _) => <- /=. naive_solver.
Qed.
Lemma thas_trace_All {EV S} T k Pσ s κs:
  (∀ x, (k x, s) ~{itree_trans EV S, κs}~>ₜ Pσ) →
  (vis (EAll T) k, s) ~{itree_trans EV S, κs}~>ₜ Pσ.
Proof. move => Ht. tstep_None; [by apply: IAllS|] => ? [? ->]. done. Qed.

(** [Exist] *)
Lemma thas_trace_Exist_inv {EV S} T k Pσ s κs:
  (vis (EExist T) k, s) ~{itree_trans EV S, κs}~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ (vis (EExist T) k, s)) ∨
   ∃ x, (k x, s) ~{ itree_trans EV S, κs }~>ₜ Pσ ).
Proof.
  move => Ht. thas_trace_inv Ht; [naive_solver|].
  inv_all @m_step; simpl in *; simplify_eq; simplify_K.
  right. eexists _. revert select (_ ⊆ _) => <- /=. naive_solver.
Qed.
Lemma thas_trace_Exist {EV S} T x k Pσ s κs:
  (k x, s) ~{itree_trans EV S, κs}~>ₜ Pσ →
  (vis (EExist T) k, s) ~{itree_trans EV S, κs}~>ₜ Pσ.
Proof. move => Ht. tstep_None; [by apply: (IExistS _ _ _ x)|] => ? ->. done. Qed.

(** [Get] *)
Lemma thas_trace_Get_inv {EV S} k Pσ s κs:
  (vis EGet k, s) ~{itree_trans EV S, κs}~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ (vis EGet k, s)) ∨
   (k s, s) ~{ itree_trans EV S, κs }~>ₜ Pσ ).
Proof.
  move => Ht. thas_trace_inv Ht; [naive_solver|].
  inv_all @m_step; simpl in *; simplify_eq; simplify_K.
  right. revert select (_ ⊆ _) => <- /=. naive_solver.
Qed.
Lemma thas_trace_Get {EV S} k Pσ s κs:
  (k s, s) ~{itree_trans EV S, κs}~>ₜ Pσ →
  (vis EGet k, s) ~{itree_trans EV S, κs}~>ₜ Pσ.
Proof. move => Ht. tstep_None; [by apply: IGetS|] => ? ->. done. Qed.

(** [Put] *)
Lemma thas_trace_Put_inv {EV S} k Pσ s s' κs:
  (vis (EPut s') k, s) ~{itree_trans EV S, κs}~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ (vis (EPut s') k, s)) ∨
   (k (), s') ~{ itree_trans EV S, κs }~>ₜ Pσ ).
Proof.
  move => Ht. thas_trace_inv Ht; [naive_solver|].
  inv_all @m_step; simpl in *; simplify_eq; simplify_K.
  right. revert select (_ ⊆ _) => <- /=. naive_solver.
Qed.
Lemma thas_trace_Put {EV S} k Pσ s s' κs:
  (k tt, s') ~{itree_trans EV S, κs}~>ₜ Pσ →
  (vis (EPut s') k, s) ~{itree_trans EV S, κs}~>ₜ Pσ.
Proof. move => Ht. tstep_None; [by econs|] => ? ->. done. Qed.

(** eutt mono *)
Definition steps_impl_eutt_rel {EV S} (b1 b2 : bool) : relation (bool → option EV → ((itree (moduleE EV S) () * S → Prop) → Prop)) := λ Pσ Pσ',
  ∀ (b b' : bool) κ (P1 P2 : _ → Prop),
    (∀ t s, P1 (t, s) → ∃ t', eqit eq b1 b2 t t' ∧ P2 (t', s)) →
    (b1 = false → b → b') →
    Pσ b κ P1 → Pσ' b' κ P2.

Lemma steps_impl_eutt_mono {EV S} t' σ (Pσ Pσ' : _ → _ → _ → Prop) b1 b2:
  steps_impl_eutt_rel b1 b2 Pσ Pσ' →
  σ -{ itree_trans EV S }-> Pσ →
  eqit eq b1 b2 σ.1 t' →
  (t', σ.2) -{ itree_trans EV S }-> Pσ'.
Proof.
  move => HP Ht Heq.
  elim/@prop_least_fixpoint_pair_ind_wf: Ht t' Pσ' Heq HP => {}σ {}Pσ IHn t' {}Pσ' Heq HP.
  destruct σ as [t s]; simpl in *.
  punfold Heq. unfold eqit_ in Heq at 1.
  move: Heq. move Hot: (observe t) => ot. move Hot': (observe t') => ot' Heq.
  elim: Heq t t' s Pσ' Pσ HP IHn Hot Hot'.
  - move => ?? -> t t' s Pσ' Pσ HP IHn Hot Hot'.
    apply steps_impl_step_end => ???. inv_all @m_step; congruence.
  - move => m1 m2 [REL|//] t t' s Pσ' Pσ HP IHn Hot Hot'. rewrite -/(eqit _ _ _) in REL.
    move: IHn => [?| {}IHn]; simplify_eq.
    + apply: steps_impl_end. eapply HP; [|done..]. move => t1 ? [? ?]. subst. eexists _. split; [|done].
      rewrite (itree_eta t1) Hot (itree_eta t') Hot'. by apply eqit_Tau.
    + apply: steps_impl_step => ???. inv_all @m_step; try congruence. have ?: t'0 = m2 by congruence. subst.
      have [?|[?[?[? Hfix]]]]:= (IHn _ _ ltac:(by econs)); simplify_eq.
      * left. eapply HP; [|done..]. naive_solver.
      * right. eexists _. split_and!; [done..|].
        move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|/=IH ?].
        { apply wf_pred_mono. apply (steps_impl_rec_mono (itree_trans _ _)). }
        apply IH => //=. unfold steps_impl_eutt_rel in *. naive_solver.
  - move => u e k1 k2 Hu t t' s Pσ' Pσ HP IHn Hot Hot'.
    move: IHn => [?|{}IHn]. {
      apply: steps_impl_end. eapply HP; [|done..]. move => t1 ? [? ?]. subst. eexists _. split; [|done].
      rewrite (itree_eta t1) Hot (itree_eta t') Hot'.
      apply eqit_Vis => v. move: (Hu v) => [|//]. done.
    }
    apply: steps_impl_step => ???.
    inv_all @m_step; rewrite ->Hot' in *; simplify_eq; simplify_K.
    + have [?|[?[?[??]]]]:= (IHn _ _ ltac:(by econs)); simplify_eq. left.
      eapply HP; [|done..]. move => t1 ? [? ?]. subst. eexists _. split; [|done].
      move: (Hu tt) => [|//]. done.
    + have [?|[?[[x ?][? Hfix]]]]:= (IHn _ _ ltac:(by econs)); simplify_eq.
      * left. eapply HP; [|done..]. move => t1 ? [x [??]]. subst. eexists _. split; [|naive_solver].
        move: (Hu x) => [|//]. done.
      * right. move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_impl_rec_mono (itree_trans _ _)). }
        eexists _. split_and!;[ naive_solver..|].
        apply: IH => /=. 2: unfold steps_impl_eutt_rel in *; naive_solver. move: (Hu x) => [|//]. done.
    + exploit IHn; [by econs|] => -[?|[?[?[? Hfix]]]]; simplify_eq.
      * left. eapply HP; [|done..]. move => t1 ? [??]. subst. eexists _. split; [|naive_solver].
        move: (Hu x) => [|//]. done.
      * right. move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|/=IH ?].
        { apply wf_pred_mono. apply (steps_impl_rec_mono (itree_trans _ _)). }
        eexists _. split_and!;[ naive_solver..|].
        apply IH => /=. 2: unfold steps_impl_eutt_rel in *; naive_solver. move: (Hu x) => [|//]. done.
    + exploit IHn; [by econs|] => -[?|[?[?[? Hfix]]]]; simplify_eq.
      * left. eapply HP; [|done..]. move => t1 ? [??]. subst. eexists _. split; [|naive_solver].
        move: (Hu s) => [|//]. done.
      * right. move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|/=IH ?].
        { apply wf_pred_mono. apply (steps_impl_rec_mono (itree_trans _ _)). }
        eexists _. split_and!;[ naive_solver..|].
        apply IH => /=. 2: unfold steps_impl_eutt_rel in *; naive_solver. move: (Hu s) => [|//]. done.
    + exploit IHn; [by econs|] => -[?|[?[?[? Hfix]]]]; simplify_eq.
      * left. eapply HP; [|done..]. move => t1 ? [??]. subst. eexists _. split; [|naive_solver].
        move: (Hu tt) => [|//]. done.
      * right. move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|/=IH ?].
        { apply wf_pred_mono. apply (steps_impl_rec_mono (itree_trans _ _)). }
        eexists _. split_and!;[ naive_solver..|].
        apply IH => /=. 2: unfold steps_impl_eutt_rel in *; naive_solver. move: (Hu tt) => [|//]. done.
  - move => t1 ot2 ? REL IH t t' s Pσ' Pσ HP IHn Hot Hot'.
    move: REL => /fold_eqitF REL. specialize (REL _ _ ltac:(done) ltac:(done)).
    destruct b1 => //. move: IHn => [?|IHn]; simplify_eq.
    + apply: steps_impl_end. eapply HP; [|done..]. move => t1' ? [??]. subst. eexists _. split; [|naive_solver].
      rewrite (itree_eta t1') Hot. by apply eqit_Tau_l.
    + exploit IHn; [by econs|] => -[?|[?[?[? Hfix]]]]; simplify_eq.
      * apply: steps_impl_end. eapply HP; [| |done]; [|done]. move => t1' ? [??]. subst. eexists _.
        split; [|naive_solver]. done.
      * apply: IH; [ | |done|done]; last first.
        -- move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH Hb].
           { apply wf_pred_mono. apply (steps_impl_rec_mono (itree_trans _ _)). }
           apply: mono_pred. 3: done. { apply (steps_impl_rec_mono (itree_trans _ _)). } done.
        -- move => ???????. apply: HP; [|done]. naive_solver.
  - move => ot1 t2 ? REL IH t t' s Pσ' Pσ HP IHn Hot Hot'.
    apply: steps_impl_step => ???. inv_all @m_step; try congruence.
    right. eexists _. split_and!;[done..|]. apply: IH; [|done|done|congruence].
    move => ????????. by apply: HP.
Qed.

Global Instance steps_impl_itree_proper EV S b1 b2:
  Proper ((prod_relation (eqit eq b1 b2) (=)) ==> steps_impl_eutt_rel b1 b2 ==> impl) (steps_impl (itree_trans EV S)).
Proof. move => [??] [??] [/= Heq ->] ?? Hf ?. by apply: (steps_impl_eutt_mono _ (_, _)). Qed.

Global Instance steps_impl_itree_proper_flip EV S b1 b2:
  Proper ((prod_relation (eqit eq b1 b2) (=)) ==> flip (steps_impl_eutt_rel b2 b1) ==> flip impl) (steps_impl (itree_trans EV S)).
Proof.
  move => [??] [??] [/= Heq ->] ?? Hf ?. apply: (steps_impl_eutt_mono _ (_, _)); [done..|].
  apply eqit_flip. by apply: eqit_mon; [..|done].
Qed.

Lemma steps_spec_eutt_mono {EV S} t' σ κ Pσ Pσ' b1 b2:
  (prod_relation (eqit eq b1 b2) (=) ==> impl)%signature Pσ Pσ' →
  σ -{ itree_trans EV S, κ }->ₛ Pσ →
  eqit eq b1 b2 σ.1 t' →
  (t', σ.2) -{ itree_trans EV S, κ }->ₛ Pσ'.
Proof.
  move => HP Ht Heq.
  elim/@prop_least_fixpoint_ind_wf: Ht t' Heq => {}σ IHn t' Heq.
  destruct σ as [t s]; simpl in *.
  punfold Heq. unfold eqit_ in Heq at 1.
  move: Heq. move Hot: (observe t) => ot. move Hot': (observe t') => ot' Heq.
  elim: Heq t t' s IHn Hot Hot'.
  - move => ?? -> t t' s IHn Hot Hot'.
    move: IHn => [[??]|[?[?[?[??]]]]]. 2: { inv_all @m_step; congruence. } subst.
    apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=.
    rewrite (itree_eta t) Hot (itree_eta t') Hot'. done.
  - move => m1 m2 [REL|//] t t' s IHn Hot Hot'. rewrite -/(eqit _ _ _) in REL.
    move: IHn => [[??]|[?[?[? [? Ht]]]]]; simplify_eq.
    + apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=.
      rewrite (itree_eta t) Hot (itree_eta t') Hot'. by apply eqit_Tau.
    + inv_all @m_step; try congruence. have ?: t'0 = m1 by congruence. subst. specialize_hyps.
      move: Ht => [[??]|[? Hfix]]; simplify_eq.
      * apply: steps_spec_step_end. { by econs. } move => ? ->. eapply HP; [|done]. done.
      * apply: steps_spec_step; [by econs|] => ? ->. move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_spec_rec_mono (itree_trans _ _)). }
        apply: IH => /=. congruence.
  - move => u e k1 k2 Hu t t' s IHn Hot Hot'.
    move: IHn => [[??]|[?[?[? [? Ht]]]]]. {
      subst. apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=.
      rewrite (itree_eta t) Hot (itree_eta t') Hot'.
      apply eqit_Vis => v. move: (Hu v) => [|//]. done.
    }
    inv_all @m_step; rewrite ->Hot in *; simplify_eq; simplify_K; specialize_hyps.
    + apply: steps_spec_step_end; [by econs|] => ? /= ->. move: Ht => [[??]|[??//]].
      eapply HP; [|done]. split; [|done].
      move: (Hu tt) => [|//]. done.
    + apply: steps_spec_step; [by econs|] => ? /= [x ->].
      have [|[??]|[? Hfix]]:= Ht (t'0 x, s); subst. { naive_solver. }
      * apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=.
        move: (Hu x) => [|//]. done.
      * move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_spec_rec_mono (itree_trans _ _)). }
        apply: IH => /=. move: (Hu x) => [|//]. done.
    + apply: steps_spec_step; [by econs|] => ? /= ->.
      have [[??]|[? Hfix]]:= Ht; subst.
      * apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=.
        move: (Hu x) => [|//]. done.
      * move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_spec_rec_mono (itree_trans _ _)). }
        apply: IH => /=. move: (Hu x) => [|//]. done.
    + apply: steps_spec_step; [by econs|] => ? /= ->.
      have [[??]|[? Hfix]]:= Ht; subst.
      * apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=.
        move: (Hu s) => [|//]. done.
      * move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_spec_rec_mono (itree_trans _ _)). }
        apply: IH => /=. move: (Hu s) => [|//]. done.
    + apply: steps_spec_step; [by econs|] => ? /= ->.
      have [[??]|[? Hfix]]:= Ht; subst.
      * apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=.
        move: (Hu tt) => [|//]. done.
      * move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_spec_rec_mono (itree_trans _ _)). }
        apply: IH => /=. move: (Hu tt) => [|//]. done.
  - move => t1 ot2 ? REL IH t t' s IHn Hot Hot'.
    move: REL => /fold_eqitF REL. specialize (REL _ _ ltac:(done) ltac:(done)).
    move: IHn => [[??]|[?[?[? [? Ht]]]]]; simplify_eq.
    + apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=. etrans; [|done].
      destruct b1 => //. rewrite (itree_eta t) Hot. by apply eqit_Tau_l.
    + inv_all @m_step; try congruence. have ?: t'0 = t1 by congruence. subst. specialize_hyps.
      move: Ht => [[??]|[? Hfix]]; simplify_eq.
      * apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=. done.
      * apply: IH; [|done|done].
        move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_spec_rec_mono (itree_trans _ _)). }
        apply: mono_pred. 3: done. { apply (steps_spec_rec_mono (itree_trans _ _)). } done.
  - move => ot1 t2 ? REL IH t t' s IHn Hot Hot'.
    apply: steps_spec_step; [by econs|] => ? /= ->.
    by apply: IH.
Qed.

Global Instance steps_spec_itree_proper EV S b1 b2:
  Proper ((prod_relation (eqit eq b1 b2) (=)) ==> (=) ==> (prod_relation (eqit eq b1 b2) (=) ==> iff) ==> iff) (steps_spec (itree_trans EV S)).
Proof.
  move => [??] [??] [/= Heq ->] ?? -> ?? Hf.
  split => ?.
  all: apply: (steps_spec_eutt_mono _ (_, _)); [try done| done |].
  - move => ????. eapply Hf; [|done]. done.
  - done.
  - move => ?? [??] ?. eapply Hf; [|done]. split; [|done]. apply eqit_flip. by apply: eqit_mon; [..|done].
  - apply eqit_flip. by apply: eqit_mon; [..|done].
Qed.

Lemma tnhas_trace_eutt_mono {EV S} t t' s κs Pσ Pσ' b1 n:
  (prod_relation (eqit eq b1 false) (=) ==> impl)%signature Pσ Pσ' →
  (t, s) ~{ itree_trans EV S, κs, n }~>ₜ Pσ →
  eqit eq b1 false t t' →
  (t', s) ~{ itree_trans EV S, κs, n }~>ₜ Pσ'.
Proof.
  move => HP Ht Heq.
  elim/o_lt_ind: n κs t t' s Ht Heq.
  move => n IHn κs t t' s Ht Heq.
  punfold Heq. unfold eqit_ in Heq at 1.
  move: Heq. move Hb2: false => b2. move Hot: (observe t) => ot. move Hot': (observe t') => ot' Heq.
  elim: Heq t t' n κs s IHn Ht Hot Hot'.
  - move => ?? -> t t' n κs s IHn Ht Hot Hot'.
    move: Ht => /(tnhas_trace_Ret_inv' _ _ _ _ _)Ht. specialize (Ht _ ltac:(done)).
    apply: tnhas_trace_under_tall; [done..|] => ? [??]. tend.
    eapply HP; [|done]. split; [|done] => /=. rewrite (itree_eta t) Hot (itree_eta t') Hot'. done.
  - move => m1 m2 [REL|//] t t' n κs s IHn Ht Hot Hot'. subst. rewrite -/(eqit _ _ _) in REL.
    move: Ht => /(tnhas_trace_Tau_inv' _ _ _ _ _)Ht. specialize (Ht _ ltac:(done)).
    apply: tnhas_trace_under_tall; [done..|] => ? /= [[??]|[?[??]]].
    + tend. eapply HP; [|done]. split => //=. rewrite (itree_eta t) Hot (itree_eta t') Hot'. by apply eqit_Tau.
    + apply: tnhas_trace_Tau'; [done| |done]. apply: IHn; [done|done|done].
  - move => u e k1 k2 Hu t t' n κs s IHn Ht Hot Hot'. subst.
    thas_trace_inv Ht. {
      tend. eapply HP; [|done]. split; [|done] => /=. rewrite (itree_eta t) Hot (itree_eta t') Hot'.
      apply eqit_Vis => v. move: (Hu v) => [|//]. done.
    }
    revert select (_ ⊆@{trace _} _) => <-.
    inv_all @m_step; rewrite ->Hot in *; simplify_eq; simplify_K.
    + specialize (H1 _ ltac:(done)).
      apply: (TNTraceStep _ _ (const (fn ((t'0 (), s) ↾ eq_refl)))).
      { by econs. } 3: { simpl; done. } 2: { etrans; [|done]. econs. econs => -[??] /=. by econs. }
      move => ? /= ->. apply: IHn;[|done|].
      * etrans; [|done]. econs. by econs.
      * move: (Hu tt) => [|//]. done.
    + apply: (TNTraceStep _ _ (const (oChoice T (λ x, fn ((t'0 x, s) ↾ ex_intro _ x eq_refl))))).
      { by econs. } 3: simpl; done.
      2: { etrans; [|done]. econs. econs => -[?[??]]. econs => ?. econs. done. }
      move => ? /= [x ->]. apply: IHn;[| |].
      * etrans; [|done]. econs. econs => ?. econs. done.
      * apply: tnhas_trace_mono; [done|done| |done]. econs. done.
      * move: (Hu x) => [|//]. done.
    + apply: (TNTraceStep _ _ (const (fn ((t'0 x, s) ↾ eq_refl)))).
      { by econs. } 3: { simpl; done. } 2: { etrans; [|done]. econs. econs => -[??] /=. by econs. }
      move => ? /= ->. apply: IHn;[|done|].
      * etrans; [|done]. econs. by econs.
      * move: (Hu x) => [|//]. done.
    + apply: (TNTraceStep _ _ (const (fn ((t'0 s, s) ↾ eq_refl)))).
      { by econs. } 3: { simpl; done. } 2: { etrans; [|done]. econs. econs => -[??] /=. by econs. }
      move => ? /= ->. apply: IHn;[|done|].
      * etrans; [|done]. econs. by econs.
      * move: (Hu s) => [|//]. done.
    + apply: (TNTraceStep _ _ (const (fn ((t'0 (), s') ↾ eq_refl)))).
      { by econs. } 3: { simpl; done. } 2: { etrans; [|done]. econs. econs => -[??] /=. by econs. }
      move => ? /= ->. apply: IHn;[|done|].
      * etrans; [|done]. econs. by econs.
      * move: (Hu tt) => [|//]. done.
  - move => t1 ot2 ? REL IH t t' n κs s IHn Ht Hot Hot'.
    move: Ht => /(tnhas_trace_Tau_inv' _ _ _ _ _ _)Ht. specialize (Ht _ ltac:(done)).
    apply: tnhas_trace_under_tall; [done..|] => ? /= [[??]|[?[??]]].
    + tend. eapply HP; [|done]. split; [|done] => /=. subst.
      move: REL => /fold_eqitF REL. specialize (REL _ _ ltac:(done) ltac:(done)). etrans; [|done].
      destruct b1 => //. rewrite (itree_eta t) Hot. by apply eqit_Tau_l.
    + apply: IH => //. apply: tnhas_trace_mono; [done..| by apply: o_lt_impl_le |done].
  - move => *. subst. done.
Qed.

Global Instance tnhas_trace_itree_proper EV S b1:
  Proper ((prod_relation (eqit eq b1 false) (=)) ==> (=) ==> (=) ==> (prod_relation (eqit eq b1 false) (=) ==> impl) ==> impl) (tnhas_trace (itree_trans EV S)).
Proof.
  move => [??] [??] [/= Heq ->] ?? -> ?? -> ?? Hf ?.
  apply: tnhas_trace_eutt_mono; [try done| done |done].
Qed.

Lemma thas_trace_eutt_mono {EV S} t t' s κs Pσ Pσ' b1 b2:
  (prod_relation (eqit eq b1 b2) (=) ==> impl)%signature Pσ Pσ' →
  (t, s) ~{ itree_trans EV S, κs }~>ₜ Pσ →
  eqit eq b1 b2 t t' →
  (t', s) ~{ itree_trans EV S, κs }~>ₜ Pσ'.
Proof.
  move => HP /thas_trace_n[n Ht] Heq.
  elim/o_lt_ind: n κs t t' s Ht Heq HP.
  move => n IHn κs t t' s Ht Heq HP.
  punfold Heq. unfold eqit_ in Heq at 1.
  move: Heq. move Hot: (observe t) => ot. move Hot': (observe t') => ot' Heq.
  elim: Heq t t' n κs s IHn Ht Hot Hot'.
  - move => ?? -> t t' n κs s IHn Ht Hot Hot'.
    move: Ht => /(tnhas_trace_Ret_inv' _ _ _ _ _)Ht. specialize (Ht _ ltac:(done)).
    apply: thas_trace_under_tall; [done..|] => ? [??]. tend.
    eapply HP; [|done]. split; [|done] => /=. rewrite (itree_eta t) Hot (itree_eta t') Hot'. done.
  - move => m1 m2 [REL|//] t t' n κs s IHn Ht Hot Hot'. rewrite -/(eqit _ _ _) in REL.
    move: Ht => /(tnhas_trace_Tau_inv' _ _ _ _ _)Ht. specialize (Ht _ ltac:(done)).
    apply: thas_trace_under_tall; [done..|] => ? /= [[??]|[?[??]]].
    + tend. eapply HP; [|done]. split => //=. rewrite (itree_eta t) Hot (itree_eta t') Hot'. by apply eqit_Tau.
    + apply: thas_trace_Tau'; [done|]. apply: IHn; [done|done| |done]. done.
  - move => u e k1 k2 Hu t t' n κs s IHn Ht Hot Hot'.
    thas_trace_inv Ht. {
      tend. eapply HP; [|done]. split; [|done] => /=. rewrite (itree_eta t) Hot (itree_eta t') Hot'.
      apply eqit_Vis => v. move: (Hu v) => [|//]. done.
    }
    revert select (_ ⊆@{trace _} _) => <-.
    inv_all @m_step; rewrite ->Hot in *; simplify_eq; simplify_K.
    + specialize (H1 _ ltac:(done)).
      tstep_Some; [by econs|] => ? ->.
      apply: IHn; [ |done| |done].
      * etrans; [|done]. econs. by econs.
      * move: (Hu tt) => [|//]. done.
    + tstep_None; [ by apply IAllS|] => ? [x ->].
      apply: IHn; [ |unshelve done; naive_solver| |done].
      * etrans; [|done]. econs. by econs.
      * move: (Hu x) => [|//]. done.
    + tstep_None; [ by apply IExistS|] => ? ->.
      apply: IHn; [ |unshelve done; naive_solver| |done].
      * etrans; [|done]. econs. by econs.
      * move: (Hu x) => [|//]. done.
    + tstep_None; [by apply IGetS|] => ? ->.
      apply: IHn; [ | unshelve done; naive_solver| |done].
      * etrans; [|done]. econs. by econs.
      * move: (Hu s) => [|//]. done.
    + tstep_None; [by apply IPutS|] => ? ->.
      apply: IHn; [ | unshelve done; naive_solver| |done].
      * etrans; [|done]. econs. by econs.
      * move: (Hu tt) => [|//]. done.
  - move => t1 ot2 ? REL IH t t' n κs s IHn Ht Hot Hot'.
    move: Ht => /(tnhas_trace_Tau_inv' _ _ _ _ _ _)Ht. specialize (Ht _ ltac:(done)).
    apply: thas_trace_under_tall; [done..|] => ? /= [[??]|[?[??]]].
    + tend. eapply HP; [|done]. split; [|done] => /=. subst.
      move: REL => /fold_eqitF REL. specialize (REL _ _ ltac:(done) ltac:(done)).
      destruct b1 => //. rewrite (itree_eta t) Hot. by apply eqit_Tau_l.
    + apply: IH => //. apply: tnhas_trace_mono; [done..| by apply: o_lt_impl_le |done].
  - move => ot1 t2 ? REL IH t t' n κs s IHn Ht Hot Hot'.
    tstep_None; [by econs|] => ? ->. by apply: IH.
Qed.

Global Instance itree_trans_proper EV S b1 b2:
  Proper ((prod_relation (eqit eq b1 b2) (=)) ==> (=) ==> (prod_relation (eqit eq b1 b2) (=) ==> iff) ==> iff) (thas_trace (itree_trans EV S)).
Proof.
  move => [??] [??] [/= Heq ->] ?? -> ?? Hf.
  split => ?.
  all: apply: thas_trace_eutt_mono; [try done| done |].
  - move => ????. by eapply Hf.
  - done.
  - move => [??] [??] [/=? ->] ?. eapply Hf; [|done]. split; [|done] => /=.
    apply eqit_flip. by apply: eqit_mon; [..|done].
  - apply eqit_flip. by apply: eqit_mon; [..|done].
Qed.

Definition itree_rel {E R S} (b : bool) (P : itree E R * S → Prop) (t : itree E R * S) : Prop :=
  ∀ t', eqit eq true b t' t.1 → P (t', t.2).
Global Instance itree_rel_proper' E R S P b1 b2:
  Proper ((prod_relation (eqit eq b1 b2) (=) ==> iff)) (@itree_rel E R S true P).
Proof.
  move => [x ?] [y ?] [Heq ?]. simplify_eq/=. rewrite /itree_rel /=.
  have {}Heq : x ≈ y. { by apply: eqit_mon; [..|done]. }
  split => ??; [rewrite -Heq | rewrite Heq]; naive_solver.
Qed.
Global Typeclasses Opaque itree_rel.

Lemma itree_rel_intro EV S σ κs P:
  σ ~{itree_trans EV S, κs }~>ₜ itree_rel true P →
  σ ~{itree_trans EV S, κs }~>ₜ P.
Proof. move => Ht. apply: thas_trace_mono; [done|done|] => -[??] Hp. by apply: Hp. Qed.

Lemma itree_rel_spec_intro EV S σ κ P:
  σ -{itree_trans EV S, κ }->ₛ itree_rel true P →
  σ -{itree_trans EV S, κ }->ₛ P.
Proof. move => ?. apply: steps_spec_mono; [done|]. move => -[??] Hp. by apply Hp. Qed.

Definition itree_impl_rel {EV S} (P : bool → option EV → (itree (moduleE EV S) () * S → Prop) → Prop) :
  bool → option EV → (itree (moduleE EV S) () * S → Prop) → Prop :=
  λ b κ Pσ, ∀ (b' : bool) (Pσ' : _ → Prop),
      (∀ t s, Pσ (t, s) → ∃ t', eqit eq false true t t' ∧ Pσ' (t', s)) →
      (b → b') →
      P b' κ Pσ'.
Global Instance itree_impl_rel_proper EV S P b:
  Proper (steps_impl_eutt_rel false b) (@itree_impl_rel EV S P).
Proof.
  move => ????? HP1 ? REL ?? HPσ' ?. apply: REL. 2: naive_solver.
  move => ?? /HP1 [? [Ht /HPσ'[?[??]]]]. eexists _. split; [|done]. etrans; [|done].
  by apply: eqit_mon; [..|done].
Qed.
Global Typeclasses Opaque itree_impl_rel.

Lemma itree_impl_rel_intro EV S σ P:
  σ -{itree_trans EV S }-> itree_impl_rel P →
  σ -{itree_trans EV S }-> P.
Proof. move => ?. apply: steps_impl_mono; [done|]. move => ??? Hp. apply Hp; [|done]. naive_solver. Qed.

Ltac clear_itree :=
  try match goal with | |- itree_rel _ _ _ => move => ?/=? end;
  repeat match goal with
         | H : eqit _ _ _ ?t _ |- _ => clear H; clear t
         | H1 : ?t ≈ ?t', H2: eqit _ _ _ ?t' _ |- _ => rewrite -H1 in H2; clear H1; clear t'
         end.

(** * Derived notions *)
Definition TVis {EV S} (e : EV) : itree (moduleE EV S) unit :=
  trigger (EVis e).

Definition TAll {EV S} T : itree (moduleE EV S) T :=
  trigger (EAll T).
Definition TExist {EV S} T : itree (moduleE EV S) T :=
  trigger (EExist T).

Definition TUb {EV S R} : itree (moduleE EV S) R :=
  x ← TAll void;;; match (x : void) with end.
Definition TNb {EV S R} : itree (moduleE EV S) R :=
  x ← TExist void;;; match (x : void) with end.

Definition TAssume {EV S} (P : Prop) : itree (moduleE EV S) unit :=
  TAll ({ x : unit | P });;;; Ret ().
Definition TAssert {EV S} (P : Prop) : itree (moduleE EV S) unit :=
  TExist ({ x : unit | P });;;; Ret ().

Definition TAssumeOpt {EV S A} (o : option A) : itree (moduleE EV S) A :=
  x ← TAll ({ x : A | o = Some x });;; Ret (proj1_sig x).
Definition TAssertOpt {EV S A} (o : option A) : itree (moduleE EV S) A :=
  x ← TExist ({ x : A | o = Some x });;; Ret (proj1_sig x).

Definition TGet {EV S} : itree (moduleE EV S) S :=
  trigger EGet.
Definition TPut {EV S} (s : S) : itree (moduleE EV S) unit :=
  trigger (EPut s).

Definition TReceive {EV S A} (e : A → EV) : itree (moduleE EV S) A :=
  x ← TExist A;;;
  TVis (e x);;;;
  Ret x.

(** * tsim *)
Global Instance tsim_itree_l_proper EV S m1 n b:
  Proper ((prod_relation (eqit eq false false) (=)) ==> (=) ==> (=) ==> iff) (tsim n b (itree_trans EV S) m1).
Proof.
  move => [??] [??] [/=Heq ->] ?? -> ?? ->.
  split => Hsim ????; (eapply Hsim; [done|]). { by rewrite Heq. } { by rewrite -Heq. }
Qed.

Global Instance tsim_itree_r_proper EV S m1 b' n b:
  Proper ((=) ==> (=) ==> (prod_relation (eqit eq b' b') (=)) ==> iff) (tsim n b m1 (itree_trans EV S)).
Proof.
  move => ?? -> ?? -> [??] [??] [/=Heq ->].
  split => Hsim ????. { rewrite -Heq. by eapply Hsim. } { rewrite Heq. by eapply Hsim. }
Qed.

Lemma tsim_remember_rec {EV S A B} {mi : mod_trans EV} (PRE : _ → _ → _ → Prop)
      (POST : _ → _ → _ → Prop) (a : A) σi r (h : B → _) s n b:
  PRE a σi s →
  (∀ σi' y s', POST σi' y s' → σi' ⪯{mi, itree_trans EV S, n, b} (h y, s')) →
  (∀ n', oS?b n' ⊆ n →
     Plater (λ b', ∀ σi s h' a, PRE a σi s →
         (∀ σi' y s', POST σi' y s' → σi' ⪯{mi, itree_trans EV S, n', b} (h' y, s')) →
         σi ⪯{mi, itree_trans EV S, n', b'} ((y ← rec r a;;; h' y), s))) →
  σi ⪯{mi, itree_trans EV S, n, b} (y ← rec r a;;; h y, s).
Proof.
  move => ? Hh Hsim x.
  eapply (tsim_remember (ms:=itree_trans _ _)
    (λ n σi '(σt, s), ∃ a h', PRE a σi s ∧ σt = (y ← rec r a;;; h' y) ∧
      ∀ σi' y s', POST σi' y s' → σi' ⪯{mi, itree_trans EV S, n, b} (h' y, s'))). { naive_solver. }
  { move => ???[??]? [?[?[?[?{}Hh]]]]. simplify_eq. split!; [done..|] => ????.
    apply: tsim_mono; [naive_solver|]. etrans; [|done]. apply o_le_S_maybe. }
  move => n' ? IH ?[??] [?[?[?[??]]]]. simplify_eq.
  apply: Hsim; [done| |done..].
  naive_solver.
Qed.

(** * tstep *)
(** ** typeclasses and infrastructure *)
Class ITreeEq {E R} (b : bool) (t t' : itree E R) := {
  itree_eq_proof : eqit eq true b t t'
}.
Global Hint Mode ITreeEq + + + ! - : typeclass_instances.
Lemma ITreeEq_refl {E R} b (t : itree E R) :
  ITreeEq b t t.
Proof. done. Qed.
Lemma ITreeEq_true {E R} b1 b2 (t t' : itree E R) :
  eqit eq b1 b2 t t' →
  ITreeEq true t t'.
Proof. move => ?. constructor. by apply: eqit_mon; [..|done]. Qed.
Lemma ITreeEq_false {E R} b1 (t t' : itree E R) :
  eqit eq b1 false t t' →
  ITreeEq false t t'.
Proof. move => ?. constructor. by apply: eqit_mon; [..|done]. Qed.

Global Hint Extern 5 (ITreeEq _ ?t _) => (assert_fails (is_var t); by apply ITreeEq_refl) : typeclass_instances.
Global Hint Extern 10 (ITreeEq true _ _) => (refine (ITreeEq_true _ _ _ _ _); eassumption) : typeclass_instances.
Global Hint Extern 10 (ITreeEq false _ _) => (refine (ITreeEq_false _ _ _ _); eassumption) : typeclass_instances.

Class ITreeTStep {EV S} (cont b : bool) (t t' : itree (moduleE EV S) unit) := {
  itree_tstep_proof : eqit eq true b t t'
}.
Global Hint Mode ITreeTStep + + + + ! - : typeclass_instances.

Class ITreeTStepS {EV S} (t : itree (moduleE EV S) unit) (s : S) (κ : option EV)
  (P : (itree (moduleE EV S) () → S → Prop) → Prop) := {
    itree_tsteps_proof G:
    P (λ t' s', itree_rel true G (t', s')) →
    (t, s) -{ itree_trans EV S, κ }->ₛ itree_rel true G
}.
Global Hint Mode ITreeTStepS + + ! ! - - : typeclass_instances.

Lemma itree_step_s_itree_step_cont EV S t t' (s : S) (κ : option EV) P `{!ITreeTStep true true t t'}
      `{!ITreeTStepS t' s κ P} :
  ITreeTStepS t s κ P.
Proof. constructor => ??. move: ITreeTStep0 => [->]. by apply itree_tsteps_proof. Qed.
Global Hint Resolve itree_step_s_itree_step_cont | 50 : typeclass_instances.

Lemma itree_step_s_itree_step_no_cont EV S t t' (s : S) `{!ITreeTStep false true t t'}:
  ITreeTStepS t s (@None EV) (λ G, G t' s).
Proof. constructor => ??. move: ITreeTStep0 => [->]. by apply steps_spec_end. Qed.
Global Hint Resolve itree_step_s_itree_step_no_cont | 100 : typeclass_instances.

Lemma itree_tstep_s {EV S} s t t' κ `{!ITreeEq true t t'} `{!ITreeTStepS t' s κ P}:
  TStepS (itree_trans EV S) (t, s) (λ G, G κ (λ G', P (λ t'' s', itree_rel true G' (t'', s')))).
Proof.
  constructor => G HG. eexists _, _. split; [done|] => ? /= ?.
  apply itree_rel_spec_intro. move: ITreeEq0 => [->]. by apply: itree_tsteps_proof.
Qed.
Global Hint Resolve itree_tstep_s : typeclass_instances.

Class ITreeTStepI {EV S} (t : itree (moduleE EV S) unit) (s : S)
      (P : (bool → option EV → ((itree (moduleE EV S) () → S → Prop) → Prop) → Prop) → Prop) := {
    itree_tstepi_proof G:
    P G →
    (t, s) -{ itree_trans EV S }-> (λ b κ Pσ, ∃ (b' : bool) P', G b' κ P' ∧ (b' → b) ∧ ∀ G', P' G' → ∃ t t' s, Pσ (t, s) ∧ eqit eq true false t t' ∧ G' t' s)
}.
Global Hint Mode ITreeTStepI + + ! ! - : typeclass_instances.

Lemma itree_step_i_itree_step_cont EV S t t' (s : S) P `{!ITreeTStep true false t t'}
      `{!ITreeTStepI t' s P} :
  ITreeTStepI (EV:=EV) t s P.
Proof.
  constructor => ??. apply itree_impl_rel_intro.
  move: ITreeTStep0 => [->].
  apply: steps_impl_mono; [by apply itree_tstepi_proof|].
  move => /= * ?? HP ?. destruct!. eexists _, _. split_and!; [done|naive_solver|].
  move => ? /H2[?[?[? [/HP[?[??]] [? HG]]]]]. eexists _, _, _. split_and!; [done| |done].
  etrans; [|done]. apply eqit_flip. by apply: eqit_mon; [..|done].
Qed.
Global Hint Resolve itree_step_i_itree_step_cont | 50 : typeclass_instances.

Lemma itree_step_i_itree_step_no_cont EV S t t' (s : S) `{!ITreeTStep false false t t'} :
  ITreeTStepI (EV:=EV) t s (λ G, G false None (λ G', G' t' s)).
Proof.
  constructor => ??. apply steps_impl_end. eexists _, _. split_and!; [done..|].
  move => /=??. eexists _, _, _. split_and!; [done| |done].
  by apply: itree_tstep_proof.
Qed.
Global Hint Resolve itree_step_i_itree_step_no_cont | 100 : typeclass_instances.

Lemma itree_tstep_i {EV S} s t t' `{!ITreeEq false t t'} `{!ITreeTStepI t' s P}:
  TStepI (itree_trans EV S) (t, s) (λ G, P (λ b κ P', G b κ (λ G', P' (λ t'' s', itree_rel false G' (t'', s'))))).
Proof.
  constructor => ??. apply itree_impl_rel_intro.
  move: ITreeEq0 => [->].
  apply: steps_impl_mono; [by apply itree_tstepi_proof|].
  move => /= * ?? HP ?. destruct!. eexists _, _. split_and!; [done|naive_solver|].
  move => ? /H2[?[?[? [/HP[?[??]] [? HG]]]]]. eexists (_, _). split; [done|]. apply HG. etrans; [|done].
  apply eqit_flip. by apply: eqit_mon; [..|done].
Qed.
Global Hint Resolve itree_tstep_i : typeclass_instances.

(** ** instances *)
Lemma itree_tstep_bind {EV S} A B h (k : A → itree _ B) (t : itree (moduleE EV S) _) cont b:
  ITreeTStep cont b (ITree.bind (ITree.bind t k) h) (ITree.bind t (fun r => ITree.bind (k r) h)).
Proof. constructor. by rewrite bind_bind. Qed.
Global Hint Resolve itree_tstep_bind : typeclass_instances.

Lemma itree_tstep_ret {EV S} A h (x : A) cont b:
  ITreeTStep (EV:=EV) (S:=S) cont b (ITree.bind (Ret x) h) (h x).
Proof. constructor. by rewrite bind_ret_l. Qed.
Global Hint Resolve itree_tstep_ret : typeclass_instances.

Lemma itree_tstep_forever EV S R (t : itree (moduleE EV S) R) b:
  ITreeTStep false b (ITree.forever t) (t;;;; ITree.forever t).
Proof.
  constructor. setoid_rewrite unfold_forever at 1.
  apply: eqit_bind'; [done|]. move => ???.
  by apply eqit_Tau_l.
Qed.
Global Hint Resolve itree_tstep_forever : typeclass_instances.

Lemma itree_step_recursive_bind_bind_s EV S R A B C D (f : A → itree (callE A B +' _) _) t (j : C → _) (k : D → _) (h : R → _) cont b:
  ITreeTStep (EV:=EV) (S:=S) cont b (x ← interp (recursive f) (y ← (z ← t;;; j z);;; k y);;; h x)
                    (x ← interp (recursive f) (z ← t ;;;y ← j z;;; k y);;; h x).
Proof. constructor. by rewrite bind_bind. Qed.
Global Hint Resolve itree_step_recursive_bind_bind_s : typeclass_instances.

Lemma itree_step_recursive_bind_ret_s EV S R A B D (f : A → itree (callE A B +' _) _) t (k : D → _) (h : R → _) cont b:
  ITreeTStep (EV:=EV) (S:=S) cont b (x ← interp (recursive f) (y ← Ret t;;; k y);;; h x)
                    (x ← interp (recursive f) (k t);;; h x).
Proof. constructor. by rewrite bind_ret_l. Qed.
Global Hint Resolve itree_step_recursive_bind_ret_s : typeclass_instances.

Lemma itree_step_recursive_bind_translate_s EV S R Q A B (f : A → itree (callE A B +' _) _) (t : itree (moduleE EV S) R) (k : R → itree (_ +' moduleE EV S) Q) cont h:
  ITreeTStep (EV:=EV) (S:=S) cont true (x ← interp (recursive f) (ITree.bind (translate inr_ t) k);;; h x)
                    (ITree.bind t (fun r => x ← interp (recursive f) (k r);;; h x)).
Proof. constructor. rewrite interp_bind bind_bind interp_translate /=/= interp_trigger_h. done. Qed.
Global Hint Resolve itree_step_recursive_bind_translate_s : typeclass_instances.

Lemma itree_step_recursive_translate_s EV S R A B (f : A → itree (callE A B +' _) _) (t : itree (moduleE EV S) R) h cont:
  ITreeTStep (EV:=EV) (S:=S) cont true (x ← interp (recursive f) (translate inr_ t);;; h x)
                    (x ← t;;; h x).
Proof. constructor. by rewrite interp_translate /= interp_trigger_h. Qed.
Global Hint Resolve itree_step_recursive_translate_s : typeclass_instances.

Lemma itree_step_recursive_call_s EV S R A B (f : A → itree (callE A B +' _) _) k (h : R → _) a:
  ITreeTStep (EV:=EV) (S:=S) false true (x ← interp (recursive f) (y ← call a;;; k y);;; h x)
                    (y ← rec f a;;; x ← interp (recursive f) (k y);;; h x).
Proof. constructor. by rewrite interp_bind interp_recursive_call bind_bind. Qed.
Global Hint Resolve itree_step_recursive_call_s : typeclass_instances.

Lemma itree_step_interp_ret_s EV S R E  (f : E ~> itree (moduleE EV S)) (a : R) h cont:
  ITreeTStep (EV:=EV) (S:=S) cont true (x ← interp f (Ret a);;; h x) (h a).
Proof. constructor. by rewrite interp_ret bind_ret_l. Qed.
Global Hint Resolve itree_step_interp_ret_s : typeclass_instances.

Lemma itree_tstep_Tau_s {EV S} t cont:
  ITreeTStep (EV:=EV) (S:=S) cont true (Tau t) t.
Proof. constructor. by rewrite tau_eutt. Qed.
Global Hint Resolve itree_tstep_Tau_s : typeclass_instances.

Lemma itree_step_Tau_i EV S t s:
  ITreeTStepI (EV:=EV) (S:=S) (Tau t) s (λ G, G true None (λ G', G' t s)).
Proof.
  constructor => ??. apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=. naive_solver.
Qed.
Global Hint Resolve itree_step_Tau_i : typeclass_instances.

Lemma itree_step_Vis_s EV S k (s : S) (e : EV):
  ITreeTStepS (r ← TVis e;;; k r) s (Some e) (λ G, G (k tt) s).
Proof.
  constructor => ??. rewrite bind_trigger.
  apply: steps_spec_step_end. { by econs. } naive_solver.
Qed.
Global Hint Resolve itree_step_Vis_s : typeclass_instances.

Lemma itree_step_Vis_i EV S k s e:
  ITreeTStepI (EV:=EV) (S:=S) (r ← TVis e;;; k r) s (λ G, G true (Some e) (λ G', G' (k tt) s)).
Proof.
  constructor => ??. apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=. cbn in H3; simplify_eq; simplify_K.
  eexists _, _. split_and!; [done..|]. move => /= ? HG. eexists _, _, _. split_and!; [done| |done].
  by setoid_rewrite bind_ret_l.
Qed.
Global Hint Resolve itree_step_Vis_i : typeclass_instances.

Lemma itree_step_Get_s EV S k s:
  ITreeTStepS (EV:=EV) (S:=S) (x ← TGet;;; k x) s None (λ G, G (k s) s).
Proof.
  constructor => ??. rewrite bind_trigger.
  apply: steps_spec_step_end. { by econs. } naive_solver.
Qed.
Global Hint Resolve itree_step_Get_s : typeclass_instances.

Lemma itree_step_Get_i EV S k s:
  ITreeTStepI (EV:=EV) (S:=S) (x ← TGet;;; k x) s (λ G, G true None (λ G', G' (k s) s)).
Proof.
  constructor => ??. apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=. cbn in H3; simplify_eq; simplify_K.
  eexists _, _. split_and!; [done..|]. move => /= ? HG. eexists _, _, _. split_and!; [done| |done].
  by setoid_rewrite bind_ret_l.
Qed.
Global Hint Resolve itree_step_Get_i : typeclass_instances.

Lemma itree_step_Put_s EV S k s s':
  ITreeTStepS (EV:=EV) (S:=S) (x ← TPut s';;; k x) s None (λ G, G (k tt) s').
Proof.
  constructor => ??. rewrite bind_trigger.
  apply: steps_spec_step_end. { by econs. } naive_solver.
Qed.
Global Hint Resolve itree_step_Put_s : typeclass_instances.

Lemma itree_step_Put_i EV S k s s':
  ITreeTStepI (EV:=EV) (S:=S) (x ← TPut s';;; k x) s (λ G, G true None (λ G', G' (k tt) s')).
Proof.
  constructor => ??. apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=. cbn in H3; simplify_eq; simplify_K.
  eexists _, _. split_and!; [done..|]. move => /= ? HG. eexists _, _, _. split_and!; [done| |done].
  by setoid_rewrite bind_ret_l.
Qed.
Global Hint Resolve itree_step_Put_i : typeclass_instances.

Lemma itree_step_All_s EV S T k s:
  ITreeTStepS (EV:=EV) (S:=S) (x ← TAll T;;; k x) s None (λ G, ∀ x, G (k x) s).
Proof.
  constructor => ??. rewrite bind_trigger.
  apply: steps_spec_step_end. { by econs. } naive_solver.
Qed.
Global Hint Resolve itree_step_All_s : typeclass_instances.

Lemma itree_step_All_i EV S T k s:
  ITreeTStepI (EV:=EV) (S:=S) (x ← TAll T;;; k x) s (λ G, G true None (λ G', ∃ x, G' (k x) s)).
Proof.
  constructor => ??. apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=. cbn in H3; simplify_eq; simplify_K.
  eexists _, _. split_and!; [done..|]. move => /= ? [? HG]. eexists _, _, _. split_and!; [naive_solver| |done].
  by setoid_rewrite bind_ret_l.
Qed.
Global Hint Resolve itree_step_All_i : typeclass_instances.

Lemma itree_step_Exist_s EV S T k s:
  ITreeTStepS (EV:=EV) (S:=S) (x ← TExist T;;; k x) s None (λ G, ∃ x, G (k x) s).
Proof.
  constructor => ? [??]. rewrite bind_trigger.
  apply: steps_spec_step_end. { by econs. } naive_solver.
Qed.
Global Hint Resolve itree_step_Exist_s : typeclass_instances.

Lemma itree_step_Exist_i EV S T k s:
  ITreeTStepI (EV:=EV) (S:=S) (x ← TExist T;;; k x) s (λ G, ∀ x, G true None (λ G', G' (k x) s)).
Proof.
  constructor => ??. apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=. cbn in H3; simplify_eq; simplify_K.
  eexists _, _. split_and!; [done..|]. move => /= ? HG. eexists _, _, _. split_and!; [naive_solver| |done].
  by setoid_rewrite bind_ret_l.
Qed.
Global Hint Resolve itree_step_Exist_i : typeclass_instances.

Lemma itree_step_Ub_s EV S T (k : T → _) s:
  ITreeTStepS (EV:=EV) (S:=S) (x ← TUb;;; k x) s None (λ G, True).
Proof.
  constructor => ??. rewrite /TUb bind_bind bind_trigger.
  apply: steps_spec_step_end. { by econs. } move => /=? [[]?].
Qed.
Global Hint Resolve itree_step_Ub_s : typeclass_instances.

Lemma itree_step_Ub_end_s EV S s:
  ITreeTStepS (EV:=EV) (S:=S) TUb s None (λ G, True).
Proof.
  constructor => ??. rewrite /TUb bind_trigger.
  apply: steps_spec_step_end. { by econs. } move => /=? [[]?].
Qed.
Global Hint Resolve itree_step_Ub_end_s : typeclass_instances.

Lemma itree_step_Nb_i EV S T (k : T → _) s:
  ITreeTStepI (EV:=EV) (S:=S) (x ← TNb;;; k x) s (λ G, G true None (λ G', True)).
Proof.
  constructor => ??. apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=. cbn in H3; simplify_eq; simplify_K. destruct x.
Qed.
Global Hint Resolve itree_step_Nb_i : typeclass_instances.

Lemma itree_step_Nb_end_i EV S s:
  ITreeTStepI (EV:=EV) (S:=S) TNb s (λ G, G true None (λ G', True)).
Proof.
  constructor => ??. apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=. cbn in H3; simplify_eq; simplify_K. destruct x.
Qed.
Global Hint Resolve itree_step_Nb_end_i : typeclass_instances.

Lemma itree_step_Assume_s EV S P k s:
  ITreeTStepS (EV:=EV) (S:=S) (x ← TAssume P;;; k x) s None (λ G, P → G (k tt) s).
Proof.
  constructor => ??. rewrite bind_bind bind_trigger. setoid_rewrite bind_ret_l.
  apply: steps_spec_step_end. { by econs. } move => ? [[]]. naive_solver.
Qed.
Global Hint Resolve itree_step_Assume_s : typeclass_instances.

Lemma itree_step_Assume_i EV S P k s:
  ITreeTStepI (EV:=EV) (S:=S) (x ← TAssume P;;; k x) s (λ G, G true None (λ G', P ∧ G' (k tt) s)).
Proof.
  constructor => ??. apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=. cbn in H3; simplify_eq; simplify_K.
  eexists _, _. split_and!; [done..|]. move => /= ? [? HG]. eexists _, _, _. split_and!; [naive_solver| |done].
  setoid_rewrite bind_ret_l. by setoid_rewrite bind_ret_l.
  Unshelve. done.
Qed.
Global Hint Resolve itree_step_Assume_i : typeclass_instances.

Lemma itree_step_Assert_s EV S P k s:
  ITreeTStepS (EV:=EV) (S:=S) (x ← TAssert P;;; k x) s None (λ G, P ∧ G (k tt) s).
Proof.
  constructor => ?[??]. rewrite bind_bind bind_trigger. setoid_rewrite bind_ret_l.
  apply: steps_spec_step_end. { by econs. } naive_solver.
  Unshelve. done.
Qed.
Global Hint Resolve itree_step_Assert_s : typeclass_instances.

Lemma itree_step_Assert_i EV S P k s:
  ITreeTStepI (EV:=EV) (S:=S) (x ← TAssert P;;; k x) s (λ G, P → G true None (λ G', G' (k tt) s)).
Proof.
  constructor => ??. apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=. cbn in H3; simplify_eq; simplify_K. destruct x.
  eexists _, _. split_and!; [naive_solver|done..|].
  move => /= ??. eexists _, _, _. split_and!; [naive_solver| |done].
  setoid_rewrite bind_ret_l. by setoid_rewrite bind_ret_l.
Qed.
Global Hint Resolve itree_step_Assert_i : typeclass_instances.

Lemma itree_step_AssumeOpt_s EV S T (o : option T) k s:
  ITreeTStepS (EV:=EV) (S:=S) (x ← TAssumeOpt o;;; k x) s None (λ G, ∀ x, o = Some x → G (k x) s).
Proof.
  constructor => ??. rewrite bind_bind bind_trigger. setoid_rewrite bind_ret_l.
  apply: steps_spec_step_end. { by econs. } move => ? [[]]. naive_solver.
Qed.
Global Hint Resolve itree_step_AssumeOpt_s : typeclass_instances.

Lemma itree_step_AssumeOpt_i EV S T (o : option T) k s:
  ITreeTStepI (EV:=EV) (S:=S) (x ← TAssumeOpt o;;; k x) s (λ G, G true None (λ G', ∃ x, o = Some x ∧ G' (k x) s)).
Proof.
  constructor => ??. apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=. cbn in H3; simplify_eq; simplify_K.
  eexists _, _. split_and!; [done..|]. move => /= ? [? [? HG]]. subst.
  eexists _, _, _. split_and!; [naive_solver| |done].
  setoid_rewrite bind_ret_l.
  Unshelve. 2: { by econstructor. } by setoid_rewrite bind_ret_l.
Qed.
Global Hint Resolve itree_step_AssumeOpt_i : typeclass_instances.

Lemma itree_step_AssertOpt_s EV S T (o : option T) k s:
  ITreeTStepS (EV:=EV) (S:=S) (x ← TAssertOpt o;;; k x) s None (λ G, ∃ x, o = Some x ∧ G (k x) s).
Proof.
  constructor => ?[?[??]]. rewrite bind_bind bind_trigger. setoid_rewrite bind_ret_l.
  apply: steps_spec_step_end. { by econs. } Unshelve. 2: by econstructor. move => [??] [??]; simplify_eq. done.
Qed.
Global Hint Resolve itree_step_AssertOpt_s : typeclass_instances.

Lemma itree_step_AssertOpt_i EV S T (o : option T) k s:
  ITreeTStepI (EV:=EV) (S:=S) (x ← TAssertOpt o;;; k x) s (λ G, ∀ x, o = Some x → G true None (λ G', G' (k x) s)).
Proof.
  constructor => ??. apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=. cbn in H3; simplify_eq; simplify_K. destruct x.
  eexists _, _. split_and!; [naive_solver|done..|].
  move => /= ??. eexists _, _, _. split_and!; [naive_solver| |done].
  setoid_rewrite bind_ret_l. by setoid_rewrite bind_ret_l.
Qed.
Global Hint Resolve itree_step_AssertOpt_i : typeclass_instances.

Global Hint Opaque TVis TAll TExist TUb TNb TAssume TAssert TAssumeOpt TAssertOpt TGet TPut : typeclass_instances.

Module itree_test.
Local Definition test_itree : itree (moduleE _ _) ()
  := ((s ← TGet;;; TPut (S s);;;; Ret tt) ;;;; TVis (1);;;; Ret tt);;;; TNb.
Goal trefines (itree_mod test_itree 0) (itree_mod test_itree 0).
  apply tsim_implies_trefines => ? /=. rewrite /test_itree.

  tstep_i; clear_itree.
  tstep_i; clear_itree.
  tstep_i; clear_itree.
  tstep_s; clear_itree.
  tstep_s; clear_itree.
  tstep_s; clear_itree.
  split!. clear_itree.
  tstep_s; clear_itree.
  tstep_i; clear_itree.
  done.
Abort.
End itree_test.
