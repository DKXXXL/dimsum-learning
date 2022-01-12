From Paco Require Import paco.
From ITree Require Export ITree ITreeFacts.
From ITree Require Export ITree.
Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.proof_techniques.

Notation "' x ← y ;;; z" := (ITree.bind y (λ x : _, z))
  (at level 20, x pattern, y at level 100, z at level 200) : stdpp_scope.
Notation "x ← y ;;; z" := (ITree.bind y (λ x : _, z))
  (at level 20, y at level 100, z at level 200) : stdpp_scope.
Notation "y ;;;; z" := (ITree.bind y (λ _, z))
  (at level 100, z at level 200, right associativity) : stdpp_scope.


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

Inductive mod_itree_step EV S : (itree (moduleE EV S) unit * S) → option EV → ((itree (moduleE EV S) unit * S) → Prop) → Prop :=
| ITauS t t' s:
  observe t = TauF t' →
  mod_itree_step EV S (t, s) None (λ σ', σ' = (t', s))
| IVisS t t' s e:
  observe t = VisF (EVis e) t' →
  mod_itree_step EV S (t, s) (Some e) (λ σ', σ' = (t' tt, s))
| IAllS T t t' s:
  observe t = VisF (EAll T) t' →
  mod_itree_step EV S (t, s) None (λ σ', ∃ x, σ' = (t' x, s))
| IExistS T x t t' s:
  observe t = VisF (EExist T) t' →
  mod_itree_step EV S (t, s) None (λ σ', σ' = (t' x, s))
| IGetS t t' s:
  observe t = VisF (EGet) t' →
  mod_itree_step EV S (t, s) None (λ σ', σ' = (t' s, s))
| IPutS t t' s s':
  observe t = VisF (EPut s') t' →
  mod_itree_step EV S (t, s) None (λ σ', σ' = (t' (), s'))
.

Definition mod_itree EV S := Mod (mod_itree_step EV S).

Global Instance itree_vis_no_all EV S: VisNoAll (mod_itree EV S).
Proof. move => *. invert_all @m_step; naive_solver. Qed.

(* Section test. *)
(* Polymorphic Universe u v w x y. *)
(* Set Printing Universes. *)
(*     Lemma itree_step_interp_translate_s EV S R (F : Type@{x} → Type@{y}) (E : Type@{v} → Type@{w}) (f : ∀ T : Type@{u}, E T -> F T) *)
(*           (g : ∀ T: Type, F T → itree (moduleE EV S) T) (t : itree E R) s κs: *)
(*       TSimStepS (mod_itree EV S) (interp f (translate g t), s) κs *)
(*             (λ G, G κs ((interp (λ _ e, g _ (f _ e)), s), s)). *)
(*     Proof. *)
(*       constructor => ????. eexists tnil, _. split; [done|]. *)
(*       apply itree_rel_intro. rewrite interp_bind bind_bind. tend => ? <-. done. *)
(*     Qed. *)
(*     Global Hint Resolve itree_step_interp_bind_s : tsim. *)

(** [Tau] *)
(* TODO: Are all these lemmas necessary? *)
Lemma tnhas_trace_Tau' {EV S} t t' n n' Pσ s κs:
  observe t = TauF t' →
  (t', s) ~{mod_itree EV S, κs, n}~>ₜ Pσ →
  tiS n ⊆ n' →
  (t, s) ~{mod_itree EV S, κs, n'}~>ₜ Pσ.
Proof.
  move => Htau Ht Hsub. apply: (TNTraceStep _ _ (λ _, n)); [by econs| | |simpl; done].
  - move => /= ? ->. done.
  - etrans; [|done]. econs. by econs.
Qed.
Lemma tnhas_trace_Tau {EV S} t n n' Pσ s κs:
  (t, s) ~{mod_itree EV S, κs, n}~>ₜ Pσ →
  tiS n ⊆ n' →
  (Tau t, s) ~{mod_itree EV S, κs, n'}~>ₜ Pσ.
Proof. by apply tnhas_trace_Tau'. Qed.

Lemma thas_trace_Tau' {EV S} t t' Pσ s κs:
  observe t = TauF t' →
  (t', s) ~{mod_itree EV S, κs}~>ₜ Pσ →
  (t, s) ~{mod_itree EV S, κs}~>ₜ Pσ.
Proof. move => Htau Ht. tstep_None; [by econs|]. naive_solver. Qed.
Lemma thas_trace_Tau {EV S} t Pσ s κs:
  (t, s) ~{mod_itree EV S, κs}~>ₜ Pσ →
  (Tau t, s) ~{mod_itree EV S, κs}~>ₜ Pσ.
Proof. by apply thas_trace_Tau'. Qed.

Lemma tnhas_trace_Tau_inv' {EV S} t t' n Pσ s κs:
  observe t' = TauF t →
  (t', s) ~{mod_itree EV S, κs, n}~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ (t', s)) ∨
    ∃ n', tiS n' ⊆ n ∧ (t, s) ~{ mod_itree _ _,  κs, n' }~>ₜ Pσ).
Proof.
  move => Htau Ht. thas_trace_inv Ht. { naive_solver. }
  right. invert_all @m_step; rewrite ->Htau in *; simplify_eq.
  eexists _. split; last first.
  - rewrite -H0. naive_solver.
  - etrans; [|done]. econs. by econs.
  Unshelve. done.
Qed.
Lemma tnhas_trace_Tau_inv {EV S} t n Pσ s κs:
  (Tau t, s) ~{mod_itree EV S, κs, n}~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ (Tau t, s)) ∨
    ∃ n', tiS n' ⊆ n ∧ (t, s) ~{ mod_itree _ _,  κs, n' }~>ₜ Pσ).
Proof. by apply tnhas_trace_Tau_inv'. Qed.

Lemma thas_trace_Tau_inv' {EV S} t t' Pσ s κs:
  observe t' = TauF t →
  (t', s) ~{mod_itree EV S, κs}~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ (t', s)) ∨ (t, s) ~{ mod_itree _ _,  κs }~>ₜ Pσ).
Proof.
  move => Htau /thas_trace_n[? /(tnhas_trace_Tau_inv' _ _ _ _ _) Ht]. specialize (Ht _ ltac:(done)).
  apply: under_tall_mono'; [done..|] => {Ht} ? [[??]|[?[??]]]. { naive_solver. }
  right. apply thas_trace_n. naive_solver.
Qed.
Lemma thas_trace_Tau_inv {EV S} t Pσ s κs:
  (Tau t, s) ~{mod_itree EV S, κs}~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ (Tau t, s)) ∨ (t, s) ~{ mod_itree _ _,  κs }~>ₜ Pσ).
Proof. by apply thas_trace_Tau_inv'. Qed.

(** [Ret] *)
Lemma tnhas_trace_Ret_inv' {EV S} t x n Pσ s κs:
  observe t = RetF x →
  (t, s) ~{mod_itree EV S, κs, n}~>ₜ Pσ →
  under_tall κs (λ κs, tnil ⊆ κs ∧ Pσ (t, s)).
Proof.
  move => Hret. move => Ht.
  thas_trace_inv Ht; [done|].
  invert_all @m_step; rewrite ->Hret in *; simplify_eq.
Qed.
Lemma tnhas_trace_Ret_inv {EV S} x n Pσ s κs:
  (Ret x, s) ~{mod_itree EV S, κs, n}~>ₜ Pσ →
  under_tall κs (λ κs, tnil ⊆ κs ∧ Pσ (Ret x, s)).
Proof. by apply: tnhas_trace_Ret_inv'. Qed.

Lemma thas_trace_Ret_inv' {EV S} t x Pσ s κs:
  observe t = RetF x →
  (t, s) ~{mod_itree EV S, κs}~>ₜ Pσ →
  under_tall κs (λ κs, tnil ⊆ κs ∧ Pσ (t, s)).
Proof. move => Hret /thas_trace_n [? /(tnhas_trace_Ret_inv' _ _ _ _ _) Ht]. naive_solver. Qed.
Lemma thas_trace_Ret_inv {EV S} x Pσ s κs:
  (Ret x, s) ~{mod_itree EV S, κs}~>ₜ Pσ →
  under_tall κs (λ κs, tnil ⊆ κs ∧ Pσ (Ret x, s)).
Proof. by apply: thas_trace_Ret_inv'. Qed.

(** [Vis] *)
Lemma thas_trace_Vis_inv {EV S} e k Pσ s κs:
  (vis (EVis e) k, s) ~{mod_itree EV S, κs}~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ (vis (EVis e) k, s)) ∨
   ∃ κs', tcons e κs' ⊆ κs ∧ (k (), s) ~{ mod_itree EV S, κs' }~>ₜ Pσ ).
Proof.
  move => Ht. thas_trace_inv Ht; [naive_solver|].
  invert_all' @m_step; simpl in *; simplify_eq; simplify_K; specialize_hyps.
  naive_solver.
Qed.

Lemma thas_trace_Vis {EV S} e k Pσ s κs:
  (k tt, s) ~{mod_itree EV S, κs}~>ₜ Pσ →
  (vis (EVis e) k, s) ~{mod_itree EV S, tcons e κs}~>ₜ Pσ.
Proof. move => Ht. tstep_Some; [by econs|] => ? ->. done. Qed.

(** [All] *)
Lemma thas_trace_All_inv {EV S} T k Pσ s κs:
  (vis (EAll T) k, s) ~{mod_itree EV S, κs}~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ (vis (EAll T) k, s)) ∨
   ∀ x, (k x, s) ~{ mod_itree EV S, κs }~>ₜ Pσ ).
Proof.
  move => Ht. thas_trace_inv Ht; [naive_solver|].
  invert_all' @m_step; simpl in *; simplify_eq; simplify_K; specialize_hyps.
  right => ?. revert select (_ ⊆ _) => <- /=. naive_solver.
Qed.
Lemma thas_trace_All {EV S} T k Pσ s κs:
  (∀ x, (k x, s) ~{mod_itree EV S, κs}~>ₜ Pσ) →
  (vis (EAll T) k, s) ~{mod_itree EV S, κs}~>ₜ Pσ.
Proof. move => Ht. tstep_None; [by apply: IAllS|] => ? [? ->]. done. Qed.

(** [Exist] *)
Lemma thas_trace_Exist_inv {EV S} T k Pσ s κs:
  (vis (EExist T) k, s) ~{mod_itree EV S, κs}~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ (vis (EExist T) k, s)) ∨
   ∃ x, (k x, s) ~{ mod_itree EV S, κs }~>ₜ Pσ ).
Proof.
  move => Ht. thas_trace_inv Ht; [naive_solver|].
  invert_all' @m_step; simpl in *; simplify_eq; simplify_K; specialize_hyps.
  right. eexists _. revert select (_ ⊆ _) => <- /=. naive_solver.
Qed.
Lemma thas_trace_Exist {EV S} T x k Pσ s κs:
  (k x, s) ~{mod_itree EV S, κs}~>ₜ Pσ →
  (vis (EExist T) k, s) ~{mod_itree EV S, κs}~>ₜ Pσ.
Proof. move => Ht. tstep_None; [by apply: (IExistS _ _ _ x)|] => ? ->. done. Qed.

(** [Get] *)
Lemma thas_trace_Get_inv {EV S} k Pσ s κs:
  (vis EGet k, s) ~{mod_itree EV S, κs}~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ (vis EGet k, s)) ∨
   (k s, s) ~{ mod_itree EV S, κs }~>ₜ Pσ ).
Proof.
  move => Ht. thas_trace_inv Ht; [naive_solver|].
  invert_all' @m_step; simpl in *; simplify_eq; simplify_K; specialize_hyps.
  right. revert select (_ ⊆ _) => <- /=. naive_solver.
Qed.
Lemma thas_trace_Get {EV S} k Pσ s κs:
  (k s, s) ~{mod_itree EV S, κs}~>ₜ Pσ →
  (vis EGet k, s) ~{mod_itree EV S, κs}~>ₜ Pσ.
Proof. move => Ht. tstep_None; [by apply: IGetS|] => ? ->. done. Qed.

(** [Put] *)
Lemma thas_trace_Put_inv {EV S} k Pσ s s' κs:
  (vis (EPut s') k, s) ~{mod_itree EV S, κs}~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ (vis (EPut s') k, s)) ∨
   (k (), s') ~{ mod_itree EV S, κs }~>ₜ Pσ ).
Proof.
  move => Ht. thas_trace_inv Ht; [naive_solver|].
  invert_all' @m_step; simpl in *; simplify_eq; simplify_K; specialize_hyps.
  right. revert select (_ ⊆ _) => <- /=. naive_solver.
Qed.
Lemma thas_trace_Put {EV S} k Pσ s s' κs:
  (k tt, s') ~{mod_itree EV S, κs}~>ₜ Pσ →
  (vis (EPut s') k, s) ~{mod_itree EV S, κs}~>ₜ Pσ.
Proof. move => Ht. tstep_None; [by econs|] => ? ->. done. Qed.

(** eutt mono *)
Lemma steps_spec_eutt_mono {EV S} t' σ κ Pσ Pσ' b1 b2:
  (prod_relation (eqit eq b1 b2) (=) ==> iff)%signature Pσ Pσ' →
  σ -{ mod_itree EV S, κ }->ₛ Pσ →
  eqit eq b1 b2 σ.1 t' →
  (t', σ.2) -{ mod_itree EV S, κ }->ₛ Pσ'.
Proof.
  move => HP Ht Heq.
  elim/@prop_least_fixpoint_ind_wf: Ht t' Heq => {}σ IHn t' Heq.
  destruct σ as [t s]; simpl in *.
  punfold Heq. unfold eqit_ in Heq at 1.
  move: Heq. move Hot: (observe t) => ot. move Hot': (observe t') => ot' Heq.
  elim: Heq t t' s IHn Hot Hot'.
  - move => ?? -> t t' s IHn Hot Hot'.
    move: IHn => [[??]|[?[?[?[??]]]]]. 2: { invert_all @m_step; congruence. } subst.
    apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=.
    rewrite (itree_eta t) Hot (itree_eta t') Hot'. done.
  - move => m1 m2 [REL|//] t t' s IHn Hot Hot'. rewrite -/(eqit _ _ _) in REL.
    move: IHn => [[??]|[?[?[? [? Ht]]]]]; simplify_eq.
    + apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=.
      rewrite (itree_eta t) Hot (itree_eta t') Hot'. by apply eqit_Tau.
    + invert_all @m_step; try congruence. have ?: t'0 = m1 by congruence. subst.
      move: Ht => [[??]|[? Hfix]]; simplify_eq.
      * apply: steps_spec_step_end. { by econs. } move => ? ->. eapply HP; [|done]. done.
      * apply: steps_spec_step; [by econs|] => ? ->. move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_spec_rec_mono (mod_itree _ _)). }
        apply: IH => /=. congruence.
  - move => u e k1 k2 Hu t t' s IHn Hot Hot'.
    move: IHn => [[??]|[?[?[? [? Ht]]]]]. {
      subst. apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=.
      rewrite (itree_eta t) Hot (itree_eta t') Hot'.
      apply eqit_Vis => v. move: (Hu v) => [|//]. done.
    }
    invert_all @m_step; rewrite ->Hot in *; simplify_eq; simplify_K.
    + apply: steps_spec_step_end; [by econs|] => ? /= ->. move: Ht => [[??]|[??//]].
      eapply HP; [|done]. split; [|done].
      move: (Hu tt) => [|//]. done.
    + apply: steps_spec_step; [by econs|] => ? /= [x ->].
      have [|[??]|[? Hfix]]:= Ht (t'0 x, s); subst. { naive_solver. }
      * apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=.
        move: (Hu x) => [|//]. done.
      * move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_spec_rec_mono (mod_itree _ _)). }
        apply: IH => /=. move: (Hu x) => [|//]. done.
    + apply: steps_spec_step; [by econs|] => ? /= ->.
      have [[??]|[? Hfix]]:= Ht; subst.
      * apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=.
        move: (Hu x) => [|//]. done.
      * move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_spec_rec_mono (mod_itree _ _)). }
        apply: IH => /=. move: (Hu x) => [|//]. done.
    + apply: steps_spec_step; [by econs|] => ? /= ->.
      have [[??]|[? Hfix]]:= Ht; subst.
      * apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=.
        move: (Hu s) => [|//]. done.
      * move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_spec_rec_mono (mod_itree _ _)). }
        apply: IH => /=. move: (Hu s) => [|//]. done.
    + apply: steps_spec_step; [by econs|] => ? /= ->.
      have [[??]|[? Hfix]]:= Ht; subst.
      * apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=.
        move: (Hu tt) => [|//]. done.
      * move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_spec_rec_mono (mod_itree _ _)). }
        apply: IH => /=. move: (Hu tt) => [|//]. done.
  - move => t1 ot2 ? REL IH t t' s IHn Hot Hot'.
    move: REL => /fold_eqitF REL. specialize (REL _ _ ltac:(done) ltac:(done)).
    move: IHn => [[??]|[?[?[? [? Ht]]]]]; simplify_eq.
    + apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=. etrans; [|done].
      destruct b1 => //. rewrite (itree_eta t) Hot. by apply eqit_Tau_l.
    + invert_all @m_step; try congruence. have ?: t'0 = t1 by congruence. subst.
      move: Ht => [[??]|[? Hfix]]; simplify_eq.
      * apply: steps_spec_end. eapply HP; [|done]. split; [|done] => /=. done.
      * apply: IH; [|done|done].
        move: Hfix => /(prop_least_fixpoint_unfold_1 _ _)[|IH ?].
        { apply wf_pred_mono. apply (steps_spec_rec_mono (mod_itree _ _)). }
        apply: mono_pred. 3: done. { apply (steps_spec_rec_mono (mod_itree _ _)). } done.
  - move => ot1 t2 ? REL IH t t' s IHn Hot Hot'.
    apply: steps_spec_step; [by econs|] => ? /= ->.
    by apply: IH.
Qed.

Lemma tnhas_trace_eutt_mono {EV S} t t' s κs Pσ Pσ' b1 n:
  (prod_relation (eqit eq b1 false) (=) ==> iff)%signature Pσ Pσ' →
  (t, s) ~{ mod_itree EV S, κs, n }~>ₜ Pσ →
  eqit eq b1 false t t' →
  (t', s) ~{ mod_itree EV S, κs, n }~>ₜ Pσ'.
Proof.
  move => HP Ht Heq.
  elim/ti_lt_ind: n κs t t' s Ht Heq.
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
    invert_all @m_step; rewrite ->Hot in *; simplify_eq; simplify_K.
    + specialize (H1 _ ltac:(done)).
      apply: (TNTraceStep _ _ (const (fn ((t'0 (), s) ↾ eq_refl)))).
      { by econs. } 3: { simpl; done. } 2: { etrans; [|done]. econs. econs => -[??] /=. by econs. }
      move => ? /= ->. apply: IHn;[|done|].
      * etrans; [|done]. econs. by econs.
      * move: (Hu tt) => [|//]. done.
    + apply: (TNTraceStep _ _ (const (tiChoice T (λ x, fn ((t'0 x, s) ↾ ex_intro _ x eq_refl))))).
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
    + apply: IH => //. apply: tnhas_trace_mono; [done..| by apply: ti_lt_impl_le |done].
  - move => *. subst. done.
Qed.

Lemma thas_trace_eutt_mono {EV S} t t' s κs Pσ Pσ':
  (prod_relation (eutt eq) (=) ==> iff)%signature Pσ Pσ' →
  (t, s) ~{ mod_itree EV S, κs }~>ₜ Pσ →
  t ≈ t' →
  (t', s) ~{ mod_itree EV S, κs }~>ₜ Pσ'.
Proof.
  move => HP /thas_trace_n[n Ht] Heq.
  elim/ti_lt_ind: n κs t t' s Ht Heq HP.
  move => n IHn κs t t' s Ht Heq HP.
  punfold Heq. unfold eqit_ in Heq at 1.
  move: Heq. move Hot: (observe t) => ot. move Hot': (observe t') => ot' Heq.
  elim: Heq t t' n κs s IHn Ht Hot Hot'.
  - move => ?? -> t t' n κs s IHn Ht Hot Hot'.
    move: Ht => /(tnhas_trace_Ret_inv' _ _ _ _ _)Ht. specialize (Ht _ ltac:(done)).
    apply: thas_trace_under_tall; [done..|] => ? [??]. tend.
    eapply HP; [|done]. split; [|done] => /=. rewrite (itree_eta t) Hot (itree_eta t') Hot'. done.
  - move => m1 m2 [REL|//] t t' n κs s IHn Ht Hot Hot'. rewrite -/(eqit _ _ _) in REL.
    apply: thas_trace_Tau'; [done|].
    move: Ht => /(tnhas_trace_Tau_inv' _ _ _ _ _)Ht. specialize (Ht _ ltac:(done)).
    apply: thas_trace_under_tall; [done..|] => ? /= [[??]|[?[??]]].
    + tend. eapply HP; [|done]. split => //=. by rewrite (itree_eta t) Hot tau_eutt REL.
    + apply: IHn; [done|done| |done]. by rewrite REL.
  - move => u e k1 k2 Hu t t' n κs s IHn Ht Hot Hot'.
    thas_trace_inv Ht. {
      tend. eapply HP; [|done]. split; [|done] => /=. rewrite (itree_eta t) Hot (itree_eta t') Hot'.
      apply eqit_Vis => v. move: (Hu v) => [|//]. done.
    }
    revert select (_ ⊆@{trace _} _) => <-.
    invert_all @m_step; rewrite ->Hot in *; simplify_eq; simplify_K.
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
      move: REL => /fold_eqitF REL. specialize (REL _ _ ltac:(done) ltac:(done)). rewrite -REL.
      by rewrite (itree_eta t) Hot tau_eutt.
    + apply: IH => //. apply: tnhas_trace_mono; [done..| by apply: ti_lt_impl_le |done].
  - move => ot1 t2 ? REL IH t t' n κs s IHn Ht Hot Hot'.
    tstep_None; [by econs|] => ? ->. by apply: IH.
Qed.

Global Instance mod_itree_proper EV S b1 b2:
  Proper ((prod_relation (eqit eq b1 b2) (=)) ==> (=) ==> (prod_relation (eutt eq) (=) ==> iff) ==> iff) (thas_trace (mod_itree EV S)).
Proof.
  move => [??] [??] [/= Heq ->] ?? -> ?? Hf.
  split => ?.
  all: apply: thas_trace_eutt_mono; [try done| done |].
  - by apply: eqit_mon; [| | |done].
  - move => ?? [??]. symmetry. by apply Hf.
  - symmetry. by apply: eqit_mon; [| | |done].
Qed.

Definition itree_rel {E R S} (P : itree E R * S → Prop) (t : itree E R * S) : Prop :=
  ∀ t', t.1 ≈ t' → P (t', t.2).
Global Instance itree_rel_proper E R S P:
    Proper ((prod_relation (eutt eq) (=) ==> iff)) (@itree_rel E R S P).
Proof.
  move => [??] [??] [Heq ?]. simplify_eq/=. rewrite /itree_rel /=.
  split => ??; [rewrite -Heq|rewrite Heq]; naive_solver.
Qed.
Typeclasses Opaque itree_rel.

Lemma itree_rel_intro EV S σ κs P:
  σ ~{mod_itree EV S, κs }~>ₜ itree_rel P →
  σ ~{mod_itree EV S, κs }~>ₜ P.
Proof. move => Ht. apply: thas_trace_mono; [done|done|] => -[??] Hp. by apply: Hp. Qed.

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

(** * tsim *)

Global Instance tsim_itree_r_proper EV S m1 b' n b:
  Proper ((=) ==> (=) ==> (prod_relation (eqit eq b' b') (=)) ==> iff) (tsim n b m1 (mod_itree EV S)).
Proof.
  move => ?? -> ?? -> [??] [??] [/=Heq ->].
  split => Hsim ????. { rewrite -Heq. by eapply Hsim. } { rewrite Heq. by eapply Hsim. }
Qed.

(** * tstep *)
(** These step rules should always apply to itree with a bind at the
top-level and discriminate on the argument of the bind.
TODO: add a step rule that adds a bind a the top-level if there is none.  *)
Lemma itree_step_bind_s EV S A B (t : itree _ A) (k : A → itree _ B) h s:
  TStepS (mod_itree EV S) (ITree.bind (ITree.bind t k) h, s)
            (λ G, G None (λ G', itree_rel G' ((ITree.bind t (fun r => ITree.bind (k r) h)), s))).
Proof.
  constructor => G HG. eexists _, _. split; [done|] => ? /= ?.
  apply itree_rel_intro. rewrite bind_bind. tend.
Qed.
Global Hint Resolve itree_step_bind_s : tstep.

Lemma itree_step_Ret_s EV S A (x : A) h s:
  TStepS (mod_itree EV S) (ITree.bind (Ret x) h, s) (λ G, G None (λ G', itree_rel G' (h x, s))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= ?.
  apply itree_rel_intro. rewrite bind_ret_l. tend.
Qed.
Global Hint Resolve itree_step_Ret_s : tstep.

Lemma itree_step_Tau_s EV S t s:
  TStepS (mod_itree EV S) (Tau t, s) (λ G, G None (λ G', itree_rel G' (t, s))).
Proof.
  constructor => ?. eexists _, _. split; [done|] => ? /= ?.
  apply itree_rel_intro. rewrite tau_eutt. tend.
Qed.
Global Hint Resolve itree_step_Tau_s : tstep.

Lemma itree_step_Vis_s EV S k s e:
  TStepS (mod_itree EV S) (TVis e;;;; k, s) (λ G, G (Some e) (λ G', itree_rel G' (k, s))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= ?.
  apply itree_rel_intro. rewrite bind_trigger.
  apply: thas_trace_Vis. tend.
Qed.
Global Hint Resolve itree_step_Vis_s : tstep.

Lemma itree_step_All_s EV S T k s:
  TStepS (mod_itree EV S) (x ← TAll T;;; k x, s)
            (λ G, G None (λ G', ∀ x, itree_rel G' (k x, s))).
Proof.
  constructor => ?. eexists _, _. split; [done|] => ? /= ?.
  apply itree_rel_intro. rewrite bind_trigger.
  apply: thas_trace_All. tend.
Qed.
Global Hint Resolve itree_step_All_s : tstep.

Lemma itree_step_Exist_s EV S T k s:
  TStepS (mod_itree EV S) (x ← TExist T;;; k x, s)
            (λ G, G None (λ G', ∃ x, itree_rel G' (k x, s))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= [??].
  apply itree_rel_intro. rewrite bind_trigger.
  apply: thas_trace_Exist. tend.
Qed.
Global Hint Resolve itree_step_Exist_s : tstep.

Lemma itree_step_Ub_s EV S T (k : T → _) s:
  TStepS (mod_itree EV S) (x ← TUb;;; k x, s) (λ G, G None (λ G', True)).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= ?.
  apply itree_rel_intro. rewrite /TUb bind_bind bind_trigger.
  apply: thas_trace_All. case.
Qed.
Global Hint Resolve itree_step_Ub_s : tstep.

Lemma itree_step_Assume_s EV S P k s:
  TStepS (mod_itree EV S) (TAssume P;;;; k, s) (λ G, G None (λ G', P → itree_rel G' (k, s))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= ?.
  apply itree_rel_intro. rewrite /TAssume bind_bind bind_trigger.
  apply: thas_trace_All => -[??]. rewrite bind_ret_l. tend. naive_solver.
Qed.
Global Hint Resolve itree_step_Assume_s : tstep.

Lemma itree_step_Assert_s EV S P k s:
  TStepS (mod_itree EV S) (TAssert P;;;; k, s) (λ G, G None (λ G', P ∧ itree_rel G' (k, s))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= [??].
  apply itree_rel_intro. rewrite /TAssert bind_bind bind_trigger.
  apply: thas_trace_Exist. { by constructor. } rewrite bind_ret_l. tend.
Qed.
Global Hint Resolve itree_step_Assert_s : tstep.

Lemma itree_step_AssumeOpt_s EV S A (o : option A) k s:
  TStepS (mod_itree EV S) (x ← TAssumeOpt o;;; k x, s) (λ G, G None (λ G', ∀ x, (o = Some x) → itree_rel G' (k x, s))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= ?.
  apply itree_rel_intro. rewrite /TAssume bind_bind bind_trigger.
  apply: thas_trace_All => -[??]. rewrite bind_ret_l. tend. naive_solver.
Qed.
Global Hint Resolve itree_step_AssumeOpt_s : tstep.

Lemma itree_step_AssertOpt_s EV S A (o : option A) k s:
  TStepS (mod_itree EV S) (x ← TAssertOpt o;;; k x, s) (λ G, G None (λ G', ∃ x, o = Some x ∧ itree_rel G' (k x, s))).
Proof.
  constructor => ??. subst. eexists _, _. split; [done|] => ? /= [?[??]].
  apply itree_rel_intro. rewrite /TAssert bind_bind bind_trigger.
  apply: (thas_trace_Exist _ (exist _ _ _)); [done|] => ?. rewrite bind_ret_l. tend.
Qed.
Global Hint Resolve itree_step_AssertOpt_s : tstep.

Lemma itree_step_recursive_bind_translate_s EV S R Q A B (f : A → itree (callE A B +' _) _) (t : itree (moduleE EV S) R) (k : R → itree (_ +' moduleE EV S) Q) h s:
  TStepS (mod_itree EV S) (x ← interp (recursive f) (ITree.bind (translate inr_ t) k);;; h x, s)
            (λ G, G None (λ G', itree_rel G' ((ITree.bind t (fun r => x ← interp (recursive f) (k r);;; h x)), s))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= ?.
  apply itree_rel_intro. rewrite interp_bind bind_bind interp_translate /= interp_trigger_h.
  tend.
Qed.
Global Hint Resolve itree_step_recursive_bind_translate_s : tstep.

Lemma itree_step_recursive_translate_s EV S R A B (f : A → itree (callE A B +' _) _) (t : itree (moduleE EV S) R) h s:
  TStepS (mod_itree EV S) (x ← interp (recursive f) (translate inr_ t);;; h x, s)
            (λ G, G None (λ G', itree_rel G' ((x ← t;;; h x), s))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= ?.
  apply itree_rel_intro. rewrite interp_translate /= interp_trigger_h.
  tend.
Qed.
Global Hint Resolve itree_step_recursive_translate_s : tstep.
Lemma itree_step_recursive_call_s EV S R A B (f : A → itree (callE A B +' _) _) k (h : R → _) s a:
  TStepS (mod_itree EV S) (x ← interp (recursive f) (y ← call a;;; k y);;; h x, s)
            (λ G, G None (λ G', itree_rel G' ((y ← rec f a;;; x ← interp (recursive f) (k y);;; h x), s))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= ?.
  apply itree_rel_intro. rewrite interp_bind interp_recursive_call bind_bind.
  tend.
Qed.
Global Hint Resolve itree_step_recursive_call_s : tstep.

Lemma itree_step_interp_ret_s EV S R E  (f : E ~> itree (moduleE EV S)) (a : R) h s:
  TStepS (mod_itree EV S) (x ← interp f (Ret a);;; h x, s) (λ G, G None (λ G', itree_rel G' (h a, s))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= ?.
  apply itree_rel_intro. rewrite interp_ret bind_ret_l. tend.
Qed.
Global Hint Resolve itree_step_interp_ret_s : tstep.


Lemma tsim_remember_rec {EV S A B} {mi : module EV} (PRE : _ → _ → _ → Prop)
      (POST : _ → _ → _ → Prop) (a : A) σi r (h : B → _) s n b:
  PRE a σi s →
  (∀ σi' y s', POST σi' y s' → σi' ⪯{mi, mod_itree EV S, n, b} (h y, s')) →
  (∀ n, Plater (λ b', ∀ σi s h' a, PRE a σi s →
         (∀ σi' y s', POST σi' y s' → σi' ⪯{mi, mod_itree EV S, n, b} (h' y, s')) →
         σi ⪯{mi, mod_itree EV S, n, b'} ((y ← rec r a;;; h' y), s))) →
  σi ⪯{mi, mod_itree EV S, n, b} (y ← rec r a;;; h y, s).
Proof.
  move => ? Hh Hsim x.
  eapply (tsim_remember (ms:=mod_itree _ _)
    (λ n σi '(σt, s), ∃ a h', PRE a σi s ∧ σt = (y ← rec r a;;; h' y) ∧
      ∀ σi' y s', POST σi' y s' → σi' ⪯{mi, mod_itree EV S, n, b} (h' y, s'))). { naive_solver. }
  { move => ???[??]? [?[?[?[?{}Hh]]]]. simplify_eq. eexists _, _. split_and!; [done..|] => ????.
    apply: tsim_mono; [naive_solver|]. by apply ti_lt_impl_le. }
  move => n' IH ?[??] [?[?[?[??]]]]. simplify_eq.
  apply: Hsim; [|done..].
  naive_solver.
Qed.

Require refframe.example_modules.
Module itree_examples.
Import refframe.example_modules.

Lemma itree_trefines_tau_l :
  trefines (MS (mod_itree nat unit) (Tau (Ret tt), tt)) (MS (mod_itree nat unit) (Ret tt, tt)).
Proof. constructor => /= ?. rewrite tau_eutt. done. Qed.

Lemma mod1_trefines_itree :
  trefines (MS mod1 0) (MS (mod_itree nat unit) ((_ ← trigger (EVis 1) ;;; Ret tt), tt)).
Proof.
  constructor => /= ? Ht.
  thas_trace_inv Ht. { tend. }
  invert_all @m_step. revert select (_ ⊆ _) => <-.
  rewrite bind_trigger. apply thas_trace_Vis.
  thas_trace_inv. { tend. }
  invert_all @m_step.
Qed.

Lemma itree_trefines_mod1 :
  trefines (MS (mod_itree nat unit) ((trigger (EVis 1);;;; Ret tt), tt)) (MS mod1 0).
Proof.
  constructor => /= ?. rewrite bind_trigger => /(thas_trace_Vis_inv _ _ _ _)Ht.
  apply: thas_trace_under_tall; [done..|] => {Ht} ? [?|?]; destruct_all?. { tend. }
  revert select (_ ⊆ _) => <-.
  tstep_Some; [by econs|] => ? ->.
  move: H0 => /(thas_trace_Ret_inv _ _ _ _)Ht.
  apply: thas_trace_under_tall; [done..|] => {Ht} ?/=?; destruct_all?. tend.
Qed.

End itree_examples.
