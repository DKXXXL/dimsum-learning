From Paco Require Import paco.
From ITree Require Export ITree ITreeFacts.
From ITree Require Export ITree.
Require Export refframe.module.
Require Import refframe.trefines.

Notation "' x ← y ;;; z" := (ITree.bind y (λ x : _, z))
  (at level 20, x pattern, y at level 100, z at level 200) : stdpp_scope.
Notation "x ← y ;;; z" := (ITree.bind y (λ x : _, z))
  (at level 20, y at level 100, z at level 200) : stdpp_scope.
Notation "y ;;;; z" := (ITree.bind y (λ _, z))
  (at level 100, z at level 200, right associativity) : stdpp_scope.


Inductive moduleE (EV S : Type) : Type → Type :=
| IVis (e : EV) : moduleE EV S unit
| IAll (T : Type) : moduleE EV S T
| IExist (T : Type) : moduleE EV S T
| IGet : moduleE EV S S
| IPut (s : S) : moduleE EV S unit
.
Arguments IVis {_ _}.
Arguments IAll {_ _}.
Arguments IExist {_ _}.
Arguments IGet {_ _}.
Arguments IPut {_ _}.

Inductive mod_itree_step EV S : (itree (moduleE EV S) unit * S) → option EV → ((itree (moduleE EV S) unit * S) → Prop) → Prop :=
| ITauS t t' s:
  observe t = TauF t' →
  mod_itree_step EV S (t, s) None (λ σ', σ' = (t', s))
| IVisS t t' s e:
  observe t = VisF (IVis e) t' →
  mod_itree_step EV S (t, s) (Some e) (λ σ', σ' = (t' tt, s))
.

Definition mod_itree EV S := Mod (mod_itree_step EV S).

(** [Tau] *)
Lemma tnhas_trace_Tau' {EV S} t t' n n' Pσ s κs:
  observe t = TauF t' →
  (t', s) ~{mod_itree EV S, κs, n}~>ₜ Pσ →
  n ⊂ n' →
  (t, s) ~{mod_itree EV S, κs, n'}~>ₜ Pσ.
Proof.
  move => Htau Ht Hsub. apply: (TNTraceStep _ _ (λ _, n)); [by econs| |done|simpl; done] => /= ? ->. done.
Qed.
Lemma tnhas_trace_Tau {EV S} t n n' Pσ s κs:
  (t, s) ~{mod_itree EV S, κs, n}~>ₜ Pσ →
  n ⊂ n' →
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
    ∃ n', n' ⊂ n ∧ (t, s) ~{ mod_itree _ _,  κs, n' }~>ₜ Pσ).
Proof.
  move => Htau Ht. thas_trace_inv Ht. { left. split; [by etrans|done]. }
  right. invert_all @m_step; rewrite ->Htau in *; simplify_eq.
  eexists _. split; [done|]. rewrite -Hsub -H0. naive_solver.
  Unshelve. done.
Qed.
Lemma tnhas_trace_Tau_inv {EV S} t n Pσ s κs:
  (Tau t, s) ~{mod_itree EV S, κs, n}~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ (Tau t, s)) ∨
    ∃ n', n' ⊂ n ∧ (t, s) ~{ mod_itree _ _,  κs, n' }~>ₜ Pσ).
Proof. by apply tnhas_trace_Tau_inv'. Qed.

Lemma thas_trace_Tau_inv' {EV S} t t' Pσ s κs:
  observe t' = TauF t →
  (t', s) ~{mod_itree EV S, κs}~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ (t', s)) ∨ (t, s) ~{ mod_itree _ _,  κs }~>ₜ Pσ).
Proof.
  move => Htau /thas_trace_n[? /(tnhas_trace_Tau_inv' _ _ _ _ _) Ht]. specialize (Ht _ ltac:(done)).
  apply: under_tall_mono; [done..|] => {Ht} ?? Hκs [[??]|[?[??]]]. { left. split; [by etrans|done]. }
  right. apply thas_trace_n. eexists _. by rewrite -Hκs.
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
  thas_trace_inv Ht. { split => //. by rewrite -Hsub. }
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


Lemma thas_trace_eutt_mono {EV S} t t' s κs Pσ Pσ':
  (prod_relation (eutt eq) (=) ==> iff)%signature Pσ Pσ' →
  (t, s) ~{ mod_itree EV S, κs }~>ₜ Pσ →
  t ≈ t' →
  (t', s) ~{ mod_itree EV S, κs }~>ₜ Pσ'.
Proof.
  move => HP /thas_trace_n[n Ht] Heq.
  elim/(well_founded_ind ti_lt_wf): n κs t t' s Ht Heq HP.
  move => n IHn κs t t' s Ht Heq HP.
  punfold Heq. unfold eqit_ in Heq at 1.
  move: Heq. move Hot: (observe t) => ot. move Hot': (observe t') => ot' Heq.
  elim: Heq t t' n κs IHn Ht Hot Hot'.
  - move => ?? -> t t' n κs IHn Ht Hot Hot'.
    move: Ht => /(tnhas_trace_Ret_inv' _ _ _ _ _)Ht. specialize (Ht _ ltac:(done)).
    apply: thas_trace_under_tall; [done..|] => ? [??]. tend.
    eapply HP; [|done]. split; [|done] => /=. rewrite (itree_eta t) Hot (itree_eta t') Hot'. done.
  - move => m1 m2 [REL|//] t t' n κs IHn Ht Hot Hot'. rewrite -/(eqit _ _ _) in REL.
    apply: thas_trace_Tau'; [done|].
    move: Ht => /(tnhas_trace_Tau_inv' _ _ _ _ _)Ht. specialize (Ht _ ltac:(done)).
    apply: thas_trace_under_tall; [done..|] => ? /= [[??]|[?[??]]].
    + tend. eapply HP; [|done]. split => //=. by rewrite (itree_eta t) Hot tau_eutt REL.
    + apply: IHn; [done|done| |done]. by rewrite REL.
  - admit.
  - move => t1 ot2 ? REL IH t t' n κs IHn Ht Hot Hot'.
    move: Ht => /(tnhas_trace_Tau_inv' _ _ _ _ _ _)Ht. specialize (Ht _ ltac:(done)).
    apply: thas_trace_under_tall; [done..|] => ? /= [[??]|[?[??]]].
    + tend. eapply HP; [|done]. split; [|done] => /=. subst.
      move: REL => /fold_eqitF REL. specialize (REL _ _ ltac:(done) ltac:(done)). rewrite -REL.
      by rewrite (itree_eta t) Hot tau_eutt.
    + apply: IH => //. apply: tnhas_trace_mono; [done..| by apply: ti_lt_impl_le |done].
  - move => ot1 t2 ? REL IH t t' n κs IHn Ht Hot Hot'.
    tstep_None; [by econs|] => ? ->. by apply: IH.
    Unshelve.
Admitted.

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

Require refframe.example_modules.
Module itree_examples.
Import refframe.example_modules.

Lemma itree_trefines_tau_l :
  trefines (MS (mod_itree nat unit) (Tau (Ret tt), tt)) (MS (mod_itree nat unit) (Ret tt, tt)).
Proof. constructor => /= ?. rewrite tau_eutt. done. Qed.

Lemma mod1_trefines_itree :
  trefines (MS mod1 0) (MS (mod_itree nat unit) ((_ ← trigger (IVis 1) ;;; Ret tt), tt)).
Proof.
  constructor => /= ? Ht.
  thas_trace_inv Ht. { tend. }
  invert_all @m_step. revert select (_ ⊆ _) => <-.
  rewrite bind_trigger. tstep_Some; [by econs|] => ? ->.
  thas_trace_inv. { tend. }
  invert_all @m_step.
Qed.

Lemma itree_trefines_mod1 :
  trefines (MS (mod_itree nat unit) ((trigger (IVis 1);;;; Ret tt), tt)) (MS mod1 0).
Proof.
  constructor => /= ?. rewrite bind_trigger.
Abort.

End itree_examples.
