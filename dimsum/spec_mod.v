From Paco Require Import paco.
From ITree Require Import ITree ITreeFacts.
From dimsum.core Require Export proof_techniques spec.
From dimsum.core Require Import axioms.

Export SpecNotations.

(** * Module semantics for spec *)

(** There is no explicit step for STau, but STau is implicitly removed
by [≡]. For a silent steps that actually performs a step use a trivial
choice. *)
Inductive spec_step EV S : (spec EV S void * S) → option EV → ((spec EV S void * S) → Prop) → Prop :=
| SVisS t t' s e:
  t ≡ SVis e t' →
  spec_step EV S (t, s) (Some e) (λ σ', σ' = (t', s))
| SAllS {X : Set} t (k : X → _) s :
  t ≡ SAll k →
  spec_step EV S (t, s) None (λ σ', ∃ x, σ' = (k x, s))
| SExS {X : Set} t (k : X → _) s x:
  t ≡ SExist k →
  spec_step EV S (t, s) None (λ σ', σ' = (k x, s))
| SGetS t k s:
  t ≡ SGet k →
  spec_step EV S (t, s) None (λ σ', σ' = (k s, s))
| SPutS t k s s':
  t ≡ SPut s' k →
  spec_step EV S (t, s) None (λ σ', σ' = (k, s'))
.

Definition spec_trans EV S := ModTrans (spec_step EV S).

Global Instance spec_vis_no_all EV S: VisNoAng (spec_trans EV S).
Proof. move => *. inv_all @m_step; naive_solver. Qed.

Definition spec_mod {EV S} (t : spec EV S void) (s : S) :=
  Mod (spec_trans EV S) (t, s).

(** * Proper instances for rewrite with spec equiv *)
Lemma spec_step_mono {EV S} σ1 σ2 e Pσ :
  spec_step EV S σ1 e Pσ →
  σ1.1 ≡ σ2.1 →
  σ1.2 = σ2.2 →
  spec_step EV S σ2 e Pσ.
Proof. destruct σ1, σ2 => /= Hs ??. inv Hs; econs. all: by etrans; [|done]. Qed.

Definition steps_impl_spec_equiv_rel {EV S} :
  relation (bool → option EV → ((spec EV S void * S → Prop) → Prop)) := λ Pσ Pσ',
  ∀ (b b' : bool) κ (P1 P2 : _ → Prop),
    (∀ t s, P1 (t, s) → ∃ t', t ≡ t' ∧ P2 (t', s)) →
    (b → b') →
    Pσ b κ P1 → Pσ' b' κ P2.

Lemma steps_impl_spec_equiv_mono {EV S} t' σ (Pσ Pσ' : _ → _ → _ → Prop) :
  steps_impl_spec_equiv_rel Pσ Pσ' →
  σ -{ spec_trans EV S }-> Pσ →
  σ.1 ≡ t' →
  (t', σ.2) -{ spec_trans EV S }-> Pσ'.
Proof.
  move => HP /steps_impl_unfold Ht Heq.
  destruct Ht as [?| Ht]; simplify_eq/=.
  { apply steps_impl_end. apply: HP; [..|done]; naive_solver. }
  apply steps_impl_step => ???.
  exploit Ht. { by apply: spec_step_mono. }
  move => [?| [?[?[??]]]]; [left|right].
  { apply: HP; [..|done]; naive_solver. }
  split!; [done|].
  apply: steps_impl_mono; [done|] => /= *.
  apply: HP; [..|done]; naive_solver.
Qed.

Global Instance steps_impl_spec_proper EV S :
  Proper ((prod_relation (≡) (=)) ==> steps_impl_spec_equiv_rel ==> impl) (steps_impl (spec_trans EV S)).
Proof. move => [??] [??] [/= Heq ->] ?? Hf ?. by apply: (steps_impl_spec_equiv_mono _ (_, _)). Qed.

Global Instance steps_impl_spec_proper_flip EV S :
  Proper ((prod_relation (≡) (=)) ==> flip steps_impl_spec_equiv_rel ==> flip impl) (steps_impl (spec_trans EV S)).
Proof.
  move => [??] [??] [/= Heq ->] ?? Hf ?. apply: (steps_impl_spec_equiv_mono _ (_, _)); [done..|].
  apply eqit_flip. by apply: eqit_mon; [..|done].
Qed.

Lemma steps_spec_spec_equiv_mono {EV S} t' σ κ Pσ Pσ' :
  (prod_relation (≡) (=) ==> impl)%signature Pσ Pσ' →
  σ -{ spec_trans EV S, κ }->ₛ Pσ →
  σ.1 ≡ t' →
  (t', σ.2) -{ spec_trans EV S, κ }->ₛ Pσ'.
Proof.
  move => HP /steps_spec_unfold Ht Heq.
  destruct Ht as [[??]| [?[?[?[? Ht]]]]]; simplify_eq/=.
  { apply steps_spec_end. apply: HP; [|done]. by split. }
  apply steps_spec_unfold. right. split!. { by apply: spec_step_mono. } { done. }
  move => ??. exploit Ht; [done..|] => -[[??]|[??]]; [left|right]; split!.
  { apply: HP; [..|done]; naive_solver. }
  apply: steps_spec_mono; [done|] => /= *.
  apply: HP; [..|done]; naive_solver.
Qed.

Global Instance steps_spec_spec_proper EV S :
  Proper ((prod_relation (≡) (=)) ==> (=) ==> (prod_relation (≡) (=) ==> iff) ==> iff) (steps_spec (spec_trans EV S)).
Proof.
  move => [??] [??] [/= Heq ->] ?? -> ?? Hf.
  split => ?.
  all: apply: (steps_spec_spec_equiv_mono _ (_, _)); [try done| done |].
  - move => ????. eapply Hf; [|done]. done.
  - done.
  - move => ?? [??] ?. eapply Hf; [|done]. split; [|done]. apply eqit_flip. by apply: eqit_mon; [..|done].
  - apply eqit_flip. by apply: eqit_mon; [..|done].
Qed.

Lemma tnhas_trace_spec_equiv_mono {EV S} t t' s κs Pσ Pσ' n:
  (prod_relation (≡) (=) ==> impl)%signature Pσ Pσ' →
  (t, s) ~{ spec_trans EV S, κs, n }~>ₜ Pσ →
  t ≡ t' →
  (t', s) ~{ spec_trans EV S, κs, n }~>ₜ Pσ'.
Proof.
  move => HP /tnhas_trace_inv Ht Heq.
  apply: tnhas_trace_under_tall; [done..|] => /= ? [[??]|[?[?[?[?[?[?[??]]]]]]]].
  { tend. apply: HP; [|done]. by split. }
  tstep; [| |done..]. { by apply: spec_step_mono. }
  move => ??. apply: tnhas_trace_mono; [by eauto|done|done|].
  move => ??. by apply: HP.
Qed.

Global Instance tnhas_trace_spec_proper EV S :
  Proper ((prod_relation (≡) (=)) ==> (=) ==> (=) ==> (prod_relation (≡) (=) ==> iff) ==> iff) (tnhas_trace (spec_trans EV S)).
Proof.
  move => [??] [??] [/= Heq ->] ?? -> ?? -> ?? Hf.
  split => ?.
  all: apply: tnhas_trace_spec_equiv_mono; [try done| done |].
  - move => ????. by eapply Hf.
  - done.
  - move => [??] [??] [/=? ->] ?. eapply Hf; [|done]. split; [|done] => /=.
    apply eqit_flip. by apply: eqit_mon; [..|done].
  - apply eqit_flip. by apply: eqit_mon; [..|done].
Qed.

Lemma thas_trace_spec_equiv_mono {EV S} t t' s κs Pσ Pσ' :
  (prod_relation (≡) (=) ==> impl)%signature Pσ Pσ' →
  (t, s) ~{ spec_trans EV S, κs }~>ₜ Pσ →
  t ≡ t' →
  (t', s) ~{ spec_trans EV S, κs }~>ₜ Pσ'.
Proof.
  move => HP /thas_trace_inv Ht Heq.
  apply: thas_trace_under_tall; [done..|] => /= ? [[??]|[?[?[?[?[??]]]]]].
  { tend. apply: HP; [|done]. by split. }
  tstep; [| |done..]. { by apply: spec_step_mono. }
  move => ??. apply: thas_trace_mono; [naive_solver|done|].
  move => ??. by apply: HP.
Qed.

Global Instance spec_trans_proper EV S :
  Proper ((prod_relation (≡) (=)) ==> (=) ==> (prod_relation (≡) (=) ==> iff) ==> iff) (thas_trace (spec_trans EV S)).
Proof.
  move => [??] [??] [/= Heq ->] ?? -> ?? Hf.
  split => ?.
  all: apply: thas_trace_spec_equiv_mono; [try done| done |].
  - move => ????. by eapply Hf.
  - done.
  - move => [??] [??] [/=? ->] ?. eapply Hf; [|done]. split; [|done] => /=.
    apply eqit_flip. by apply: eqit_mon; [..|done].
  - apply eqit_flip. by apply: eqit_mon; [..|done].
Qed.

Definition spec_rel {EV R S} (P : spec EV S R * S → Prop) (t : spec EV S R * S) : Prop :=
  ∀ t', t' ≡ t.1 → P (t', t.2).
Global Instance spec_rel_proper EV R S P :
  Proper ((prod_relation (≡) (=) ==> iff)) (@spec_rel EV R S P).
Proof.
  move => [x ?] [y ?] [Heq ?]. simplify_eq/=. rewrite /spec_rel /=.
  split => ??; [rewrite -Heq | rewrite Heq]; naive_solver.
Qed.
Global Typeclasses Opaque spec_rel.

Lemma spec_rel_intro EV S σ κs P:
  σ ~{spec_trans EV S, κs }~>ₜ spec_rel P →
  σ ~{spec_trans EV S, κs }~>ₜ P.
Proof. move => Ht. apply: thas_trace_mono; [done|done|] => -[??] Hp. by apply: Hp. Qed.

Lemma spec_rel_spec_intro EV S σ κ P:
  σ -{spec_trans EV S, κ }->ₛ spec_rel P →
  σ -{spec_trans EV S, κ }->ₛ P.
Proof. move => ?. apply: steps_spec_mono; [done|]. move => -[??] Hp. by apply Hp. Qed.

Definition spec_impl_rel {EV S} (P : bool → option EV → (spec EV S void * S → Prop) → Prop) :
  bool → option EV → (spec EV S void * S → Prop) → Prop :=
  λ b κ Pσ, ∀ (b' : bool) (Pσ' : _ → Prop),
      (∀ t s, Pσ (t, s) → ∃ t', t ≡ t' ∧ Pσ' (t', s)) →
      (b → b') →
      P b' κ Pσ'.
Global Instance spec_impl_rel_proper EV S P :
  Proper (steps_impl_spec_equiv_rel) (@spec_impl_rel EV S P).
Proof.
  move => ????? HP1 ? REL ?? HPσ' ?. apply: REL. 2: naive_solver.
  move => ?? /HP1 [? [Ht /HPσ'[?[??]]]]. eexists _. split; [|done]. etrans; [|done].
  by apply: eqit_mon; [..|done].
Qed.
Global Typeclasses Opaque spec_impl_rel.

Lemma spec_impl_rel_intro EV S σ P:
  σ -{spec_trans EV S }-> spec_impl_rel P →
  σ -{spec_trans EV S }-> P.
Proof. move => ?. apply: steps_impl_mono; [done|]. move => ??? Hp. apply Hp; [|done]. naive_solver. Qed.

Ltac clear_spec :=
  try match goal with | |- spec_rel _ _ => move => ?/=? end;
  repeat match goal with
         | H : @equiv _ spec_equiv ?t _ |- _ => clear H; clear t
         | H1 : @equiv _ spec_equiv ?t ?t', H2: @equiv _ spec_equiv ?t' _ |- _ => rewrite -H1 in H2; clear H1; clear t'
         end.

(** * tsim *)
Global Instance tsim_spec_l_proper EV S m1 n b:
  Proper ((prod_relation (≡) (=)) ==> (=) ==> (=) ==> iff) (tsim n b (spec_trans EV S) m1).
Proof.
  move => [??] [??] [/=Heq ->] ?? -> ?? ->.
  split => Hsim ????; (eapply Hsim; [done|]). { by rewrite Heq. } { by rewrite -Heq. }
Qed.

Global Instance tsim_spec_r_proper EV S m1 n b:
  Proper ((=) ==> (=) ==> (prod_relation (≡) (=)) ==> iff) (tsim n b m1 (spec_trans EV S)).
Proof.
  move => ?? -> ?? -> [??] [??] [/=Heq ->].
  split => Hsim ????. { rewrite -Heq. by eapply Hsim. } { rewrite Heq. by eapply Hsim. }
Qed.

(** * tstep *)
(** ** typeclasses and infrastructure *)
Class SpecEq {EV S R} (t t' : spec EV S R) := {
  spec_eq_proof : t ≡ t'
}.
Global Hint Mode SpecEq + + + ! - : typeclass_instances.
Lemma SpecEq_refl {EV S R} (t : spec EV S R) :
  SpecEq t t.
Proof. done. Qed.

Global Hint Extern 5 (SpecEq ?t _) => (assert_fails (is_var t); by apply SpecEq_refl) : typeclass_instances.
Global Hint Extern 10 (SpecEq _ _) => (constructor; eassumption) : typeclass_instances.

Class SpecTStep {EV S} (cont : bool) (t t' : spec EV S void) := {
  spec_tstep_proof : t ≡ t'
}.
Global Hint Mode SpecTStep + + + ! - : typeclass_instances.

Class SpecTStepS {EV S} (t : spec EV S void) (s : S) (κ : option EV)
  (P : (spec EV S void → S → Prop) → Prop) := {
    spec_tsteps_proof G:
    P (λ t' s', spec_rel G (t', s')) →
    (t, s) -{ spec_trans EV S, κ }->ₛ spec_rel G
}.
Global Hint Mode SpecTStepS + + ! ! - - : typeclass_instances.

Lemma spec_step_s_spec_step_cont EV S t t' (s : S) (κ : option EV) P `{!SpecTStep true t t'}
      `{!SpecTStepS t' s κ P} :
  SpecTStepS t s κ P.
Proof. constructor => ??. move: SpecTStep0 => [->]. by apply spec_tsteps_proof. Qed.
Global Hint Resolve spec_step_s_spec_step_cont | 50 : typeclass_instances.

Lemma spec_step_s_spec_step_no_cont EV S t t' (s : S) `{!SpecTStep false t t'}:
  SpecTStepS t s (@None EV) (λ G, G t' s).
Proof. constructor => ??. move: SpecTStep0 => [->]. by apply steps_spec_end. Qed.
Global Hint Resolve spec_step_s_spec_step_no_cont | 100 : typeclass_instances.

Lemma spec_tstep_s {EV S} s t t' κ `{!SpecEq t t'} `{!SpecTStepS t' s κ P}:
  TStepS (spec_trans EV S) (t, s) (λ G, G κ (λ G', P (λ t'' s', spec_rel G' (t'', s')))).
Proof.
  constructor => G HG. eexists _, _. split; [done|] => ? /= ?.
  apply spec_rel_spec_intro. move: SpecEq0 => [->]. by apply: spec_tsteps_proof.
Qed.
Global Hint Resolve spec_tstep_s : typeclass_instances.

Class SpecTStepI {EV S} (t : spec EV S void) (s : S)
      (P : (bool → option EV → ((spec EV S void → S → Prop) → Prop) → Prop) → Prop) := {
    spec_tstepi_proof G:
    P G →
    (t, s) -{ spec_trans EV S }-> (λ b κ Pσ, ∃ (b' : bool) P', G b' κ P' ∧ (b' → b) ∧ ∀ G', P' G' → ∃ t t' s, Pσ (t, s) ∧ t ≡ t' ∧ G' t' s)
}.
Global Hint Mode SpecTStepI + + ! ! - : typeclass_instances.

Lemma spec_step_i_spec_step_cont EV S t t' (s : S) P `{!SpecTStep true t t'}
      `{!SpecTStepI t' s P} :
  SpecTStepI (EV:=EV) t s P.
Proof.
  constructor => ??. apply spec_impl_rel_intro.
  move: SpecTStep0 => [->].
  apply: steps_impl_mono; [by apply spec_tstepi_proof|].
  move => /= * ?? HP ?. destruct!. eexists _, _. split_and!; [done|naive_solver|].
  move => ? /H2[?[?[? [/HP[?[??]] [? HG]]]]]. eexists _, _, _. split_and!; [done| |done].
  etrans; [|done]. apply eqit_flip. by apply: eqit_mon; [..|done].
Qed.
Global Hint Resolve spec_step_i_spec_step_cont | 50 : typeclass_instances.

Lemma spec_step_i_spec_step_no_cont EV S t t' (s : S) `{!SpecTStep false t t'} :
  SpecTStepI (EV:=EV) t s (λ G, G false None (λ G', G' t' s)).
Proof.
  constructor => ??. apply steps_impl_end. eexists _, _. split_and!; [done..|].
  move => /=??. eexists _, _, _. split_and!; [done| |done].
  by apply: spec_tstep_proof.
Qed.
Global Hint Resolve spec_step_i_spec_step_no_cont | 100 : typeclass_instances.

Lemma spec_tstep_i {EV S} s t t' `{!SpecEq t t'} `{!SpecTStepI t' s P}:
  TStepI (spec_trans EV S) (t, s) (λ G, P (λ b κ P', G b κ (λ G', P' (λ t'' s', spec_rel G' (t'', s'))))).
Proof.
  constructor => ??. apply spec_impl_rel_intro.
  move: SpecEq0 => [->].
  apply: steps_impl_mono; [by apply spec_tstepi_proof|].
  move => /= * ?? HP ?. destruct!. eexists _, _. split_and!; [done|naive_solver|].
  move => ? /H2[?[?[? [/HP[?[??]] [? HG]]]]]. eexists (_, _). split; [done|]. apply HG. etrans; [|done].
  apply eqit_flip. by apply: eqit_mon; [..|done].
Qed.
Global Hint Resolve spec_tstep_i : typeclass_instances.

(** ** instances *)
Lemma spec_tstep_bind {EV S} A B h (k : A → spec _ _ B) (t : spec EV S _) cont :
  SpecTStep cont (Spec.bind (Spec.bind t k) h) (Spec.bind t (fun r => Spec.bind (k r) h)).
Proof. constructor. by rewrite bind_bind. Qed.
Global Hint Resolve spec_tstep_bind : typeclass_instances.

Lemma spec_tstep_ret {EV S} A h (x : A) cont:
  SpecTStep (EV:=EV) (S:=S) cont (Spec.bind (TRet x) h) (h x).
Proof. constructor. by rewrite unfold_bind. Qed.
Global Hint Resolve spec_tstep_ret : typeclass_instances.

Lemma spec_tstep_forever EV S R (t : spec EV S R) :
  SpecTStep false (Spec.forever t) (t;; Spec.forever t).
Proof. constructor. apply unfold_forever. Qed.
Global Hint Resolve spec_tstep_forever : typeclass_instances.

Lemma spec_tstep_Tau {EV S} t cont:
  SpecTStep (EV:=EV) (S:=S) cont (STau t) t.
Proof. constructor. by rewrite stau_equiv. Qed.
Global Hint Resolve spec_tstep_Tau : typeclass_instances.

Lemma spec_step_Vis_s EV S k (s : S) (e : EV):
  SpecTStepS (Spec.bind (TVis e) k) s (Some e) (λ G, G (k tt) s).
Proof.
  constructor => ??. rewrite unfold_bind/= unfold_bind/=.
  apply: steps_spec_step_end. { by econs. } naive_solver.
Qed.
Global Hint Resolve spec_step_Vis_s : typeclass_instances.

Lemma spec_step_Vis_i EV S k s e:
  SpecTStepI (EV:=EV) (S:=S) (Spec.bind (TVis e) k) s (λ G, G true (Some e) (λ G', G' (k tt) s)).
Proof.
  constructor => ??. rewrite /TVis.
  apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=.
  all: revert select (_ ≡ _); try by move => /spec_equiv_inv.
  rewrite unfold_bind/=unfold_bind/= => /spec_equiv_inv //=.
  naive_solver.
Qed.
Global Hint Resolve spec_step_Vis_i : typeclass_instances.

Lemma spec_step_All_s EV S (T : Set) (k : T → _) s:
  SpecTStepS (EV:=EV) (S:=S) (Spec.bind (TAll _) k) s None (λ G, ∀ x, G (k x) s).
Proof.
  constructor => ??. rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
  apply: steps_spec_step_end. { by econs. } naive_solver.
Qed.
Global Hint Resolve spec_step_All_s : typeclass_instances.

Lemma spec_step_All_i EV S (T : Set) (k : T → _) s:
  SpecTStepI (EV:=EV) (S:=S) (Spec.bind (TAll _) k) s (λ G, G true None (λ G', ∃ x, G' (k x) s)).
Proof.
  constructor => ??. apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=.
  all: revert select (_ ≡ _); try by move => /spec_equiv_inv.
  rewrite unfold_bind/=. setoid_rewrite unfold_bind. move => /=/spec_equiv_inv //=.
  naive_solver.
Qed.
Global Hint Resolve spec_step_All_i : typeclass_instances.

Lemma spec_step_Exist_s EV S (T : Set) (k : T → _) s:
  SpecTStepS (EV:=EV) (S:=S) (Spec.bind (TExist _) k) s None (λ G, ∃ x, G (k x) s).
Proof.
  constructor => ? [??]. rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
  apply: steps_spec_step_end. { by econs. } naive_solver.
Qed.
Global Hint Resolve spec_step_Exist_s : typeclass_instances.

Lemma spec_step_Exist_i EV S (T : Set) (k : T → _) s:
  SpecTStepI (EV:=EV) (S:=S) (Spec.bind (TExist _) k) s (λ G, ∀ x, G true None (λ G', G' (k x) s)).
Proof.
  constructor => ??. apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=.
  all: revert select (_ ≡ _); try by move => /spec_equiv_inv.
  rewrite unfold_bind/=. setoid_rewrite unfold_bind. move => /=/spec_equiv_inv //=.
  naive_solver.
Qed.
Global Hint Resolve spec_step_Exist_i : typeclass_instances.

Lemma spec_step_Get_s EV S k s:
  SpecTStepS (EV:=EV) (S:=S) (Spec.bind TGet k) s None (λ G, G (k s) s).
Proof.
  constructor => ? ?. rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
  apply: steps_spec_step_end. { by econs. } naive_solver.
Qed.
Global Hint Resolve spec_step_Get_s : typeclass_instances.

Lemma spec_step_Get_i EV S k s:
  SpecTStepI (EV:=EV) (S:=S) (Spec.bind TGet k) s (λ G, G true None (λ G', G' (k s) s)).
Proof.
  constructor => ??. apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=.
  all: revert select (_ ≡ _); try by move => /spec_equiv_inv.
  rewrite unfold_bind/=. setoid_rewrite unfold_bind. move => /=/spec_equiv_inv //=.
  naive_solver.
Qed.
Global Hint Resolve spec_step_Get_i : typeclass_instances.

Lemma spec_step_Put_s EV S k s s':
  SpecTStepS (EV:=EV) (S:=S) (Spec.bind (TPut s') k) s None (λ G, G (k tt) s').
Proof.
  constructor => ? ?. rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
  apply: steps_spec_step_end. { by econs. } naive_solver.
Qed.
Global Hint Resolve spec_step_Put_s : typeclass_instances.

Lemma spec_step_Put_i EV S k s s':
  SpecTStepI (EV:=EV) (S:=S) (Spec.bind (TPut s') k) s (λ G, G true None (λ G', G' (k tt) s')).
Proof.
  constructor => ??. apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=.
  all: revert select (_ ≡ _); try by move => /spec_equiv_inv.
  rewrite unfold_bind/=. setoid_rewrite unfold_bind. move => /=/spec_equiv_inv //=.
  naive_solver.
Qed.
Global Hint Resolve spec_step_Put_i : typeclass_instances.

Lemma spec_step_Ub_s EV S T (k : T → _) s:
  SpecTStepS (EV:=EV) (S:=S) (Spec.bind TUb k) s None (λ G, True).
Proof.
  constructor => ? ?. rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
  apply: steps_spec_step_end. { by econs. } move => /=? [[]?].
Qed.
Global Hint Resolve spec_step_Ub_s : typeclass_instances.

Lemma spec_step_Ub_end_s EV S s:
  SpecTStepS (EV:=EV) (S:=S) TUb s None (λ G, True).
Proof.
  constructor => ? ?. rewrite /TUb. apply: steps_spec_step_end. { by econs. } move => /= ? [[] ?].
Qed.
Global Hint Resolve spec_step_Ub_end_s : typeclass_instances.

Lemma spec_step_Nb_i EV S T (k : T → _) s:
  SpecTStepI (EV:=EV) (S:=S) (Spec.bind TNb k) s (λ G, G true None (λ G', True)).
Proof.
  constructor => ??. apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=.
  all: revert select (_ ≡ _); try by move => /spec_equiv_inv.
  rewrite unfold_bind/=. move => /=/spec_equiv_inv //=[??]. simplify_eq. destruct x.
Qed.
Global Hint Resolve spec_step_Nb_i : typeclass_instances.

Lemma spec_step_Nb_end_i EV S s:
  SpecTStepI (EV:=EV) (S:=S) TNb s (λ G, G true None (λ G', True)).
Proof.
  constructor => ??. apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=.
  all: revert select (_ ≡ _) => /spec_equiv_inv//=[??]; simplify_eq/=.
  destruct x.
Qed.
Global Hint Resolve spec_step_Nb_end_i : typeclass_instances.

Lemma spec_step_Assume_s EV S P k s:
  SpecTStepS (EV:=EV) (S:=S) (Spec.bind (TAssume P) k) s None (λ G, P → G (k tt) s).
Proof.
  constructor => ? ?. rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
  apply: steps_spec_step_end. { by econs. } naive_solver.
Qed.
Global Hint Resolve spec_step_Assume_s : typeclass_instances.

Lemma spec_step_Assume_i EV S P k s:
  SpecTStepI (EV:=EV) (S:=S) (Spec.bind (TAssume P) k) s (λ G, G true None (λ G', P ∧ G' (k tt) s)).
Proof.
  constructor => ??. apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=.
  all: revert select (_ ≡ _); try by move => /spec_equiv_inv.
  rewrite unfold_bind/=. setoid_rewrite unfold_bind. move => /=/spec_equiv_inv //=[??]; simplify_eq/=.
  split!; [done..|]. move => ? [??]. eexists _, _, _. split_and!; [naive_solver| |done].
  done.
  Unshelve. done.
Qed.
Global Hint Resolve spec_step_Assume_i : typeclass_instances.

Lemma spec_step_Assert_s EV S P k s:
  SpecTStepS (EV:=EV) (S:=S) (Spec.bind (TAssert P) k) s None (λ G, P ∧ G (k tt) s).
Proof.
  constructor => ? ?. rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
  apply: steps_spec_step_end. { by econs. } naive_solver.
  Unshelve. naive_solver.
Qed.
Global Hint Resolve spec_step_Assert_s : typeclass_instances.

Lemma spec_step_Assert_i EV S P k s:
  SpecTStepI (EV:=EV) (S:=S) (Spec.bind (TAssert P) k) s (λ G, P → G true None (λ G', G' (k tt) s)).
Proof.
  constructor => ??. apply: steps_impl_step_end => ???.
  inv_all @m_step; simplify_eq/=.
  all: revert select (_ ≡ _); try by move => /spec_equiv_inv.
  rewrite unfold_bind/=. setoid_rewrite unfold_bind. move => /=/spec_equiv_inv //=[??]; simplify_eq/=.
  naive_solver.
Qed.
Global Hint Resolve spec_step_Assert_i : typeclass_instances.

Lemma spec_step_AssumeOpt_s EV S T (o : option T) k s:
  SpecTStepS (EV:=EV) (S:=S) (Spec.bind (TAssumeOpt o) k) s None (λ G, ∀ x, o = Some x → G (k x) s).
Proof.
  constructor => ??. destruct o => /=.
  - rewrite unfold_bind/=. apply: steps_spec_end. naive_solver.
  - rewrite /TUb unfold_bind/=. apply: steps_spec_step_end. { by econs. } move => /= ? [[] ?].
Qed.
Global Hint Resolve spec_step_AssumeOpt_s : typeclass_instances.

Lemma spec_step_AssumeOpt_i EV S T (o : option T) k s:
  SpecTStepI (EV:=EV) (S:=S) (Spec.bind (TAssumeOpt o) k) s (λ G, G false None (λ G', ∃ x, o = Some x ∧ G' (k x) s)).
Proof.
  constructor => ??. destruct o => /=.
  - apply: steps_impl_end. split!; [done..|].
    move => ?[? [[?]?]]. subst. eexists _, _, _. split_and!; [naive_solver| |naive_solver].
    by rewrite unfold_bind/=.
  - apply: steps_impl_step_end => ???.
    inv_all @m_step; simplify_eq/=.
    all: revert select (_ ≡ _); try by move => /spec_equiv_inv.
    rewrite unfold_bind/=. move => /=/spec_equiv_inv //=.
    naive_solver.
Qed.
Global Hint Resolve spec_step_AssumeOpt_i : typeclass_instances.

Lemma spec_step_AssertOpt_s EV S T (o : option T) k s:
  SpecTStepS (EV:=EV) (S:=S) (Spec.bind (TAssertOpt o) k) s None (λ G, ∃ x, o = Some x ∧ G (k x) s).
Proof.
  constructor => ?[?[??]]. simplify_eq/=. rewrite unfold_bind/=. by apply: steps_spec_end.
Qed.
Global Hint Resolve spec_step_AssertOpt_s : typeclass_instances.

Lemma spec_step_AssertOpt_i EV S T (o : option T) k s:
  SpecTStepI (EV:=EV) (S:=S) (Spec.bind (TAssertOpt o) k) s (λ G, ∀ x, o = Some x → G false None (λ G', G' (k x) s)).
Proof.
  constructor => ??. destruct o => /=.
  - apply: steps_impl_end. split!; [naive_solver|done..|].
    move => ??. eexists _, _, _. split_and!; [naive_solver| |naive_solver].
    by rewrite unfold_bind/=.
  - apply: steps_impl_step_end => ???.
    inv_all @m_step; simplify_eq/=.
    all: revert select (_ ≡ _); try by move => /spec_equiv_inv.
    rewrite unfold_bind/=. move => /=/spec_equiv_inv //=[??]; simplify_eq/=. destruct x.
Qed.
Global Hint Resolve spec_step_AssertOpt_i : typeclass_instances.

Global Hint Opaque TRet TVis TAll TExist TUb TNb TAssume TAssert TAssumeOpt TAssertOpt TGet TPut : typeclass_instances.

Module spec_test.
Local Definition test_spec : spec nat nat Empty_set
  := s ← TGet; TPut (S s);; ((s ← TGet; TPut(S s);; TRet tt);; TVis(1);; TRet tt);; TNb.
Goal trefines (spec_mod test_spec 0) (spec_mod test_spec 0).
  apply tsim_implies_trefines => ? /=. rewrite /test_spec.

  tstep_i; clear_spec.
  tstep_i; clear_spec.
  tstep_i; clear_spec.
  tstep_i; clear_spec.
  tstep_i; clear_spec.
  tstep_s; clear_spec.
  tstep_s; clear_spec.
  tstep_s; clear_spec.
  tstep_s; clear_spec.
  tstep_s; clear_spec. split; [done|]. clear_spec.
  tstep_s; clear_spec.
  tstep_i; clear_spec.
  done.
Abort.
End spec_test.
