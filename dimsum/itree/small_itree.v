From Paco Require Import paco.
From ITree.Eq Require Import Paco2.
From dimsum.core.itree Require Export upstream.
From stdpp Require Import prelude.
From dimsum.core Require Import base universes.

Module SmallITree.
Local Set Implicit Arguments.
Local Set Contextual Implicit.
Local Set Primitive Projections.

Section itree.

  Context {E : TypeBelowState -> TypeState} {R : TypeState}.

  (** The type [itree] is defined as the final coalgebra ("greatest
      fixed point") of the functor [itreeF]. *)
  Variant itreeF (itree : TypeState) :=
  | RetF (r : R)
  | TauF (t : itree)
  | VisF {X : TypeBelowState} (e : E X) (k : X -> itree)
  .

  CoInductive itree : TypeState := go
  { _observe : itreeF itree }.

End itree.

Arguments itreeF _ _ _ : clear implicits.
Arguments itree _ _ : clear implicits.

Definition from_itree {E : TypeBelowState -> TypeState} {R : TypeState}
  : ITreeDefinition.itree E R -> itree E R :=
  cofix _from_itree (u : ITreeDefinition.itree E R) : itree E R :=
    match observe u with
    | ITreeDefinition.RetF r => go (RetF r)
    | ITreeDefinition.TauF t => go (TauF (_from_itree t))
    | ITreeDefinition.VisF e h => go (VisF e (fun x => _from_itree (h x)))
    end.

Definition to_itree {E : TypeBelowState -> TypeState} {R : TypeState}
  : itree E R → ITreeDefinition.itree E R :=
  cofix _to_itree (u : itree E R) : ITreeDefinition.itree E R :=
    match _observe u with
    | RetF r => (Ret r)
    | TauF t => (Tau (_to_itree t))
    | VisF e h => (Vis e (fun x => _to_itree (h x)))
    end.

Section from_itree.
  Local Notation from_itree_ i :=
    match observe i with
    | ITreeDefinition.RetF r => go (RetF r)
    | ITreeDefinition.TauF t => go (TauF (from_itree t))
    | ITreeDefinition.VisF e h => go (VisF e (fun x => from_itree (h x)))
    end.

  Lemma unfold_from_itree_ {E R} (t : ITreeDefinition.itree E R)
    : eq (_observe (from_itree t)) (_observe (from_itree_ t)).
  Proof. constructor; reflexivity. Qed.
End from_itree.

Section to_itree.
  Local Notation to_itree_ i :=
    match _observe i with
    | RetF r => (Ret r)
    | TauF t => (Tau (to_itree t))
    | VisF e h => (Vis e (fun x => to_itree (h x)))
    end.

  Lemma unfold_to_itree_ {E R} (t : itree E R)
    : observing eq (to_itree t) (to_itree_ t).
  Proof. constructor; reflexivity. Qed.
End to_itree.


Lemma from_to_itree E R (i : ITreeDefinition.itree E R) :
  to_itree (from_itree i) ≅ i.
Proof.
  revert i. ginit. pcofix IH => i.
  rewrite ->unfold_to_itree_, unfold_from_itree_.
  rewrite ->(itree_eta i).
  destruct (observe i); simpl.
  - gstep. by constructor.
  - gstep. constructor. eauto with paco.
  - gstep. constructor => ? /=. eauto with paco.
Qed.

Global Instance SmallITree_equiv {E R} : Equiv (itree E R) :=
  λ t1 t2, SmallITree.to_itree t1 ≅ SmallITree.to_itree t2.

Lemma equiv_from_itree E R (x y : ITreeDefinition.itree E R) :
  from_itree x ≡ from_itree y ↔ x ≅ y.
Proof.
  unfold equiv, SmallITree_equiv. by rewrite !from_to_itree.
Qed.

Lemma eqit_to_itree E R (x y : itree E R) :
  to_itree x ≅ to_itree y ↔ x ≡ y.
Proof. done. Qed.

Global Instance SmallITree_equiv_proper E R :
  Proper ((eq_itree eq) ==> (≡)) (@SmallITree.from_itree E R).
Proof. intros ?? Heq. by apply equiv_from_itree. Qed.

Global Instance SmallITree_to_itree_proper E R :
  Proper ((≡) ==> (eq_itree eq)) (@SmallITree.to_itree E R).
Proof. intros ?? Heq. by apply eqit_to_itree. Qed.

Global Instance SmallITree_equiv_rewrite {E R} : RewriteRelation (≡@{itree E R}) := { }.

Global Instance SmallITree_equiv_equiv {E R} : Equivalence (≡@{itree E R}).
Proof.
  unfold equiv, SmallITree_equiv.
  constructor.
  - intros ?. done.
  - intros ??. done.
  - intros ??? ->. done.
Qed.

Global Instance SmallITree_supseteq {E R} : SqSupsetEq (itree E R) :=
  λ t1 t2, SmallITree.to_itree t1 ≳ SmallITree.to_itree t2.

Lemma supseteq_from_itree E R (x y : ITreeDefinition.itree E R) :
  from_itree x ⊒ from_itree y ↔ x ≳ y.
Proof.
  unfold sqsupseteq, SmallITree_supseteq. by rewrite !from_to_itree.
Qed.

Lemma euttge_to_itree E R (x y : itree E R) :
  to_itree x ≳ to_itree y ↔ x ⊒ y.
Proof. done. Qed.

Global Instance SmallITree_supseteq_proper_equiv E R :
  Proper ((≡) ==> (≡) ==> iff) (⊒@{SmallITree.itree E R}).
Proof.
  unfold equiv, SmallITree_equiv, sqsupseteq, SmallITree_supseteq.
  intros ?? Heq1 ?? Heq2. by rewrite Heq1 Heq2.
Qed.
Global Instance SmallITree_supseteq_proper E R :
  Proper ((euttge eq) ==> (⊒)) (@SmallITree.from_itree E R).
Proof. intros ?? Heq. by apply supseteq_from_itree. Qed.
Global Instance SmallITree_supseteq_proper_flip E R :
  Proper (flip (euttge eq) ==> flip (⊒)) (@SmallITree.from_itree E R).
Proof. intros ?? Heq. by apply supseteq_from_itree. Qed.

Global Instance SmallITree_supseteq_preorder {E R} : PreOrder (⊒@{itree E R}).
Proof.
  unfold sqsupseteq, SmallITree_supseteq.
  constructor.
  - intros ?. done.
  - intros ??? ->. done.
Qed.
End SmallITree.

Notation "↓ᵢ" := SmallITree.from_itree : stdpp_scope.
Notation "↑ᵢ" := SmallITree.to_itree : stdpp_scope.

From dimsum.core.itree Require Export events.

Check ∀ t : itree (stateE nat +' choiceE +' visibleE nat) unit, SmallITree.from_itree t = SmallITree.from_itree t.
Fail Check ∀ t : itree (choiceE +' visibleE (itree choiceE nat)) unit, SmallITree.from_itree t = SmallITree.from_itree t.
