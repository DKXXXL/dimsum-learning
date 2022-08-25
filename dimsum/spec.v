From Paco Require Import paco.
From ITree Require Export ITree ITreeFacts.
From ITree.Eq Require Import Paco2.
From dimsum.core Require Export proof_techniques.
From dimsum.core Require Import axioms.

(** This file is derived from
https://github.com/DeepSpec/InteractionTrees/blob/4.0.0/theories/Core/ITreeDefinition.v
This file also contains many useful comments why definitions are set up in this
particular way.
*)

Section spec.

  Local Set Primitive Projections.

  Context {EV : TypeEvent} {S : TypeState} {R : TypeState}.

  (** We need to define our own spec language since the itree type
  lives in a universe that is too large, which means that it cannot be
  used in the state type of a module. [specF] explicitly only allows
  choices over Set such that it can stay in a low universe. The
  universe problems of itree are probably caused by
  https://gitlab.mpi-sws.org/iris/stdpp/-/issues/80. *)
  Variant specF {spec : TypeState} : TypeState :=
  | SRetF (r : R)
  | STauF (t : spec)
  | SVisF (e : EV) (t : spec)
  | SAllF {X : Set} (k : X → spec)
  | SExistF {X : Set} (k : X → spec)
  | SGetF (k : S → spec)
  | SPutF (s : S) (k : spec)
  .

  CoInductive spec : TypeState := sgo
  { sobserve : @specF spec }.

End spec.

Declare Scope spec_scope.
Bind Scope spec_scope with spec.
Delimit Scope spec_scope with spec.

Arguments specF _ _ _ : clear implicits.
Arguments spec _ _ _ : clear implicits.

(** An [spec'] is a "forced" [spec]. It is the type of inputs
    of [sgo], and outputs of [sobserve]. *)
Notation spec' EV S R := (specF EV S R (spec EV S R)).

Notation SRet x := (sgo (SRetF x)).
Notation STau t := (sgo (STauF t)).
Notation SVis e k := (sgo (SVisF e k)).
Notation SAll k := (sgo (SAllF k)).
Notation SExist k := (sgo (SExistF k)).
Notation SGet k := (sgo (SGetF k)).
Notation SPut s k := (sgo (SPutF s k)).

(** * Functions on spec *)

Module Spec.

Definition subst {EV S : Type} {T U : Type} (k : T -> spec EV S U)
  : spec EV S T -> spec EV S U :=
  cofix _subst (u : spec EV S T) : spec EV S U :=
    match sobserve u with
    | SRetF r => k r
    | STauF t => STau (_subst t)
    | SVisF e k => SVis e (_subst k)
    | SAllF k => SAll (λ x, _subst (k x))
    | SExistF k => SExist (λ x, _subst (k x))
    | SGetF k => SGet (λ x, _subst (k x))
    | SPutF s k => SPut s (_subst k)
    end.

Definition bind {EV S : Type} {T U : Type} (u : spec EV S T) (k : T -> spec EV S U)
  : spec EV S U :=
  subst k u.

Definition cat {EV S T U V}
           (k : T -> spec EV S U) (h : U -> spec EV S V) :
  T -> spec EV S V :=
  fun t => bind (k t) h.

Notation on_left lr l t :=
  (match lr with
  | inl l => t
  | inr r => SRet r
  end) (only parsing).

Definition iter {EV S : Type} {R I: Type}
           (step : I -> spec EV S (I + R)) : I -> spec EV S R :=
  cofix iter_ i := bind (step i) (fun lr => on_left lr l (STau (iter_ l))).

(** Functorial map ([fmap] in Haskell) *)
Definition map {EV S R T} (f : R -> T)  (t : spec EV S R) : spec EV S T :=
  bind t (fun x => SRet (f x)).

(** Ignore the result. *)
Definition ignore {EV S R} : spec EV S R -> spec EV S unit :=
  map (fun _ => tt).

(** Infinite taus. *)
CoFixpoint spin {EV S R} : spec EV S R := STau spin.

(** Repeat a computation infinitely. *)
Definition forever {EV S R T} (t : spec EV S R) : spec EV S T :=
  cofix forever_t := bind t (fun _ => STau (forever_t)).
End Spec.

(** * Derived notions *)
Definition TRet {EV S R} (x : R) : spec EV S R :=
  SRet x.

Definition TVis {EV S} (e : EV) : spec EV S unit :=
  SVis e (SRet tt).

Definition TAll {EV S} (T : Set) : spec EV S T :=
  SAll (λ x, SRet x).
Definition TExist {EV S} (T : Set) : spec EV S T :=
  SExist (λ x, SRet x).

Definition TGet {EV S} : spec EV S S :=
  SGet (λ x, SRet x).
Definition TPut {EV S} (s : S) : spec EV S unit :=
  SPut s (SRet tt).

Definition TUb {EV S R} : spec EV S R :=
  SAll (λ x : void, match (x : void) with end).
Definition TNb {EV S R} : spec EV S R :=
  SExist (λ x : void, match (x : void) with end).

Definition TAssume {EV S} (P : Prop) : spec EV S unit :=
  SAll (λ x : P, SRet tt).
Definition TAssert {EV S} (P : Prop) : spec EV S unit :=
  SExist (λ x : P, SRet tt).

Definition TAssumeOpt {EV S A} (o : option A) : spec EV S A :=
  if o is Some x then SRet x else TUb.
Definition TAssertOpt {EV S A} (o : option A) : spec EV S A :=
  if o is Some x then SRet x else TNb.

Definition TReceive {EV S} {A : Set} (e : A → EV) : spec EV S A :=
  Spec.bind (TExist A) (λ x, Spec.bind (TVis (e x)) (λ _, TRet x)).
(** * Notations *)

Module SpecNotations.
Notation "m ≫= f" := (Spec.bind f m) (at level 60, right associativity) : spec_scope.
Notation "x ← y ; z" := (Spec.bind y (λ x : _, z%spec))
  (at level 20, y at level 100, z at level 200,
  format "x  ←  y ;  '/' z") : spec_scope.
Notation "' x ← y ; z" := (Spec.bind y (λ x_ : _, match x_ with x => z%spec end))
  (at level 20, x pattern, y at level 100, z at level 200,
  format "' x  ←  y ;  '/' z") : spec_scope.
Notation "x ;; z" := (Spec.bind x (λ _, z%spec))
  (at level 100, z at level 200, right associativity) : spec_scope.
Notation "∀ x .. y , z" :=
  (Spec.bind (TAll _) (λ x, .. (Spec.bind (TAll _) (λ y, z%spec)) ..)) : spec_scope.
Notation "∃ x .. y , z" :=
  (Spec.bind (TExist _) (λ x, .. (Spec.bind (TExist _) (λ y, z%spec)) ..)) : spec_scope.
End SpecNotations.

Import SpecNotations.
Definition test1 : spec nat nat nat :=
  '(a, b) ← TRet (1, 2);
  x ← TRet 3;
  TRet (3 + x);;
  TVis x;;
  ∀ (x : bool) y,
  ∃ z,
  if x then x ← TRet 3; TAssert (x = 2);; TUb else
  if x then x ← TRet 3; TAssume (x = 2);; TNb else
  x ← TAssumeOpt (Some 1);
  x ← TAssertOpt (Some x);
  s ← TGet ;
  TPut (s + z +1);;
  (SRet 3;; SRet 3);;
  SRet (a - y + b).
(* Print test1. *)

(** * [sobserving] *)
(** See https://github.com/DeepSpec/InteractionTrees/blob/4.0.0/theories/Eq/Shallow.v *)
Record sobserving {EV S R1 R2}
           (eq_ : spec' EV S R1 -> spec' EV S R2 -> Prop)
           (t1 : spec EV S R1) (t2 : spec EV S R2) : Prop :=
  sobserving_intros
  { sobserving_observe : eq_ (sobserve t1) (sobserve t2) }.
Global Hint Constructors sobserving: core.

Arguments sobserving_observe {_ _ _ _ _ _ _} _.

Section observing_relations.

Context {EV S R : Type}.
Variable (eq_ : spec' EV S R -> spec' EV S R -> Prop).

Global Instance sobserving_observe_ :
  Proper (sobserving eq_ ==> eq_) (@sobserve EV S R).
Proof. intros ? ? []; cbv; auto. Qed.

Global Instance sobserving_sgo : Proper (eq_ ==> sobserving eq_) (@sgo EV S R).
Proof. intros ???. constructor. simpl. done. Qed.

Global Instance monotonic_sobserving eq_' :
  subrelation eq_ eq_' ->
  subrelation (sobserving eq_) (sobserving eq_').
Proof. intros ? ? ? []; cbv; eauto. Qed.

Global Instance Equivalence_sobserving :
  Equivalence eq_ -> Equivalence (sobserving eq_).
Proof.
  intros []; split; cbv; auto.
  - intros ? ? []; auto.
  - intros ? ? ? [] []; eauto.
Qed.

End observing_relations.

(** * spec_to_itree *)
Inductive specE (EV S : Type) : Type → Type :=
| EVis (e : EV) : specE EV S unit
| EAll (T : Type) : specE EV S T
| EExist (T : Type) : specE EV S T
| EGet : specE EV S S
| EPut (s : S) : specE EV S unit
.
Arguments EVis {_ _}.
Arguments EAll {_ _}.
Arguments EExist {_ _}.
Arguments EGet {_ _}.
Arguments EPut {_ _}.

Definition spec_to_itree {EV S R} : spec EV S R → itree (specE EV S) R :=
  cofix _spec_to_itree (t : spec EV S R) : itree _ _ :=
    match sobserve t with
    | SRetF x => Ret x
    | STauF t => Tau (_spec_to_itree t)
    | SVisF e t => Vis (EVis e) (λ _, (_spec_to_itree t))
    | SAllF t => Vis (EAll _) (λ x, _spec_to_itree (t x))
    | SExistF t => Vis (EExist _) (λ x, _spec_to_itree (t x))
    | SGetF t => Vis EGet (λ x, _spec_to_itree (t x))
    | SPutF s t => Vis (EPut s) (λ _, _spec_to_itree t)
    end.

Section spec_to_itree.
  Notation spec_to_itree_ t :=
    match sobserve t with
    | SRetF x => Ret x
    | STauF t => Tau (spec_to_itree t)
    | SVisF e t => Vis (EVis e) (λ _, (spec_to_itree t))
    | SAllF t => Vis (EAll _) (λ x, spec_to_itree (t x))
    | SExistF t => Vis (EExist _) (λ x, spec_to_itree (t x))
    | SGetF t => Vis EGet (λ x, spec_to_itree (t x))
    | SPutF s t => Vis (EPut s) (λ _, spec_to_itree t)
    end.

  Lemma unfold_spec_to_itree_ {EV S R} (t : spec EV S R)
    : observing eq (spec_to_itree t) (spec_to_itree_ t).
  Proof. constructor; reflexivity. Qed.

  Lemma unfold_spec_to_itree_eq {EV S R} (t : spec EV S R)
    : (spec_to_itree t) ≅ (spec_to_itree_ t).
  Proof. apply observing_sub_eqit; constructor; reflexivity. Qed.

  Lemma unfold_spec_to_itree {EV S R} (t : spec EV S R)
    : spec_to_itree t ≈ spec_to_itree_ t.
  Proof. apply observing_sub_eqit; constructor; reflexivity. Qed.
End spec_to_itree.

Global Instance sobserving_spec_to_itree {EV S R} :
  Proper (sobserving eq ==> observing eq) (@spec_to_itree EV S R).
Proof.
  repeat intro; subst. constructor. unfold observe. cbn.
  rewrite (sobserving_observe H). reflexivity.
Qed.

(** * Equivalence *)
Global Instance spec_equiv {EV S R} : Equiv (spec EV S R) :=
  λ t1 t2, eutt eq (spec_to_itree t1) (spec_to_itree t2).

Global Instance spec_equiv_rewrite {EV S R} : RewriteRelation (≡@{spec EV S R}) := { }.

Global Instance spec_equiv_equiv {EV S R} : Equivalence (≡@{spec EV S R}).
Proof.
  unfold equiv, spec_equiv.
  constructor.
  - move => ?. done.
  - move => ??. done.
  - move => ??? ->. done.
Qed.

Global Instance sobserving_sub_equiv EV S R :
  subrelation (sobserving eq) (≡@{spec EV S R}).
Proof. move => ?? Heq. rewrite /equiv/spec_equiv. by rewrite Heq. Qed.

Global Instance spec_equiv_proper {EV S R} RR `{!Reflexive RR} :
  Proper ((≡) ==> eutt RR) (@spec_to_itree EV S R).
Proof. unfold equiv, spec_equiv. move => ?? ->. done. Qed.

Lemma spec_eta {EV S R} (t : spec EV S R) : t ≡ sgo (sobserve t).
Proof. apply sobserving_sub_equiv. econstructor. reflexivity. Qed.

Lemma spec_eta_obs {EV S R} (t : spec EV S R) : sobserving eq t (sgo (sobserve t)).
Proof. done. Qed.

Lemma spec_eta' {EV S R} (ot : spec' EV S R) : ot = sobserve (sgo ot).
Proof. reflexivity. Qed.

Section spec_equiv_inv.

  Context {EV S R : Type}.

  Notation spec_equiv_ t1_ t2_ :=
    match sobserve t1_, sobserve t2_ with
    | SRetF r1, SRetF r2 => r1 = r2
    | STauF t1, STauF t2 => t1 ≡ t2
    | SVisF e1 t1, SVisF e2 t2 => e1 = e2 ∧ t1 ≡ t2
    | @SAllF _ _ _ _ X1 t1, @SAllF _ _ _ _ X2 t2 =>
         ∃ p : @eq Type X1 X2, pweqeq (≡) p t1 t2
    | @SExistF _ _ _ _ X1 t1, @SExistF _ _ _ _ X2 t2 =>
         ∃ p : @eq Type X1 X2, pweqeq (≡) p t1 t2
    | SGetF t1, SGetF t2 => ∀ x, t1 x ≡ t2 x
    | SPutF s1 t1, SPutF s2 t2 => s1 = s2 ∧ t1 ≡ t2
    | STauF t1, _ => t1 ≡ t2_%spec
    | _, STauF t2 => t1_%spec ≡ t2
    | _, _ => False
    end.

  Lemma spec_equiv_inv (t1 t2 : spec EV S R) : t1 ≡ t2 -> spec_equiv_ t1 t2.
  Proof.
    rewrite /equiv/spec_equiv => Heq. rewrite !unfold_spec_to_itree in Heq. move: Heq.
    move Heq1: (sobserve t1) => ot1. move Heq2: (sobserve t2) => ot2.
    move => /eqit_inv. destruct ot1, ot2 => //=.
    all: rewrite ?(spec_eta t1) ?Heq1 ?(spec_eta t2) ?Heq2.
    all: try move => <-; try move => ->.
    all: try (etrans; [apply unfold_spec_to_itree|done]).
    all: try (symmetry; etrans; [apply unfold_spec_to_itree|done]).
    all: clear Heq1 Heq2 => -[p [He Heq]]; simplify_eq/=.
    all: try pose proof (UIP_refl _ _ p); simplify_eq/=.
    - naive_solver.
    - eexists eq_refl => /=. done.
    - eexists eq_refl => /=. done.
    - done.
    - naive_solver.
  Qed.

End spec_equiv_inv.

(** * Equivalence on spec' *)
(* TODO: in itrees, this is handled via going. Should we do this as well here? *)
Global Instance spec'_equiv {EV S R} : Equiv (spec' EV S R) :=
  λ t1 t2, sgo t1 ≡ sgo t2.

Global Instance sgo_proper {EV S R} :
  Proper ((≡) ==> (≡)) (@sgo EV S R).
Proof. move => ???. done. Qed.

Global Instance STauF_proper {EV S R} :
  Proper ((≡) ==> (≡)) (@STauF EV S R (spec _ _ _)).
Proof.
  move => ??. rewrite /equiv/spec'_equiv/equiv/spec_equiv => Heq. rewrite !unfold_spec_to_itree/=.
  by setoid_rewrite Heq.
Qed.

Global Instance SVisF_proper {EV S R} :
  Proper ((=) ==> (≡) ==> (≡)) (@SVisF EV S R (spec _ _ _)).
Proof.
  move => ?? -> ??. rewrite /equiv/spec'_equiv/equiv/spec_equiv => Heq. rewrite !unfold_spec_to_itree/=.
  by setoid_rewrite Heq.
Qed.

Global Instance SAllF_proper {EV S R} X :
  Proper (pointwise_relation _ (≡) ==> (≡)) (@SAllF EV S R (spec _ _ _) X).
Proof.
  move => ??. rewrite /equiv/spec'_equiv/equiv/spec_equiv => Heq. rewrite !unfold_spec_to_itree/=.
  by setoid_rewrite Heq.
Qed.

Global Instance SExistF_proper {EV S R} X :
  Proper (pointwise_relation _ (≡) ==> (≡)) (@SExistF EV S R (spec _ _ _) X).
Proof.
  move => ??. rewrite /equiv/spec'_equiv/equiv/spec_equiv => Heq. rewrite !unfold_spec_to_itree/=.
  by setoid_rewrite Heq.
Qed.

Global Instance SGetF_proper {EV S R} :
  Proper (pointwise_relation _ (≡) ==> (≡)) (@SGetF EV S R (spec _ _ _)).
Proof.
  move => ??. rewrite /equiv/spec'_equiv/equiv/spec_equiv => Heq. rewrite !unfold_spec_to_itree/=.
  by setoid_rewrite Heq.
Qed.

Global Instance SPutF_proper {EV S R} :
  Proper ((=) ==> (≡) ==> (≡)) (@SPutF EV S R (spec _ _ _)).
Proof.
  move => ?? -> ??. rewrite /equiv/spec'_equiv/equiv/spec_equiv => Heq. rewrite !unfold_spec_to_itree/=.
  by setoid_rewrite Heq.
Qed.

(** * Unfolding of functions  *)
Section unfold.
  Notation subst_ k u :=
    match sobserve u with
    | SRetF r => k%function r
    | STauF t => STau (Spec.subst k t)
    | SVisF e t => SVis e (Spec.subst k t)
    | SAllF t => SAll (λ x, Spec.subst k (t x))
    | SExistF t => SExist (λ x, Spec.subst k (t x))
    | SGetF t => SGet (λ x, Spec.subst k (t x))
    | SPutF s t => SPut s (Spec.subst k t)
    end.

  Lemma unfold_subst {EV S T U} (k : T → spec EV S U) (u : spec EV S T)
    : Spec.subst k u ≡ (subst_ k u).
  Proof. apply sobserving_sub_equiv; constructor; reflexivity. Qed.

  Notation bind_ u k :=
    match sobserve u with
    | SRetF r => k%function r
    | STauF t => STau (Spec.bind t k)
    | SVisF e t => SVis e (Spec.bind t k)
    | SAllF t => SAll (λ x, Spec.bind (t x) k)
    | SExistF t => SExist (λ x, Spec.bind (t x) k)
    | SGetF t => SGet (λ x, Spec.bind (t x) k)
    | SPutF s t => SPut s (Spec.bind t k)
    end.

  Lemma unfold_bind_ {EV S T U} (k : T → spec EV S U) (u : spec EV S T)
    : sobserving eq (Spec.bind u k) (bind_ u k).
  Proof. constructor; reflexivity. Qed.

  Lemma unfold_bind {EV S T U} (k : T → spec EV S U) (u : spec EV S T)
    : Spec.bind u k ≡ (bind_ u k).
  Proof. apply sobserving_sub_equiv; constructor; reflexivity. Qed.

  Lemma unfold_forever_ {EV S T U} (t : spec EV S T)
    : sobserving eq (Spec.forever (T:=U) t) (Spec.bind t (λ _, STau (Spec.forever t))).
  Proof. rewrite /Spec.forever/=. constructor. reflexivity. Qed.

End unfold.

(** * Lemmas about equivalences  *)
Lemma stau_equiv {EV S R} (t : spec EV S R) :
  STau t ≡ t.
Proof. by rewrite /equiv/spec_equiv unfold_spec_to_itree/= tau_eutt. Qed.

Lemma spec_to_itree_bind {EV S R T} (s : spec EV S R) (t : R → spec EV S T) :
  spec_to_itree (Spec.bind s t) ≈ ITree.bind (spec_to_itree s) (λ x, spec_to_itree (t x)).
Proof.
  revert s t. ginit. pcofix IH => s t.
  rewrite (unfold_spec_to_itree_eq s).
  (* TODO: Why is this so slow? *)
  rewrite unfold_bind_.
  destruct (sobserve s) => /=.
  1: rewrite bind_ret_l; by apply reflexivity.
  all: rewrite unfold_spec_to_itree_eq /= Eqit.unfold_bind/=.
  all: gstep; constructor; simpl; eauto with paco.
Qed.

Global Instance bind_Proper {EV S T U} :
  Proper ((≡) ==> pointwise_relation _ (≡) ==> (≡)) (@Spec.bind EV S T U).
Proof.
  move => x y Heq1 ?? Heq2.
  rewrite /equiv/spec_equiv !spec_to_itree_bind Heq1. by setoid_rewrite Heq2.
Qed.

Lemma spec_bind_bind {EV S R T U} (s : spec EV S R) (k : R → spec EV S U) (h : U → spec EV S T) :
  Spec.bind (Spec.bind s k) h ≡ Spec.bind s (fun r => Spec.bind (k r) h).
Proof.
  rewrite /equiv/spec_equiv !spec_to_itree_bind bind_bind.
  f_equiv => ?. rewrite spec_to_itree_bind. done.
Qed.

Lemma unfold_forever {EV S T U} (t : spec EV S T)
  : (Spec.forever (T:=U) t) ≡ (Spec.bind t (λ _, Spec.forever t)).
Proof. rewrite {1}unfold_forever_. setoid_rewrite stau_equiv. done. Qed.

Lemma bind_ret_l {EV S R U} (r : R) (k : R -> spec EV S U) :
  Spec.bind (TRet r) k ≡ (k r).
Proof. by rewrite unfold_bind. Qed.
