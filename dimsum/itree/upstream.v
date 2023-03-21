From ITree Require Export ITree ITreeFacts.

(* TODO: upstream *)
Module ITreeStdppNotations.
Notation "m ≫= f" := (ITree.bind f m) (at level 60, right associativity) : itree_scope.
Notation "x ← y ; z" := (ITree.bind y (fun x : _ => z))
  (at level 20, y at level 100, z at level 200,
  format "x  ←  y ;  '/' z") : itree_scope.
Notation "' x ← y ; z" := (ITree.bind y (fun x_ : _ => match x_ with x => z end))
  (at level 20, x pattern, y at level 100, z at level 200,
  format "' x  ←  y ;  '/' z") : itree_scope.
Notation "x ;; z" := (ITree.bind x (fun _ => z))
  (at level 100, z at level 200, right associativity) : itree_scope.
End ITreeStdppNotations.

Module ITree.
  Import ITreeStdppNotations.
  Fixpoint flat_map {A E R} (f : A -> itree E R) (xs : list A) : itree E (list R) :=
    match xs with
    | nil => Ret nil
    | cons y ys =>
        r ← f y;
        rs ← flat_map f ys;
        Ret (cons r rs)
        end%itree.
End ITree.

Definition Tau_maybe {E R} (b : bool) (t : itree E R) :=
  if b then Tau t else t.
Notation "'Tau?' b t" := (Tau_maybe b t)
  (at level 20, b at level 9, t at level 20, right associativity, format "'Tau?' b  t").

Require Import Paco.paco.

From Coq Require Import
     Program.Tactics
     Setoid
     Morphisms.

From ITree Require Import
     Basics.Tacs
     Basics.Category
     Basics.Basics
     Basics.Function
     Core.ITreeDefinition
     Core.KTree
     Eq.Eqit
     Eq.UpToTaus
     Eq.Paco2
     Indexed.Sum
     Indexed.Function
     Indexed.Relation
     Interp.Handler
     Interp.Interp
     Interp.InterpFacts
     Interp.Recursion.

Global Instance eqit_false_true_rewrite {R E} r : RewriteRelation (@eqit E R R r false true) := { }.
Global Instance eqit_true_false_rewrite {R E} r : RewriteRelation (@eqit E R R r true false) := { }.

Lemma interp_trigger_eq {E F : Type -> Type} {R : Type}
      (f : E ~> (itree F))
      (e : E R) :
  interp f (ITree.trigger e) ≅ ITree.bind (f _ e) (fun x => Tau (Ret x)).
Proof.
  unfold ITree.trigger. rewrite interp_vis.
  setoid_rewrite interp_ret.
  reflexivity.
Qed.

(* We cannot have ≅ here because interp inserts a Tau after every
visible event in t. *)
Lemma interp_trigger_h_ge {E R} (t : itree E R) :
  interp ITree.trigger t ≳ t.
Proof. apply interp_id_h. Qed.

Lemma translate_trigger_eq {E F G} `{E -< F} :
  forall X (e: E X) (h: F ~> G),
    translate h (trigger e) ≅ trigger (h _ (subevent X e)).
Proof.
  intros; unfold trigger; rewrite translate_vis; setoid_rewrite translate_ret; reflexivity.
Qed.

#[global]
Instance euttge_cong_eq {E R1 R2 RR}:
  Proper (eq_itree eq ==> eq_itree eq ==> iff)
    (@eqit E R1 R2 RR true false).
Proof. split; ginit; intros; [rewrite <-H, <-H0|rewrite H, H0]; eauto with paco. Qed.

Definition interp_mrec' {D E : Type -> Type}
           (ctx : D ~> itree (D +' E)) : itree (D +' E) ~> itree E :=
  fun R =>
    ITree.iter (fun t : itree (D +' E) R =>
      match observe t with
      | RetF r => Ret (inr r)
      | TauF t => Ret (inl t)
      | VisF (inl1 d) k => Ret (inl (ITree.bind (ctx _ d) (fun x => Tau (k x))))
      | VisF (inr1 e) k => Vis e (fun x => Ret (inl (k x)))
      end).

Arguments interp_mrec' {D E} & ctx [T].

Definition mrec' {D E : Type -> Type}
           (ctx : D ~> itree (D +' E)) : D ~> itree E :=
  fun R d => interp_mrec' ctx (ctx _ d).

Arguments mrec' {D E} & ctx [T].

Definition rec' {E : Type -> Type} {A B : Type}
           (body : A -> itree (callE A B +' E) B) :
  A -> itree E B :=
  fun a => mrec' (calling' body) (Call a).

Arguments rec' {E A B} &.

Section Facts.
Context {D E : Type -> Type} (ctx : D ~> itree (D +' E)).

Definition _interp_mrec' {R : Type} (ot : itreeF (D +' E) R _) : itree E R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (interp_mrec' ctx t)
  | VisF e k =>
    match e with
    | inl1 d => Tau (interp_mrec' ctx ((ITree.bind (ctx _ d) (fun x => Tau (k x)))))
    | inr1 e => Vis e (fun x => Tau (interp_mrec' ctx (k x)))
    end
  end.


Lemma unfold_interp_mrec' R (t : itree (D +' E) R) :
  interp_mrec' ctx t ≅ _interp_mrec' (observe t).
Proof.
  unfold interp_mrec'.
  rewrite unfold_iter.
  destruct observe; cbn.
  - rewrite bind_ret_l; reflexivity.
  - rewrite bind_ret_l. pstep; constructor. intros. left. apply reflexivity.
  - destruct e; cbn.
    + rewrite bind_ret_l; reflexivity.
    + rewrite bind_vis.
      pstep; constructor. intros. left.
      rewrite bind_ret_l.
      apply reflexivity.
Qed.

Definition mrecursive' (f : D ~> itree (D +' E))
  : (D +' E) ~> itree E := fun _ m =>
  match m with
  | inl1 m => Tau (mrec' f m)
  | inr1 m => ITree.trigger m
  end.

Global Instance eq_itree_mrec' {R} :
  Proper (eq_itree eq ==> eq_itree eq) (@interp_mrec' _ _ ctx R).
Proof.
  ginit. pcofix CIH. intros.
  rewrite !unfold_interp_mrec'.
  punfold H0. inv H0; try discriminate; pclearbot; simpobs; [| |destruct e]; gstep.
  - apply reflexivity.
  - econstructor. eauto with paco.
  - econstructor. gbase. eapply CIH. apply eqit_bind; auto; [reflexivity|].
    intros ?. pstep; constructor. left. eauto.
  - econstructor. gstep; constructor. auto with paco itree.
Qed.


Theorem interp_mrec_bind' {U T} (t : itree _ U) (k : U -> itree _ T) :
  interp_mrec' ctx (ITree.bind t k) ≅
  ITree.bind (interp_mrec' ctx t) (fun x => interp_mrec' ctx (k x)).
Proof.
  revert t k; ginit. pcofix CIH; intros.
  rewrite (unfold_interp_mrec' _ t).
  rewrite (unfold_bind t).
  destruct (observe t); cbn;
    [| |destruct e];
    autorewrite with itree.
  1: apply reflexivity.
  all: rewrite unfold_interp_mrec'; ITree.fold_subst.
  all: try (gstep; econstructor; eauto with paco).
  - setoid_rewrite <-bind_tau. rewrite <-bind_bind. eauto with paco.
  - intros. red. rewrite bind_tau. gstep; constructor; auto with paco.
Qed.

Theorem interp_mrec'_as_interp_eq {T} (c : itree _ T) :
  interp_mrec' ctx c ≅ interp (mrecursive' ctx) c.
Proof.
  revert_until T. ginit. pcofix CIH. intros.
  rewrite unfold_interp_mrec', unfold_interp.
  destruct (observe c); [| |destruct e]; simpl; eauto with paco.
  - gstep; repeat econstructor; eauto.
  - gstep; constructor; eauto with paco.
  - rewrite bind_tau. rewrite interp_mrec_bind'. unfold mrec'.
    gstep; constructor.
    guclo eqit_clo_bind; econstructor; [reflexivity|].
    intros ? _ []. rewrite unfold_interp_mrec'. cbn.
    gstep; constructor. eauto with paco.
  - unfold ITree.trigger, case_; simpl. rewrite bind_vis.
    gstep. constructor.
    intros; red.
    rewrite bind_ret_l.
    gstep. constructor.
    auto with paco.
Qed.

Theorem mrec'_as_interp_eq {T} (d : D T) :
  mrec' ctx d ≅ interp (mrecursive' ctx) (ctx _ d).
Proof.
  apply interp_mrec'_as_interp_eq.
Qed.

End Facts.

Local Opaque interp_mrec'.

(** [rec' body] is equivalent to [interp (recursive' body)],
    where [recursive'] is defined as follows. *)
Definition recursive' {E A B} (f : A -> itree (callE A B +' E) B) : (callE A B +' E) ~> itree E :=
  case_ (calling' (fun a => Tau (rec' f a))) ITree.trigger.

Lemma rec'_as_interp_eq {E A B} (f : A -> itree (callE A B +' E) B) (x : A) :
  rec' f x ≅ interp (recursive' f) (f x).
Proof.
  unfold rec'.
  rewrite mrec'_as_interp_eq.
  eapply eq_itree_interp.
  - red. unfold case_; intros ? [[] | ]; reflexivity.
  - reflexivity.
Qed.

Lemma interp_recursive'_call_eq {E A B} (f : A -> itree (callE A B +' E) B) (x:A) :
   interp (recursive' f) (call x) ≅ Tau (ITree.bind (rec' f x) (fun x => Tau (Ret x))).
Proof.
  unfold recursive'. unfold call.
  rewrite interp_trigger_eq. cbn.
  rewrite bind_tau. reflexivity.
Qed.

From stdpp Require Import prelude.

Class ITreeToTranslate {E1 E2 R} (i : itree E1 R) (H : E2 -< E1) (o : itree E2 R) := {
    itree_to_translate : i ≅ translate (@resum _ _ _ _ H) o
}.
Global Hint Mode ITreeToTranslate + + + ! + - : typeclass_instances.

Lemma ITreeToTranslate_trigger R E E1 E2 (e : E _)
  (Hin : E1 -< E2) (Hin2 : E -< E1) (Hin3 : E -< E2) :
  Hin3 R e = (Hin R (Hin2 R e)) →
  ITreeToTranslate (R:=R) (ITree.trigger (subevent _ e)) Hin (ITree.trigger (subevent _ e)).
Proof. constructor. rewrite translate_trigger_eq. by f_equiv. Qed.

Global Instance ITreeToTranslate_bind R S E1 E2 (Hin : E1 -< E2) t1 t2 (k1 k2 : R → _) :
  ITreeToTranslate (R:=R) t1 Hin t2 →
  (∀ x, ITreeToTranslate (k1 x) Hin (k2 x)) →
  ITreeToTranslate (R:=S) (ITree.bind t1 k1) Hin (ITree.bind t2 k2).
Proof. intros [?] Hk. constructor. rewrite translate_bind. f_equiv; [done|]. intros ?. apply Hk. Qed.

Global Instance ITreeToTranslate_Ret R E1 E2 (Hin : E1 -< E2) (x : R) :
  ITreeToTranslate (Ret x) Hin (Ret x).
Proof. constructor. by rewrite translate_ret. Qed.
