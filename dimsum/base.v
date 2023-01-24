From Coq Require Import Ascii.
From Coq Require Export ssreflect.
From RecordUpdate Require Export RecordSet.
From stdpp Require Export prelude gmap strings pretty.
From iris.prelude Require Export prelude.
From iris.proofmode Require Import proofmode.
Export RecordSetNotations.

Global Unset Program Cases.
Local Set Default Proof Using "Type*".

(** * Tactics *)
(** Inspired by inv in CompCert/Coqlib.v *)
(* TODO: upstream? See https://gitlab.mpi-sws.org/iris/stdpp/-/issues/40 *)
Ltac inv H := inversion H; clear H; simplify_eq.
Tactic Notation "inv/=" ident(H) := inversion H; clear H; simplify_eq/=.

Ltac inv_all_tac f :=
  repeat lazymatch goal with
         | H : f |- _ => inv H
         | H : f _ |- _ => inv H
         | H : f _ _|- _ => inv H
         | H : f _ _ _|- _ => inv H
         | H : f _ _ _ _|- _ => inv H
         | H : f _ _ _ _ _|- _ => inv H
         | H : f _ _ _ _ _ _|- _ => inv H
         | H : f _ _ _ _ _ _ _|- _ => inv H
         | H : f _ _ _ _ _ _ _ _|- _ => inv H
         | H : f _ _ _ _ _ _ _ _ _|- _ => inv H
         end.

Tactic Notation "inv_all/=" constr(f) := inv_all_tac f; simplify_eq/=.
Tactic Notation "inv_all" constr(f) := inv_all_tac f.

(** admit with string *)
Tactic Notation "admit:" constr(H) := admit.

(* TODO: make version for case_decide and case_match and upstream  *)
(** [case_bool_decide] variant that takes a pattern  *)
Tactic Notation "case_bool_decide" open_constr(pat) "as" ident(Hd) :=
  match goal with
  | H : context [@bool_decide ?P ?dec] |- _ =>
    unify P pat;
    destruct_decide (@bool_decide_reflect P dec) as Hd
  | |- context [@bool_decide ?P ?dec] =>
    unify P pat;
    destruct_decide (@bool_decide_reflect P dec) as Hd
  end.
Tactic Notation "case_bool_decide" open_constr(pat) :=
  let H := fresh in case_bool_decide pat as H.

(** abbreviations for [econstructor] *)
Tactic Notation "econs" := econstructor.
Tactic Notation "econs" integer(n) := econstructor n.

(** [fast_set_solver] is a faster version of [set_solver] that does
not call set_unfold and setoid_subst so often. *)
(* TODO: figure out why this is necessary *)
Ltac fast_set_solver := set_unfold; naive_solver.

(** exploit from CompCert/Coqlib.v *)
(* TODO: Is this a good idea? *)
Ltac exploit x := efeed generalize x.

(** [specialize_hyps] looks for hypothesis of the form [∀ x, P x → ...] and
 tries to find a unique solution for x. *)
Ltac specialize_hyps :=
  repeat match goal with
  | H : ∀ x, @?P x → ?G |- _ =>
      let i := open_constr:(_) in
      let H' := fresh in
      assert (P i) as H' by done;
      assert_succeeds (clear; assert (∀ x, P x → x = i) by naive_solver);
      specialize (H i H');
      clear H'
   end.

(** [destruct!] destructs things in the context *)
Ltac destruct_go tac :=
  repeat match goal with
         | H : context [ match ?x with | (y, z) => _ end] |- _ =>
             let y := fresh y in
             let z := fresh z in
             destruct x as [y z]
         | H : ∃ x, _ |- _ => let x := fresh x in destruct H as [x H]
         | |- _ => destruct_and!
         | |- _ => destruct_or!
         | |- _ => progress simplify_eq
         | |- _ => tac
         end.

Tactic Notation "destruct!" := destruct_go ltac:(fail).
Tactic Notation "destruct!/=" := destruct_go ltac:( progress csimpl in * ).

(** [split_or] tries to simplify an or in the goal by proving that one side implies False. *)
Ltac split_or :=
  repeat match goal with
         | |- ?P ∨ _ =>
             assert_succeeds (exfalso; assert P; [|
               destruct!;
               repeat match goal with | H : ?Q |- _ => has_evar Q; clear H end;
               done]);
             right
         | |- _ ∨ ?P =>
             assert_succeeds (exfalso; assert P; [|
               destruct!;
               repeat match goal with | H : ?Q |- _ => has_evar Q; clear H end;
               done]);
             left
         end.

(** [SplitAssumeInj] *)
Class SplitAssumeInj {A B} (R : relation A) (S : relation B) (f : A → B) : Prop := split_assume_inj : True.
Global Instance split_assume_inj_inj A B R S (f : A → B) `{!Inj R S f} : SplitAssumeInj R S f.
Proof. done. Qed.

Class SplitAssumeInj2 {A B C} (R1 : relation A) (R2 : relation B) (S : relation C) (f : A → B → C) : Prop := split_assume_inj2 : True.
Global Instance split_assume_inj2_inj2 A B C R1 R2 S (f : A → B → C) `{!Inj2 R1 R2 S f} : SplitAssumeInj2 R1 R2 S f.
Proof. done. Qed.

(** [split!] splits the goal *)
Ltac split_step tac :=
  match goal with
  | |- ∃ x, _ => eexists _
  | |- _ ∧ _ => split
  | |- _ ∨ _ => split_or
  | |- True → _ => intros _
  (* | |- ?P → ?Q => *)
   (* lazymatch type of P with *)
   (* TODO: replace this with assert_is_trivial from RefinedC? *)
   (* | Prop => assert_succeeds (assert (P) as _;[fast_done|]); intros _ *)
   (* end *)
  | |- ?e1 = ?e2 => is_evar e1; reflexivity
  | |- ?e1 = ?e2 => is_evar e2; reflexivity
  | |- ?e1 ≡ ?e2 => is_evar e1; reflexivity
  | |- ?e1 ≡ ?e2 => is_evar e2; reflexivity
  | |- ?G => assert_fails (has_evar G); done
  | H : ?o = Some ?x |- ?o = Some ?y => assert (x = y); [|congruence]
  | |- ?x = ?y  =>
      (* simplify goals where the head are constructors, like
         EICall f vs h = EICall ?Goal7 ?Goal8 ?Goal9 *)
      once (first [ has_evar x | has_evar y]);
      let hx := get_head x in
      is_constructor hx;
      let hy := get_head y in
      match hx with
      | hy => idtac
      end;
      apply f_equal_help
  | |- ?f ?a1 ?a2 = ?f ?b1 ?b2 =>
      let _ := constr:(_ : SplitAssumeInj2 (=) (=) (=) f) in
      apply f_equal_help; [apply f_equal_help; [done|]|]
  | |- ?f ?a = ?f ?b =>
      let _ := constr:(_ : SplitAssumeInj (=) (=) f) in
      apply f_equal_help; [done|]
  | |- _ => tac
  end; simpl.

Ltac split_tac tac :=
  (* The outer repeat is because later split_steps may have
  instantiated evars and thus we try earlier goals again. *)
  repeat (simpl; repeat split_step tac).

Tactic Notation "split!" := split_tac ltac:(fail).

(** [simplify_map_eq'] is a version of [simplify_map_eq] that also simplifies lookup total. *)
Tactic Notation "simpl_map_total" "by" tactic3(tac) := repeat
   match goal with
   | H : ?m !! ?i = Some ?x |- context [?m !!! ?i] =>
       rewrite (lookup_total_correct m i x H)
   | H1 : context [?m !!! ?i], H2 : ?m !! ?i = Some ?x |- _ =>
      rewrite (lookup_total_correct m i x H2) in H1
   | |- context [<[ ?i := ?x ]> (<[ ?i := ?y ]> ?m)] =>
       rewrite (insert_insert m i x y)
   | |- context[ (<[_:=_]>_) !!! _ ] =>
       rewrite lookup_total_insert || rewrite ->lookup_total_insert_ne by tac
   | H : context[ (<[_:=_]>_) !!! _ ] |- _ =>
       rewrite lookup_total_insert in H || rewrite ->lookup_total_insert_ne in H by tac
   | H : ?m !!! ?i = ?x |- context [?m !!! ?i] =>
       rewrite H
   | H : ?x = ?m !!! ?i |- context [?m !!! ?i] =>
       is_closed_term x; rewrite -H
   | H1 : ?m !!! ?i = ?x, H2 : context [?m !!! ?i] |- _ =>
       rewrite H1 in H2
   | H1 : ?x = ?m !!! ?i, H2 : context [?m !!! ?i] |- _ =>
       is_closed_term x; rewrite -H1 in H2
   (* | H : ?m !!! ?i = ?m2 !!! ?i2 |- context [?m !!! ?i] => *)
   (*     rewrite H *)
   (* | H1 : ?m !!! ?i = ?m2 !!! ?i2, H2 : context [?m !!! ?i] |- _ => *)
   (*     rewrite H1 in H2 *)
   end.
 Tactic Notation "simplify_map_eq'" "/=" "by" tactic3(tac) :=
  repeat (progress csimpl in * || (progress simpl_map_total by tac) || simplify_map_eq by tac ).
 Tactic Notation "simplify_map_eq'" :=
  repeat (progress (simpl_map_total by eauto with simpl_map map_disjoint) || simplify_map_eq by eauto with simpl_map map_disjoint ).
Tactic Notation "simplify_map_eq'" "/=" :=
  simplify_map_eq'/= by eauto with simpl_map map_disjoint.

(** [sort_map_insert] sorts concrete inserts such that they can later be eliminated via [insert_insert]. *)
Ltac sort_map_insert :=
  repeat match goal with
         | |- context [<[ ?i := ?x ]> (<[ ?j := ?y ]> ?m)] =>
             is_closed_term i;
             is_closed_term j;
             assert_succeeds (assert (encode j <? encode i)%positive; [vm_compute; exact I|]);
             rewrite (insert_commute m i j x y); [|done]
         end.

(** [simpl_map_decide] tries to simplify bool_decide in the goal *)
(* TODO: make more principled *)
Ltac simpl_map_decide :=
  let go' := first [done | by apply elem_of_dom | by apply not_elem_of_dom] in
  let go := solve [ first [go' | by match goal with | H : _ ## _ |- _ => move => ?; apply: H; go' end] ] in
  repeat (match goal with
  | |- context [bool_decide (?P)] => rewrite (bool_decide_true P); [|go]
  | |- context [bool_decide (?P)] => rewrite (bool_decide_false P); [|go]
  end; simpl).

(** ** [iDestruct!] *)
Tactic Notation "iDestruct!" :=
  repeat (
     iMatchHyp (fun H P =>
        match P with
        | False%I => iDestruct H as %[]
        | True%I => iDestruct H as %_
        | emp%I => iDestruct H as "_"
        | ⌜_⌝%I => iDestruct H as %?
        | (_ ∗ _)%I => iDestruct H as "[??]"
        | (∃ x, _)%I => iDestruct H as (?) "?"
        | (□ _)%I => iDestruct H as "#?"
        end)
  || simplify_eq/=).

Tactic Notation "iIntros!" := iIntros; iDestruct!.

(** ** [iSplit!] *)
Ltac iSplit_step tac :=
  lazymatch goal with
  | |- environments.envs_entails _ (∃ x, _)%I => iExists _
  | |- environments.envs_entails _ (_ ∗ _)%I => iSplit
  | |- environments.envs_entails _ (⌜_⌝)%I => iPureIntro
  | |- _ => split_step tac
  end; simpl.

Ltac iSplit_tac tac :=
  (* The outer repeat is because later split_steps may have
  instantiated evars and thus we try earlier goals again. *)
  repeat (simpl; repeat iSplit_step tac).

Tactic Notation "iSplit!" := iSplit_tac ltac:(fail).

(** * map_union_weak *)
Definition map_union_weak `{∀ A, Insert K A (M A), ∀ A, Empty (M A), ∀ A, Lookup K A (M A),
    ∀ A, FinMapToList K A (M A)} {A} (m1 m2 : M A) :=
  map_imap (λ l v, Some (default v (m1 !! l))) m2.

Section theorems.
  Lemma map_union_weak_insert {K A} `{Countable K} (m1 m2 : gmap K A) (i : K) (x : A):
    map_union_weak (<[i := x]>m1) m2 = alter (λ _, x) i (map_union_weak m1 m2).
  Proof.
    rewrite /map_union_weak. apply map_eq => j. rewrite !map_lookup_imap.
    destruct (decide (i = j)); subst.
    - rewrite lookup_insert /= lookup_alter map_lookup_imap. by destruct (m2 !! j).
    - by rewrite lookup_insert_ne // lookup_alter_ne // map_lookup_imap.
  Qed.

  Lemma map_union_weak_empty {K A} `{Countable K} (m : gmap K A):
    map_union_weak ∅ m = m.
  Proof.
    rewrite /map_union_weak. apply map_eq => i. rewrite map_lookup_imap.
    rewrite lookup_empty /=. by destruct (m !! i).
  Qed.
End theorems.

(** * Lemmas about maps *)
(** ** [fresh_map] *)
Definition fresh_map `{Countable A} `{Countable B} `{Infinite B}
    (S : gset A) (X : gset B) : gmap A B :=
  list_to_map (zip (elements S) (fresh_list (length (elements S)) X)).

Section fresh_map.
  Context `{Countable A} `{Countable B} `{Infinite B}.
  Implicit Types (S : gset A) (X : gset B).

  Lemma fresh_map_lookup_Some (S : gset A) (X : gset B) i x:
    fresh_map S X !! i = Some x → i ∈ S ∧ x ∉ X.
  Proof.
    rewrite -elem_of_list_to_map.
    - move => /(elem_of_zip_with _ _ _ _)[?[?[?[??]]]]. simplify_eq. split; [set_solver|].
      by apply: fresh_list_is_fresh.
    - rewrite fst_zip ?fresh_list_length //. apply NoDup_elements.
  Qed.

  Lemma fresh_map_lookup_None (S : gset A) (X : gset B) i:
    fresh_map S X !! i = None ↔ i ∉ S.
  Proof. rewrite -not_elem_of_list_to_map. rewrite fst_zip; [set_solver|]. by rewrite fresh_list_length. Qed.


  Lemma fresh_map_bij S X i1 i2 j :
    fresh_map S X !! i1 = Some j →
    fresh_map S X !! i2 = Some j →
    i1 = i2.
  Proof.
    rewrite -!elem_of_list_to_map.
    2: { rewrite fst_zip ?fresh_list_length //. apply NoDup_elements. }
    2: { rewrite fst_zip ?fresh_list_length //. apply NoDup_elements. }
    move => /elem_of_lookup_zip_with[i1'[?[?[?[??]]]]].
    move => /elem_of_lookup_zip_with[i2'[?[?[?[??]]]]]. simplify_eq.
    have ? : i1' = i2'  by apply: NoDup_lookup; [eapply (NoDup_fresh_list _ X)|..]. subst.
    naive_solver.
  Qed.

End fresh_map.

(** ** [codom] (not used) *)
Definition codom {K A} `{Countable K} `{Countable A} (m : gmap K A) : gset A :=
  list_to_set (snd <$> (map_to_list m)).

(** ** Misc lemmas about map *)

Section map_filter.
  Context `{FinMap K M}.
  Context {A} (P : K * A → Prop) `{!∀ x, Decision (P x)}.
  Implicit Types m : M A.
  Lemma map_filter_lookup_true m i :
    (∀ x, m !! i = Some x → P (i, x)) → filter P m !! i = m !! i.
  Proof. move => ?. rewrite map_filter_lookup. destruct (m !! i) => //=. case_option_guard; naive_solver. Qed.

(* https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/394 *)
  Lemma map_filter_empty_iff_2 m :
    map_Forall (λ i x, ¬P (i,x)) m →
    filter P m = ∅.
  Proof. apply map_filter_empty_iff. Qed.
End map_filter.

Section curry_uncurry.
  Context `{Countable K1, Countable K2} {A : Type}.

Lemma lookup_total_gmap_curry (m : gmap (K1 * K2) A) (i : K1) (j : K2):
  ((gmap_curry m !!! i): gmap K2 A) !! j = m !! (i, j).
Proof.
  rewrite -lookup_gmap_curry lookup_total_alt.
  destruct (gmap_curry m !! i); simpl; first done.
  by eapply lookup_empty.
Qed.
End curry_uncurry.

Section theorems.
Context `{FinMap K M}.
Lemma insert_union_r_Some {A} (m1 m2 : M A) i x :
  is_Some (m1 !! i) → m1 ∪ m2 = m1 ∪ <[i:=x]>m2.
Proof.
  intro. rewrite !insert_union_singleton_l. rewrite !(assoc_L (∪)).
  f_equal. apply map_eq => j. destruct (decide (i = j)); simplify_eq/=.
  - by rewrite lookup_union_l'.
  - rewrite lookup_union_l //. by apply lookup_singleton_None.
Qed.
End theorems.

(** ** Lemmas about map_difference *)
Section theorems.
Context `{FinMap K M}.
Lemma map_disjoint_difference_l' {A} (m1 m2 : M A) : m2 ∖ m1 ##ₘ m1.
Proof.
  intros i.
  unfold difference, map_difference; rewrite lookup_difference_with.
  by destruct (m1 !! i), (m2 !! i).
Qed.
Lemma map_disjoint_difference_r' {A} (m1 m2 : M A) : m1 ##ₘ m2 ∖ m1.
Proof. intros. symmetry. by apply map_disjoint_difference_l'. Qed.

Lemma map_difference_union_r {A} (m1 m2 : M A) :
  m1 ∪ m2 = m1 ∪ (m2 ∖ m1).
Proof.
  apply map_eq. intros i.
  apply option_eq. intros v.
  unfold difference, map_difference, difference_with, map_difference_with.
  rewrite !lookup_union_Some_raw (lookup_merge _).
  destruct (m1 !! i) as [x'|], (m2 !! i) => /=; intuition congruence.
Qed.

Lemma map_difference_difference {A} (m1 m2 m3 : M A) :
  m1 ∖ m2 ∖ m3 = m1 ∖ (m2 ∪ m3).
Proof.
  apply map_eq. intros i. apply option_eq. intros v.
  rewrite !lookup_difference_Some lookup_union_None.
  naive_solver.
Qed.

Lemma map_difference_id {A} (m1 m2 : M A) :
  m2 ⊆ m1 →
  m1 ∖ (m1 ∖ m2) = m2.
Proof.
  move => Hm.
  apply map_eq. intros i. apply option_eq. intros v.
  rewrite !lookup_difference_Some lookup_difference_None.
  split.
  - move => [Hm1 [?|[v' Hm2]]]; simplify_eq.
    have ? : m1 !! i = Some v' by apply: lookup_weaken.
    naive_solver.
  - move => ?. split; [|naive_solver]. by apply: lookup_weaken.
Qed.

Lemma map_difference_union_distr {A} (m1 m2 m : M A) :
  (m1 ∪ m2) ∖ m = (m1 ∖ m) ∪ (m2 ∖ m).
Proof.
  apply map_eq. intros i.
  apply option_eq. intros v.
  rewrite !(lookup_difference_Some, lookup_difference_None, lookup_union_Some_raw) /is_Some.
  naive_solver.
Qed.

Lemma map_difference_disj_id {A} (m1 m2 : M A) :
  m1 ##ₘ m2 →
  m1 ∖ m2 = m1.
Proof.
  intros Hdisj.
  apply map_eq. intros i.
  apply option_eq. intros v.
  rewrite !lookup_difference_Some. split; [naive_solver|]. move => ?. split; [done|].
  by apply: map_disjoint_Some_l.
Qed.

(* TODO: upstream *)
Lemma map_difference_fmap {A B} (m1 m2 : M A) (f : A → B) :
  f <$> (m1 ∖ m2) = (f <$> m1) ∖ (f <$> m2).
Proof.
  apply map_eq => ?. apply option_eq => ?.
  rewrite lookup_fmap fmap_Some. setoid_rewrite lookup_difference_Some.
  rewrite !lookup_fmap fmap_Some fmap_None. naive_solver.
Qed.

Lemma map_difference_difference_add {A} (m1 m2 : M A) :
  (m1 ∖ m2) = m1 ∖ (m2 ∖ (m2 ∖ m1)).
Proof.
  apply map_eq => ?. apply option_eq => ?.
  rewrite !lookup_difference_Some !lookup_difference_None /is_Some.
  setoid_rewrite lookup_difference_Some. naive_solver.
Qed.

Lemma map_difference_difference_subseteq {A} (m1 m2 : M A) :
  map_agree m1 m2 →
  m1 ∖ (m1 ∖ m2) ⊆ m2.
Proof.
  rewrite map_agree_spec. move => Hin.
  apply map_subseteq_spec => ??.
  rewrite !lookup_difference_Some !lookup_difference_None /is_Some. naive_solver.
Qed.
End theorems.

Section theorems.
Context `{FinMapDom K M D}.

Lemma map_difference_empty_dom {A} (m1 m2 : M A):
  dom m1 ⊆ dom m2 →
  m1 ∖ m2 = ∅.
Proof.
  move => Hdom. apply map_eq => i. rewrite lookup_empty.
  apply lookup_difference_None.
  destruct (m1 !! i) eqn: Heq; [|naive_solver].
  right. apply elem_of_dom. apply Hdom. by apply elem_of_dom.
Qed.

Lemma map_difference_eq_dom {A} (m m1 m2 : M A) :
  dom m1 ≡ dom m2 →
  m ∖ m1 = m ∖ m2.
Proof.
  move => Hdom.
  apply map_eq. intros i. move: (Hdom i). rewrite !elem_of_dom -!not_eq_None_Some => ?.
  apply option_eq. intros v.
  unfold difference, map_difference, difference_with, map_difference_with.
  rewrite !(lookup_merge _).
  destruct (m !! i), (m1 !! i) as [x'|] eqn: Heq1, (m2 !! i) eqn: Heq2 => /=; try intuition congruence.
Qed.
Lemma map_difference_eq_dom_L {A} (m m1 m2 : M A) `{!LeibnizEquiv D}:
  dom m1 = dom m2 →
  m ∖ m1 = m ∖ m2.
Proof. unfold_leibniz. apply: map_difference_eq_dom. Qed.
End theorems.

(** ** Lemmas about [list_to_map] *)
Section theorems.
Context `{FinMap K M}.
Lemma list_to_map_list_find {A} (l : list (K * A)) i y:
  (list_to_map l : M A) !! i = Some y ↔ ∃ j, list_find (λ e, e.1 = i) l = Some (j, (i, y)).
Proof.
  elim: l i => /=. { move => ?. split => ?; simplify_map_eq; naive_solver. }
  move => [??] ? IH i /=. rewrite lookup_insert_Some. case_decide; [naive_solver|].
  rewrite IH. setoid_rewrite fmap_Some. split => ?; destruct!.
  - eexists _, (_, (_, _)). done.
  - destruct x as [?[??]]. naive_solver.
Qed.

Lemma list_to_map_lookup_Some {A} (l : list (K * A)) i y:
  (list_to_map l : M A) !! i = Some y ↔
           ∃ j, l !! j = Some (i, y) ∧ (∀ j' y', l.*1 !! j' = Some y' → j' < j → y' ≠ i).
Proof.
  rewrite list_to_map_list_find. f_equiv => ?. rewrite list_find_Some.
  setoid_rewrite list_lookup_fmap. setoid_rewrite fmap_Some. naive_solver.
Qed.

Lemma list_to_map_lookup_is_Some {A} (l : list (K * A)) i :
  is_Some ((list_to_map l : M A) !! i) ↔ ∃ x, (i,x) ∈ l.
Proof.
  split.
  - move => [? /(elem_of_list_to_map_2 _ _ _)]. naive_solver.
  - move => [?]. induction l as [|i' l]. { by intros ?%elem_of_nil. }
    intros [?|?]%elem_of_cons; simplify_eq/=.
    { by rewrite lookup_insert. }
    destruct (decide (i'.1 = i)); subst.
    { by rewrite lookup_insert. }
    rewrite lookup_insert_ne; [|done].
    naive_solver.
Qed.
End theorems.

(** * Lemmas about sets *)
Lemma subseteq_eq A `{!SubsetEq A} `{!Reflexive (⊆@{A})} (X Y : A) :
  X = Y →
  X ⊆ Y.
Proof. intros ->. done. Qed.

Section semi_set.
  Context `{SemiSet A C}.
  Implicit Types x y : A.
  Implicit Types X Y : C.
  Implicit Types Xs Ys : list C.

  Lemma not_elem_of_disjoint x X Y:
    x ∈ X →
    X ## Y →
    x ∉ Y.
  Proof. set_solver. Qed.

  (* TODO: upstream, figure out naming scheme *)
  Lemma disjoint_mono X Y X' Y' :
    X' ## Y' →
    X ⊆ X' →
    Y ⊆ Y' →
    X ## Y.
  Proof. set_solver. Qed.
  Lemma subseteq_mono_eq_r X Y Y' :
    X ⊆ Y →
    Y = Y' →
    X ⊆ Y'.
  Proof. set_solver. Qed.
End semi_set.

(** * Lemmas about lists *)
Lemma snoc_inv {A} (l : list A):
  l = [] ∨ ∃ x l', l = l' ++ [x].
Proof. destruct l as [|x l'] using rev_ind; eauto. Qed.

Lemma list_elem_of_weaken {A} (xs ys : list A) x:
  x ∈ xs → xs ⊆ ys → x ∈ ys.
Proof. set_solver. Qed.

Lemma list_subseteq_cons_l {A} x (xs ys : list A):
  x ∈ ys → xs ⊆ ys → x :: xs ⊆ ys.
Proof. set_solver. Qed.

Lemma elem_of_drop {A} x n (xs : list A):
  x ∈ drop n xs → x ∈ xs.
Proof.  move => /elem_of_list_lookup. setoid_rewrite lookup_drop => -[??]. apply elem_of_list_lookup. naive_solver. Qed.

Section mjoin.
  Context {A : Type}.
  Implicit Types x y z : A.
  Implicit Types l k : list A.
  Implicit Types ls : list (list A).

  Lemma join_lookup_Some_same_length_2 n ls j i x l:
    Forall (λ l, length l = n) ls →
    (i < n)%nat →
    ls !! j = Some l →
    l !! i = Some x →
    mjoin ls !! (j * n + i)%nat = Some x.
  Proof. intros. apply join_lookup_Some_same_length'; naive_solver. Qed.
End mjoin.


Lemma sum_list_with_sum_list {A} f (xs : list A):
  sum_list_with f xs = sum_list (f <$> xs).
Proof. elim: xs => // ??; csimpl. lia. Qed.

Lemma Forall_zip_with_1 {A B} l1 l2 (f : A → B → Prop):
  Forall id (zip_with f l1 l2) →
  length l1 = length l2 →
  Forall2 f l1 l2.
Proof.
  elim: l1 l2 => /=. { case => //; econs. }
  move => ?? IH []//?? /(Forall_cons_1 _ _)[??] [?]. econs; [done|]. by apply: IH.
Qed.

Lemma Forall_zip_with_2 {A B} l1 l2 (f : A → B → Prop):
  Forall2 f l1 l2 →
  Forall id (zip_with f l1 l2).
Proof. elim => /=; by econs. Qed.

Section fmap.
  Context {A B : Type} (f : A → option B).
  Implicit Types l : list A.

  Lemma NoDup_omap_2_strong l :
    (∀ x y z, x ∈ l → y ∈ l → f x = Some z → f y = Some z → x = y) →
    NoDup l →
    NoDup (omap f l).
  Proof.
    intros Hinj. induction 1 as [|x l Hnotin ? IH]; csimpl; [constructor|].
    case_match. 2: apply IH; set_solver. constructor.
    - intros [y [Hxy ?]]%elem_of_list_omap. contradict Hnotin.
      erewrite (Hinj x); set_solver.
    - apply IH. set_solver.
  Qed.
End fmap.

(* TODO: upstream *)
Lemma NoDup_delete {X} p (L: list X):
  NoDup L →
  NoDup (delete p L).
Proof.
  intros Hnd. induction Hnd in p |-*; destruct p; simpl; eauto using NoDup_nil_2.
  eapply NoDup_cons. split; last done.
  intros [j Hlook]%elem_of_list_lookup_1.
  destruct (decide (j < p)).
  - rewrite lookup_delete_lt // in Hlook.
    eapply elem_of_list_lookup_2 in Hlook. done.
  - rewrite lookup_delete_ge // in Hlook; last lia.
    eapply elem_of_list_lookup_2 in Hlook. done.
Qed.

Lemma app_inj_middle {A} (l1 l2 l1' l2' : list A) x:
  x ∉ l2 →
  x ∉ l2' →
  l1 ++ x :: l2 = l1' ++ x :: l2' → l1 = l1' ∧ l2 = l2'.
Proof.
  move => Hnotin1 Hnotin2 Heq.
  destruct (decide (length l1 = length l1')). { move: Heq => /app_inj_1. naive_solver. }
  exfalso.
  have Hi : ∀ i, (l1 ++ x :: l2) !! i = (l1' ++ x :: l2') !! i by rewrite Heq.
  destruct (decide (length l1 < length l1')).
  - have := Hi (length l1').
    rewrite lookup_app_r ?list_lookup_middle ?lookup_cons_ne_0; [|lia..].
    move => /(elem_of_list_lookup_2 _ _ _). done.
  - have := Hi (length l1).
    rewrite list_lookup_middle ?lookup_app_r ?lookup_cons_ne_0; [|lia..].
    move => ?. apply Hnotin2. by apply: elem_of_list_lookup_2.
Qed.

(** * Lemmas about [option] *)
Definition option_prefix {A} (o1 o2 : option A) : Prop :=
  match o1 with
  | Some x1 => o2 = Some x1
  | None => True
  end.

Definition option_drop {A} (o1 o2 : option A) : option A :=
  match o1 with
  | Some _ => None
  | None => o2
  end.

Lemma default_eq_Some {A} (x : A) o:
  x = default x o ↔ (∀ y, o = Some y → x = y).
Proof. destruct o; naive_solver. Qed.

Lemma default_eq_Some' {A} (x : A) o:
  default x o = x ↔ (∀ y, o = Some y → x = y).
Proof. destruct o; naive_solver. Qed.

Lemma default_eq_neq {A} (x y : A) o:
  x ≠ y →
  default x o = y ↔ o = Some y.
Proof. destruct o; naive_solver. Qed.

(** * Strings and pretty *)
Notation string_to_list := list_ascii_of_string.

Lemma string_list_eq s1 s2 :
  s1 = s2 ↔ string_to_list s1 = string_to_list s2.
Proof.
  elim: s1 s2 => //=. { case; naive_solver. }
  move => ???. case; naive_solver.
Qed.

Global Instance string_to_list_inj : Inj (=) (=) (string_to_list).
Proof. move => ?? /string_list_eq. done. Qed.

Lemma string_to_list_app s1 s2 :
  string_to_list (s1 +:+ s2) = string_to_list s1 ++ string_to_list s2.
Proof. elim: s1 => //. cbn. move => ?? <-. done. Qed.

Lemma string_app_inj_r x y z:
  x +:+ z = y +:+ z → x = y.
Proof. move => /string_list_eq. rewrite !string_to_list_app => /app_inj_2[//|??]. by simplify_eq. Qed.

Definition digits : list ascii :=
  ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"]%char.

Lemma pretty_N_char_digits n:
  pretty_N_char n ∈ digits.
Proof. compute. repeat case_match; set_solver. Qed.

Lemma pretty_N_go_digits (n : N) s:
  string_to_list s ⊆ digits →
  string_to_list (pretty_N_go n s) ⊆ digits.
Proof.
  revert s. induction (N.lt_wf_0 n) as [n _ IH] => s Hs.
  destruct (decide (n = 0%N)); subst => //=.
  rewrite pretty_N_go_step; [|lia].
  apply IH => /=. { apply N.div_lt; lia. }
  apply list_subseteq_cons_l; [|done].
  apply pretty_N_char_digits.
Qed.

Lemma pretty_N_digits (n : N):
  string_to_list (pretty n) ⊆ digits.
Proof. rewrite /pretty/pretty_N. case_decide; [set_solver|]. apply pretty_N_go_digits. set_solver. Qed.

Lemma pretty_N_go_last n s c:
  last (string_to_list s) = Some c →
  last (string_to_list (pretty_N_go n s)) = Some c.
Proof.
  revert s. induction (N.lt_wf_0 n) as [n _ IH] => s Hs.
  destruct (decide (n = 0%N)); subst => //=.
  rewrite pretty_N_go_step; [|lia].
  apply IH => /=. { apply N.div_lt; lia. }
  by rewrite last_cons Hs.
Qed.

Lemma pretty_N_last (n : N):
  last (string_to_list (pretty n)) = Some (pretty_N_char (n `mod` 10)).
Proof.
  rewrite /pretty/pretty_N. case_decide; subst => //.
  rewrite pretty_N_go_step; [|lia]. by erewrite pretty_N_go_last.
Qed.

(** * Fixpoints based on iris/bi/lib/fixpoint.v *)
Class MonoPred {A : Type} (F : (A → Prop) → (A → Prop)) := {
  mono_pred (Φ Ψ : _ → Prop) :
    (∀ x, Φ x → Ψ x) → ∀ x, F Φ x → F Ψ x;
}.
Global Arguments mono_pred {_ _ _} _ _.

Definition prop_least_fixpoint {A : Type}
    (F : (A → Prop) → (A → Prop)) (x : A) : Prop :=
  tc_opaque (∀ Φ : A -> Prop, (∀ x, F Φ x → Φ x) → Φ x).
Global Arguments prop_least_fixpoint : simpl never.

Section least.
  Context {A : Type} (F : (A → Prop) → (A → Prop)) `{!MonoPred F}.

  Lemma prop_least_fixpoint_unfold_2 x : F (prop_least_fixpoint F) x → prop_least_fixpoint F x.
  Proof using Type*.
    rewrite /prop_least_fixpoint /=. move => HF Φ Hincl.
    apply Hincl. apply: mono_pred; [|done].
    move => /= y Hy. apply Hy. done.
  Qed.

  Lemma prop_least_fixpoint_unfold_1 x : prop_least_fixpoint F x → F (prop_least_fixpoint F) x.
  Proof using Type*.
    move => HF. apply HF. move => y Hy /=. apply: mono_pred; [|done].
    move => z Hz. by apply: prop_least_fixpoint_unfold_2.
  Qed.

  Lemma prop_least_fixpoint_unfold x : prop_least_fixpoint F x ↔ F (prop_least_fixpoint F) x.
  Proof using Type*. split; eauto using prop_least_fixpoint_unfold_1, prop_least_fixpoint_unfold_2. Qed.
End least.

Section least.
  Context {A : Type} (F : (A → Prop) → (A → Prop)) `{!MonoPred F}.

  Lemma prop_least_fixpoint_ind (Φ : A → Prop) :
    (∀ y, F Φ y → Φ y) → ∀ x, prop_least_fixpoint F x → Φ x.
  Proof using Type*. move => HΦ x HF. by apply: HF. Qed.

  Definition wf_pred_mono Φ : MonoPred (λ (Ψ : A → Prop) (a : A), Φ a ∧ F Ψ a).
  Proof using Type*.
    constructor. intros Ψ Ψ' Mon x [Ha ?]. split; [done|]. apply: mono_pred; [|done]. done.
  Qed.
  Local Existing Instance wf_pred_mono.

  Lemma prop_least_fixpoint_ind_wf (Φ : A → Prop) :
    (∀ y, F (prop_least_fixpoint (λ Ψ a, Φ a ∧ F Ψ a)) y → Φ y) →
    ∀ x, prop_least_fixpoint F x → Φ x.
  Proof using Type*.
    move => Hmon x. rewrite prop_least_fixpoint_unfold => Hx.
    apply Hmon. apply: mono_pred; [|done].
    apply prop_least_fixpoint_ind => y Hy.
    rewrite prop_least_fixpoint_unfold. split; [|done].
    by apply: Hmon.
  Qed.
End least.

Lemma prop_least_fixpoint_strong_mono {A : Type} (F : (A → Prop) → (A → Prop)) `{!MonoPred F}
    (G : (A → Prop) → (A → Prop)) `{!MonoPred G} :
  (∀ Φ x, F Φ x → G Φ x) →
  ∀ x, prop_least_fixpoint F x → prop_least_fixpoint G x.
Proof.
  move => Hmon. apply prop_least_fixpoint_ind; [done|].
  move => y IH. apply prop_least_fixpoint_unfold; [done|].
  by apply Hmon.
Qed.

Section least.
  Context {A B : Type} (F : ((A * B) → Prop) → ((A * B) → Prop)) `{!MonoPred F}.

  Lemma prop_least_fixpoint_pair_ind (Φ : A → B → Prop) :
    (∀ y1 y2, F (uncurry Φ) (y1, y2) → Φ y1 y2) → ∀ x1 x2, prop_least_fixpoint F (x1, x2) → Φ x1 x2.
  Proof using Type*.
    move => ? x1 x2. change (Φ x1 x2) with ((uncurry Φ) (x1, x2)).
    apply prop_least_fixpoint_ind; [done|]. move => [??] /=. naive_solver.
  Qed.

  Lemma prop_least_fixpoint_pair_ind_wf (Φ : A → B → Prop) :
    (∀ y1 y2, F (prop_least_fixpoint (λ Ψ a, uncurry Φ a ∧ F Ψ a)) (y1, y2) → Φ y1 y2) →
    ∀ x1 x2, prop_least_fixpoint F (x1, x2) → Φ x1 x2.
  Proof using Type*.
    move => ? x1 x2. change (Φ x1 x2) with ((uncurry Φ) (x1, x2)).
    apply prop_least_fixpoint_ind_wf; [done|]. move => [??] /=. naive_solver.
  Qed.
End least.


(** * map_list operations *)
(** ** Definitions *)
Definition map_list_included {K A} `{Countable K} (ns : list K) (rs : gmap K A) :=
  list_to_set ns ⊆ dom rs.

Definition map_scramble {K A} `{Countable K} `{!Inhabited A} (ns : list K) (rs rs' : gmap K A) :=
  ∀ i, i ∉ ns → rs !!! i = rs' !!! i.

Definition map_preserved {K A} `{Countable K} `{!Inhabited A} (ns : list K) (rs rs' : gmap K A) :=
  ∀ i, i ∈ ns → rs !!! i = rs' !!! i.

(** ** Lemmas *)
(** *** map_list_included *)
Lemma map_list_included_nil {K A} `{Countable K} (m : gmap K A):
  map_list_included [] m.
Proof. unfold map_list_included. set_solver. Qed.

Lemma map_list_included_cons {K A} `{Countable K} (m : gmap K A) n ns:
  n ∈ dom m →
  map_list_included ns m →
  map_list_included (n::ns) m.
Proof. unfold map_list_included. set_solver. Qed.

Lemma map_list_included_app {K A} `{Countable K} (m : gmap K A) ns1 ns2:
  map_list_included (ns1 ++ ns2) m ↔
  map_list_included ns1 m ∧ map_list_included ns2 m.
Proof. unfold map_list_included. set_solver. Qed.

Lemma map_list_included_is_Some {K A} `{Countable K} ns (m : gmap K A) i :
  map_list_included ns m →
  i ∈ ns →
  is_Some (m !! i).
Proof. move => Hin ?. apply elem_of_dom. apply Hin. set_solver. Qed.

Lemma map_list_included_insert {K A} `{Countable K} ns (m : gmap K A) i x:
  map_list_included ns m →
  map_list_included ns (<[i := x]>m).
Proof. unfold map_list_included. set_solver. Qed.

Lemma map_list_included_mono {K A} `{Countable K} (ns ns' : list K) (rs : gmap K A) :
  map_list_included ns rs →
  list_to_set ns' ⊆@{gset _} list_to_set ns →
  map_list_included ns' rs.
Proof. set_solver. Qed.

(** *** map_scramble *)
Global Instance map_scramble_preorder {K A} `{Countable K} `{!Inhabited A} ns : PreOrder (map_scramble (K:=K) (A:=A) ns).
Proof.
  constructor.
  - move => ???. done.
  - move => ??? Hm1 Hm2 ??. etrans; [by apply Hm1|]. by apply Hm2.
Qed.

Lemma map_scramble_sym {K A} `{Countable K} `{!Inhabited A} ns (m m' : gmap K A) :
  map_scramble ns m m' ↔ map_scramble ns m' m.
Proof. unfold map_scramble. naive_solver. Qed.

Lemma map_scramble_insert_r_in {K A} `{Countable K} `{!Inhabited A} ns (m m' : gmap K A) i x:
  i ∈ ns →
  map_scramble ns m (<[i:=x]>m') ↔ map_scramble ns m m'.
Proof.
  move => Hin. unfold map_scramble. apply forall_proper => ?.
  apply forall_proper => ?. rewrite lookup_total_insert_ne //. naive_solver.
Qed.

Lemma map_scramble_insert_r_not_in {K A} `{Countable K} `{!Inhabited A} ns (m m' : gmap K A) i x:
  i ∉ ns →
  map_scramble ns m (<[i:=x]>m') ↔ m !!! i = x ∧ map_scramble (i :: ns) m m'.
Proof.
  unfold map_scramble. move => ?. split.
  - move => Hm. split; [rewrite Hm //; by simplify_map_eq'|]. move => ??. rewrite Hm; [|set_solver].
    rewrite lookup_total_insert_ne; [|set_solver]. done.
  - move => [? Hm] i' ?. destruct (decide (i = i')); simplify_map_eq' => //. apply Hm. set_solver.
Qed.

Lemma map_scramble_insert_l_in {K A} `{Countable K} `{!Inhabited A} ns (m m' : gmap K A) i x:
  i ∈ ns →
  map_scramble ns (<[i:=x]>m) m' ↔ map_scramble ns m m'.
Proof. move => ?. rewrite map_scramble_sym map_scramble_insert_r_in // map_scramble_sym. done. Qed.

Lemma map_scramble_insert_l_not_in {K A} `{Countable K} `{!Inhabited A} ns (m m' : gmap K A) i x:
  i ∉ ns →
  map_scramble ns (<[i:=x]>m) m' ↔ m' !!! i = x ∧ map_scramble (i :: ns) m m'.
Proof. move => ?. rewrite map_scramble_sym map_scramble_insert_r_not_in // map_scramble_sym //. Qed.

Lemma map_scramble_eq {K A} `{Countable K} `{!Inhabited A} ns (m : gmap K A):
  map_scramble ns m m.
Proof. unfold map_scramble. naive_solver. Qed.

Lemma map_scramble_eq' {K A} `{Countable K} `{!Inhabited A} ns (m : gmap K A):
  map_scramble ns m m ↔ True.
Proof. unfold map_scramble. naive_solver. Qed.

Lemma map_scramble_mono {K A} `{Countable K} `{!Inhabited A} ns ns' (m m' : gmap K A):
  map_scramble ns m m' →
  ns ⊆ ns' →
  map_scramble ns' m m'.
Proof. unfold map_scramble. set_solver. Qed.

(** *** map_preserved *)
Global Instance map_preserved_preorder {K A} `{Countable K} `{!Inhabited A} ns : PreOrder (map_preserved (K:=K) (A:=A) ns).
Proof.
  constructor.
  - move => ???. done.
  - move => ??? Hm1 Hm2 ??. etrans; [by apply Hm1|]. by apply Hm2.
Qed.

Lemma map_preserved_sym {K A} `{Countable K} `{!Inhabited A} ns (m m' : gmap K A) :
  map_preserved ns m m' ↔ map_preserved ns m' m.
Proof. unfold map_preserved. naive_solver. Qed.

Lemma map_preserved_insert_r_not_in {K A} `{Countable K} `{!Inhabited A} ns (m m' : gmap K A) i x:
  i ∉ ns →
  map_preserved ns m (<[i:=x]>m') ↔ map_preserved ns m m'.
Proof.
  move => Hin. unfold map_preserved. apply forall_proper => ?.
  apply forall_proper => ?. rewrite lookup_total_insert_ne //. naive_solver.
Qed.

Lemma map_preserved_insert_r_in {K A} `{Countable K} `{!Inhabited A} ns (m m' : gmap K A) i x:
  i ∈ ns →
  map_preserved ns m (<[i:=x]>m') ↔ m !!! i = x ∧ map_preserved (filter (i≠.) ns) m m'.
Proof.
  unfold map_preserved. move => ?. split.
  - move => Hm. split; [rewrite Hm //; by simplify_map_eq'|]. move => ? /elem_of_list_filter[??].
    by rewrite Hm //  lookup_total_insert_ne.
  - move => [? Hm] i' ?. destruct (decide (i = i')); simplify_map_eq' => //. apply Hm. by apply elem_of_list_filter.
Qed.

Lemma map_preserved_insert_l_not_in {K A} `{Countable K} `{!Inhabited A} ns (m m' : gmap K A) i x:
  i ∉ ns →
  map_preserved ns (<[i:=x]>m) m' ↔ map_preserved ns m m'.
Proof. move => ?. rewrite map_preserved_sym map_preserved_insert_r_not_in // map_preserved_sym. done. Qed.

Lemma map_preserved_insert_l_in {K A} `{Countable K} `{!Inhabited A} ns (m m' : gmap K A) i x:
  i ∈ ns →
  map_preserved ns (<[i:=x]>m) m' ↔ m' !!! i = x ∧ map_preserved (filter (i≠.) ns) m m'.
Proof. move => ?. rewrite map_preserved_sym map_preserved_insert_r_in // map_preserved_sym. done. Qed.

Lemma map_preserved_eq {K A} `{Countable K} `{!Inhabited A} ns (m : gmap K A):
  map_preserved ns m m.
Proof. unfold map_preserved. naive_solver. Qed.

Lemma map_preserved_eq' {K A} `{Countable K} `{!Inhabited A} ns (m : gmap K A):
  map_preserved ns m m ↔ True.
Proof. unfold map_preserved. naive_solver. Qed.

Lemma map_preserved_app {K A} `{Countable K} `{!Inhabited A} ns1 ns2 (m m' : gmap K A) :
  map_preserved (ns1 ++ ns2) m m' ↔ map_preserved ns1 m m' ∧ map_preserved ns2 m m'.
Proof. unfold map_preserved. set_solver. Qed.

Lemma map_preserved_mono {K A} `{Countable K} `{!Inhabited A} ns1 ns2 (m m' : gmap K A) :
  map_preserved ns1 m m' →
  ns2 ⊆ ns1 →
  map_preserved ns2 m m'.
Proof. unfold map_preserved. set_solver. Qed.

Lemma map_preserved_nil {K A} `{Countable K} `{!Inhabited A} (m m' : gmap K A) :
  map_preserved [] m m'.
Proof. move => ??. set_solver. Qed.
Lemma map_preserved_nil' {K A} `{Countable K} `{!Inhabited A} (m m' : gmap K A) ns:
  ns = [] →
  map_preserved ns m m'.
Proof. move => -> ??. set_solver. Qed.

Lemma map_preserved_cons {K A} `{Countable K} `{!Inhabited A} n ns (m m' : gmap K A) :
  m !!! n = m' !!! n →
  map_preserved ns m m' →
  map_preserved (n::ns) m m'.
Proof. move => ? Hpre ? /elem_of_cons[?|?]; [naive_solver| by apply Hpre]. Qed.

Lemma map_scramble_preserved {K A} `{Countable K} `{!Inhabited A} ns1 ns2 (m m' : gmap K A) :
  map_scramble ns1 m m' → ns1 ## ns2 → map_preserved ns2 m m'.
Proof. unfold map_preserved, map_scramble. set_solver. Qed.

Global Opaque map_list_included map_scramble map_preserved.

(** ** [simplify_map_list] tactic *)
Ltac simplify_map_list :=
  repeat match goal with
         | H : map_list_included ?ns ?m |- is_Some (?m !! ?r) =>
             is_closed_term ns;
             apply (map_list_included_is_Some _ _ _ H);
             compute_done
         | |- map_list_included ?ns (<[?i:=?x]> ?m) =>
             apply (map_list_included_insert ns m i x)
         | |- context [ map_scramble ?ns ?m (<[?i:=?x]> ?m') ] =>
             is_closed_term ns;
             rewrite ->(map_scramble_insert_r_in ns m m' i x) by compute_done
         | |- context [ map_preserved ?ns ?m (<[?i:=?x]> ?m') ] =>
             is_closed_term ns;
             rewrite ->(map_preserved_insert_r_not_in ns m m' i x) by compute_done
         | H : map_scramble ?ns (<[?i:=?x]> ?m) ?m' |- _ =>
             is_closed_term ns;
             rewrite ->(map_scramble_insert_l_in ns m m' i x) in H by compute_done
         | H : map_preserved ?ns (<[?i:=?x]> ?m) ?m' |- _ =>
             is_closed_term ns;
             rewrite ->(map_preserved_insert_l_not_in ns m m' i x) in H by compute_done
         | H : map_scramble ?ns (<[?i:=?x]> ?m) ?m' |- _ =>
             is_closed_term ns;
             apply map_scramble_insert_l_not_in in H; [|compute_done];
             let H' := fresh in
             destruct H as [H' H]
         | H : map_preserved ?ns (<[?i:=?x]> ?m) ?m' |- _ =>
             is_closed_term ns;
             apply map_preserved_insert_l_in in H; [|compute_done];
             let H' := fresh in
             destruct H as [H' H]
         | |- context [map_scramble ?ns ?m (<[?i:=?x]> ?m')] =>
             is_closed_term ns;
             rewrite ->(map_scramble_insert_r_not_in ns m m' i x) by compute_done
         | |- context [map_preserved ?ns ?m (<[?i:=?x]> ?m')] =>
             is_closed_term ns;
             rewrite ->(map_preserved_insert_r_in ns m m' i x) by compute_done
         | |- context [ map_scramble ?ns ?m ?m ] =>
             rewrite ->(map_scramble_eq' ns m)
         | |- context [ map_preserved ?ns ?m ?m ] =>
             rewrite ->(map_preserved_eq' ns m)
         end.

(** * Lemmas about [big_sepL] *)
Section big_op.
Context {PROP : bi}.
Implicit Types P Q : PROP.
Implicit Types Ps Qs : list PROP.
Implicit Types A : Type.
(* TODO: upstream, but also add all versions (i.e. where one pullsout equality) *)
Lemma big_sepL_zip_with_same_length {A B C} (Φ : nat → A → PROP) f (l1 : list B) (l2 : list C) :
  length l1 = length l2 →
  ([∗ list] k↦x ∈ zip_with f l1 l2, Φ k x) ⊣⊢
  ([∗ list] k↦x1;x2 ∈ l1;l2, Φ k (f x1 x2)).
Proof.
  intros Hlen.
  rewrite big_sepL2_alt.
  rewrite zip_with_zip big_sepL_fmap bi.pure_True // left_id.
  by f_equiv => ? [??].
Qed.
End big_op.

(** * Lemmas about [big_sepM] *)
Section big_op.
Context {PROP : bi}.
Implicit Types P Q : PROP.
Implicit Types Ps Qs : list PROP.
Implicit Types A : Type.
Section sep_map.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → PROP.

  Lemma big_sepM_alter (f : A → A) (Φ : K → A → PROP) m i :
    ([∗ map] k↦y ∈ alter f i m, Φ k y) ⊣⊢ ([∗ map] k↦y ∈ m, Φ k (if bool_decide (k = i) then f y else y)).
  Proof.
    induction m as [|k y m Hk IH] using map_ind.
    { by rewrite alter_id // !big_sepM_empty. }
    rewrite big_sepM_insert // -IH. case_bool_decide; subst.
    - rewrite alter_insert big_sepM_insert // alter_id //. naive_solver.
    - rewrite alter_insert_ne // big_sepM_insert //. by apply lookup_alter_None.
  Qed.

  Lemma big_sepM_list_to_map xs Φ :
    NoDup xs.*1 →
    ([∗ map] k↦y ∈ list_to_map xs, Φ k y) ⊣⊢ [∗ list] x∈xs, Φ x.1 x.2.
  Proof.
    induction xs as [|x xs IH]; csimpl.
    { intros _. by rewrite big_sepM_empty. }
    intros [??]%NoDup_cons. rewrite big_sepM_insert ?IH; [done..|].
    by apply not_elem_of_list_to_map.
  Qed.

  Lemma big_sepM_map_seq xs n (Φ : nat → A → PROP) :
    ([∗ map] k↦y ∈ map_seq n xs, Φ k y) ⊣⊢ [∗ list] i↦x∈xs, Φ (n + i) x.
  Proof.
    revert n. induction xs as [|x xs IH]; csimpl.
    { intros _. by rewrite big_sepM_empty. }
    intros n. rewrite big_sepM_insert ?IH. 2: apply map_seq_cons_disjoint.
    rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. setoid_rewrite Nat.add_succ_l. done.
  Qed.

  Lemma big_sepM_map_seq_0 xs (Φ : nat → A → PROP) :
    ([∗ map] k↦y ∈ map_seq 0 xs, Φ k y) ⊣⊢ [∗ list] i↦x∈xs, Φ i x.
  Proof. apply big_sepM_map_seq. Qed.

  Lemma big_sepM_kmap_intro {B} `{Countable B} (f : K → B) m Φ `{!Inj (=) (=) f} `{!BiAffine PROP}:
    ([∗ map] k↦y∈kmap f m, ∃ x, ⌜f x = k⌝ ∗ Φ x y) ⊣⊢
    [∗ map] k↦y∈m, Φ k y.
  Proof.
    induction m as [|k y m Hk IH] using map_ind.
    { by rewrite kmap_empty !big_sepM_empty. }
    rewrite kmap_insert !big_sepM_insert //. 2: { apply lookup_kmap_None; [done|]. naive_solver. }
    rewrite IH. f_equiv.
    iSplit.
    - iIntros "[%x [% ?]]". by simplify_eq.
    - iIntros "?". iExists _. by iFrame.
  Qed.

  Lemma big_sepM_impl_strong' {B}
        (Φ : K → A → PROP) (Ψ : K → B → PROP) (m1 : gmap K A) (m2 : gmap K B) `{!BiAffine PROP}:
    ([∗ map] k↦x ∈ m1, Φ k x) -∗
    □ (∀ (k : K) (y : B),
      (if m1 !! k is Some x then Φ k x else emp) -∗
      ⌜m2 !! k = Some y⌝ →
      Ψ k y) -∗
    ([∗ map] k↦y ∈ m2, Ψ k y).
  Proof. iIntros "Hm Hi". by iDestruct (big_sepM_impl_strong with "Hm Hi") as "[? _]". Qed.

  Lemma big_sepM_delete_2 Φ m i:
    (∀ y, Affine (Φ i y)) →
    ([∗ map] k↦y ∈ m, Φ k y) -∗
    ([∗ map] k↦y ∈ delete i m, Φ k y).
  Proof.
    iIntros (?) "Hm".
    destruct (m !! i) as [v|] eqn: Hi.
    - rewrite big_sepM_delete; [|done]. iDestruct "Hm" as "[_ $]".
    - by rewrite delete_notin.
  Qed.

  Lemma big_sepM_union_2 Φ m1 m2 :
    (∀ i y, Affine (Φ i y)) →
    ([∗ map] k↦y ∈ m1, Φ k y) -∗
    ([∗ map] k↦y ∈ m2, Φ k y) -∗
    ([∗ map] k↦y ∈ m1 ∪ m2, Φ k y).
  Proof.
    iIntros (?) "Hm1 Hm2".
    iInduction m2 as [|k x m2 ?] "IH" using map_ind forall (m1). { by rewrite right_id_L. }
    rewrite big_sepM_insert //. iDestruct "Hm2" as "[? ?]". iDestruct ("IH" with "Hm1 [$]") as "?".
    destruct (m1 !! k) as [y|] eqn:?.
    - have -> : (m1 ∪ <[k:=x]> m2) = m1 ∪ m2. 2: done.
      apply map_eq => ?. apply option_eq => ?.
      rewrite !lookup_union_Some_raw lookup_insert_Some. naive_solver.
    - rewrite -insert_union_r //. rewrite !big_sepM_insert //. 2: { by apply lookup_union_None. }
      iFrame.
Qed.
End sep_map.
End big_op.

(** * Lemmas about [big_sepM2] *)
Section big_op.
Context {PROP : bi}.
Implicit Types P Q : PROP.
Implicit Types Ps Qs : list PROP.
Implicit Types A : Type.
Section map2.
  Context `{Countable K} {A B : Type}.
  Implicit Types Φ Ψ : A → B → PROP.

  Lemma big_sepM2_list_to_map_2 xs ys Φ :
    BiAffine PROP →
    xs.*1 = ys.*1 →
    ([∗ list] x;y∈xs.*2;ys.*2, Φ x y) -∗
    ([∗ map] x;y ∈ list_to_map (K:=K) xs;list_to_map ys, Φ x y).
  Proof.
    iIntros (? Heq) "Hxs".
    iInduction xs as [|x xs] "IH" forall (ys Heq); destruct ys as [|y ys] => //; simplify_eq/=.
    iDestruct "Hxs" as "[Hx Hxs]".
    rewrite H1. iApply (big_sepM2_insert_2 with "[Hx]"); [done|].
    by iApply "IH".
  Qed.
End map2.
End big_op.
