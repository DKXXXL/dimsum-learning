From Coq Require Export ssreflect.
Require Export stdpp.prelude.
Require Export stdpp.gmap.
Require Export stdpp.strings.

Global Unset Program Cases.

(* from Iris prelude.v*)
Global Open Scope general_if_scope.
Global Set SsrOldRewriteGoalsOrder. (* See Coq issue #5706 *)
Ltac done := stdpp.tactics.done.


Definition LEM (P : Prop) := P ∨ ¬ P.

Lemma snoc_inv {A} (l : list A):
  l = [] ∨ ∃ x l', l = l' ++ [x].
Proof.
  destruct l as [|x l']. by left. right.
  elim: l' x => //. move => x. by eexists _, [].
  move => x ? IH x'. move: (IH x) => [x'' [l'' ->]].
  eexists x'', _. by apply: app_comm_cons.
Qed.

Record wrap A := Wrap { a : A }.

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

Ltac destruct_hyps :=
  simplify_eq/=;
  repeat (
      lazymatch goal with
      | H : (_ * _) |- _ => destruct H as [??]
      | H : unit |- _ => destruct H
      | H : ∃ x, _ |- _ => destruct H as [??]
      | H : _ ∧ _ |- _ => destruct H as [??]
      end; simplify_eq/=
    ).

Tactic Notation "econs" := econstructor.
Tactic Notation "econs" integer(n) := econstructor n.

Tactic Notation "destruct_prod" "?" ident(H) :=
  repeat match type of H with
         | context [ match ?x with | (y, z) => _ end] =>
             let y := fresh y in
             let z := fresh z in
             destruct x as [y z]
         end.
Tactic Notation "destruct_prod" "!" ident(H) := progress (destruct_prod? H).
Tactic Notation "destruct_prod" "?" :=
  repeat match goal with H : _ |- _ => progress (destruct_prod? H) end.
Tactic Notation "destruct_prod" "!" :=
  progress destruct_prod?.
Tactic Notation "destruct_exist" "?" ident(H) :=
  repeat match type of H with
         | ∃ x, _ => let x := fresh x in destruct H as [x H]
         end.
Tactic Notation "destruct_exist" "!" ident(H) := progress (destruct_exist? H).
Tactic Notation "destruct_exist" "?" :=
  repeat match goal with H : _ |- _ => progress (destruct_exist? H) end.
Tactic Notation "destruct_exist" "!" :=
  progress destruct_exist?.
Tactic Notation "destruct_all" "?" :=
  repeat first [
      destruct_prod!
      | destruct_and!
      | destruct_or!
      | destruct_exist!
      ].
Tactic Notation "destruct_all" "!" :=
  progress destruct_all?.

Ltac simpl_or :=
  repeat match goal with
         | |- ?P ∨ _ =>
             assert_succeeds (exfalso; assert P; [| destruct_all?;
                  repeat match goal with | H : ?Q |- _ => has_evar Q; clear H end;
                                                    done]);
             right
         | |- _ ∨ ?P =>
             assert_succeeds (exfalso; assert P; [| destruct_all?;
                  repeat match goal with | H : ?Q |- _ => has_evar Q; clear H end;
                                                    done]);
             left
         end.

Ltac split_step :=
  match goal with
  | |- ∃ x, _ => eexists _
  | |- _ ∧ _ => split
  | |- _ ∨ _ => simpl_or
  | |- ?e1 = ?e2 => is_evar e1; reflexivity
  | |- ?e1 = ?e2 => is_evar e2; reflexivity
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
  end; simpl.

Ltac original_split_tac :=
  (* The outer repeat is because later split_steps may have
  instantiated evars and thus we try earlier goals again. *)
  repeat (simpl; repeat split_step).

Ltac split_tac :=
  original_split_tac.

Tactic Notation "split!" := split_tac.

Ltac simpl_map_ext tac := idtac.

Tactic Notation "simpl_map_total" "by" tactic3(tac) := repeat
   match goal with
   | H : ?m !! ?i = Some ?x |- context [?m !!! ?i] =>
       rewrite (lookup_total_correct m i x H)
   | |- context [<[ ?i := ?x ]> (<[ ?i := ?y ]> ?m)] =>
       rewrite (insert_insert m i x y)
   | |- context[ (<[_:=_]>_) !!! _ ] =>
       rewrite lookup_total_insert || rewrite ->lookup_total_insert_ne by tac
   | H : context[ (<[_:=_]>_) !!! _ ] |- _ =>
       rewrite lookup_total_insert in H || rewrite ->lookup_total_insert_ne in H by tac
   end.
 Tactic Notation "simplify_map_eq'" "/=" "by" tactic3(tac) :=
  repeat (progress csimpl in * || (progress simpl_map_total by tac) || (progress simpl_map_ext tac) || simplify_map_eq by tac ).
 Tactic Notation "simplify_map_eq'" :=
  repeat (progress (simpl_map_total by eauto with simpl_map map_disjoint) || (progress simpl_map_ext ltac:(eauto with simpl_map map_disjoint)) || simplify_map_eq by eauto with simpl_map map_disjoint ).
Tactic Notation "simplify_map_eq'" "/=" :=
  simplify_map_eq'/= by eauto with simpl_map map_disjoint.

Ltac sort_map_insert :=
  repeat match goal with
         | |- context [<[ ?i := ?x ]> (<[ ?j := ?y ]> ?m)] =>
             is_closed_term i;
             is_closed_term j;
             assert_succeeds (assert (encode j <? encode i)%positive; [vm_compute; exact I|]);
             rewrite (insert_commute m i j x y); [|done]
         end.

Ltac simpl_map_decide :=
  let go' := first [done | by apply elem_of_dom | by apply not_elem_of_dom] in
  let go := solve [ first [go' | by match goal with | H : _ ## _ |- _ => move => ?; apply: H; go' end] ] in
  repeat (match goal with
  | |- context [bool_decide (?P)] => rewrite (bool_decide_true P); [|go]
  | |- context [bool_decide (?P)] => rewrite (bool_decide_false P); [|go]
  end; simpl).

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
End theorems.

Section map.
  Context `{FinMap K M}.
  Context {A : Type} .
  Implicit Types m : M A.
Lemma lookup_union_l' (m1 m2 : M A) i :
  m2 !! i = None → (m1 ∪ m2) !! i = m1 !! i.
Proof using Type*. intros Hi. rewrite lookup_union Hi. by destruct (m1 !! i). Qed.
End map.

Section theorems.
Context `{FinMap K M}.
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

Section map_filter_lookup.
  Local Set Default Proof Using "Type*".
  Context `{FinMap K M}.
  Context {A} (P : K * A → Prop) `{!∀ x, Decision (P x)}.
  Implicit Types m : M A.
  Lemma map_filter_lookup_true m i :
    (∀ x, m !! i = Some x → P (i, x)) → filter P m !! i = m !! i.
  Proof. move => ?. rewrite map_filter_lookup. destruct (m !! i) => //=. case_option_guard; naive_solver. Qed.
End map_filter_lookup.

Section dom.
Context `{FinMapDom K M D}.
Lemma map_difference_eq_dom {A} (m m1 m2 : M A) :
  dom D m1 ≡ dom D m2 →
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
  dom D m1 = dom D m2 →
  m ∖ m1 = m ∖ m2.
Proof. unfold_leibniz. apply: map_difference_eq_dom. Qed.
End dom.

Section semi_set.
  Context `{SemiSet A C}.
  Implicit Types x y : A.
  Implicit Types X Y : C.
  Implicit Types Xs Ys : list C.
Lemma elem_of_subseteq_1 X Y x: X ⊆ Y → x ∈ X → x ∈ Y.
Proof. set_solver. Qed.
End semi_set.

Section theorems.
Context `{FinMap K M}.

Lemma lookup_union_None_1 {A} (m1 m2 : M A) i :
  (m1 ∪ m2) !! i = None → m1 !! i = None ∧ m2 !! i = None.
Proof. apply lookup_union_None. Qed.
Lemma lookup_union_None_2 {A} (m1 m2 : M A) i :
  m1 !! i = None → m2 !! i = None → (m1 ∪ m2) !! i = None.
Proof. move => ??. by apply lookup_union_None. Qed.
End theorems.

Lemma omap_app {A B} l1 l2 (f : A → option B) :
  omap f (l1 ++ l2) = omap f l1 ++ omap f l2.
Proof. elim: l1 => //; csimpl => ?? ->. by case_match. Qed.

Lemma omap_option_list {A B} (f : A → option B) o :
  omap f (option_list o) = option_list (o ≫= f).
Proof. by destruct o. Qed.

(** fixpoints based on iris/bi/lib/fixpoint.v *)
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

Ltac invert_all_tac f :=
  let do_invert H := inversion H; clear H in
  repeat lazymatch goal with
         | H : f |- _ => do_invert H
         | H : f _ |- _ => do_invert H
         | H : f _ _|- _ => do_invert H
         | H : f _ _ _|- _ => do_invert H
         | H : f _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _ _ _ _ _|- _ => do_invert H
         end.

Tactic Notation "invert_all" constr(f) := invert_all_tac f; simplify_eq/=; specialize_hyps.
Tactic Notation "invert_all'" constr(f) := invert_all_tac f.

Tactic Notation "case_match" "as" ident(Hd) :=
  match goal with
  | H : context [ match ?x with _ => _ end ] |- _ => destruct x eqn:Hd
  | |- context [ match ?x with _ => _ end ] => destruct x eqn:Hd
  end.


Definition map_list_included {K A} `{Countable K} (ns : list K) (rs : gmap K A) :=
  list_to_set ns ⊆ dom (gset _) rs.

Definition map_scramble {K A} `{Countable K} (ns : list K) (rs rs' : gmap K A) :=
  ∀ i, i ∉ ns → rs !! i = rs' !! i.

Definition map_preserved {K A} `{Countable K} (ns : list K) (rs rs' : gmap K A) :=
  ∀ i, i ∈ ns → rs !! i = rs' !! i.

Lemma map_list_included_is_Some {K A} `{Countable K} ns (m : gmap K A) i :
  map_list_included ns m →
  i ∈ ns →
  is_Some (m !! i).
Proof. move => Hin ?. apply elem_of_dom. apply Hin. set_solver. Qed.

Lemma map_list_included_insert {K A} `{Countable K} ns (m : gmap K A) i x:
  map_list_included ns m →
  map_list_included ns (<[i := x]>m).
Proof. unfold map_list_included. set_solver. Qed.

Global Instance map_scramble_preorder {K A} `{Countable K} ns : PreOrder (map_scramble (K:=K) (A:=A) ns).
Proof.
  constructor.
  - move => ???. done.
  - move => ??? Hm1 Hm2 ??. etrans; [by apply Hm1|]. by apply Hm2.
Qed.

Global Instance map_preserved_preorder {K A} `{Countable K} ns : PreOrder (map_preserved (K:=K) (A:=A) ns).
Proof.
  constructor.
  - move => ???. done.
  - move => ??? Hm1 Hm2 ??. etrans; [by apply Hm1|]. by apply Hm2.
Qed.

Lemma map_scramble_sym {K A} `{Countable K} ns (m m' : gmap K A) :
  map_scramble ns m m' ↔ map_scramble ns m' m.
Proof. unfold map_scramble. naive_solver. Qed.

Lemma map_scramble_insert_r_in {K A} `{Countable K} ns (m m' : gmap K A) i x:
  i ∈ ns →
  map_scramble ns m (<[i:=x]>m') ↔ map_scramble ns m m'.
Proof.
  move => Hin. unfold map_scramble. apply forall_proper => ?.
  apply forall_proper => ?. rewrite lookup_insert_ne //. naive_solver.
Qed.

Lemma map_scramble_insert_r_not_in {K A} `{Countable K} ns (m m' : gmap K A) i x:
  i ∉ ns →
  map_scramble ns m (<[i:=x]>m') ↔ m !! i = Some x ∧ map_scramble (i :: ns) m m'.
Proof.
  unfold map_scramble. move => ?. split.
  - move => Hm. split; [rewrite Hm //; by simplify_map_eq|]. move => ??. rewrite Hm; [|set_solver].
    rewrite lookup_insert_ne; [|set_solver]. done.
  - move => [? Hm] i' ?. destruct (decide (i = i')); simplify_map_eq => //. apply Hm. set_solver.
Qed.

Lemma map_scramble_insert_l_in {K A} `{Countable K} ns (m m' : gmap K A) i x:
  i ∈ ns →
  map_scramble ns (<[i:=x]>m) m' ↔ map_scramble ns m m'.
Proof. move => ?. rewrite map_scramble_sym map_scramble_insert_r_in // map_scramble_sym. done. Qed.

Lemma map_scramble_insert_l_not_in {K A} `{Countable K} ns (m m' : gmap K A) i x:
  i ∉ ns →
  map_scramble ns (<[i:=x]>m) m' ↔ m' !! i = Some x ∧ map_scramble (i :: ns) m m'.
Proof. move => ?. rewrite map_scramble_sym map_scramble_insert_r_not_in // map_scramble_sym //. Qed.

Lemma map_scramble_eq {K A} `{Countable K} ns (m : gmap K A):
  map_scramble ns m m.
Proof. unfold map_scramble. naive_solver. Qed.

Lemma map_scramble_eq' {K A} `{Countable K} ns (m : gmap K A):
  map_scramble ns m m ↔ True.
Proof. unfold map_scramble. naive_solver. Qed.


Lemma map_preserved_sym {K A} `{Countable K} ns (m m' : gmap K A) :
  map_preserved ns m m' ↔ map_preserved ns m' m.
Proof. unfold map_preserved. naive_solver. Qed.

Lemma map_preserved_insert_r_not_in {K A} `{Countable K} ns (m m' : gmap K A) i x:
  i ∉ ns →
  map_preserved ns m (<[i:=x]>m') ↔ map_preserved ns m m'.
Proof.
  move => Hin. unfold map_preserved. apply forall_proper => ?.
  apply forall_proper => ?. rewrite lookup_insert_ne //. naive_solver.
Qed.

Lemma map_preserved_insert_r_in {K A} `{Countable K} ns (m m' : gmap K A) i x:
  i ∈ ns →
  map_preserved ns m (<[i:=x]>m') ↔ m !! i = Some x ∧ map_preserved (filter (i≠.) ns) m m'.
Proof.
  unfold map_preserved. move => ?. split.
  - move => Hm. split; [rewrite Hm //; by simplify_map_eq|]. move => ? /elem_of_list_filter[??].
    by rewrite Hm //  lookup_insert_ne.
  - move => [? Hm] i' ?. destruct (decide (i = i')); simplify_map_eq => //. apply Hm. by apply elem_of_list_filter.
Qed.

Lemma map_preserved_insert_l_not_in {K A} `{Countable K} ns (m m' : gmap K A) i x:
  i ∉ ns →
  map_preserved ns (<[i:=x]>m) m' ↔ map_preserved ns m m'.
Proof. move => ?. rewrite map_preserved_sym map_preserved_insert_r_not_in // map_preserved_sym. done. Qed.

Lemma map_preserved_insert_l_in {K A} `{Countable K} ns (m m' : gmap K A) i x:
  i ∈ ns →
  map_preserved ns (<[i:=x]>m) m' ↔ m' !! i = Some x ∧ map_preserved (filter (i≠.) ns) m m'.
Proof. move => ?. rewrite map_preserved_sym map_preserved_insert_r_in // map_preserved_sym. done. Qed.

Lemma map_preserved_eq {K A} `{Countable K} ns (m : gmap K A):
  map_preserved ns m m.
Proof. unfold map_preserved. naive_solver. Qed.

Lemma map_preserved_eq' {K A} `{Countable K} ns (m : gmap K A):
  map_preserved ns m m ↔ True.
Proof. unfold map_preserved. naive_solver. Qed.

Global Opaque map_list_included map_scramble map_preserved.

Section semi_set.
  Context `{SemiSet A C}.
  Implicit Types x y : A.
  Implicit Types X Y : C.
  Implicit Types Xs Ys : list C.
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
