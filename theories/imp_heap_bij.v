Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.filter.
Require Import refframe.product.
Require Import refframe.seq_product.
Require Import refframe.link.
Require Import refframe.prepost.
Require Import refframe.proof_techniques.
Require Import refframe.imp.


Module pure_bij.
Implicit Types (p : prov).

(** * imp_heap_bij *)
Inductive heap_bij_elem :=
| HBShared (p : prov) | HBOwned (p : player).
Global Instance heap_bij_elem_eq_dec : EqDecision heap_bij_elem.
Proof. solve_decision. Qed.
Global Instance heap_bij_elem_inhabited : Inhabited heap_bij_elem := populate (HBOwned Prog).

(* Naming scheme: pi for provenances in the implementation (right side
of hb_bij), ps for provanences in the spec (left side) *)

Record heap_bij := HeapBij {
  hb_bij : gmap prov heap_bij_elem;
  hb_players_i : gmap prov player;
  hb_disj ps pi:
   hb_bij !! ps = Some (HBShared pi) →
   hb_players_i !! pi = None;
  hb_iff pi ps ps' :
   hb_bij !! ps = Some (HBShared pi) →
   hb_bij !! ps' = Some (HBShared pi) →
   ps = ps'
}.
Add Printing Constructor heap_bij.

Ltac simplify_bij :=
  repeat (simplify_eq; match goal with
         | H1 : hb_bij ?bij !! ?ps1 = Some (HBShared ?pi),
             H2 : hb_bij ?bij !! ?ps2 = Some (HBShared ?pi) |- _ =>
             pose proof (hb_iff bij pi ps1 ps2 H1 H2); clear H2
         end); simplify_eq.

Lemma heap_bij_eq bij1 bij2 :
  bij1 = bij2 ↔ hb_bij bij1 = hb_bij bij2 ∧ hb_players_i bij1 = hb_players_i bij2.
Proof.
  split; [naive_solver|]. move => [??]. destruct bij1, bij2 => /=. simplify_eq/=. f_equal.
  (* TODO: get rid of this *)
  all: apply proof_irrelevance.
Qed.

Global Program Instance imp_heap_bij_empty : Empty heap_bij :=
  HeapBij ∅ ∅ _ _.
Solve Obligations with set_solver.

(** hb_shared_i *)
Definition hb_shared_i (bij : heap_bij) : gset prov :=
  list_to_set (omap (λ x, if x.2 is HBShared p then Some p else None) (map_to_list (hb_bij bij))).
Global Typeclasses Opaque hb_shared_i.

Lemma elem_of_hb_shared_i bij pi:
  pi ∈ hb_shared_i bij ↔ ∃ ps, hb_bij bij !! ps = Some (HBShared pi).
Proof.
  rewrite /hb_shared_i elem_of_list_to_set elem_of_list_omap.
  setoid_rewrite elem_of_map_to_list'.
  split.
  - move => [[??] /= [??]]. case_match; simplify_eq/=. naive_solver.
  - move => [??]. by eexists (_, _).
Qed.

(** hb_shared *)
Definition hb_shared (bij : heap_bij) : gmap prov prov :=
  (omap (λ v, if v is HBShared p then Some p else None) (hb_bij bij)).

Lemma hb_shared_lookup bij ps :
  hb_shared bij !! ps = hb_bij bij !! ps ≫= λ v, if v is HBShared p then Some p else None.
Proof. apply lookup_omap. Qed.

Lemma hb_shared_lookup_Some bij ps pi :
  hb_shared bij !! ps = Some pi ↔ hb_bij bij !! ps = Some (HBShared pi).
Proof. rewrite hb_shared_lookup. destruct (hb_bij bij !! ps) => //=. case_match; naive_solver. Qed.

Lemma hb_shared_lookup_None bij ps :
  hb_shared bij !! ps = None ↔ ∀ pi, hb_bij bij !! ps = Some (HBShared pi) → False.
Proof. rewrite hb_shared_lookup. destruct (hb_bij bij !! ps) => //=. case_match; naive_solver. Qed.

(** hb_shared_s *)
Definition hb_shared_s (bij : heap_bij) : gset prov :=
  (locked (dom _) (hb_shared bij)).

Lemma elem_of_hb_shared_s bij ps :
  ps ∈ hb_shared_s bij ↔ ∃ pi, hb_bij bij !! ps = Some (HBShared pi).
Proof. rewrite /hb_shared_s; unlock. rewrite elem_of_dom /is_Some. f_equiv => ?. apply hb_shared_lookup_Some. Qed.

(** hb_player_s *)
Definition hb_player_s (pl : player) (bij : heap_bij) : gset prov :=
  (locked (dom _) (filter (λ '(k, e), e = HBOwned pl) (hb_bij bij))).

Lemma elem_of_hb_player_s pl bij ps :
  ps ∈ hb_player_s pl bij ↔ hb_bij bij !! ps = Some (HBOwned pl).
Proof.
  unfold hb_player_s. unlock. rewrite elem_of_dom /is_Some. setoid_rewrite map_filter_lookup_Some.
  naive_solver.
Qed.

Lemma not_elem_of_hb_player_s pl bij ps :
  ps ∉ hb_player_s pl bij ↔ hb_bij bij !! ps ≠ Some (HBOwned pl).
Proof. by rewrite elem_of_hb_player_s. Qed.

Lemma hb_player_s_empty pl bij :
  hb_player_s pl bij = ∅ ↔ (∀ ps, hb_bij bij !! ps ≠ Some (HBOwned pl)).
Proof. rewrite set_eq. setoid_rewrite elem_of_hb_player_s. set_solver. Qed.

(** hb_player_i *)
Definition hb_player_i (pl : player) (bij : heap_bij) : gset prov :=
  (locked (dom _) (filter (λ '(k, e), e = pl) (hb_players_i bij))).

Lemma elem_of_hb_player_i pl bij pi :
  pi ∈ hb_player_i pl bij ↔ hb_players_i bij !! pi = Some pl.
Proof.
  unfold hb_player_i. unlock. rewrite elem_of_dom /is_Some. setoid_rewrite map_filter_lookup_Some.
  naive_solver.
Qed.

Lemma not_elem_of_hb_player_i pl bij pi :
  pi ∉ hb_player_i pl bij ↔ hb_players_i bij !! pi ≠ Some pl.
Proof. by rewrite elem_of_hb_player_i. Qed.

Lemma hb_player_i_empty pl bij :
  hb_player_i pl bij = ∅ ↔ (∀ ps, hb_players_i bij !! ps ≠ Some pl).
Proof. rewrite set_eq. setoid_rewrite elem_of_hb_player_i. set_solver. Qed.

(** hb_provs_i *)
(* hb_provs_s is directly written as [dom _ (hb_bij bij)] *)

Definition hb_provs_i (bij : heap_bij) : gset prov :=
  dom _ (hb_players_i bij) ∪ hb_shared_i bij.

Lemma elem_of_hb_provs_i bij pi :
  pi ∈ hb_provs_i bij ↔ (∃ pl, hb_players_i bij !! pi = Some pl) ∨ ∃ ps, hb_bij bij !! ps = Some (HBShared pi).
Proof. unfold hb_provs_i. rewrite elem_of_union elem_of_dom elem_of_hb_shared_i. naive_solver. Qed.

(** general hb_bij *)
Lemma heap_bij_eq_parts bij1 bij2 :
  bij1 = bij2 ↔
    hb_shared bij1 = hb_shared bij2 ∧
    ∀ pl, hb_player_s pl bij1 = hb_player_s pl bij2 ∧ hb_player_i pl bij1 = hb_player_i pl bij2.
Proof.
  split; [naive_solver|]. move => [Hshared Hp]. apply heap_bij_eq.
  split.
  - apply map_eq => ?. apply option_eq => -[?|?]; rewrite -?hb_shared_lookup_Some -?elem_of_hb_player_s.
    + naive_solver congruence.
    + set_solver.
  - apply map_eq => ?. apply option_eq => ?. rewrite -?elem_of_hb_player_i. set_solver.
Qed.

Global Instance heap_bij_subseteq : SubsetEq heap_bij :=
  λ bij bij', ∀ ps pi, hb_bij bij !! ps = Some (HBShared pi) → hb_bij bij' !! ps = Some (HBShared pi).

Global Instance heap_bij_preorder : PreOrder (⊆@{heap_bij}).
Proof. unfold subseteq,heap_bij_subseteq. constructor; naive_solver. Qed.

Definition heap_bij_extend (pl : player) (bij bij' : heap_bij) :=
  bij ⊆ bij'
  ∧ hb_player_s (opponent pl) bij = hb_player_s (opponent pl) bij'
  ∧ hb_player_i (opponent pl) bij = hb_player_i (opponent pl) bij'.

Global Instance heap_bij_extend_preorder pl : PreOrder (heap_bij_extend pl).
Proof.
  unfold heap_bij_extend. constructor.
  - move => *. done.
  - move => *. destruct_all?. split; [by etrans|split; by etrans].
Qed.
Global Typeclasses Opaque heap_bij_extend.

Local Ltac bij_solver := unfold heap_bij_extend, subseteq, heap_bij_subseteq in *; set_unfold; naive_solver.

(** heap_bij constructors *)
Program Definition heap_bij_add_shared (pi ps : prov) (bij : heap_bij)
        (H : pi ∉ hb_provs_i bij) :=
  HeapBij (<[ps := HBShared pi]> (hb_bij bij)) (hb_players_i bij) _ _.
Next Obligation.
  move => ??? Hnotin ??. move: Hnotin. rewrite elem_of_hb_provs_i => ?.
  rewrite !lookup_insert_Some => ?. destruct_all?; simplify_eq/= => //; try naive_solver.
  - apply eq_None_ne_Some => ??. naive_solver.
  - by apply: hb_disj.
Qed.
Next Obligation.
  move => ??? Hnotin ???. move: Hnotin. rewrite elem_of_hb_provs_i => ?.
  rewrite !lookup_insert_Some => ??. destruct_all?; simplify_eq/= => //; try naive_solver.
  by apply: hb_iff.
Qed.

Program Definition heap_bij_add_player (ps : prov) (pl : player) (bij : heap_bij) :=
  HeapBij (<[ps := HBOwned pl]> (hb_bij bij)) (hb_players_i bij) _ _.
Next Obligation.
  move => ?????.
  rewrite !lookup_insert_Some => ?. destruct_all?; simplify_eq/= => //. by apply: hb_disj.
Qed.
Next Obligation.
  move => ??????.
  rewrite !lookup_insert_Some => ??. destruct_all?; simplify_eq/= => //. by apply: hb_iff.
Qed.

Program Definition heap_bij_delete (ps : prov) (bij : heap_bij) :=
  HeapBij (delete ps (hb_bij bij)) (hb_players_i bij) _ _.
Next Obligation.
  move => ????.
  rewrite !lookup_delete_Some => ?. destruct_all?; simplify_eq/= => //. by apply: hb_disj.
Qed.
Next Obligation.
  move => ?????.
  rewrite !lookup_delete_Some => ??. destruct_all?; simplify_eq/= => //. by apply: hb_iff.
Qed.

(* Definition heap_bij_map_player_bij (f : prov → player → player) (bij : heap_bij) : gmap prov heap_bij_elem := *)
(*   map_imap (λ ps e, Some $ if e is HBOwned p then HBOwned (f ps p) else e) (hb_bij bij). *)

(* Lemma heap_bij_map_player_bij_lookup f bij p2 : *)
(*   heap_bij_map_player_bij f bij !! p2 = *)
(*     (λ x, if x is HBOwned p then HBOwned (f p2 p) else x) <$> hb_bij bij !! p2. *)
(* Proof. rewrite map_lookup_imap. by destruct (hb_bij bij !! p2). Qed. *)

(* Lemma heap_bij_map_player_bij_lookup_shared f bij p2 p1: *)
(*   heap_bij_map_player_bij f bij !! p2 = Some (HBShared p1) ↔ hb_bij bij !! p2 = Some (HBShared p1). *)
(* Proof. *)
(*   rewrite heap_bij_map_player_bij_lookup. rewrite fmap_Some. split; [|naive_solver]. *)
(*   move => [[?|?][??]]//. naive_solver. *)
(* Qed. *)

(* Program Definition heap_bij_map_player (f : prov → player → player) (bij : heap_bij) := *)
(*   HeapBij (heap_bij_map_player_bij f bij) _. *)
(* Next Obligation. *)
(*   move => ?????? /heap_bij_map_player_bij_lookup_shared?/heap_bij_map_player_bij_lookup_shared?. apply: hb_iff; naive_solver. *)
(* Qed. *)

(* Lemma heap_bij_map_player_subseteq_l f bij1 bij2: *)
(*   heap_bij_map_player f bij1 ⊆ bij2 ↔ bij1 ⊆ bij2. *)
(* Proof. unfold subseteq, heap_bij_subseteq. by setoid_rewrite heap_bij_map_player_bij_lookup_shared. Qed. *)

(* Lemma heap_bij_map_player_subseteq_r f bij1 bij2: *)
(*   bij1 ⊆ heap_bij_map_player f bij2 ↔ bij1 ⊆ bij2. *)
(* Proof. unfold subseteq, heap_bij_subseteq. by setoid_rewrite heap_bij_map_player_bij_lookup_shared. Qed. *)

(* (* Lemma elem_of_hb_player_s_map p x f bij : *) *)
(* (*   x ∈ hb_player_s p (heap_bij_map_player f bij) ↔ f  *) *)

(* only provenances which are shared in both bijections become shared
in the merged bijection, otherwise they become private. *)
Program Definition heap_bij_merge (bija bijb : heap_bij) :=
  HeapBij ((λ x, if x is HBShared pi then default (HBOwned Prog) (hb_bij bija !! pi) else x) <$> hb_bij bijb)
          (hb_players_i bija ∪ gset_to_gmap Prog (filter (λ pii,
              map_Forall (λ pi pii', ¬ (pii' = pii ∧ pi ∈ hb_shared_i bijb))
                         (hb_shared bija)) (hb_shared_i bija)))
          _ _.
Next Obligation.
  move => ????. rewrite !lookup_fmap=> /fmap_Some[?[??]].
  unfold default in *; repeat case_match; simplify_eq/=.
  apply lookup_union_None. split; [by apply: hb_disj|].
  rewrite lookup_gset_to_gmap_None. rewrite elem_of_filter.
  move => [Hall _]. apply: Hall; [by rewrite hb_shared_lookup_Some|]. rewrite elem_of_hb_shared_i.
  naive_solver.
Qed.
Next Obligation.
  move => ?????. rewrite !lookup_fmap => /fmap_Some[?[??]] /fmap_Some[?[??]].
  unfold default in *; repeat case_match; simplify_bij; simplify_eq/=; by simplify_bij.
Qed.

Lemma heap_bij_merge_lookup bijb bija ps :
  hb_bij (heap_bij_merge bija bijb) !! ps =
  (λ x, if x is HBShared pi then default (HBOwned Prog) (hb_bij bija !! pi) else x) <$> hb_bij bijb !! ps.
Proof. by rewrite lookup_fmap. Qed.

Lemma heap_bij_merge_player_i pii bijb bija pl:
  pii ∈ hb_player_i pl (heap_bij_merge bija bijb) ↔
    hb_players_i bija !! pii = Some pl ∨
    ∃ pi, pl = Prog ∧ hb_bij bija !! pi = Some (HBShared pii) ∧ pi ∉ hb_shared_i bijb.
Proof.
  rewrite elem_of_hb_player_i /= lookup_union_Some_raw lookup_gset_to_gmap_Some elem_of_filter.
  split => ?; destruct_all?; simplify_eq; try naive_solver.
  - right. revert select (_ ∈ _). rewrite elem_of_hb_shared_i => -[??]. eexists _.
    split; [done|]. split; [done|].
    move => ?. revert select (map_Forall _ _). apply; [|done]. by rewrite hb_shared_lookup_Some.
  - right. split_and!. { by apply: hb_disj. } { done. }
    + move => ??. rewrite hb_shared_lookup_Some => ? [??]. simplify_bij. naive_solver.
    + rewrite elem_of_hb_shared_i. naive_solver.
Qed.
Opaque heap_bij_merge.

Lemma heap_bij_merge_player_s ps bijb bija pl:
  ps ∈ hb_player_s pl (heap_bij_merge bija bijb) ↔
    hb_bij bijb !! ps = Some (HBOwned pl) ∨ ∃ pi, hb_bij bijb !! ps = Some (HBShared pi) ∧
       default (HBOwned Prog) (hb_bij bija !! pi) = HBOwned pl.
Proof.
  rewrite elem_of_hb_player_s heap_bij_merge_lookup fmap_Some.
  destruct (hb_bij bijb !! ps) as [[]|]; naive_solver.
Qed.

Lemma heap_bij_merge_shared bijb bija ps pii :
  hb_bij (heap_bij_merge bija bijb) !! ps = Some (HBShared pii) ↔
     ∃ pi, hb_bij bijb !! ps = Some (HBShared pi) ∧ hb_bij bija !! pi = Some (HBShared pii).
Proof.
  simpl. rewrite heap_bij_merge_lookup fmap_Some.  split.
  - move => [[p'|?][??]] //. destruct (hb_bij bija !! p') eqn:?; naive_solver.
  - move => [?[Hl1 Hl2]]. eexists _. split; [done|] => /=. by rewrite Hl2.
Qed.

Lemma heap_bij_merge_shared_i bija bijb pii:
  pii ∈ hb_shared_i (heap_bij_merge bija bijb) ↔
    ∃ pi, hb_bij bija !! pi = Some (HBShared pii) ∧ pi ∈ hb_shared_i bijb.
Proof.
  rewrite !elem_of_hb_shared_i.
  setoid_rewrite heap_bij_merge_shared.
  setoid_rewrite elem_of_hb_shared_i.
  naive_solver.
Qed.

Lemma heap_bij_merge_dom bijb bija :
  dom (gset _) (hb_bij (heap_bij_merge bija bijb)) = dom _ (hb_bij bijb).
Proof. apply set_eq => ?. by rewrite !elem_of_dom heap_bij_merge_lookup fmap_is_Some. Qed.

Lemma heap_bij_merge_provs_i bija bijb pii:
  pii ∈ hb_provs_i (heap_bij_merge bija bijb) ↔ pii ∈ hb_provs_i bija.
Proof.
  rewrite !elem_of_hb_provs_i.
  setoid_rewrite heap_bij_merge_shared.
  setoid_rewrite <-elem_of_hb_player_i at 1.
  setoid_rewrite heap_bij_merge_player_i.
  split; [naive_solver|]. move => [?|[pi Hpi]]. 1: naive_solver.
  destruct (decide (pi ∈ hb_shared_i bijb)) as [Hps|Hps]; [|naive_solver].
  rewrite elem_of_hb_shared_i in Hps. naive_solver.
Qed.

Lemma heap_bij_merge_prog_eq_s bija bijb bij' ps:
  hb_player_s Prog (heap_bij_merge bija bijb) = hb_player_s Prog bij' →
  hb_bij bij' !! ps = Some (HBOwned Prog) ↔
  hb_bij bijb !! ps = Some (HBOwned Prog) ∨ (∃ pi,
    hb_bij bijb !! ps = Some (HBShared pi) ∧ (∀ y, hb_bij bija !! pi = Some y → y = HBOwned Prog))
  .
Proof.
  move => /set_eq/(_ ps). rewrite heap_bij_merge_player_s elem_of_hb_player_s.
  setoid_rewrite default_eq_Some'. naive_solver.
Qed.

Lemma heap_bij_merge_prog_eq_i bija bijb bij' pii:
  hb_player_i Prog (heap_bij_merge bija bijb) = hb_player_i Prog bij' →
  hb_players_i bij' !! pii = Some Prog ↔
  hb_players_i bija !! pii = Some Prog ∨ (∃ pi, hb_bij bija !! pi = Some (HBShared pii) ∧ pi ∉ hb_shared_i bijb)
  .
Proof. move => /set_eq/(_ pii). rewrite heap_bij_merge_player_i elem_of_hb_player_i. naive_solver. Qed.

(* TODO: clean up the following lemmas *)
Lemma heap_bij_merge_extend_env bija bijb bij' ps x:
  heap_bij_extend Env (heap_bij_merge bija bijb) bij' →
  hb_bij bij' !! ps = Some (HBOwned Env) →
  hb_player_s Env bija = ∅ →
  hb_bij bijb !! ps = Some x →
  x = HBOwned Env.
Proof.
  move => [/=Hsub [Hprog ?]] Hbij' /hb_player_s_empty Hbija Hbijb.
  destruct x as [pi|[]] => //=. 2: { move: Hprog => /heap_bij_merge_prog_eq_s. naive_solver. }
  move: Hprog => /heap_bij_merge_prog_eq_s?.
  destruct (hb_bij bija !! pi) as [[pii|[]]|] eqn:?; [|naive_solver..].
  have := Hsub ps pii. rewrite heap_bij_merge_shared. naive_solver.
Qed.

Lemma heap_bij_merge_extend_a ps pi pii bija bijb bij' :
  heap_bij_extend Env (heap_bij_merge bija bijb) bij' →
  hb_bij bij' !! ps = Some (HBShared pii) →
  hb_bij bijb !! ps = Some (HBShared pi) →
  hb_player_s Env bija = ∅ →
  hb_bij bija !! pi = Some (HBShared pii).
Proof.
  move => [/=Hsub [Hprog ?]] Hbij' Hbijb /hb_player_s_empty Hempty.
  move: Hprog => /heap_bij_merge_prog_eq_s?.
  destruct (hb_bij bija !! pi) as [[pii'|[]]|] eqn:Hbij1; simplify_eq; [|naive_solver..].
  have := Hsub ps pii'. rewrite heap_bij_merge_shared. naive_solver.
Qed.

Lemma heap_bij_merge_extend_env_i bija bijb bij' pi pii:
  heap_bij_extend Env (heap_bij_merge bija bijb) bij' →
  hb_bij bija !! pi = Some (HBShared pii) →
  hb_players_i bij' !! pii ≠ Some Env.
Proof.
  move => [/=Hsub [_ /heap_bij_merge_prog_eq_i Hprog]] Hbija Hbij'.
  destruct (decide (pi ∈ hb_shared_i bijb)) as [Hin|Hin]; [|naive_solver].
  rewrite elem_of_hb_shared_i in Hin. move: Hin => [ps ?].
  move: (Hsub ps pii). rewrite heap_bij_merge_shared => /(_ _)/hb_disj.
  naive_solver.
Qed.

Lemma heap_bij_merge_extend_prog_i bija bijb bij' pi pii:
  heap_bij_extend Env (heap_bij_merge bija bijb) bij' →
  hb_players_i bija !! pii = Some Prog →
  hb_bij bij' !! pi ≠ Some (HBShared pii).
Proof. move => [/=Hsub [_ /heap_bij_merge_prog_eq_i Hprog]] Hbija /hb_disj Hbij'. naive_solver. Qed.

(** ** val_in_bij *)
Definition val_in_bij (bij : heap_bij) (v1 v2 : val) : Prop :=
  match v1, v2 with
  | ValNum n1, ValNum n2 => n1 = n2
  | ValBool b1, ValBool b2 => b1 = b2
  | ValLoc l1, ValLoc l2 => hb_bij bij !! l2.1 = Some (HBShared l1.1) /\ l1.2 = l2.2
  | _, _ => False
  end.

Lemma val_in_bij_mono bij bij' v1 v2:
  val_in_bij bij v1 v2 →
  bij ⊆ bij' →
  val_in_bij bij' v1 v2.
Proof. destruct v1, v2 => //=. bij_solver. Qed.

Lemma val_in_bij_merge bija bijb vii vs :
  val_in_bij (heap_bij_merge bija bijb) vii vs ↔ ∃ vi,
      val_in_bij bija vii vi ∧ val_in_bij bijb vi vs.
Proof.
   split.
   - destruct vii, vs => //=. { by eexists (ValNum _). } { by eexists (ValBool _). }
     move => [/heap_bij_merge_shared[?[??]] ?].
     eexists (ValLoc (_, _)) => /=. naive_solver.
   - move => [vi [??]]. destruct vii, vi, vs => //; simplify_eq/= => //.
     split; [|naive_solver congruence]. apply heap_bij_merge_shared. naive_solver.
Qed.

(** ** expr_in_bij *)
Fixpoint expr_in_bij (bij : heap_bij) (e1 e2 : expr) {struct e1} : Prop :=
  match e1, e2 with
  | Var v, Var v' => v = v'
  | Val v, Val v' => val_in_bij bij v v'
  | BinOp e1 o e2, BinOp e1' o' e2' => o = o' ∧ expr_in_bij bij e1 e1' ∧ expr_in_bij bij e2 e2'
  | Load e, Load e' => expr_in_bij bij e e'
  | Store e1 e2, Store e1' e2' => expr_in_bij bij e1 e1' ∧ expr_in_bij bij e2 e2'
  | Alloc e, Alloc e' => expr_in_bij bij e e'
  | Free e, Free e' => expr_in_bij bij e e'
  | If e e1 e2, If e' e1' e2' => expr_in_bij bij e e' ∧ expr_in_bij bij e1 e1' ∧ expr_in_bij bij e2 e2'
  | LetE v e1 e2, LetE v' e1' e2' => v = v' ∧ expr_in_bij bij e1 e1' ∧ expr_in_bij bij e2 e2'
  | Call f args, Call f' args' => f = f' ∧ length args = length args' ∧
                                   Forall id (zip_with (expr_in_bij bij) args args')
  | UbE, UbE => True
  | ReturnExt b e, ReturnExt b' e' => b = b' ∧ expr_in_bij bij e e'
  | Waiting b, Waiting b' => b = b'
  | _, _ => False
  end.

Lemma Forall2_bij_val_inv_l bij vl el :
  Forall2 (expr_in_bij bij) (Val <$> vl) el →
  ∃ vl', el = Val <$> vl' ∧ Forall2 (val_in_bij bij) vl vl'.
Proof.
  elim: vl el; csimpl. { move => ? /Forall2_nil_inv_l->. by eexists []. }
  move => ?? IH ? /(Forall2_cons_inv_l _ _)[v' [?[?[/IH[?[??]]?]]]]; subst.
  destruct v' => //. eexists (_::_). split; [done|]. by econs.
Qed.

Lemma Forall2_bij_val_inv_r bij vl el :
  Forall2 (expr_in_bij bij) el (Val <$> vl) →
  ∃ vl', el = Val <$> vl' ∧ Forall2 (val_in_bij bij) vl' vl.
Proof.
  elim: vl el; csimpl. { move => ? /Forall2_nil_inv_r->. by eexists []. }
  move => ?? IH ? /(Forall2_cons_inv_r _ _ _ _) [v' [?[?[/IH[?[??]] ?]]]]; subst.
  destruct v' => //. eexists (_::_). split; [done|]. by econs.
Qed.

Lemma expr_in_bij_mono bij bij' e1 e2:
  expr_in_bij bij e1 e2 →
  bij ⊆ bij' →
  expr_in_bij bij' e1 e2.
Proof.
  elim: e1 e2 => //=*; repeat case_match => //; try naive_solver (eauto using val_in_bij_mono).
  destruct_all?; simplify_eq. split!.
  revert select (Forall id _). generalize dependent args.
  revert select (Forall _ _). elim. { by case. }
  move => ????? []//=??? *; decompose_Forall_hyps. econs; naive_solver.
Qed.

Lemma expr_in_bij_subst bij x v e v' e':
  expr_in_bij bij e e' →
  val_in_bij bij v v' →
  expr_in_bij bij (subst x v e) (subst x v' e').
Proof.
  elim: e e' => //= *; repeat (case_match => //); simplify_eq/=; repeat case_bool_decide => //; try naive_solver.
  destruct_all?. rewrite !fmap_length. split!.
  revert select (Forall _ _). generalize dependent args.
  revert select (Forall _ _). elim. { by case. }
  move => ????? []//=??? /(Forall_cons_1 _ _)[??]. econs; naive_solver.
Qed.

Lemma expr_in_bij_subst_l bij xs vs e vs' e':
  expr_in_bij bij e e' →
  Forall2 (val_in_bij bij) vs vs' →
  length xs = length vs →
  expr_in_bij bij (subst_l xs vs e) (subst_l xs vs' e').
Proof.
  move => He Hall. elim: Hall xs e e' He. { by case. }
  move => ?????? IH []//=??????. apply: IH; [|lia]. by apply expr_in_bij_subst.
Qed.

Lemma expr_in_bij_static bij e:
  static_expr false e →
  expr_in_bij bij e e.
Proof.
  elim: e => //=; try naive_solver. { by case. }
  move => ?? IH Hb. split!.
  elim: IH Hb => //=; econs; naive_solver.
Qed.

(** ** ectx_in_bij *)
Definition ectx_item_in_bij (bij : heap_bij) (Ki Ki' : expr_ectx) : Prop :=
  match Ki, Ki' with
  | BinOpLCtx op e2, BinOpLCtx op' e2' => op = op' ∧ expr_in_bij bij e2 e2'
  | BinOpRCtx v1 op, BinOpRCtx v1' op' => op = op' ∧ val_in_bij bij v1 v1'
  | LoadCtx, LoadCtx => True
  | StoreLCtx e2, StoreLCtx e2' => expr_in_bij bij e2 e2'
  | StoreRCtx v1, StoreRCtx v1' => val_in_bij bij v1 v1'
  | AllocCtx, AllocCtx => True
  | FreeCtx, FreeCtx => True
  | IfCtx e2 e3, IfCtx e2' e3' => expr_in_bij bij e2 e2' ∧ expr_in_bij bij e3 e3'
  | LetECtx v e2, LetECtx v' e2' => v = v' ∧ expr_in_bij bij e2 e2'
  | CallCtx f vl el, CallCtx f' vl' el' => f = f' ∧ Forall2 (val_in_bij bij) vl vl' ∧
                                            Forall2 (expr_in_bij bij) el el'
  | ReturnExtCtx b, ReturnExtCtx b' => b = b'
  | _, _ => False
  end.

Definition ectx_in_bij (bij : heap_bij) (K1 K2 : list expr_ectx) : Prop :=
  Forall2 (ectx_item_in_bij bij) K1 K2.

Lemma ectx_item_in_bij_mono bij bij' K1 K2:
  ectx_item_in_bij bij K1 K2 →
  bij ⊆ bij' →
  ectx_item_in_bij bij' K1 K2.
Proof.
  destruct K1, K2 => //=; try naive_solver (eauto using expr_in_bij_mono, val_in_bij_mono).
  move => [?[??]] ?. split_and!; [done|..].
  all: apply: Forall2_impl; [done|]; eauto using expr_in_bij_mono, val_in_bij_mono.
Qed.

Lemma ectx_in_bij_mono bij bij' K1 K2:
  ectx_in_bij bij K1 K2 →
  bij ⊆ bij' →
  ectx_in_bij bij' K1 K2.
Proof. move => ??. apply: Forall2_impl; [done|]. move => *; by apply: ectx_item_in_bij_mono.  Qed.

Lemma ectx_in_bij_cons bij Ki K Ki' K':
  ectx_in_bij bij (Ki :: K) (Ki' :: K') ↔ ectx_item_in_bij bij Ki Ki' ∧ ectx_in_bij bij K K'.
Proof. apply Forall2_cons. Qed.

Lemma ectx_in_bij_app bij Ki K Ki' K':
  ectx_in_bij bij Ki Ki' →
  ectx_in_bij bij K K' →
  ectx_in_bij bij (Ki ++ K) (Ki' ++ K').
Proof. apply Forall2_app. Qed.

Lemma ectx_in_bij_cons_inv_l bij Ki K K':
  ectx_in_bij bij (Ki::K) K' →
  ∃ Ki' K'', ectx_item_in_bij bij Ki Ki' ∧ ectx_in_bij bij K K'' ∧ K' = Ki' :: K''.
Proof. apply Forall2_cons_inv_l. Qed.

Lemma expr_in_bij_fill_item_2 bij K1 K2 e1 e2 :
  ectx_item_in_bij bij K1 K2 →
  expr_in_bij bij e1 e2 →
  expr_in_bij bij (expr_fill_item K1 e1) (expr_fill_item K2 e2).
Proof.
  move => ??.
  destruct K1, K2 => //; simplify_eq/=; destruct_all? => //.
  rewrite !app_length /=. split_and!; [done|solve_length|].
  apply Forall_zip_with_2. apply Forall2_app; [by apply Forall2_fmap|by econs].
Qed.

Lemma expr_in_bij_fill_2 bij K1 K2 e1 e2 :
  ectx_in_bij bij K1 K2 →
  expr_in_bij bij e1 e2 →
  expr_in_bij bij (expr_fill K1 e1) (expr_fill K2 e2).
Proof.
  elim: K1 K2 e1 e2. { move => ??? /Forall2_nil_inv_l->. done. }
  move => Ki1 K1 IH ??? /(Forall2_cons_inv_l _ _)[Ki2 [K2 [?[??]]]] ?; subst => /=.
  apply: IH; [done|]. by apply expr_in_bij_fill_item_2.
Qed.

Lemma expr_in_bij_fill_item_l bij Ki e1 e2 :
  expr_in_bij bij (expr_fill_item Ki e1) e2 →
  ∃ Ki' e', e2 = expr_fill_item Ki' e' ∧ ectx_item_in_bij bij Ki Ki' ∧ expr_in_bij bij e1 e'.
Proof.
  destruct Ki, e2 => //= *; destruct_all?; simplify_eq; try case_match => //; simplify_eq. 10: {
    revert select (Forall _ _) => /Forall_zip_with_1 Hall.
    move: (Hall ltac:(done)) => /Forall2_app_inv_l[?[?[Hv[/(Forall2_cons_inv_l _ _)[?[?[?[??]]]]?]]]]. simplify_eq.
    move: Hv => /Forall2_bij_val_inv_l[?[??]]. simplify_eq.
    by eexists (CallCtx _ _ _), _.
  }
  all: (unshelve eexists _); [econs; shelve| naive_solver].
Qed.

Lemma expr_in_bij_fill_l bij K e1 e2 :
  expr_in_bij bij (expr_fill K e1) e2 →
  ∃ K' e', e2 = expr_fill K' e' ∧ ectx_in_bij bij K K' ∧ expr_in_bij bij e1 e'.
Proof.
  elim: K e1 e2 => /=. { move => *. eexists [], _. split!. econs. }
  move => Ki K IH e1 e2 /IH[K'[?[?[?/expr_in_bij_fill_item_l?]]]].
  destruct_all?; simplify_eq. eexists (_ :: _), _ => /=. split_and!; [done| |done].
  by econs.
Qed.

Lemma eval_binop_bij o v1 v2 v1' v2' v bij:
  eval_binop o v1 v2 = Some v →
  val_in_bij bij v1' v1 →
  val_in_bij bij v2' v2 →
  ∃ v', eval_binop o v1' v2' = Some v' ∧
       val_in_bij bij v' v.
Proof.
  destruct o, v1, v2, v1', v2' => //= *; destruct_all?; simplify_eq. all: split!.
  lia.
Qed.

(** *** heap_in_bij *)
Definition heap_in_bij (bij : heap_bij) (h h' : heap_state) : Prop :=
  ∀ p1 p2 o,
  hb_bij bij !! p2 = Some (HBShared p1) →

  (is_Some (h.(h_heap) !! (p1, o)) ↔ is_Some (h'.(h_heap) !! (p2, o)))
  /\
  ∀ v1 v2,
  h.(h_heap)  !! (p1, o) = Some v1 →
  h'.(h_heap) !! (p2, o) = Some v2 →
  val_in_bij bij v1 v2.

Lemma heap_in_bij_mono bij bij' h h':
  heap_in_bij bij h h' →
  bij' ⊆ bij →
  bij ⊆ bij' →
  heap_in_bij bij' h h'.
Proof.
  move => Hh Hsub1 Hsub2 ????. split; [by apply Hh, Hsub1|].
  move => ????. apply: val_in_bij_mono; [|done]. eapply Hh; [|done..].
  by apply Hsub1.
Qed.

Lemma heap_in_bij_merge bija bijb hii hi hs :
  heap_in_bij bija hii hi →
  heap_in_bij bijb hi hs →
  heap_in_bij (heap_bij_merge bija bijb) hii hs.
Proof.
  move => Hha Hhb pii ps o /heap_bij_merge_shared[pi[??]].
  split. { etrans; [by apply Hha| by eapply Hhb]. }
  move => ????. apply val_in_bij_merge.
  move: (Hha pii pi o) => [//|??].
  have [??]: is_Some (h_heap hi !! (pi, o)) by naive_solver.
  move: (Hhb pi ps o) => [//|??].
  naive_solver.
Qed.

Lemma heap_in_bij_alive bij h1 h2 l1 l2:
  heap_in_bij bij h1 h2 →
  heap_alive h2 l2 →
  hb_bij bij !! l2.1 = Some (HBShared l1.1) →
  l1.2 = l2.2 →
  heap_alive h1 l1.
Proof.
  move => ? Hbij ??. destruct l1 as [p1 ?], l2 as [p2 o]; simplify_eq/=.
  unfold heap_in_bij, heap_alive in *. naive_solver.
Qed.

Lemma heap_in_bij_lookup bij h1 h2 l1 l2 v:
  h_heap h2 !! l2 = Some v →
  heap_in_bij bij h1 h2 →
  hb_bij bij !! l2.1 = Some (HBShared l1.1) →
  l1.2 = l2.2 →
  ∃ v', h_heap h1 !! l1 = Some v' ∧ val_in_bij bij v' v.
Proof.
  move => ? Hbij ??. destruct l1 as [p1 ?], l2 as [p2 o]; simplify_eq/=.
  have [[? H2]?]:= Hbij _ _ o ltac:(done).
  have [??]:= H2 ltac:(done).
  naive_solver.
Qed.

Lemma heap_in_bij_update bij h1 h2 l1 l2 v1 v2:
  heap_in_bij bij h1 h2 →
  val_in_bij bij v1 v2 →
  hb_bij bij !! l2.1 = Some (HBShared l1.1) →
  l1.2 = l2.2 →
  heap_in_bij bij (heap_update h1 l1 v1) (heap_update h2 l2 v2).
Proof.
  move => Hbij ???. destruct l1 as [p1 ?], l2 as [p2 o]; simplify_eq/=.
  move => p1' p2' o' /=?.
  split.
  - rewrite !lookup_alter_is_Some. by apply Hbij.
  - move => ?? /lookup_alter_Some[[?[?[??]]]|[??]] /lookup_alter_Some[[?[?[??]]]|[??]]; simplify_bij.
    all: try by eapply Hbij. all: try naive_solver.
Qed.

Lemma heap_in_bij_update_r bij h1 h2 l2 v2:
  heap_in_bij bij h1 h2 →
  (∀ p, hb_bij bij !! l2.1 = Some (HBShared p) → False) →
  heap_in_bij bij h1 (heap_update h2 l2 v2).
Proof.
  move => Hbij Hin ? ??? /=.
  rewrite !lookup_alter_ne. 1: by apply Hbij.
  move => ?; subst => /=. by apply: Hin.
Qed.

(*
Lemma heap_in_bij_alloc l1 l2 hi hs n bij H1:
  heap_in_bij bij hi hs →
  heap_is_fresh hi l1 →
  heap_is_fresh hs l2 →
  (∀ p, hb_bij bij !! l2.1 = Some (HBShared p) → False) →
  heap_in_bij (heap_bij_add_shared l1.1 l2.1 bij H1) (heap_alloc hi l1 n) (heap_alloc hs l2 n).
Proof.
  move => /= Hbij [Hi1 ?] [Hi2 ?] ?  p1 p2 o /= /lookup_insert_Some[[??]|[??]]; simplify_eq.
  - destruct l1 as [p1 ?], l2 as [p2 ?]; simplify_eq/=.
    rewrite !lookup_union_l'.
    2: { apply eq_None_ne_Some => ??. apply Hi2. by apply: (heap_wf _ (_, _)). }
    2: { apply eq_None_ne_Some => ??. apply Hi1. by apply: (heap_wf _ (_, _)). }
    split.
    + rewrite !list_to_map_lookup_is_Some. f_equiv => ?. rewrite !elem_of_list_fmap.
      f_equiv => ?. naive_solver.
    + move => ?? /(elem_of_list_to_map_2 _ _ _)/elem_of_list_fmap[?[??]].
      move => /(elem_of_list_to_map_2 _ _ _)/elem_of_list_fmap[?[??]]. by simplify_eq/=.
  - have ? : p1 ≠ l1.1. { contradict H1. apply elem_of_hb_shared_i. naive_solver. }
    have [Hbij1 Hbij2]:= Hbij p1 p2 o ltac:(set_solver).
    rewrite !lookup_union_r.
    2, 3: apply not_elem_of_list_to_map_1;
        move => /elem_of_list_fmap[[[??]?] [?/elem_of_list_fmap[?[??]]]]; simplify_eq/=.
    split; [done|] => *. apply: val_in_bij_mono; [naive_solver|].
    move => ??/=?. apply lookup_insert_Some. naive_solver.
Qed.
*)
Lemma heap_in_bij_alloc_r l2 hi hs n bij:
  heap_in_bij bij hi hs →
  (∀ p, hb_bij bij !! l2.1 = Some (HBShared p) → False) →
  heap_in_bij bij hi (heap_alloc hs l2 n).
Proof.
  move => /= Hbij Hin ???? /=. rewrite lookup_union_r. 1: by apply Hbij.
  apply not_elem_of_list_to_map_1. contradict Hin.
  move: Hin => /elem_of_list_fmap[[??][?/elem_of_list_fmap[?[??]]]]; simplify_eq/=.
  naive_solver.
Qed.

Lemma heap_in_bij_free hi hs l1 l2 bij:
  heap_in_bij bij hi hs →
  hb_bij bij !! l2.1 = Some (HBShared l1.1) →
  heap_in_bij bij (heap_free hi l1) (heap_free hs l2).
Proof.
  move => Hbij Hin p1 p2 o /=?.
  have [Hbij1 Hbij2]:= Hbij p1 p2 o ltac:(done).
  split.
  - rewrite !map_filter_lookup /=. destruct (h_heap hi !! (p1, o)), (h_heap hs !! (p2, o)) => //=.
    all: repeat case_option_guard => //; simplify_bij; naive_solver.
  - move => ??. rewrite !map_filter_lookup => /bind_Some[?[??]] /bind_Some[?[??]].
    repeat case_option_guard => //; naive_solver.
Qed.

Lemma heap_in_bij_free_r hi hs l2 bij:
  heap_in_bij bij hi hs →
  (∀ p, hb_bij bij !! l2.1 = Some (HBShared p) → False) →
  heap_in_bij bij hi (heap_free hs l2).
Proof.
  move => /= Hbij Hin ???? /=. rewrite map_filter_lookup_true. 1: by apply Hbij.
  naive_solver.
Qed.

(** *** heap_preserved *)
Definition heap_preserved (ps : gset prov) (h h' : heap_state) :=
  ∀ p o, p ∈ ps → h.(h_heap) !! (p, o) = h'.(h_heap) !! (p, o).

Global Instance heap_preserved_equivalence ps : Equivalence (heap_preserved ps).
Proof.
  unfold heap_preserved. constructor.
  - done.
  - move => ???. naive_solver.
  - move => ??? Hp1 Hp2 ???. etrans; [by apply Hp1|]. by apply Hp2.
Qed.

Lemma heap_preserved_mono ps1 ps2 h h':
  heap_preserved ps1 h h' →
  ps2 ⊆ ps1 →
  heap_preserved ps2 h h'.
Proof. unfold heap_preserved => Hp ????. apply: Hp. set_solver. Qed.

Lemma heap_preserved_lookup_r ps h h' l v:
  h_heap h' !! l = Some v →
  heap_preserved ps h h' →
  l.1 ∈ ps →
  h_heap h !! l = Some v.
Proof. move => Hl Hp ?. destruct l. by rewrite Hp. Qed.

Lemma heap_preserved_update_r l v he hp ps:
  heap_preserved ps he hp →
  l.1 ∉ ps →
  heap_preserved ps he (heap_update hp l v).
Proof.
  move => Hp ? p o /=?. rewrite lookup_alter_ne; [by eapply Hp|set_solver].
Qed.

Lemma heap_preserved_player pl pi ps l v he hp bij:
  hb_bij bij !! ps = Some (HBShared pi) →
  l.1 = ps →
  heap_preserved (hb_player_s pl bij) he hp →
  heap_preserved (hb_player_s pl bij) he (heap_update hp l v).
Proof.
  move => ???. apply heap_preserved_update_r; [done|].
  move => /elem_of_hb_player_s?. naive_solver.
Qed.

Lemma heap_preserved_bij_player_free pl pi ps l he hp bij:
  hb_bij bij !! ps = Some (HBShared pi) →
  l.1 = ps →
  heap_preserved (hb_player_s pl bij) he hp →
  heap_preserved (hb_player_s pl bij) he (heap_free hp l).
Proof.
  move => ?? Hp p' o /= Hin. rewrite map_filter_lookup. etrans; [by apply Hp|].
  destruct (h_heap hp !! (p', o)) => //=. case_option_guard => //.
  exfalso. move: Hin => /elem_of_hb_player_s?. naive_solver.
Qed.

Lemma heap_preserved_alloc_r l n he hp bij:
  l.1 ∉ bij →
  heap_preserved bij he hp →
  heap_preserved bij he (heap_alloc hp l n).
Proof.
  move => Hni Hp p o /= ?. rewrite lookup_union_r; [by apply Hp|].
  apply not_elem_of_list_to_map_1 => /elem_of_list_fmap[[[??]?] [?/elem_of_list_fmap[?[??]]]]; simplify_eq/=.
  done.
Qed.

Lemma heap_preserved_free_r l he hp bij:
  l.1 ∉ bij →
  heap_preserved bij he hp →
  heap_preserved bij he (heap_free hp l).
Proof. move => Hni Hp p o /= ?. rewrite map_filter_lookup_true; [by apply Hp|]. set_solver. Qed.

(** * imp_heap_bij module *)
Record imp_heap_bij_state := ImpHeapBij {
  ihb_bij : heap_bij;
  (* last seen heaps *)
  ihb_heap_i : heap_state;
  ihb_heap_s : heap_state;
}.
Add Printing Constructor imp_heap_bij_state.

Definition imp_heap_bij_pre (e : imp_event) (s : imp_heap_bij_state) : prepost (imp_event * imp_heap_bij_state) unitUR :=
  let hi := heap_of_event e.2 in
  pp_quant $ λ bij',
  pp_quant $ λ vss,
  pp_quant $ λ hs,
  pp_prop (heap_bij_extend Env s.(ihb_bij) bij') $
  pp_prop (dom _ (hb_bij bij') ⊆ h_provs hs) $
  pp_prop (hb_provs_i bij' ⊆ h_provs hi) $
  pp_prop (Forall2 (val_in_bij bij') (vals_of_event e.2) vss) $
  pp_prop (heap_in_bij bij' hi hs) $
  pp_prop (heap_preserved (hb_player_s Prog bij') s.(ihb_heap_s) hs) $
  pp_prop (heap_preserved (hb_player_i Prog bij') s.(ihb_heap_i) hi) $
  pp_end ((e.1, event_set_vals_heap e.2 vss hs), ImpHeapBij bij' hi hs).

Definition imp_heap_bij_post (e : imp_event) (s : imp_heap_bij_state) : prepost (imp_event * imp_heap_bij_state) unitUR :=
  let hs := heap_of_event e.2 in
  pp_quant $ λ bij',
  pp_quant $ λ vsi,
  pp_quant $ λ hi,
  pp_prop (heap_bij_extend Prog s.(ihb_bij) bij') $
  pp_prop (dom _ (hb_bij bij') ⊆ h_provs hs) $
  pp_prop (hb_provs_i bij' ⊆ h_provs hi) $
  pp_prop (Forall2 (val_in_bij bij') vsi (vals_of_event e.2)) $
  pp_prop (heap_in_bij bij' hi hs) $
  pp_prop (heap_preserved (hb_player_i Env bij') s.(ihb_heap_i) hi) $
  pp_prop (heap_preserved (hb_player_s Env bij') s.(ihb_heap_s) hs) $
  pp_end ((e.1, event_set_vals_heap e.2 vsi hi), ImpHeapBij bij' hi hs).

Definition imp_heap_bij (m : module imp_event) : module imp_event :=
  mod_prepost imp_heap_bij_pre imp_heap_bij_post m.

Definition initial_imp_heap_bij_state (m : module imp_event) (σ : m.(m_state)) :=
  (@SMFilter imp_event, σ, (@PPOutside imp_event imp_event, ImpHeapBij ∅ initial_heap_state initial_heap_state, (True%I : uPred unitUR))).

(** * vertical compositionality *)
(** ** map values and heaps through bij *)
(** *** val_through_bij *)
Definition val_through_bij (bij : heap_bij) (vs : val) : val :=
  match vs with
  | ValLoc l => ValLoc (if hb_bij bij !! l.1 is Some (HBShared p) then p else inhabitant, l.2)
  | _ => vs
  end.

Lemma val_through_in_bij bij vs:
  (∀ l, vs = ValLoc l → ∃ p, hb_bij bij !! l.1 = Some (HBShared p)) →
  val_in_bij bij (val_through_bij bij vs) vs.
Proof. move => ?. destruct vs => //=. case_match; naive_solver. Qed.

(** *** heap_through_bij *)
Program Definition heap_through_bij (bij : heap_bij) (h : heap_state) : heap_state :=
  Heap (list_to_map $ omap (OMap:=list_omap) (λ '(l, v), if hb_bij bij !! l.1 is Some (HBShared p) then
         Some ((p, l.2), val_through_bij bij v) else None) (map_to_list (h_heap h)))
       (gset_to_gmap tt $ hb_shared_i bij) _.
Next Obligation.
  move => ??. apply bool_decide_spec. move => ? /elem_of_map[?[?/elem_of_dom]]. subst.
  rewrite dom_gset_to_gmap.
  rewrite list_to_map_lookup_is_Some => -[?]. rewrite elem_of_list_omap => -[[[??]?]]/=[??].
  repeat case_match; simplify_eq. rewrite elem_of_hb_shared_i. naive_solver.
Qed.

Lemma heap_through_bij_provs bij h :
  h_provs (heap_through_bij bij h) = hb_shared_i bij.
Proof. by rewrite /h_provs dom_gset_to_gmap. Qed.

Lemma heap_through_bij_Some bij h pi o vi:
  h_heap (heap_through_bij bij h) !! (pi, o) = Some vi ↔
    ∃ ps vs, hb_bij bij !! ps = Some (HBShared pi) ∧ h_heap h !! (ps, o) = Some vs ∧ vi = val_through_bij bij vs.
Proof.
  simpl. rewrite -elem_of_list_to_map. 2: {
    rewrite list_fmap_omap. apply NoDup_omap_2_strong; [|apply NoDup_map_to_list].
    move => [[??]?] [[??]?] [??] /=.
    move => /elem_of_map_to_list ?/elem_of_map_to_list? /fmap_Some[[??][??]] /fmap_Some[[??][??]].
    by repeat case_match; simplify_eq/=; simplify_bij.
  }
  rewrite elem_of_list_omap.
  split.
  - move => [[[??]?]]. rewrite elem_of_map_to_list => ?. repeat case_match => //; naive_solver.
  - move => ?. destruct_all?. eexists (_,_,_). rewrite elem_of_map_to_list. split; [done|].
    by simplify_option_eq.
Qed.
Opaque heap_through_bij.

Lemma heap_through_bij_is_Some bij h pi o:
  is_Some (h_heap (heap_through_bij bij h) !! (pi, o)) ↔
          ∃ ps, hb_bij bij !! ps = Some (HBShared pi) ∧ is_Some (h_heap h !! (ps, o)).
Proof. rewrite /is_Some. setoid_rewrite heap_through_bij_Some. naive_solver. Qed.

Lemma heap_through_bij_is_Some' bij h pi ps o:
  hb_bij bij !! ps = Some (HBShared pi) →
  is_Some (h_heap (heap_through_bij bij h) !! (pi, o)) ↔ is_Some (h_heap h !! (ps, o)).
Proof.
  move => ?. rewrite heap_through_bij_is_Some. split; [|naive_solver].
  move => [p'[??]]. by simplify_bij.
Qed.

(** ** splitting bij' into two parts *)
Lemma fresh_map_learn bij' bijb (X : gset prov) ps pi:
  fresh_map (hb_shared_s bij' ∖ hb_shared_s bijb) X !! ps = Some pi →
  (∃ pii, hb_bij bij' !! ps = Some (HBShared pii) ∧ ∀ pi', hb_bij bijb !! ps ≠ Some (HBShared pi'))
   ∧ pi ∉ X.
Proof. move => /(fresh_map_lookup_Some _ _ _ _)[/elem_of_difference ]. rewrite !elem_of_hb_shared_s. naive_solver. Qed.
Ltac fresh_map_learn :=
  repeat match goal with
         | H : fresh_map (hb_shared_s _ ∖ hb_shared_s _) _ !! _ = Some _ |- _ =>
             learn_hyp (fresh_map_learn _ _ _ _ _ H)
         end.

Definition heap_bij_splitb_bij (X : gset prov) (bijb bij' : heap_bij) :=
  (gset_to_gmap (HBOwned Prog) (hb_player_s Prog bijb) ∪
   (HBShared <$> (hb_shared bijb ∪ fresh_map (hb_shared_s bij' ∖ hb_shared_s bijb) X)) ∪
   hb_bij bij').

Lemma heap_bij_splitb_bij_prog X bijb bija bij' ps :
  hb_player_s Prog (heap_bij_merge bija bijb) = hb_player_s Prog bij' →
  heap_bij_splitb_bij X bijb bij' !! ps = Some (HBOwned Prog) ↔ ps ∈ hb_player_s Prog bijb.
Proof.
  move => /heap_bij_merge_prog_eq_s Hprog.
  rewrite elem_of_hb_player_s /heap_bij_splitb_bij !lookup_union_Some_raw lookup_union_None lookup_fmap.
  rewrite fmap_None fmap_Some lookup_union_None hb_shared_lookup.
  rewrite !lookup_gset_to_gmap_Some lookup_gset_to_gmap_None elem_of_hb_player_s.
  split; [|naive_solver]. move => ?. destruct_all? => //. naive_solver (simplify_option_eq).
Qed.

Lemma heap_bij_splitb_bij_env X bijb bija bij' ps :
  heap_bij_extend Env (heap_bij_merge bija bijb) bij' →
  hb_player_s Env bija = ∅ →
  heap_bij_splitb_bij X bijb bij' !! ps = Some (HBOwned Env) ↔ ps ∈ hb_player_s Env bij'.
Proof.
  move => ??.
  rewrite elem_of_hb_player_s /heap_bij_splitb_bij !lookup_union_Some_raw lookup_union_None lookup_fmap.
  rewrite fmap_None fmap_Some lookup_union_None hb_shared_lookup.
  rewrite !lookup_gset_to_gmap_Some lookup_gset_to_gmap_None elem_of_hb_player_s.
  split => ?; destruct_all?; simplify_option_eq => //.
  right.
  rewrite fresh_map_lookup_None not_elem_of_difference elem_of_hb_shared_s.
  destruct (hb_bij bijb !! ps) eqn:? => /=; [|naive_solver].
  efeed pose proof heap_bij_merge_extend_env; [done..|]; simplify_eq. naive_solver.
Qed.

Lemma heap_bij_splitb_bij_bij X bijb bija bij' ps pi:
  heap_bij_extend Env (heap_bij_merge bija bijb) bij' →
  heap_bij_splitb_bij X bijb bij' !! ps = Some (HBShared pi) ↔
   hb_bij bijb !! ps = Some (HBShared pi) ∨ fresh_map (hb_shared_s bij' ∖ hb_shared_s bijb) X !! ps = Some pi.
Proof.
  move => [/=Hsub [Hprog ?]].
  rewrite /heap_bij_splitb_bij !lookup_union_Some_raw lookup_union_None lookup_fmap.
  rewrite fmap_None fmap_Some lookup_union_None.
  rewrite !lookup_gset_to_gmap_Some lookup_gset_to_gmap_None elem_of_hb_player_s.
  split => Heq; destruct_all?; simplify_eq.
  - revert select ((_ ∪ _) !! _ = Some _) => /lookup_union_Some_raw.
    rewrite hb_shared_lookup_Some. naive_solver.
  - left. revert select (fresh_map _ _ !! _ = None) => /fresh_map_lookup_None. rewrite not_elem_of_difference.
    revert select (hb_shared _ !! _ = None). rewrite hb_shared_lookup_None !elem_of_hb_shared_s. naive_solver.
  - left. right. rewrite Heq. split; [done|]. eexists _. split; [|done].
    apply lookup_union_Some_raw. rewrite hb_shared_lookup_Some. naive_solver.
  - fresh_map_learn. move: Hprog => /heap_bij_merge_prog_eq_s?.
    left. right. split; [naive_solver|].
    eexists _. split; [|done]. apply lookup_union_Some_raw.
    rewrite hb_shared_lookup_Some hb_shared_lookup_None. naive_solver.
Qed.

Program Definition heap_bij_splitb (X : gset prov) (bija bijb bij' : heap_bij)
        (H1 : heap_bij_extend Env (heap_bij_merge bija bijb) bij')
        (H2 : hb_provs_i bijb ⊆ X) : heap_bij :=
  HeapBij (heap_bij_splitb_bij X bijb bij') (hb_players_i bijb) _ _.
Next Obligation.
  move => X bija bijb bij' Hex Hshared ps pi.
  rewrite !heap_bij_splitb_bij_bij // => -[?|?]; [by apply: hb_disj|].
  apply eq_None_ne_Some => ??.
  have : (pi ∈ hb_provs_i bijb) by rewrite elem_of_hb_provs_i; naive_solver.
  fresh_map_learn. set_solver.
Qed.
Next Obligation.
  move => ????? Hp pi ??.
  rewrite !heap_bij_splitb_bij_bij // => ??.
  destruct_all?; simplify_bij.
  - done.
  - fresh_map_learn. move: (Hp pi). rewrite elem_of_hb_provs_i. naive_solver.
  - fresh_map_learn. move: (Hp pi). rewrite elem_of_hb_provs_i. naive_solver.
  - by apply: fresh_map_bij.
Qed.


(* Instead of trying to understand this definition, one can also look
at the lemmas below. *)
Definition heap_bij_splita_bij (X : gset prov) (bija bijb bij' : heap_bij) :=
  (hb_bij bija ∪ list_to_map (
     (λ '(ps, pi), (pi, HBShared $ if hb_bij bij' !! ps is Some (HBShared pii) then pii else inhabitant))
       <$> (map_to_list (fresh_map (hb_shared_s bij' ∖ hb_shared_s bijb) X)))).

Lemma heap_bij_splita_bij_None X bijb bija bij' pi :
  heap_bij_splita_bij X bija bijb bij' !! pi = None ↔
      hb_bij bija !! pi = None ∧ ∀ ps, fresh_map (hb_shared_s bij' ∖ hb_shared_s bijb) X !! ps ≠ Some pi.
Proof.
  rewrite lookup_union_None. f_equiv.
  rewrite -not_elem_of_list_to_map -list_fmap_compose elem_of_list_fmap /=.
  split.
  - move => Hneg ??. apply Hneg. eexists (_, _) => /=. split; [done|]. by apply elem_of_map_to_list.
  - move => ? [[??]/=[? /elem_of_map_to_list?]]. naive_solver.
Qed.

Lemma heap_bij_splita_bij_player X bijb bija bij' pi pl:
  heap_bij_splita_bij X bija bijb bij' !! pi = Some (HBOwned pl) ↔ pi ∈ hb_player_s pl bija.
Proof.
  rewrite elem_of_hb_player_s /heap_bij_splita_bij !lookup_union_Some_raw. split; [|naive_solver].
  move => [?//|[?]]. move => /(elem_of_list_to_map_2 _ _ _)/elem_of_list_fmap[[??]/=[??]]. simplify_eq.
Qed.

Lemma heap_bij_splita_bij_bij X bijb bija bij' pi pii:
  dom _ (hb_bij bija) ⊆ X →
  heap_bij_splita_bij X bija bijb bij' !! pi = Some (HBShared pii) ↔
    hb_bij bija !! pi = Some (HBShared pii) ∨
    ∃ ps, fresh_map (hb_shared_s bij' ∖ hb_shared_s bijb) X !! ps = Some pi
          ∧ hb_bij bij' !! ps = Some (HBShared pii).
Proof.
  move => Hdom.
  rewrite /heap_bij_splita_bij !lookup_union_Some_raw.
  rewrite -elem_of_list_to_map.
  2: { rewrite -list_fmap_compose. apply NoDup_fmap_2_strong; [|apply NoDup_map_to_list].
       move => [??] [??] /elem_of_map_to_list? /elem_of_map_to_list? /= ?. subst.
       f_equal. by apply: fresh_map_bij. }
  rewrite elem_of_list_fmap.
  split => ?; destruct_all?; simplify_eq; try naive_solver.
  - revert select (_ ∈ map_to_list _) => /elem_of_map_to_list Hfresh. right. eexists _. split; [done|].
    fresh_map_learn. destruct_all?. by simplify_option_eq.
  - fresh_map_learn. destruct_all?; simplify_eq.
    right. split. { apply eq_None_not_Some. rewrite -elem_of_dom. set_solver. }
    eexists (_, _). rewrite elem_of_map_to_list. split; [|done]. by simplify_option_eq.
Qed.

Definition heap_bij_splita_players_i (bija bij' : heap_bij) : gmap prov player :=
  gset_to_gmap Prog (hb_player_i Prog bija) ∪ gset_to_gmap Env (hb_player_i Env bij').

Lemma heap_bij_splita_player_i_prog bija bij' pii :
  heap_bij_splita_players_i bija bij' !! pii = Some Prog ↔ pii ∈ hb_player_i Prog bija.
Proof. rewrite lookup_union_Some_raw !lookup_gset_to_gmap_Some. naive_solver. Qed.

Lemma heap_bij_splita_player_i_env bija bijb bij' pii :
  heap_bij_extend Env (heap_bij_merge bija bijb) bij' →
  heap_bij_splita_players_i bija bij' !! pii = Some Env ↔ pii ∈ hb_player_i Env bij'.
Proof.
  move => [/=? [? /heap_bij_merge_prog_eq_i Hprog_i]].
  rewrite lookup_union_Some_raw !lookup_gset_to_gmap_Some lookup_gset_to_gmap_None.
  split; [naive_solver|]. rewrite !elem_of_hb_player_i => ?. split!.
  move => ?. naive_solver.
Qed.

Program Definition heap_bij_splita (X : gset prov) (bija bijb bij' : heap_bij)
        (H1 : dom _ (hb_bij bija) ⊆ X)
        (H3 : heap_bij_extend Env (heap_bij_merge bija bijb) bij') :=
  HeapBij (heap_bij_splita_bij X bija bijb bij') (heap_bij_splita_players_i bija bij') _ _.
Next Obligation.
  move => X bija bijb bij' HX Hextend pi pii.
  rewrite !heap_bij_splita_bij_bij // => -[Hpi |[?[??]]].
  - apply eq_None_ne_Some => -[].
    + rewrite heap_bij_splita_player_i_prog elem_of_hb_player_i. move: Hpi => /hb_disj. naive_solver.
    + rewrite heap_bij_splita_player_i_env // elem_of_hb_player_i.
      by apply: heap_bij_merge_extend_env_i.
  - apply eq_None_ne_Some => -[].
    + rewrite heap_bij_splita_player_i_prog elem_of_hb_player_i => ?.
      by apply: heap_bij_merge_extend_prog_i.
    + rewrite heap_bij_splita_player_i_env // elem_of_hb_player_i.
      apply eq_None_ne_Some_1. by apply: hb_disj.
Qed.
Next Obligation.
  move => X bija bijb bij' HX [/=Hsub [Hprog_s Hprog_i]] pii pi pi'.
  rewrite !heap_bij_splita_bij_bij // => ??. destruct_all?; simplify_bij.
  - done.
  - fresh_map_learn. destruct_all?; simplify_eq.
    destruct (decide (pi' ∈ hb_shared_i bijb)) as [Hin'|Hin'].
    + move: Hin'. rewrite elem_of_hb_shared_i => -[ps' ?]. move: (Hsub ps' pii).
      rewrite heap_bij_merge_shared => /(_ ltac:(naive_solver)) ?. simplify_bij.
      naive_solver.
    + revert select (hb_bij bij' !! _ = Some _) => /hb_disj?.
      have : hb_players_i bij' !! pii = Some Prog; [|naive_solver].
      eapply heap_bij_merge_prog_eq_i; [done|]. naive_solver.
  - fresh_map_learn. destruct_all?; simplify_eq.
    destruct (decide (pi ∈ hb_shared_i bijb)) as [Hin'|Hin'].
    + move: Hin'. rewrite elem_of_hb_shared_i => -[ps' ?]. move: (Hsub ps' pii).
      rewrite heap_bij_merge_shared => /(_ ltac:(naive_solver)) ?. simplify_bij.
      naive_solver.
    + revert select (hb_bij bij' !! _ = Some _) => /hb_disj?.
      have : hb_players_i bij' !! pii = Some Prog; [|naive_solver].
      eapply heap_bij_merge_prog_eq_i; [done|]. naive_solver.
  - done.
Qed.

Lemma heap_bij_merge_extend (X : gset prov) bijb bija bij':
  heap_bij_extend Env (heap_bij_merge bija bijb) bij' →
  hb_provs_i bijb ⊆ X →
  dom (gset prov) (hb_bij bija) ⊆ X →
  hb_player_s Env bija = ∅ →
  ∃ bijb' bija', bij' = heap_bij_merge bija' bijb'
    ∧ heap_bij_extend Env bija bija'
    ∧ hb_player_s Env bija' = ∅
    ∧ heap_bij_extend Env bijb bijb'
    ∧ hb_provs_i bijb' ⊆ hb_shared_i bijb' ∪ X
    ∧ dom (gset prov) (hb_bij bija') ⊆ hb_shared_i bijb' ∪ X
    ∧ (∀ pi pii, hb_bij bija' !! pi = Some (HBShared pii) →
         (∀ ps, hb_bij bijb' !! ps ≠ Some (HBShared pi)) →
         hb_bij bija !! pi = Some (HBShared pii))
    ∧ (∀ ps pi, hb_bij bijb' !! ps = Some (HBShared pi) →
         (∀ pii, hb_bij bija' !! pi ≠ Some (HBShared pii)) →
         hb_bij bijb !! ps = Some (HBShared pi))
.
Proof.
  move => [/=Hextend1 [Hprog_s Hprog_i]] HX1 HX2 Hempty.
  unshelve eexists (heap_bij_splitb X bija bijb bij' _ _); [done..|].
  unshelve eexists (heap_bij_splita X bija bijb bij' _ _); [done..|].
  split_and!.
  - apply heap_bij_eq_parts. split.
    + apply map_eq => ps. apply option_eq => pii.
      rewrite !hb_shared_lookup_Some heap_bij_merge_shared /=.
      setoid_rewrite heap_bij_splitb_bij_bij; [|done].
      setoid_rewrite heap_bij_splita_bij_bij; [|done].
      split.
      * move => Hbij'. destruct (hb_bij bijb !! ps) as [[pi|[]]|] eqn:Hbijb.
        -- eexists _. split; [naive_solver|]. left.
           apply: heap_bij_merge_extend_a; [|done..]. done.
        -- exfalso. move: Hprog_s => /heap_bij_merge_prog_eq_s. naive_solver.
        -- have [??]: is_Some (fresh_map (hb_shared_s bij' ∖ hb_shared_s bijb) X !! ps).
           { apply not_eq_None_Some. rewrite fresh_map_lookup_None. apply. apply elem_of_difference.
             rewrite !elem_of_hb_shared_s. naive_solver. }
           naive_solver.
        -- have [??]: is_Some (fresh_map (hb_shared_s bij' ∖ hb_shared_s bijb) X !! ps).
           { apply not_eq_None_Some. rewrite fresh_map_lookup_None. apply. apply elem_of_difference.
             rewrite !elem_of_hb_shared_s. naive_solver. }
           naive_solver.
      * move => [? [Hor ?]].
        destruct_all?; simplify_eq.
        -- apply Hextend1. rewrite heap_bij_merge_shared. naive_solver.
        -- exfalso. fresh_map_learn. destruct_all?. revert select (_ ∉ _). apply.
           apply HX2. rewrite elem_of_dom. naive_solver.
        -- exfalso. fresh_map_learn. destruct_all?. revert select (_ ∉ _). apply.
           apply HX1. rewrite elem_of_hb_provs_i. naive_solver.
        -- have := fresh_map_bij _ _ ps0 ps _ ltac:(done) ltac:(done). naive_solver.
    + move => pl. split; apply set_eq => ?; destruct pl.
      * rewrite - {1}Hprog_s !heap_bij_merge_player_s heap_bij_splitb_bij_prog ?elem_of_hb_player_s//.
        setoid_rewrite heap_bij_splitb_bij_bij; [|done].
        split => ?; destruct_all?; simplify_eq; try naive_solver.
        -- right. eexists _. split; [naive_solver|].
           apply default_eq_Some' => -[?|?] /=.
           ++ rewrite heap_bij_splita_bij_bij // => -[?|?]; simplify_option_eq. destruct_all?.
              exfalso. fresh_map_learn. destruct_all?. revert select (_ ∉ _). apply.
              apply HX1. rewrite elem_of_hb_provs_i. naive_solver.
           ++ rewrite heap_bij_splita_bij_player elem_of_hb_player_s => ?. by simplify_option_eq.
        -- right. eexists _. split; [done|]. rewrite default_eq_Some' /= => y.
           revert select (default _ _ = _). rewrite default_eq_Some' => /(_ y). move: y => -[?|?].
           ++ rewrite heap_bij_splita_bij_bij //. naive_solver.
           ++ rewrite heap_bij_splita_bij_player elem_of_hb_player_s => ?. naive_solver.
        -- simpl in *. unfold default in *. case_match as Hc => /=; simplify_eq/=.
           ++ move: Hc. rewrite heap_bij_splita_bij_player elem_of_hb_player_s => ?.
              exfalso. fresh_map_learn. destruct_all?. revert select (_ ∉ _). apply.
              apply HX2. rewrite elem_of_dom. naive_solver.
           ++ move: Hc => /heap_bij_splita_bij_None. naive_solver.
      * rewrite !heap_bij_merge_player_s heap_bij_splitb_bij_env //=.
        setoid_rewrite heap_bij_splitb_bij_bij; [|done].
        setoid_rewrite default_eq_neq => //.
        setoid_rewrite heap_bij_splita_bij_player.
        rewrite Hempty. set_solver.
      * rewrite - {1}Hprog_i !heap_bij_merge_player_i /= heap_bij_splita_player_i_prog elem_of_hb_player_i.
        setoid_rewrite heap_bij_splita_bij_bij; [|done].
        split => ?; destruct_all?; simplify_eq; try by left.
        -- right. split!; [by left|]. rewrite elem_of_hb_shared_i => /= -[?].
           rewrite heap_bij_splitb_bij_bij // => -[?|?].
           ++ revert select (_ ∉ _). apply. rewrite elem_of_hb_shared_i. naive_solver.
           ++ fresh_map_learn. destruct_all?; simplify_eq. revert select (_ ∉ _). apply. apply HX2.
              rewrite elem_of_dom. naive_solver.
        -- right. split!; [done|] => Hb. revert select (_ ∉ _). apply.
           move: Hb. rewrite !elem_of_hb_shared_i => -[??]. eexists _.
           rewrite heap_bij_splitb_bij_bij //. naive_solver.
        -- exfalso. revert select (_ ∉ _). apply. rewrite !elem_of_hb_shared_i. eexists _.
           rewrite heap_bij_splitb_bij_bij //. naive_solver.
      * rewrite !heap_bij_merge_player_i !elem_of_hb_player_i /= heap_bij_splita_player_i_env //.
        rewrite elem_of_hb_player_i. naive_solver.
  - split => /=; [|split].
    + move => ?? /=. rewrite heap_bij_splita_bij_bij //. naive_solver.
    + apply set_eq => p. by rewrite !elem_of_hb_player_s /= heap_bij_splita_bij_player elem_of_hb_player_s.
    + apply set_eq => p. by rewrite !elem_of_hb_player_i /= heap_bij_splita_player_i_prog elem_of_hb_player_i.
  - apply set_eq => p. rewrite elem_of_hb_player_s /= heap_bij_splita_bij_player. set_solver.
  - split => /=; [|split].
    + move => ?? /=. rewrite heap_bij_splitb_bij_bij //. naive_solver.
    + apply set_eq => p. by rewrite !elem_of_hb_player_s /= heap_bij_splitb_bij_prog // elem_of_hb_player_s.
    + apply set_eq => p. by rewrite !elem_of_hb_player_i /=.
  - move => ?. rewrite elem_of_union. rewrite elem_of_hb_provs_i/= => -[[??]|[?]].
    { right. apply HX1. rewrite elem_of_hb_provs_i. naive_solver. }
    rewrite heap_bij_splitb_bij_bij // => -[?|?].
    { right. apply HX1. rewrite elem_of_hb_provs_i. naive_solver. }
    rewrite elem_of_hb_shared_i/=.
    setoid_rewrite heap_bij_splitb_bij_bij; [|done]. naive_solver.
  - move => ? /=/elem_of_dom[x ]. rewrite elem_of_union elem_of_hb_shared_i /=.
    setoid_rewrite heap_bij_splitb_bij_bij; [|done].
    destruct x.
    + rewrite heap_bij_splita_bij_bij //. move => ?. destruct_all?. 2: naive_solver.
      right. apply HX2. by apply elem_of_dom.
    + rewrite heap_bij_splita_bij_player elem_of_hb_player_s. right. apply HX2. by apply elem_of_dom.
  - move => ?? /=. rewrite heap_bij_splita_bij_bij //. setoid_rewrite heap_bij_splitb_bij_bij; [|done].
    naive_solver.
  - move => ?? /=. rewrite heap_bij_splitb_bij_bij //. setoid_rewrite heap_bij_splita_bij_bij; [|done].
    move => [//|?]. fresh_map_learn; destruct_all?. naive_solver.
Qed.

(** ** proof of vertical compositionality *)
Local Ltac split_solve :=
  match goal with
  | _ => rewrite event_set_vals_heap_idemp
  | |- event_set_vals_heap _ _ _ = event_set_vals_heap _ _ _ => reflexivity
  end.
Local Ltac split_tac ::=
  repeat (original_split_tac; try split_solve).

Lemma imp_heap_bij_vertical m σ `{!VisNoAll m}:
  trefines (MS (imp_heap_bij (imp_heap_bij m))
               (initial_imp_heap_bij_state (imp_heap_bij m) (initial_imp_heap_bij_state m σ)))
           (MS (imp_heap_bij m)
               (initial_imp_heap_bij_state m σ))
.
Proof.
  unshelve apply: mod_prepost_combine. {
    exact (λ pl '(ImpHeapBij bija hia hsa) '(ImpHeapBij bijb hib hsb) '(ImpHeapBij bij hi hs) xa xb x,
    hb_player_s Env bija = ∅
    ∧ satisfiable xb
    ∧ x = xa
    ∧ bij = heap_bij_merge bija bijb
    ∧ hsb = hs
    ∧ hia = hi
    ∧ hsa = hib
    ∧
    if pl is Env then
      heap_in_bij bijb hsa hsb ∧
      heap_in_bij bija hia hib ∧
      dom (gset prov) (hb_bij bija) ⊆ h_provs hsa ∧
      hb_provs_i bijb ⊆ h_provs hsa
    else
      True
). }
  { split!.
    - apply set_eq => ?. rewrite elem_of_hb_player_s. set_solver.
    - by apply satisfiable_pure_1.
    - apply heap_bij_eq_parts => /=. split; [apply map_eq|move => pl; split; apply set_eq] => ?.
      + rewrite !hb_shared_lookup heap_bij_merge_lookup. by simplify_map_eq.
      + by rewrite elem_of_hb_player_s.
      + by rewrite elem_of_hb_player_i.
  }
  all: move => [bija hia hsa] [bijb hib hsb] [bij hi hs] ??? e ? /=.
  - move => bij' vs h' Hextend Hdh Hprovs Hvs Hh Hps Hpi.
    destruct_all?; simplify_eq/=.
    move: (Hextend) => /(heap_bij_merge_extend (h_provs hib))[//|//|//|bijb' [bija' [?[?[Hbij1e[?[?[??]]]]]]]]
                      ; simplify_eq.
    eexists _, (val_through_bij bijb' <$> vs),
      (heap_merge (heap_restrict (heap_through_bij bijb' h') (λ p, p ∈ hb_shared_s bija'))
                  (heap_restrict hib (λ x, x ∉ hb_shared_s bija' ∨ x ∉ hb_shared_i bijb'))).
    split!; rewrite ?heap_of_event_event_set_vals_heap; split!; last done. all: split!.
    + rewrite heap_merge_provs !heap_restrict_provs heap_through_bij_provs. done.
    + etrans; [|done]. move => ?. by rewrite heap_bij_merge_provs_i.
    + rewrite Forall2_fmap_r. apply: Forall2_impl; [done|] => v_ii v_s /=.
      destruct v_ii, v_s => //= -[/heap_bij_merge_shared[?[??]]?].
      by simplify_option_eq.
    + move => pii pi o /= ?.
      rewrite lookup_union.
      rewrite map_filter_lookup_true. 2: { move => *. rewrite elem_of_hb_shared_s. naive_solver. }
      destruct (decide (pi ∈ hb_shared_i bijb')) as [Hpi'|Hpi'].
      all: rewrite elem_of_hb_shared_i in Hpi'; destruct_all?.
      * rewrite map_filter_lookup_None_2.
        2: { right. move => *. rewrite !elem_of_hb_shared_s elem_of_hb_shared_i /=. naive_solver. }
        rewrite right_id_L.
        rewrite heap_through_bij_is_Some' //.
        split. { apply Hh. rewrite heap_bij_merge_shared. naive_solver. }
        move => ???/heap_through_bij_Some[ps'[?[?[??]]]]. simplify_bij.
        move: (Hh pii ps' o) => [|_ Hv]. { rewrite heap_bij_merge_shared. naive_solver. }
        efeed pose proof Hv as Hv'; [done..|].
        move: Hv'. rewrite val_in_bij_merge => -[?[Hv1 Hv2]].
        unfold val_in_bij in Hv1, Hv2. repeat case_match => //; destruct_all?; simplify_option_eq => //.
        split; [done|]. congruence.
      * destruct (h_heap (heap_through_bij bijb' h') !! (pi, o)) as [|] eqn: Hht => /=.
        { move: Hht => /heap_through_bij_Some. naive_solver. }
        rewrite left_id.
        rewrite map_filter_lookup_true. 2: { move => *. rewrite elem_of_hb_shared_i. naive_solver. }
        move: (Hpi pii o) => <-. 2: {
          rewrite heap_bij_merge_player_i. right. split!; [done|]. by rewrite elem_of_hb_shared_i.
        }
        revert select (heap_in_bij bija hi hib) => Hhbij.
        move: (Hhbij pii pi o) => [|HS Hv]. { naive_solver. }
        rewrite HS. split; [done|]. move => ????. apply: val_in_bij_mono; [naive_solver|].
        unfold heap_bij_extend in *. naive_solver.
    + move => pi o /=. rewrite elem_of_hb_player_s => ?. rewrite lookup_union_r.
      2: { apply map_filter_lookup_None. right. move => ??. rewrite elem_of_hb_shared_s. naive_solver. }
      rewrite map_filter_lookup_true //.
      move => ??. rewrite elem_of_hb_shared_s. naive_solver.
    + apply: heap_preserved_mono; [done|]. move => ?.
      rewrite {1}elem_of_hb_player_i /= heap_bij_merge_player_i. naive_solver.
    + etrans; [|done]. by rewrite heap_bij_merge_dom.
    + rewrite heap_merge_provs !heap_restrict_provs heap_through_bij_provs. done.
    + rewrite vals_of_event_event_set_vals_heap. 2: rewrite fmap_length; solve_length.
      rewrite Forall2_fmap_l. apply Forall_Forall2_diag, Forall_forall => ?/= /elem_of_list_lookup [? Hin].
      apply val_through_in_bij => ??. simplify_eq.
      move: Hvs => /(Forall2_lookup_r _ _ _ _ _)/(_ Hin)[v [?]]. destruct v => //=.
      rewrite heap_bij_merge_shared. naive_solver.
    + move => pi ps o /= ?.
      destruct (decide (pi ∈ hb_shared_s bija')) as [Hpi'|Hpi'];
        rewrite elem_of_hb_shared_s in Hpi'; destruct_all?.
      * rewrite lookup_union.
        rewrite map_filter_lookup_true. 2: { move => *. rewrite elem_of_hb_shared_s. naive_solver. }
        rewrite map_filter_lookup_None_2.
        2: { right. move => *. rewrite elem_of_hb_shared_s elem_of_hb_shared_i. naive_solver. }
        rewrite right_id_L.
        rewrite heap_through_bij_is_Some' //. split; [done|].
        move => ??. rewrite heap_through_bij_Some => ? ?. destruct_all?; simplify_bij.
        eapply val_through_in_bij => ??.
        move: (Hh pi0 ps0 o) => [|]. { rewrite heap_bij_merge_shared. naive_solver. }
        simplify_option_eq. revert select (h_heap h' !! _ = Some _) => ->. move => [_ [//|v' ?]] Hv.
        efeed pose proof Hv as Hv'; [done..|]. destruct v' => //; simplify_eq/=.
        move: Hv'. rewrite heap_bij_merge_shared. naive_solver.
      * rewrite lookup_union.
        rewrite map_filter_lookup_None_2. 2: { right. move => *. rewrite elem_of_hb_shared_s. naive_solver. }
        rewrite map_filter_lookup_true. 2: { move => *. rewrite elem_of_hb_shared_s. naive_solver. }
        rewrite left_id_L.
        move: (Hps ps o) => <-. 2: {
          rewrite heap_bij_merge_player_s. right. eexists _. split; [done|]. apply default_eq_Some'.
          move => [|[]]; [naive_solver|naive_solver|]. move => ?.
          move: Hbij1e =>/set_eq/(_ pi). rewrite elem_of_hb_player_s. set_solver.
        }
        revert select (heap_in_bij bijb hib hs) => Hhbij.
        move: (Hhbij pi ps o) => [|HS Hv]. { naive_solver. }
        rewrite HS. split; [done|]. move => ????. apply: val_in_bij_mono; [naive_solver|].
        unfold heap_bij_extend in *. naive_solver.
    + apply: heap_preserved_mono; [done|].
      move => ?. rewrite heap_bij_merge_player_s elem_of_hb_player_s. naive_solver.
    + move => pi o /=. rewrite elem_of_hb_player_i => ?. rewrite lookup_union_r.
      2: { apply map_filter_lookup_None. right. move => /=?/heap_through_bij_Some[?[?[/hb_disj??]]]. naive_solver. }
      rewrite map_filter_lookup_true //.
      move => ??. rewrite elem_of_hb_shared_i /=. right => -[? /hb_disj]. naive_solver.
    + instantiate (1 := True%I). by rewrite !right_id.
    + by apply: satisfiable_pure_1.
  - move => bijb' vsb hb' [Hextendb [Henvb_s Henvb_i]] Hdhb Hpsb Hvsb Hhb Hpb_i Hpb_s ??.
    move => bija' vsa ha' [Hextenda [Henva_s Henva_i]] Hdha Hpsa Hvsa Hha Hpa_i Hpa_s ??.
    destruct_all?; simplify_eq/=.
    rewrite ->heap_of_event_event_set_vals_heap in *.
    rewrite ->vals_of_event_event_set_vals_heap in *. 2: solve_length.
    split!.
    + split => /=.
      * move => ??. rewrite !heap_bij_merge_shared. bij_solver.
      * split; apply set_eq => ?.
        -- rewrite !heap_bij_merge_player_s. f_equiv.
           ++ rewrite -!elem_of_hb_player_s. by rewrite Henvb_s.
           ++ setoid_rewrite default_eq_neq => //. setoid_rewrite <-elem_of_hb_player_s.
              f_equiv => ?. rewrite -Henva_s. revert select (hb_player_s Env bija = ∅) => ->. set_solver.
        -- rewrite !heap_bij_merge_player_i. f_equiv.
           ++ rewrite -!elem_of_hb_player_i. set_solver.
           ++ naive_solver.
    + etrans; [|done]. by rewrite heap_bij_merge_dom.
    + etrans; [|done]. move => ?. by rewrite heap_bij_merge_provs_i.
    + elim: Hvsa (vals_of_event e.2) Hvsb. { move => *. decompose_Forall_hyps. econs. }
      move => va vab {}vsa {}vsb ?? IH ??. decompose_Forall_hyps. econs; [|naive_solver].
      apply val_in_bij_merge. naive_solver.
    + by apply: heap_in_bij_merge.
    + apply: heap_preserved_mono; [done|].
      move => ?. rewrite heap_bij_merge_player_i elem_of_hb_player_i. naive_solver.
    + apply: heap_preserved_mono; [done|].
      move => ?. rewrite heap_bij_merge_player_s elem_of_hb_player_s.
      setoid_rewrite default_eq_neq => //. setoid_rewrite <-elem_of_hb_player_s. set_solver.
    + by rewrite -Henva_s.
    + revert select (satisfiable _) => _. revert select (satisfiable _) => Hsat.
      iSatMono Hsat. iIntros "[$ [??]]".
Qed.

End pure_bij.


(*

Local Ltac split_solve :=
  match goal with
  (* | |- heap_in_bij ?p _ _ => is_evar p; eassumption *)
  | |- heap_in_bij _ _ _ => apply: heap_in_bij_mono; [eassumption|..]
  | |- event_set_vals_heap _ _ _ = event_set_vals_heap _ _ _ => reflexivity
  | |- heap_bij_extend ?p ?a ?b =>
      assert_fails (has_evar p); assert_fails (has_evar a); assert_fails (has_evar b); by etrans
  (* | |- ?a ⊆ ?b => *)
      (* assert_fails (has_evar a); assert_fails (has_evar b); etrans; [eassumption|] *)
  (* | |- ?a ⊆ ?b => *)
      (* assert_fails (has_evar a); assert_fails (has_evar b); etrans; [|eassumption] *)
  | |- _ ⊆ heap_bij_map_player _ _ => apply heap_bij_map_player_subseteq_r
  | |- heap_bij_map_player _ _ ⊆ _ => apply heap_bij_map_player_subseteq_l
  | |- heap_preserved ?p ?a ?b =>
      assert_fails (has_evar p); assert_fails (has_evar a); assert_fails (has_evar b); etrans; [eassumption|]
  end.
Local Ltac split_tac ::=
  repeat (original_split_tac; try split_solve).

Lemma imp_heap_bij_combine fns1 fns2 m1 m2 σ1 σ2 `{!VisNoAll m1} `{!VisNoAll m2}:
  trefines (MS (imp_prod fns1 fns2 (imp_heap_bij m1) (imp_heap_bij m2))
               (MLFNone, [], initial_imp_heap_bij_state m1 σ1,
                 initial_imp_heap_bij_state m2 σ2))
           (MS (imp_heap_bij (imp_prod fns1 fns2 m1 m2))
               (initial_imp_heap_bij_state (imp_prod _ _ _ _)
                  (MLFNone, [], σ1, σ2) )
).
Proof.
  unshelve apply: mod_prepost_link. { exact
      (λ ips '(ImpHeapBij bij1 hi1) '(ImpHeapBij bij2 hi2) '(ImpHeapBij bij hi) _ _ ics1 ics2,
        ∃ bijm,
          ics1 = ics2 ∧
          bij1 ⊆ bijm ∧
          bij2 ⊆ bijm ∧
          bij ⊆ bijm ∧
       ((ips = SPNone ∧ bijm = bij ∧
          hb_player Prog bij = hb_player Prog bij1 ∪ hb_player Prog bij2 ∧
          hb_player Prog bij1 ## hb_player Prog bij2 ∧
          heap_preserved (hb_player Prog bij1) hi1 hi ∧
          heap_preserved (hb_player Prog bij2) hi2 hi) ∨
        ((ips = SPLeft ∧ bijm = bij1 ∧
          hb_player Env bij1 = hb_player Env bij ∪ hb_player Prog bij2 ∧
          hb_player Prog bij2 ## hb_player Env bij ∧
          heap_preserved (hb_player Env bij) hi hi1 ∧
          heap_preserved (hb_player Prog bij2) hi2 hi1) ∨
         (ips = SPRight ∧ bijm = bij2 ∧
          hb_player Env bij2 = hb_player Env bij ∪ hb_player Prog bij1 ∧
          hb_player Prog bij1 ## hb_player Env bij ∧
          heap_preserved (hb_player Env bij) hi hi2 ∧
          heap_preserved (hb_player Prog bij1) hi1 hi2)))). }
  { move => ?? [] /=*; naive_solver. }
  { by rewrite left_id. } { by apply satisfiable_pure_1. }
  { split!.  all: rewrite /hb_player; unlock; set_solver. }
  all: move => [bij1 hi1] [bij2 hi2] [bij hi] ? ? ics1 ics2.
  - move => e ics' e' /= *. unfold heap_bij_extend in *. destruct_all?; simplify_eq/=.
    eexists (heap_bij_map_player (λ p2 p, if decide (p2 ∈ hb_player Prog bij2) then Env else p) bij).
    split!.
    { set_unfold.
    1: {
1: econstructor. all: shelve_unifiable. all: split!. all: split!.
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
    1: by iIntros "$".
    1: by destruct e.
    1: { apply: disjoint_mono; [apply hb_disj_priv| |done]. set_unfold; naive_solver. }
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
  - move => e ics' e' /= *. unfold heap_bij_extend in *; destruct_all?; simplify_eq/=.
    unshelve split!. 1: econstructor. all: shelve_unifiable. all: split!. all: split!.
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
    1: by iIntros "$".
    1: by destruct e.
    1: { apply: disjoint_mono; [apply hb_disj_priv| |done]. set_unfold; naive_solver. }
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
  - move => [? e] /= *. unfold heap_bij_extend in *; destruct_all?; simplify_eq/=.
    unshelve split!. 1: econstructor. all: shelve_unifiable.
    all: split!; rewrite ?heap_of_event_event_set_vals_heap; split!. all: split!.
    1: { rewrite vals_of_event_event_set_vals_heap //. by apply: Forall2_length. }
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
    1: { iIntros "[? $]". iStopProof. etrans; [done|]. by iIntros ">[_ $]". }
    1: { apply: disjoint_mono; [apply hb_disj_priv|done|]. set_unfold; naive_solver. }
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
    1: by destruct e.
    1: by destruct e.
  - move => [? e] /= *. unfold heap_bij_extend in *; destruct_all?; simplify_eq/=.
    unshelve split!. 1: econstructor. all: shelve_unifiable.
    all: split!; rewrite ?heap_of_event_event_set_vals_heap; split!. all: split!.
    1: by destruct e.
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
    1: { etrans; [done|]. iIntros ">[? $]". iStopProof. etrans; [done|]. by iIntros ">[_ $]". }
    1: { apply: disjoint_mono; [apply hb_disj_priv|done|]. set_unfold; naive_solver. }
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
  - move => [? e] /= *. unfold heap_bij_extend in *; destruct_all?; simplify_eq/=.
    unshelve split!. 1: econstructor. all: shelve_unifiable.
    all: split!; rewrite ?heap_of_event_event_set_vals_heap; split!. all: split!.
    1: { rewrite vals_of_event_event_set_vals_heap //. by apply: Forall2_length. }
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
    1: { iIntros "[$ ?]". iStopProof. etrans; [done|]. by iIntros ">[_ $]". }
    1: { apply: disjoint_mono; [apply hb_disj_priv|done|]. set_unfold; naive_solver. }
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
    1: by destruct e.
    1: by destruct e.
  - move => [? e] /= *. unfold heap_bij_extend in *; destruct_all?; simplify_eq/=.
    unshelve split!. 1: econstructor. all: shelve_unifiable.
    all: split!; rewrite ?heap_of_event_event_set_vals_heap; split!. all: split!.
    1: by destruct e.
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
    1: { etrans; [done|]. iIntros ">[$ ?]". iStopProof. etrans; [done|]. by iIntros ">[_ $]". }
    1: { symmetry. apply: disjoint_mono; [apply hb_disj_priv|done|]. set_unfold; naive_solver. }
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
    Unshelve.
    (* We need to use abstract here as otherwise Qed does not terminate. *)
    all: try abstract (by apply hb_iff).
    all: abstract (
      try (apply disjoint_union_l; split);
      try (apply disjoint_union_r; split);
      try (by apply hb_disj_env);
      try (by apply hb_disj_prog);
      try done;
      try (apply: disjoint_mono; [apply hb_disj_prog| |done]; apply: subseteq_mono_eq_r; [|eassumption]);
      try (apply: disjoint_mono; [apply hb_disj_priv| |done]; apply: subseteq_mono_eq_r; [|eassumption]);
      try (apply: disjoint_mono; [apply hb_disj_env| |done]; apply: subseteq_mono_eq_r; [|eassumption]);
      try (apply: disjoint_mono; [apply hb_disj_priv|done|]; apply: subseteq_mono_eq_r; [|eassumption]);
      try (symmetry; apply: disjoint_mono; [apply hb_disj_priv|done|]; apply: subseteq_mono_eq_r; [|eassumption]);
      set_unfold; naive_solver).
Qed.


Local Ltac split_solve ::=
  match goal with
  | |- expr_fill (?K' ++ ?K) _ = expr_fill ?K _ =>
      assert_fails (has_evar K'); assert_fails (has_evar K); apply expr_fill_app
  | |- expr_fill ?K _ = expr_fill ?K _ =>
      assert_fails (has_evar K); reflexivity
  | |- Is_true (static_expr _ (expr_fill _ _)) => apply static_expr_expr_fill
  | |- expr_in_bij ?b (expr_fill _ _) (expr_fill _ _) =>
      assert_fails (has_evar b); apply expr_in_bij_fill_2
  | |- ectx_in_bij ?b (_ ++ _) (_ ++ _) => assert_fails (has_evar b); by apply ectx_in_bij_app
  end.
Local Ltac split_tac ::=
  repeat (original_split_tac; try split_solve).

Local Ltac bij_solver := unfold heap_bij_extend in *; set_unfold; naive_solver.

Lemma imp_heap_bij_imp_refl fns:
  trefines (MS imp_module (initial_imp_state fns))
           (MS (imp_heap_bij imp_module)
               (initial_imp_heap_bij_state imp_module (initial_imp_state fns))).
Proof.
  epose (R := λ (b : bool) '(ImpHeapBij bij1 h1, _) '(ImpHeapBij bij2 h2, _),
          (hb_prog bij1 = ∅ → hb_prog bij2 = ∅) ∧ hb_bij bij1 ⊆ hb_bij bij2).
  apply: (imp_prepost_proof R); unfold R in *.
  { constructor. { move => [[??]?]. naive_solver. }
    { move => [[??]?] [[??]?] [[??]?] [??] [??]. split. naive_solver. by etrans. } }
  { move => [??] ? [??] ?. naive_solver. }
  move => n K1 K2 f fn1 vs1 h1 [bij0 ?] ??? /= bij1 *.
  split!. move => ?. split; [solve_length|].
  move => Hcall Hret.
  unshelve apply: tsim_remember. { simpl. exact (λ _ '(Imp ei hi fnsi) '(ips, Imp es hs fnss, (pp, ImpHeapBij bij he, P)),
    (* bij' : current bijection, bij : bijection when last communicated with the environment,
     bij1: bijection at the start of the function (necessary to reestablish R) *)
    ∃ bij' ei' es',
    fnsi = fns ∧ fnss = fns ∧
    hb_env bij = hb_env bij' ∧
    hb_prog bij = ∅ ∧ hb_prog bij' = ∅ ∧
    hb_bij bij ⊆ hb_bij bij' ∧
    hb_bij bij1 ⊆ hb_bij bij ∧
    heap_preserved (hb_env bij') he hs ∧
    ei = expr_fill K1 ei' ∧
    es = expr_fill K2 es' ∧
    expr_in_bij (hb_bij bij') ei' es' ∧
    heap_in_bij (hb_bij bij') hi hs ∧
    set_map fst (hb_bij bij') ⊆ h_provs hi ∧
    pp = PPInside ∧
    static_expr true ei' ∧
    ips = SMProg
 ). }
  { eexists _. split!. done. all: split!.
    { unfold heap_bij_extend in *. clear Hcall Hret. bij_solver. }
    { unfold heap_bij_extend in *. clear Hcall Hret. bij_solver. }
    { apply expr_in_bij_subst_l; [|done|solve_length]. apply expr_in_bij_static. apply fd_static. }
    { apply static_expr_subst_l; [|solve_length]. apply static_expr_mono. apply fd_static. }   }
  { naive_solver. }
  move => /= n' ? Hloop [ei hi fnsi] [[ips [es hs fnss]] [[pp [bij he]] ?]] ?.
  destruct_all?; simplify_eq.
  destruct (to_val ei') eqn:?.
  - destruct ei' => //; simplify_eq/=. destruct es' => //; simplify_eq/=.
    apply Hret; [done|]. clear Hloop Hret Hcall. split!.
    { unfold heap_bij_extend. split!; [done..|]. bij_solver. }
    all: split!. by econs. { instantiate (1:=True%I). iIntros "? !>". done. }
    { done. }
    { etrans; [|done]. etrans; [|done]. bij_solver. }
  - (* TODO: remove this use of EM *)
    have [?|?]:= EM (∃ K f vs, fns !! f = None ∧ ei' = expr_fill K (Call f (Val <$> vs))).
    + destruct_all?; simplify_eq/=.
      revert select (expr_in_bij _ (expr_fill _ _) _) => /expr_in_bij_fill_l[?[?[?[??]]]].
      destruct_all?; simplify_eq/=.
      revert select (Is_true (static_expr _ _)) => /static_expr_expr_fill/=[??]//.
      case_match => //; destruct_all?; simplify_eq/=.
      revert select (Forall id _) => /Forall_zip_with_1 Hall.
      move: (Hall ltac:(done)) => /Forall2_bij_val_inv_l[?[??]]; simplify_eq.
      apply: Hcall; [done..| | |].
      1,2: by apply Forall2_fmap_l, Forall_Forall2_diag, Forall_true.
      clear Hret. split!.
      { unfold heap_bij_extend. split!; [done..|]. bij_solver. }
      all: split!.
      { instantiate (1:=True%I). iIntros "? !>". done. }
      { etrans; [|done]. etrans; [|done]. bij_solver. }
      move => ?? [??] *. decompose_Forall_hyps. split!.
      apply Hloop; [done|]. split!. 1: done. all: split!.
      1: bij_solver.
      1: bij_solver.
      { etrans; [done|]. etrans; [done|]. bij_solver. }
      { apply: ectx_in_bij_mono; [done|]. bij_solver. }
    + tstep_both.
      apply steps_impl_step_end => ?? /= Hprim.
      move: Hprim => /prim_step_inv[//|??].
      destruct_all?; simplify_eq.
      revert select (expr_in_bij _ (expr_fill _ _) _) => /expr_in_bij_fill_l[?[?[?[??]]]].
      destruct_all?; simplify_eq.
      revert select (Is_true (static_expr _ _)) => /static_expr_expr_fill/=[??]//.
      invert_all' @head_step; destruct_all?; simplify_eq/=.
      all: repeat (case_match; destruct_all? => //); simplify_eq.
      * tstep_s => ? /eval_binop_bij Hbin. have [?[??]]:= Hbin _ _ _ ltac:(done) ltac:(done).
        tend. split!. apply: Hloop; [done|]. split!. 1: done. 1: done. all: split!.
      * tstep_s => *; simplify_eq/=. destruct v1 => //; simplify_eq/=; destruct_all?; simplify_eq/=. tend.
        have [//|?[??]]:= heap_in_bij_lookup _ _ _ _ _ _ ltac:(done) ltac:(done) ltac:(done).
        split!. 1: done.
        apply: Hloop; [done|]. split!. 1: done. 1: done. all: split!.
      * tstep_s => *; simplify_eq/=. destruct v1 => //; simplify_eq/=; destruct_all?; simplify_eq/=. tend.
        split!. 1: by apply: heap_in_bij_alive.
        apply: Hloop; [done|]. split!. 1: done. 1: done. all: split!.
        1: by apply: heap_preserved_bij_env.
        1: by apply heap_in_bij_update.
      * tstep_s => *; simplify_eq/=.
        set (l' := (heap_fresh (hb_provs_right bij') hs)).
        eexists l'. split; [apply heap_fresh_is_fresh|] => *; simplify_eq/=. tend.
        destruct v => //; simplify_eq/=; destruct_all?; simplify_eq/=.
        split!.
        apply Hloop; [done|].
        unshelve eexists (heap_bij_add_loc l.1 l'.1 bij' _ _).
        { abstract (apply: not_elem_of_weaken; [|done]; unfold heap_is_fresh in *; naive_solver). }
        { apply: heap_fresh_not_in. }
        split!.
        1: bij_solver.
        1: { apply heap_preserved_alloc_r; [|done] => ?.
             apply: (heap_fresh_not_in (hb_provs_right bij') hs). bij_solver. }
        1: { apply: ectx_in_bij_mono; [done|bij_solver]. }
        1: bij_solver.
        1: unfold heap_is_fresh in *; naive_solver.
        1: { apply: (heap_in_bij_alloc l l').
             { abstract (apply: not_elem_of_weaken; [|done]; unfold heap_is_fresh in *; naive_solver). }
             { apply: heap_fresh_not_in. }
          done. done. apply heap_fresh_is_fresh. }
        1: bij_solver.
      * tstep_s => *; simplify_eq/=. tend.
        destruct v => //; simplify_eq/=; destruct_all?; simplify_eq/=.
        split!. 1: by apply: heap_in_bij_alive. apply: Hloop; [done|]. split!. 1: done. 1: done. all: split!.
        1: by apply: heap_preserved_bij_env_free.
        1: by apply heap_in_bij_free.
      * tstep_s => *; simplify_eq/=. destruct v => //; simplify_eq/=. tend.
        split!. apply: Hloop; [done|]. split!. 1: done. 1: done. all: split!. all: by case_match.
      * tstep_s. tend. split!. apply: Hloop; [done|]. split!. 1: done. all: split!.
        1: by apply expr_in_bij_subst.
        1: by apply static_expr_subst.
      * by tstep_s.
      * revert select (Forall id _) => /Forall_zip_with_1 Hall.
        move: (Hall ltac:(done)) => /Forall2_bij_val_inv_l[?[??]]; simplify_eq.
        tstep_s. left. split! => ?. tend. split!; [solve_length|].
        apply Hloop; [done|]. split!. 1: done. all: split!.
        1: { apply expr_in_bij_subst_l; [|done|solve_length]. apply expr_in_bij_static. apply fd_static. }
        apply static_expr_subst_l; [|solve_length]. apply static_expr_mono. apply fd_static.
      * naive_solver.
Qed.

Lemma imp_heap_bij_imp_closed m σ:
  trefines (MS (imp_closed (imp_heap_bij m)) (SMFilter, initial_imp_heap_bij_state m σ, ICStart))
           (MS (imp_closed m) (SMFilter, σ, ICStart)).
Proof.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { simpl. exact (λ _
          '(σm1, (σf, σ1, (pp, ImpHeapBij bij hi, _)), σc1)
          '(σm2, σ2, σc2),
           σ1 = σ2 ∧ σc1 = σc2 ∧
             ((σc1 = ICStart ∧ σf = SMFilter ∧ pp = PPOutside ∧ σm1 = σm2 ∧ σm2 = SMFilter ∧ bij = ∅) ∨
              ( ((∃ e, σf = SMProgRecv e ∧ σm2 = SMProgRecv e) ∨ (σf = SMProg ∧ σm2 = SMProg)
                 ) ∧ σm1 = SMProg ∧ σc1 = ICRunning ∧ pp = PPInside))
                             ). }
  { split!. } { done. }
  move => {}n _ /= Hloop [[σm1 [[σf σ1] [[pp [bij hi]] ?]]] σc1] [[σm2 σ2] σc2] ?.
  destruct_all?; simplify_eq/=.
  - tstep_i. apply steps_impl_step_end => ???. invert_all' @m_step; simplify_eq/=. split!.
    tstep_s. eexists (Some (inr _)). split!. apply: steps_spec_step_end; [econs|] => ??. simplify_eq/=.
    tstep_i. apply steps_impl_step_end => ???. invert_all @m_step. split!.
    tstep_s. eexists (Some (inl _)). split!. apply: steps_spec_step_end; [econs|] => ??. simplify_eq/=.
    tstep_i => ??; simplify_eq/=.
    tstep_i. eexists ∅, (ValNum <$> vs), initial_heap_state. split!.
    1: { apply Forall2_fmap. apply Forall_Forall2_diag. by apply Forall_true. }
    apply: Hloop; [done|]. split!.
  - tstep_both. apply steps_impl_step_end => κ ??. case_match => *; simplify_eq.
    + tstep_s.  eexists (Some _). split; [done|]. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [done|]. split!.
    + tstep_s. eexists None. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [done|]. split!.
  - tstep_both. apply steps_impl_step_end => κ ??. tstep_s. eexists _. apply: steps_spec_step_end; [done|] => ??.
    case_match; tend; (split!; [done|]). 2: { apply: Hloop; [done|]. split!. }
    tstep_i => ? vs *. tstep_both => *.
    apply steps_impl_step_end => ???. invert_all @m_step => ?; simplify_eq.
    + destruct i as [? [? vs' |]]; simplify_eq/=.
      tstep_s. eexists (Some _). split!.
      apply: steps_spec_step_end; [econs|]=> /=??. destruct_all?; simplify_eq/=. tend.
      split!.
      tstep_both. apply steps_impl_step_end => ???. invert_all @m_step.
      tstep_s. eexists (None). apply: steps_spec_step_end; [econs|]=> /=??. destruct_all?; simplify_eq/=. tend.
      have ?: vs0 = ValNum <$> vs'0. {
        revert select (m_step _ _ _ _) => _.
        revert select (Forall2 _ _ _). elim: vs'0 vs0; csimpl => *; decompose_Forall_hyps => //.
        match goal with |- ?x :: _ = _ => destruct x; simplify_eq/= => // end. naive_solver.
      } subst.
      split!; [done|].
      tstep_i. apply steps_impl_step_end => ???. invert_all @m_step. split!.
      tstep_s. eexists (Some (inr _)). split!. apply: steps_spec_step_end; [econs|] => /=? ->.
      tstep_i. apply steps_impl_step_end => ???. invert_all @m_step. split!.
      tstep_s. eexists (Some (inl _)). split!. apply: steps_spec_step_end; [econs|] => /=? ->.
      tstep_i => ? <-.
      tstep_i. eexists _, [ValNum _]. split!. 1: done. 1: done. 1: econs; [done|econs]. 1: done. 1: done.
      apply: Hloop; [done|]. split!.
    + destruct i as [? []]; simplify_eq/=.
      tstep_s. eexists (Some _). split!.
      apply: steps_spec_step_end; [econs|]=> /=??. destruct_all?; simplify_eq/=.
      tstep_s. eexists None. apply: steps_spec_step_end; [econs|]=> /=??. destruct_all?; simplify_eq/=.
      destruct vs as [|v ?]; decompose_Forall_hyps. destruct v => //; simplify_eq/=.
      tend. split!.
      tstep_i. apply: steps_impl_step_end => ???. invert_all @m_step. split!.
      tstep_i. apply: steps_impl_step_end => ???. invert_all @m_step. split!.
      tstep_s. eexists (Some (inr _)). split!.
      apply: steps_spec_step_end; [econs|]=> /=? ->.
      tstep_i. apply: steps_impl_step_end => ???. invert_all @m_step.
Qed.

Lemma imp_heap_bij_trefines_implies_ctx_refines fnsi fnss :
  dom (gset _) fnsi = dom (gset _) fnss →
  trefines (MS imp_module (initial_imp_state fnsi))
           (MS (imp_heap_bij imp_module) (initial_imp_heap_bij_state imp_module (initial_imp_state fnss))) →
  imp_ctx_refines fnsi fnss.
Proof.
  move => Hdom Href C. rewrite /imp_link map_difference_union_r (map_difference_union_r fnss).
  etrans; [|apply imp_heap_bij_imp_closed].
  apply mod_seq_map_trefines. { apply _. } { apply _. }
  etrans. { apply imp_link_refines_prod. apply map_disjoint_difference_r'. }
  etrans. { apply: imp_prod_trefines. 1: done. 1: apply imp_heap_bij_imp_refl. }
  etrans. { apply imp_heap_bij_combine; apply _. }
  apply: mod_prepost_trefines.
  etrans. 2: { apply imp_prod_refines_link. apply map_disjoint_difference_r'. }
  rewrite !dom_difference_L Hdom.
  erewrite map_difference_eq_dom_L => //.
  apply _.
Qed.

Module imp_heap_bij_example.

Local Open Scope Z_scope.

Definition bij_alloc : fndef := {|
  fd_args := [];
  fd_body := (LetE "tmp" (Alloc (Val 1))
             (LetE "_" (Store (Var "tmp") (Val 1))
             (LetE "_" (Call "ext" [])
             (LetE "res" (Load (Var "tmp"))
             (LetE "_" (Free (Var "tmp"))
             (Var "res"))))));
  fd_static := I;
|}.

Definition bij_alloc_opt : fndef := {|
  fd_args := [];
  fd_body := (LetE "_" (Call "ext" [])
             (Val 1));
  fd_static := I;
|}.

Lemma bij_alloc_opt_refines :
  trefines (MS imp_module (initial_imp_state (<["f" := bij_alloc_opt]> ∅)))
           (MS (imp_heap_bij imp_module) (initial_imp_heap_bij_state imp_module
                                            (initial_imp_state (<["f" := bij_alloc]> ∅)))).
Proof.
  epose (R := λ (b : bool) '(ImpHeapBij bij1 h1, _) '(ImpHeapBij bij2 h2, _),
          hb_prog bij1 ⊆ hb_prog bij2 ∧ heap_preserved (hb_prog bij1) h1 h2).
  apply: (imp_prepost_proof R); unfold R in *.
  { constructor. { move => [[??]?]. naive_solver. }
    { move => [[??]?] [[??]?] [[??]?] [??] [??]. split; [by etrans|]. etrans; [done|].
      by apply: heap_preserved_mono. } }
  { move => [??] ? [??] ?. naive_solver. }
  move => n K1 K2 f fn1 vs1 h0 [bij0 ?] ? ?.
  rewrite !lookup_insert_Some => ?; destruct_all?; simplify_map_eq/=.
  move => bij1 ? h1 *. split!. move => ?. split!; [solve_length|].
  move => Hcall Hret.
  pose (l := (heap_fresh (hb_provs_right bij1) h1)).
  have Hf := heap_fresh_not_in (hb_provs_right bij1) h1.
  tstep_s. eexists l. split!. { apply heap_fresh_is_fresh. }
  move => *; simplify_eq.
  tstep_s. tstep_s. move => ? [<-] ?.
  tstep_s.
  apply: (Hcall _ _ ([LetECtx _ _]) ([LetECtx _ _])); [done|..].
  1, 2: by simplify_map_eq. 1,2: by econs.
  unshelve eexists (heap_bij_add_prog l.1 bij1 _), []. { apply Hf. }
  split!.
  { apply heap_in_bij_update_r; [|set_solver]. apply heap_in_bij_alloc_r; [done|set_solver]. }
  { apply heap_preserved_update_r; [|set_solver]. apply heap_preserved_alloc_r; [set_solver|done]. }
  { instantiate (1:=True%I). iIntros "? !>". done. }
  { bij_solver. }
  { etrans; [apply: heap_preserved_mono; [done|bij_solver]|].
    apply heap_preserved_update_r; [|bij_solver].
    apply heap_preserved_alloc_r; [bij_solver|done]. }
  move => ? h2 [bij2 h3] ? [??] bij4 ? h4 *. decompose_Forall_hyps.
  split!.
  tstep_i.
  tstep_s.
  tstep_s.
  move => ?? [<-] /heap_preserved_lookup_r Hlookup.
  efeed pose proof Hlookup as Hlookup'.
  { etrans. 2: apply: heap_preserved_mono; [done|]. 1: done. bij_solver. }
  { bij_solver. } simplify_map_eq/=.
  tstep_s.
  tstep_s => *. simplify_eq.
  tstep_s.
  apply: Hret; [done|].
  eexists _, [ValNum 1]. split!. done. all: split!. 1: by econs.
  { apply heap_in_bij_free_r; [done|]. have ? := hb_disj_prog bij4. bij_solver. }
  { apply: heap_preserved_free_r; [|done]. have ? := hb_disj_priv bij4. bij_solver. }
  { instantiate (1:=True%I). iIntros "? !>". done. }
  1: bij_solver.
  { apply: heap_preserved_free_r. { have ? := hb_disj_priv bij4. bij_solver. }
    apply: heap_preserved_mono. 1: etrans; [done|]. 2: bij_solver.
    etrans. 2: apply: heap_preserved_mono; [done|bij_solver].
    etrans. 2: apply: heap_preserved_mono; [done|bij_solver].
    apply heap_preserved_update_r; [|bij_solver].
    apply heap_preserved_alloc_r; [bij_solver|done]. }
Qed.

Lemma bij_alloc_ctx_refines :
  imp_ctx_refines (<["f" := bij_alloc_opt]> ∅) (<["f" := bij_alloc]> ∅).
Proof.
  apply: imp_heap_bij_trefines_implies_ctx_refines. { set_solver. }
  apply bij_alloc_opt_refines.
Qed.
End imp_heap_bij_example.
*)