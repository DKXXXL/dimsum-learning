Require Export iris.algebra.lib.gmap_view.
Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.filter.
Require Import refframe.product.
Require Import refframe.seq_product.
Require Import refframe.link.
Require Import refframe.prepost.
Require Import refframe.proof_techniques.
Require Import refframe.imp.

Set Default Proof Using "Type".


(* TODO: Allow also ownership of the outer heap, probably by adding a
   second gmap prov (option Z → option val) and adding an new
   heap_preserved and making sure that if hb_bij !! p2 = Some p1 then
   we have the persistent fragment {[ p1 := None ]} *)

(** * camera definition *)
Inductive heap_bij_elem :=
| HBShared (p : prov) | HBConstant (h : gmap loc val).
Canonical Structure heap_bij_elemO := leibnizO heap_bij_elem.
Inductive heap_bij_priv_elem := HBIConstant (h : gmap loc val).
Canonical Structure heap_bij_priv_elemO := leibnizO heap_bij_priv_elem.

Definition heap_bijUR : ucmra :=
  prodUR (gmap_viewUR prov heap_bij_elemO) (gmap_viewUR prov heap_bij_priv_elemO).

Definition heap_bijUR_s_inj (r : (gmap_viewUR prov heap_bij_elemO)) : heap_bijUR := (r, ε).
Definition heap_bijUR_i_inj (r : (gmap_viewUR prov heap_bij_priv_elemO)) : heap_bijUR := (ε, r).


(** * imp_heap_bij_own *)
(*

                                   e_in'    e_out
                                  ------> m ------
                                 /                \
                         e_in    |                v       e_out'
IMP_HEAP_BIJ [ m ]     : ---> PRE e_in         POST e_out ------->



*)

Record heap_bij := HeapBij {
  hb_bij : gmap prov heap_bij_elem;
  hb_priv_i : gmap prov heap_bij_priv_elem;
  hb_disj ps pi:
   hb_bij !! ps = Some (HBShared pi) →
   hb_priv_i !! pi = None;
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

Global Program Instance heap_bij_empty : Empty heap_bij := HeapBij ∅ ∅ _ _.
Solve Obligations with set_solver.

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

(** hb_shared_i *)
Definition hb_shared_i (bij : heap_bij) : gset prov :=
  list_to_set (omap (λ x, if x.2 is HBShared p then Some p else None) (map_to_list (hb_bij bij))).
Global Typeclasses Opaque hb_shared_i.

Lemma elem_of_hb_shared_i bij p1:
  p1 ∈ hb_shared_i bij ↔ ∃ p2, hb_bij bij !! p2 = Some (HBShared p1).
Proof.
  rewrite /hb_shared_i elem_of_list_to_set elem_of_list_omap.
  setoid_rewrite elem_of_map_to_list'.
  split.
  - move => [[??] /= [??]]. case_match; simplify_eq/=. naive_solver.
  - move => [??]. by eexists (_, _).
Qed.

(** hb_priv_s *)
Definition hb_priv_s (bij : heap_bij) : gmap prov heap_bij_priv_elem :=
  omap (λ v, if v is HBConstant h then Some (HBIConstant h) else None) (hb_bij bij).

Lemma hb_priv_s_lookup_None bij ps :
  hb_priv_s bij !! ps = None ↔ ∀ h, hb_bij bij !! ps = Some (HBConstant h) → False.
Proof. rewrite lookup_omap. destruct (hb_bij bij !! ps) => //=. case_match; naive_solver. Qed.

Lemma hb_priv_s_lookup_Some bij ps h :
  hb_priv_s bij !! ps = Some (HBIConstant h) ↔ hb_bij bij !! ps = Some (HBConstant h).
Proof.
  rewrite lookup_omap_Some.
  split.
  - move => [?[??]]. case_match => //; naive_solver.
  - move => ?. eexists _. split; [|done]. done.
Qed.

(** hb_provs_i *)
(* hb_provs_s is directly written as [dom _ (hb_bij bij)] *)
Definition hb_provs_i (bij : heap_bij) : gset prov :=
  dom _ (hb_priv_i bij) ∪ hb_shared_i bij.

Lemma elem_of_hb_provs_i bij pi :
  pi ∈ hb_provs_i bij ↔ (∃ h, hb_priv_i bij !! pi = Some h) ∨ ∃ ps, hb_bij bij !! ps = Some (HBShared pi).
Proof. unfold hb_provs_i. rewrite elem_of_union elem_of_dom elem_of_hb_shared_i. naive_solver. Qed.

(** heap_bij constructors *)
Program Definition heap_bij_share (p1 p2 : prov) (bij : heap_bij)
        (H : p1 ∉ hb_provs_i bij) :=
  HeapBij (<[p2 := HBShared p1]> (hb_bij bij)) (hb_priv_i bij) _ _.
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

Program Definition heap_bij_update_const_s (p : prov) (h : gmap loc val) (bij : heap_bij) :=
  HeapBij (<[p := HBConstant h]> (hb_bij bij)) (hb_priv_i bij) _ _.
Next Obligation.
  move => ?????.
  rewrite !lookup_insert_Some => ?. destruct_all?; simplify_eq/= => //. by apply: hb_disj.
Qed.
Next Obligation.
  move => ??????.
  rewrite !lookup_insert_Some => ??. destruct_all?; simplify_eq/= => //. by apply: hb_iff.
Qed.

Program Definition heap_bij_delete_s (p : prov) (bij : heap_bij) :=
  HeapBij (delete p (hb_bij bij)) (hb_priv_i bij) _ _.
Next Obligation.
  move => ????.
  rewrite !lookup_delete_Some => ?. destruct_all?; simplify_eq/= => //. by apply: hb_disj.
Qed.
Next Obligation.
  move => ?????.
  rewrite !lookup_delete_Some => ??. destruct_all?; simplify_eq/= => //. by apply: hb_iff.
Qed.

Lemma hb_privs_s_share pi ps bij H:
  hb_priv_s (heap_bij_share pi ps bij H) = delete ps (hb_priv_s bij).
Proof.
  apply map_eq => ?. apply option_eq => -[?]. rewrite !hb_priv_s_lookup_Some/=.
  rewrite lookup_delete_Some hb_priv_s_lookup_Some lookup_insert_Some.
  naive_solver.
Qed.

Lemma hb_priv_s_update_const_s bij ps h :
  hb_priv_s (heap_bij_update_const_s ps h bij) = <[ps := HBIConstant h]> (hb_priv_s bij).
Proof.
  apply map_eq => ?. apply option_eq => -[?]. rewrite !hb_priv_s_lookup_Some/=.
  rewrite !lookup_insert_Some hb_priv_s_lookup_Some/=. naive_solver.
Qed.

Lemma hb_provs_i_share p1 p2 bij H:
  hb_provs_i (heap_bij_share p1 p2 bij H) ⊆ {[p1]} ∪ hb_provs_i bij.
Proof.
  move => ?. rewrite elem_of_union !elem_of_hb_provs_i /=.
  setoid_rewrite lookup_insert_Some at 1. set_solver.
Qed.

Lemma hb_provs_i_update_const_s p h bij:
  hb_provs_i (heap_bij_update_const_s p h bij) ⊆ hb_provs_i bij.
Proof.
  move => ?. rewrite !elem_of_hb_provs_i /=.
  setoid_rewrite lookup_insert_Some. naive_solver.
Qed.

(** ghost theory *)
Definition heap_bij_auth (bij : heap_bij) : uPred heap_bijUR :=
  uPred_ownM (heap_bijUR_s_inj $ gmap_view_auth (DfracOwn 1) (hb_bij bij)) ∗
  uPred_ownM (heap_bijUR_i_inj $ gmap_view_auth (DfracOwn 1) (hb_priv_i bij)).

Definition heap_bij_shared (p1 p2 : prov) : uPred (heap_bijUR) :=
  uPred_ownM (heap_bijUR_s_inj $ gmap_view_frag p2 DfracDiscarded (HBShared p1)).

Definition heap_bij_const_s (p : prov) (h : gmap loc val) : uPred (heap_bijUR) :=
  uPred_ownM (heap_bijUR_s_inj $ gmap_view_frag p (DfracOwn 1) (HBConstant h)).

Definition heap_bij_const_i (p : prov) (h : gmap loc val) : uPred (heap_bijUR) :=
  uPred_ownM (heap_bijUR_i_inj $ gmap_view_frag p (DfracOwn 1) (HBIConstant h)).

Lemma heap_bij_alloc_shared bij p1 p2 H:
  p2 ∉ dom (gset _) (hb_bij bij) →
  heap_bij_auth bij ==∗ heap_bij_auth (heap_bij_share p1 p2 bij H) ∗ heap_bij_shared p1 p2.
Proof.
  iIntros (?) "[? $]". iStopProof. rewrite -uPred.ownM_op. apply uPred.bupd_ownM_update.
  rewrite -pair_op_1. apply prod_update; [|done].
  apply gmap_view_alloc; [|done]. by apply not_elem_of_dom.
Qed.

Lemma heap_bij_shared_lookup p1 p2 bij :
  heap_bij_auth bij -∗
  heap_bij_shared p1 p2 -∗
  ⌜hb_bij bij !! p2 = Some (HBShared p1)⌝.
Proof.
  iIntros "[? _]". iStopProof.
  apply bi.wand_intro_r. rewrite -uPred.ownM_op -pair_op_1.
  etrans; [apply uPred.ownM_valid|]. iPureIntro. move => [/gmap_view_both_valid_L? ?]. naive_solver.
Qed.

Lemma heap_bij_alloc_const_s bij p h:
  p ∉ dom (gset _) (hb_bij bij) →
  heap_bij_auth bij ==∗ heap_bij_auth (heap_bij_update_const_s p h bij) ∗ heap_bij_const_s p h.
Proof.
  iIntros (?) "[? $]". iStopProof. rewrite -uPred.ownM_op. apply uPred.bupd_ownM_update.
  rewrite -pair_op_1. apply prod_update; [|done].
  apply gmap_view_alloc; [|done]. by apply not_elem_of_dom.
Qed.

Lemma heap_bij_const_s_lookup p f bij :
  heap_bij_auth bij -∗
  heap_bij_const_s p f -∗
  ⌜hb_bij bij !! p = Some (HBConstant f)⌝.
Proof.
  iIntros "[? _]". iStopProof.
  apply bi.wand_intro_r. rewrite -uPred.ownM_op.
  etrans; [apply uPred.ownM_valid|]. iPureIntro. move => [/gmap_view_both_valid_L??]. naive_solver.
Qed.

Lemma heap_bij_frag_update_const_s bij p f h:
  heap_bij_auth bij ∗ heap_bij_const_s p f ==∗
  heap_bij_auth (heap_bij_update_const_s p h bij) ∗ heap_bij_const_s p h.
Proof.
  iIntros "[[? $] ?]". iStopProof.
  rewrite -!uPred.ownM_op. apply uPred.bupd_ownM_update.
  rewrite -!pair_op_1. apply prod_update; [|done].
  apply gmap_view_update.
Qed.

(** ** val_in_bij *)
Definition val_in_bij (v1 v2 : val) : uPred heap_bijUR :=
  match v1, v2 with
  | ValNum n1, ValNum n2 => ⌜n1 = n2⌝
  | ValBool b1, ValBool b2 => ⌜b1 = b2⌝
  | ValLoc l1, ValLoc l2 => ⌜l1.2 = l2.2⌝ ∗ heap_bij_shared l1.1 l2.1
  | _, _ => False
  end.

Global Instance val_in_bij_Persistent v1 v2 : Persistent (val_in_bij v1 v2).
Proof. destruct v1, v2 => /=; apply _. Qed.

Lemma big_sepL2_ValNum_inv_r vl zl :
  ([∗ list] y1;y2 ∈ vl;(ValNum <$> zl), val_in_bij y1 y2) -∗
  ⌜vl = (ValNum <$> zl)⌝.
Proof.
  iIntros "Hvl".
  iInduction vl as [|v] "IH" forall (zl); csimpl.
  { iDestruct (big_sepL2_nil_inv_l with "[$]") as %->. done. }
  iDestruct (big_sepL2_cons_inv_l with "[$]") as (???) "[Hv ?]"; subst.
  destruct zl; simplify_eq/=. destruct v => //=. iDestruct "Hv" as %?.
  iDestruct ("IH" with "[$]") as %?.
  naive_solver.
Qed.

(** ** expr_in_bij *)
Fixpoint expr_in_bij (e1 e2 : expr) {struct e1} : uPred heap_bijUR :=
  match e1, e2 with
  | Var v, Var v' => ⌜v = v'⌝
  | Val v, Val v' => val_in_bij v v'
  | BinOp e1 o e2, BinOp e1' o' e2' => ⌜o = o'⌝ ∗ expr_in_bij e1 e1' ∗ expr_in_bij e2 e2'
  | Load e, Load e' => expr_in_bij e e'
  | Store e1 e2, Store e1' e2' => expr_in_bij e1 e1' ∗ expr_in_bij e2 e2'
  | Alloc e, Alloc e' => expr_in_bij e e'
  | Free e, Free e' => expr_in_bij e e'
  | If e e1 e2, If e' e1' e2' => expr_in_bij e e' ∗ expr_in_bij e1 e1' ∗ expr_in_bij e2 e2'
  | LetE v e1 e2, LetE v' e1' e2' => ⌜v = v'⌝ ∗ expr_in_bij e1 e1' ∗ expr_in_bij e2 e2'
  | Call f args, Call f' args' => ⌜f = f'⌝ ∗ ⌜length args = length args'⌝ ∗
        [∗] zip_with expr_in_bij args args'
  | UbE, UbE => True
  | ReturnExt b e, ReturnExt b' e' => ⌜b = b'⌝ ∗ expr_in_bij e e'
  | Waiting b, Waiting b' => ⌜b = b'⌝
  | _, _ => False
  end.

Global Instance expr_in_bij_Persistent e1 e2 : Persistent (expr_in_bij e1 e2).
Proof.
  revert e2. induction e1 => e2; destruct e2 => /=; try apply _.
  apply bi.sep_persistent; [apply _ |].
  apply bi.sep_persistent; [apply _ |].
  apply big_sepL_persistent_id. apply TCForall_Forall.
  apply: Forall_zip_with_fst; [done|]. apply Forall_forall.
  naive_solver.
Qed.

Lemma big_sepL2_Val_inv_l vl el :
  ([∗ list] y1;y2 ∈ (Val <$> vl);el, expr_in_bij y1 y2) -∗
  ∃ vl', ⌜el = Val <$> vl'⌝ ∗ [∗ list] y1;y2 ∈ vl;vl', val_in_bij y1 y2.
Proof.
  iIntros "Hel".
  iInduction vl as [] "IH" forall (el); csimpl.
  { iDestruct (big_sepL2_nil_inv_l with "[$]") as %->. iExists []. by iSplit. }
  iDestruct (big_sepL2_cons_inv_l with "[$]") as (???) "[??]"; subst.
  iDestruct ("IH" with "[$]") as (??) "?" => /=. subst. case_match => //.
  iExists (_::_); csimpl. iSplit; [done|]. iFrame.
Qed.

(* Lemma Forall2_bij_val_inv_l r vl el : *)
(*   Forall2 (expr_in_bij r) (Val <$> vl) el → *)
(*   ∃ vl', el = Val <$> vl' ∧ Forall2 (val_in_bij r) vl vl'. *)
(* Proof. *)
(*   elim: vl el; csimpl. { move => ? /Forall2_nil_inv_l->. by eexists []. } *)
(*   move => ?? IH ? /(Forall2_cons_inv_l _ _)[v' [?[?[/IH[?[??]]?]]]]; subst. *)
(*   destruct v' => //. eexists (_::_). split; [done|]. by econs. *)
(* Qed. *)

(* Lemma Forall2_bij_val_inv_r r vl el : *)
(*   Forall2 (expr_in_bij r) el (Val <$> vl) → *)
(*   ∃ vl', el = Val <$> vl' ∧ Forall2 (val_in_bij r) vl' vl. *)
(* Proof. *)
(*   elim: vl el; csimpl. { move => ? /Forall2_nil_inv_r->. by eexists []. } *)
(*   move => ?? IH ? /(Forall2_cons_inv_r _ _ _ _) [v' [?[?[/IH[?[??]] ?]]]]; subst. *)
(*   destruct v' => //. eexists (_::_). split; [done|]. by econs. *)
(* Qed. *)

Lemma expr_in_bij_subst x v e v' e':
  expr_in_bij e e' -∗
  val_in_bij v v' -∗
  expr_in_bij (subst x v e) (subst x v' e').
Proof.
  revert e'. induction e; iIntros (e') "#He #Hv"; destruct e' => //=; iDestruct!.
  all: repeat iSplit => //.
  all: rewrite ?fmap_length //; try case_bool_decide => //.
  all: try by [iApply IHe]; try by [iApply IHe1]; try by [iApply IHe2]; try by [iApply IHe3].
  rewrite !big_sepL_zip_with_same_length ?fmap_length //. rewrite big_sepL2_fmap_l big_sepL2_fmap_r.
  iApply big_sepL2_impl; [done|].
  iIntros "!>" (?? ???) "#?".
  revert select (Forall _ _) => /Forall_forall IH. iApply IH => //. apply elem_of_list_lookup.
  naive_solver.
Qed.

Lemma expr_in_bij_subst_l xs vs e vs' e':
  length xs = length vs →
  expr_in_bij e e' -∗
  ([∗ list] v;v'∈vs;vs', val_in_bij v v') -∗
  expr_in_bij (subst_l xs vs e) (subst_l xs vs' e').
Proof.
  iIntros (Hlen) "He Hv".
  iInduction xs as [] "IH" forall(vs vs' e e' Hlen); destruct vs, vs'; simplify_eq/= => //.
  iDestruct "Hv" as "[Hv Hvs]".
  iApply ("IH" with "[//] [He Hv] Hvs").
  iApply (expr_in_bij_subst with "He Hv").
Qed.

Lemma expr_in_bij_static e:
  static_expr false e →
  ⊢ expr_in_bij e e.
Proof.
  elim: e => //=; try naive_solver. { case => //= *; by iPureIntro. }
  move => ?? IH Hb. iSplit; [done|]. iSplit; [done|]. iStopProof.
  elim: IH Hb => //= ?? Hs ? IH ?. iIntros "_". iSplit.
  - iApply Hs; naive_solver.
  - iApply IH; naive_solver.
Qed.

(** ** ectx_in_bij *)
Definition ectx_item_in_bij (Ki Ki' : expr_ectx) : uPred heap_bijUR :=
  match Ki, Ki' with
  | BinOpLCtx op e2, BinOpLCtx op' e2' => ⌜op = op'⌝ ∗ expr_in_bij e2 e2'
  | BinOpRCtx v1 op, BinOpRCtx v1' op' => ⌜op = op'⌝ ∗ val_in_bij v1 v1'
  | LoadCtx, LoadCtx => True
  | StoreLCtx e2, StoreLCtx e2' => expr_in_bij e2 e2'
  | StoreRCtx v1, StoreRCtx v1' => val_in_bij v1 v1'
  | AllocCtx, AllocCtx => True
  | FreeCtx, FreeCtx => True
  | IfCtx e2 e3, IfCtx e2' e3' => expr_in_bij e2 e2' ∗ expr_in_bij e3 e3'
  | LetECtx v e2, LetECtx v' e2' => ⌜v = v'⌝ ∗ expr_in_bij e2 e2'
  | CallCtx f vl el, CallCtx f' vl' el' =>
      ⌜f = f'⌝ ∗ ([∗ list] v;v'∈vl;vl', val_in_bij v v') ∗ [∗ list] e;e'∈el;el', expr_in_bij e e'
  | ReturnExtCtx b, ReturnExtCtx b' => ⌜b = b'⌝
  | _, _ => False
  end.

Definition ectx_in_bij (K1 K2 : list expr_ectx) : uPred heap_bijUR :=
  [∗ list] Ki1;Ki2∈K1;K2, ectx_item_in_bij Ki1 Ki2.

Global Instance ectx_item_in_bij_persistent Ki Ki' :
  Persistent (ectx_item_in_bij Ki Ki').
Proof. destruct Ki, Ki' => /=; apply _. Qed.

Global Instance ectx_in_bij_persistent K K' :
  Persistent (ectx_in_bij K K').
Proof. destruct K, K' => /=; apply _. Qed.

Lemma expr_in_bij_fill_item_2 K1 K2 e1 e2 :
  ectx_item_in_bij K1 K2 -∗
  expr_in_bij e1 e2 -∗
  expr_in_bij (expr_fill_item K1 e1) (expr_fill_item K2 e2).
Proof.
  iIntros "??".
  destruct K1, K2 => //; try by iDestruct!; iFrame => //.
  iDestruct select (ectx_item_in_bij _ _) as (?) "[#Hvl #Hel]".
  iDestruct (big_sepL2_length with "Hvl") as %?.
  iDestruct (big_sepL2_length with "Hel") as %?.
  iSplit!. { rewrite !app_length !fmap_length /=. lia. }
  rewrite big_sepL_zip_with_same_length. 2: { rewrite !app_length !fmap_length /=. lia. }
  iApply big_sepL2_app => /=; iFrame "∗#".
  rewrite big_sepL2_fmap_l big_sepL2_fmap_r /=. iApply "Hvl".
Qed.

Lemma expr_in_bij_fill_2 K1 K2 e1 e2 :
  ectx_in_bij K1 K2 -∗
  expr_in_bij e1 e2 -∗
  expr_in_bij (expr_fill K1 e1) (expr_fill K2 e2).
Proof.
  unfold ectx_in_bij. iIntros "H1 H2". iInduction K1 as [] "IH" forall (K2 e1 e2).
  { iDestruct (big_sepL2_nil_inv_l with "[$]") as %->. iFrame. }
  iDestruct (big_sepL2_cons_inv_l with "[$]") as (???) "[??]"; simplify_eq/=.
  iApply ("IH" with "[$]").
  iApply (expr_in_bij_fill_item_2 with "[$] [$]").
Qed.

Lemma expr_in_bij_fill_item_l Ki e1 e2 :
  expr_in_bij (expr_fill_item Ki e1) e2 -∗
  ∃ Ki' e', ⌜e2 = expr_fill_item Ki' e'⌝ ∗ ectx_item_in_bij Ki Ki' ∗ expr_in_bij e1 e'.
Proof.
  iIntros "He".
  destruct Ki, e2 => //=; iDestruct!; destruct_all?; simplify_eq; try case_match => //; simplify_eq. 10: {
    rewrite big_sepL_zip_with_same_length //.
    iDestruct (big_sepL2_app_inv_l with "[$]") as (???) "[Hv1 Hel]".
    iDestruct (big_sepL2_cons_inv_l with "[$]") as (???) "[He Hel]". subst.
    iDestruct (big_sepL2_Val_inv_l with "[$]") as (??) "Hvl'"; subst.
    iExists (CallCtx _ _ _), _.
    iSplit!; [done|..]; iFrame.
  }
  all: (unshelve iExists _); [econs; shelve| naive_solver].
Qed.

Lemma expr_in_bij_fill_l K e1 e2 :
  expr_in_bij (expr_fill K e1) e2 -∗
  ∃ K' e', ⌜e2 = expr_fill K' e'⌝ ∗ ectx_in_bij K K' ∗ expr_in_bij e1 e'.
Proof.
  elim: K e1 e2 => /=. { iIntros. iExists []. iSplit!. unfold ectx_in_bij. done. }
  move => Ki K IH e1 e2. iIntros "He".
  iDestruct (IH with "He") as (???) "[HK He]"; subst.
  iDestruct (expr_in_bij_fill_item_l with "[$]") as (???) "[??]"; subst.
  iExists (_::_). iSplit! => //; iFrame.
Qed.

Lemma eval_binop_bij o v1 v2 v1' v2' v:
  eval_binop o v1 v2 = Some v →
  val_in_bij v1' v1 -∗
  val_in_bij v2' v2 -∗
  ∃ v', ⌜eval_binop o v1' v2' = Some v'⌝ ∗ val_in_bij v' v.
Proof.
  iIntros (?) "??".
  destruct o, v1, v2, v1', v2' => //= *; iDestruct!; iSplit!.
  lia.
Qed.

(** *** heap_in_bij *)
Definition heap_in_bij (bij : heap_bij) (h h' : heap_state) : uPred heap_bijUR :=
  ∀ p1 p2 o,
  ⌜hb_bij bij !! p2 = Some (HBShared p1)⌝ -∗

  ⌜(is_Some (h.(h_heap) !! (p1, o)) ↔ is_Some (h'.(h_heap) !! (p2, o)))⌝
  ∗
  ∀ v1 v2,
  ⌜h.(h_heap)  !! (p1, o) = Some v1⌝ -∗
  ⌜h'.(h_heap) !! (p2, o) = Some v2⌝ -∗
  val_in_bij v1 v2.

Global Instance heap_in_bij_Persitent bij h h': Persistent (heap_in_bij bij h h').
Proof. apply _. Qed.

Lemma heap_in_bij_mono_bij bij bij' h h':
  (∀ p1 p2, hb_bij bij' !! p2 = Some (HBShared p1) → hb_bij bij !! p2 = Some (HBShared p1)) →
  heap_in_bij bij  h h' -∗
  heap_in_bij bij' h h'.
Proof. iIntros (?) "Hh". iIntros (????). iApply "Hh". iPureIntro. naive_solver. Qed.

Lemma heap_in_bij_alive bij h1 h2 l1 l2:
  heap_alive h2 l2 →
  hb_bij bij !! l2.1 = Some (HBShared l1.1) →
  l1.2 = l2.2 →
  heap_in_bij bij h1 h2 -∗
  ⌜heap_alive h1 l1⌝.
Proof.
  iIntros (???) "Hh". destruct l1 as [p1 ?], l2 as [p2 o]; simplify_eq/=.
  unfold heap_in_bij, heap_alive in *. iDestruct ("Hh" with "[//]") as "[% ?]".
  iPureIntro. naive_solver.
Qed.

Lemma heap_in_bij_lookup bij h1 h2 l1 l2 v:
  h_heap h2 !! l2 = Some v →
  hb_bij bij !! l2.1 = Some (HBShared l1.1) →
  l1.2 = l2.2 →
  heap_in_bij bij h1 h2 -∗
  ∃ v', ⌜h_heap h1 !! l1 = Some v'⌝ ∗ val_in_bij v' v.
Proof.
  iIntros (???) "Hh". destruct l1 as [p1 ?], l2 as [p2 o]; simplify_eq/=.
  iDestruct ("Hh" with "[//]") as "[%Hx Hv]". move: Hx => [_ Hx].
  have [??]:= Hx ltac:(done). iSplit!. by iApply "Hv".
Qed.

Lemma heap_in_bij_update bij h1 h2 l1 l2 v1 v2:
  hb_bij bij !! l2.1 = Some (HBShared l1.1) →
  l1.2 = l2.2 →
  heap_in_bij bij h1 h2 -∗
  val_in_bij v1 v2 -∗
  heap_in_bij bij (heap_update h1 l1 v1) (heap_update h2 l2 v2).
Proof.
  iIntros (??) "Hh Hv". destruct l1 as [p1 ?], l2 as [p2 o]; simplify_eq/=.
  iIntros (p1' p2' o' ?) => /=. iDestruct ("Hh" with "[//]") as "[%Hh1 Hh2]". iSplit.
  - iPureIntro. by rewrite !lookup_alter_is_Some.
  - iIntros (???%lookup_alter_Some?%lookup_alter_Some); destruct_all?; simplify_bij => //.
    by iApply "Hh2".
Qed.

Lemma heap_in_bij_update_r bij h1 h2 l2 v2:
  (∀ p, hb_bij bij !! l2.1 = Some (HBShared p) → False) →
  heap_in_bij bij h1 h2 -∗
  heap_in_bij bij h1 (heap_update h2 l2 v2).
Proof.
  iIntros (?) "Hh". iIntros (????).
  rewrite !lookup_alter_ne. 1: by iApply "Hh".
  naive_solver.
Qed.

Lemma heap_in_bij_alloc l1 l2 hi hs n bij H:
  heap_is_fresh hi l1 →
  heap_is_fresh hs l2 →
  heap_in_bij bij hi hs -∗
  heap_in_bij (heap_bij_share l1.1 l2.1 bij H) (heap_alloc hi l1 n) (heap_alloc hs l2 n).
Proof.
  iIntros ([Hi1 ?] [Hi2 ?]) "Hh". iIntros (p1 p2 o) => /=. iIntros ([[??]|[??]]%lookup_insert_Some); simplify_eq.
  - destruct l1 as [p1 ?], l2 as [p2 ?]; simplify_eq/=.
    rewrite !lookup_union_l'.
    2: { apply eq_None_ne_Some => ??. apply Hi2. by apply: (heap_wf _ (_, _)). }
    2: { apply eq_None_ne_Some => ??. apply Hi1. by apply: (heap_wf _ (_, _)). }
    iSplit.
    + iPureIntro. rewrite !list_to_map_lookup_is_Some. f_equiv => ?. rewrite !elem_of_list_fmap.
      f_equiv => ?. naive_solver.
    + iIntros (?? [?[??]]%elem_of_list_to_map_2%elem_of_list_fmap).
      iIntros ([?[??]]%elem_of_list_to_map_2%elem_of_list_fmap).
      by simplify_eq.
  - have ? : p1 ≠ l1.1. { contradict H. apply elem_of_hb_provs_i. naive_solver. }
    iDestruct ("Hh" with "[//]") as "[Hh1 Hh2]".
    rewrite !lookup_union_r. 1: by iSplit.
    all: apply not_elem_of_list_to_map_1;
        move => /elem_of_list_fmap[[[??]?] [?/elem_of_list_fmap[?[??]]]]; simplify_eq/=.
Qed.

Lemma heap_in_bij_alloc_r l2 hi hs n bij:
  (∀ p, hb_bij bij !! l2.1 = Some (HBShared p) → False) →
  heap_in_bij bij hi hs -∗
  heap_in_bij bij hi (heap_alloc hs l2 n).
Proof.
  iIntros (?) "Hh". iIntros (????). rewrite lookup_union_r. 1: by iApply "Hh".
  apply not_elem_of_list_to_map_1.
  move => /elem_of_list_fmap[[??][?/elem_of_list_fmap[?[??]]]]; simplify_eq/=.
  naive_solver.
Qed.

Lemma heap_in_bij_free hi hs l1 l2 bij:
  hb_bij bij !! l2.1 = Some (HBShared l1.1) →
  heap_in_bij bij hi hs -∗
  heap_in_bij bij (heap_free hi l1) (heap_free hs l2).
Proof.
  iIntros (?) "Hh". iIntros (p1 p2 o ?).
  iDestruct ("Hh" $! p1 p2 o with "[//]") as "[%Hh1 Hh2]".
  iSplit => /=.
  - iPureIntro. rewrite !map_filter_lookup /=. destruct (h_heap hi !! (p1, o)), (h_heap hs !! (p2, o)) => //=.
    all: repeat case_option_guard => //; simplify_bij; naive_solver.
  - iIntros (??). rewrite !map_filter_lookup. iIntros ([?[??]]%bind_Some [?[??]]%bind_Some).
    repeat case_option_guard => //; simplify_bij; try naive_solver.
    by iApply "Hh2".
Qed.

Lemma heap_in_bij_free_r l2 hi hs bij:
  (∀ p, hb_bij bij !! l2.1 = Some (HBShared p) → False) →
  heap_in_bij bij hi hs -∗
  heap_in_bij bij hi (heap_free hs l2).
Proof.
  iIntros (?) "Hh". iIntros (????) => /=. rewrite map_filter_lookup_true. 1: by iApply "Hh".
  naive_solver.
Qed.

(** *** heap_preserved *)
Definition heap_preserved (m : gmap prov heap_bij_priv_elem) (h : heap_state) :=
  ∀ l h', m !! l.1 = Some (HBIConstant h') → h.(h_heap) !! l = h' !! l.

Lemma heap_preserved_mono m1 m2 h:
  heap_preserved m1 h →
  m2 ⊆ m1 →
  heap_preserved m2 h.
Proof. unfold heap_preserved => Hp Hsub ???. apply: Hp. by eapply map_subseteq_spec. Qed.

Lemma heap_preserved_lookup_r m h h' l v:
  h_heap h !! l = v →
  heap_preserved m h →
  m !! l.1 = Some (HBIConstant h') →
  h' !! l = v.
Proof. move => Hl Hp ?. by rewrite -Hp. Qed.

Lemma heap_preserved_update l v h m:
  heap_preserved m h →
  m !! l.1 = None →
  heap_preserved m (heap_update h l v).
Proof.
  move => Hp ???? /=. rewrite lookup_alter_ne; [by eapply Hp|naive_solver].
Qed.

Lemma heap_preserved_alloc l n h m:
  heap_preserved m h →
  m !! l.1 = None →
  heap_preserved m (heap_alloc h l n).
Proof.
  move => Hp ? l' f /= ?. rewrite lookup_union_r; [by apply Hp|].
  apply not_elem_of_list_to_map_1 => /elem_of_list_fmap[[[??]?] [?/elem_of_list_fmap[?[??]]]]; simplify_eq/=.
Qed.

Lemma heap_preserved_free l h m:
  heap_preserved m h →
  m !! l.1 = None →
  heap_preserved m (heap_free h l).
Proof.
  move => Hp ? l' f ? /=. rewrite map_filter_lookup. etrans; [|by eapply Hp].
  destruct (h_heap h !! l') => //=. case_option_guard => //. destruct l, l'; naive_solver.
Qed.

(* Lemma heap_preserved_share p1 p2 bij H h: *)
(*   heap_preserved bij h → *)
(*   heap_preserved (heap_bij_share p1 p2 bij H) h. *)
(* Proof. move => Hp l f /= /lookup_insert_Some[[??//]|[??]]. by apply Hp. Qed. *)

Lemma heap_preserved_insert_const p m h:
  heap_preserved (delete p m) h →
  heap_preserved (<[p := HBIConstant (h_heap h)]> m) h.
Proof.
  move => Hp l f /= /lookup_insert_Some[[??]|[??]]; simplify_eq. 1: by destruct l.
  apply: Hp => /=. rewrite lookup_delete_Some. done.
Qed.

Definition imp_heap_bij_pre (e : imp_event) (s : unit) : prepost (imp_event * unit) heap_bijUR :=
  let hi := heap_of_event e.2 in
  pp_quant $ λ bij,
  pp_quant $ λ vss,
  pp_quant $ λ hs,
  pp_star (heap_bij_auth bij ∗ heap_in_bij bij hi hs ∗ [∗ list] v1;v2∈vals_of_event e.2; vss, val_in_bij v1 v2) $
  pp_prop (dom _ (hb_bij bij) ⊆ h_provs hs) $
  pp_prop (hb_provs_i bij ⊆ h_provs hi) $
  pp_prop (heap_preserved (hb_priv_s bij) hs) $
  pp_prop (heap_preserved (hb_priv_i bij) hi) $
  pp_end ((e.1, event_set_vals_heap e.2 vss hs), tt).

Definition imp_heap_bij_post (e : imp_event) (s : unit) : prepost (imp_event * unit) heap_bijUR :=
  let hs := heap_of_event e.2 in
  pp_quant $ λ bij,
  pp_quant $ λ vsi,
  pp_quant $ λ hi,
  pp_star (heap_bij_auth bij ∗ heap_in_bij bij hi hs ∗ [∗ list] v1;v2∈vsi;vals_of_event e.2, val_in_bij v1 v2) $
  pp_prop (dom _ (hb_bij bij) ⊆ h_provs hs) $
  pp_prop (hb_provs_i bij ⊆ h_provs hi) $
  pp_prop (heap_preserved (hb_priv_s bij) hs) $
  pp_prop (heap_preserved (hb_priv_i bij) hi) $
  pp_end ((e.1, event_set_vals_heap e.2 vsi hi), tt).

Definition imp_heap_bij (m : module imp_event) : module imp_event :=
  mod_prepost imp_heap_bij_pre imp_heap_bij_post m.

Definition initial_imp_heap_bij_state (m : module imp_event) (σ : m.(m_state)) :=
  (@SMFilter imp_event, σ, (@PPOutside imp_event imp_event, tt, (True : uPred heap_bijUR)%I)).

Local Ltac split_solve :=
  match goal with
  | |- heap_preserved ?p _ => eassumption
  | |- event_set_vals_heap _ _ _ = event_set_vals_heap _ _ _ => reflexivity
  | |- ?P ⊣⊢ _ => is_evar P; reflexivity
(*   | |- ?a ⊆ ?b => *)
(*       assert_fails (has_evar a); assert_fails (has_evar b); etrans; [eassumption|] *)
(*   | |- ?a ⊆ ?b => *)
(*       assert_fails (has_evar a); assert_fails (has_evar b); etrans; [|eassumption] *)
(*   | |- heap_preserved ?p ?a ?b => *)
(*       assert_fails (has_evar p); assert_fails (has_evar a); assert_fails (has_evar b); etrans; [eassumption|] *)
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
      (λ ips s1 s2 s x1 x2 x ics1 ics2,
        ics1 = ics2 ∧
        match ips with
        | SPNone => x ⊣⊢ x1 ∗ x2
        | SPLeft => x1 = (x ∗ x2)%I
        | SPRight => x2 = (x ∗ x1)%I
        end
      ). }
  { move => ?? [] /=*; naive_solver. }
  { split!. by rewrite left_id. }
  all: move => [] [] [] P1 P2 P ics1 ics2.
  - move => e ics' e' /= ? ? *; destruct_all?; simplify_eq/=.
    setoid_subst.
    split!.
    { iSatMono. iIntros!. iFrame. }
    { by destruct e. }
  - move => e ics' e' /= ? ? *; destruct_all?; simplify_eq/=.
    setoid_subst.
    split!.
    { iSatMono; iIntros!; iFrame. }
    { by destruct e. }
  - move => [? e] /= ? Hr *; destruct_all?; simplify_eq/=.
    all: rewrite ?heap_of_event_event_set_vals_heap; split!.
    split!.
    { iSatMono; iIntros!; iFrame.
      iDestruct (big_sepL2_length with "[$]") as %?. rewrite vals_of_event_event_set_vals_heap //. }
    { by destruct e. }
    { by destruct e. }
  - move => [? e] /= *; destruct_all?; simplify_eq/=.
    split!.
    1: by destruct e.
    { iSatMono; iIntros!; iFrame. }
  - move => [? e] /= ? *; destruct_all?; simplify_eq/=.
    split!.
    all: rewrite ?heap_of_event_event_set_vals_heap; split!.
    { iSatMono; iIntros!; iFrame.
      iDestruct (big_sepL2_length with "[$]") as %?. rewrite vals_of_event_event_set_vals_heap //. }
    1: by destruct e.
    1: by destruct e.
  - move => [? e] /= ? *; destruct_all?; simplify_eq/=.
    split!.
    1: by destruct e.
    { iSatMono; iIntros!; iFrame. }
Qed.

Local Ltac split_solve ::=
  match goal with
  | |- expr_fill (?K' ++ ?K) _ = expr_fill ?K _ =>
      assert_fails (has_evar K'); assert_fails (has_evar K); apply expr_fill_app
  | |- expr_fill ?K _ = expr_fill ?K _ =>
      assert_fails (has_evar K); reflexivity
  | |- Is_true (static_expr _ (expr_fill _ _)) => apply static_expr_expr_fill
  | |- _ ≡ _ => reflexivity
  | |- heap_preserved ?p _ => eassumption
  (* | |- expr_in_bij ?b (expr_fill _ _) (expr_fill _ _) => *)
  (*     assert_fails (has_evar b); apply expr_in_bij_fill_2 *)
  (* | |- ectx_in_bij ?b (_ ++ _) (_ ++ _) => assert_fails (has_evar b); by apply ectx_in_bij_app *)
  end.
Local Ltac split_tac ::=
  repeat (original_split_tac; try split_solve).


Lemma imp_heap_bij_imp_refl fns:
  trefines (MS imp_module (initial_imp_state fns))
           (MS (imp_heap_bij imp_module)
               (initial_imp_heap_bij_state imp_module (initial_imp_state fns))).
Proof.
  pose (R := λ (b : bool) (s1 s2 : (unit * uPred heap_bijUR)), if b then s1.2 ≡ s2.2 else True).
  apply: (imp_prepost_proof R); unfold R in *.
  { destruct b.
    - constructor => ? // ?? -> //.
    - by constructor => ?. }
  { move => ????. naive_solver. }
  move => n K1 K2 f fn1 vs1 h1 [] P1 ? ? /= bij vs *.
  iSatStart. iIntros!. iDestruct (big_sepL2_length with "[$]") as %?. iSatStop.
  split!. move => ?. split; [lia|].
  move => Hcall Hret.
  unshelve apply: tsim_remember. { simpl. exact (λ _ '(Imp ei hi fnsi) '(ips, Imp es hs fnss, (pp, _, P')),
    ∃ bij' ei' es',
    fnsi = fns ∧ fnss = fns ∧
    satisfiable (heap_bij_auth bij' ∗ expr_in_bij ei' es' ∗ heap_in_bij bij' hi hs ∗ P1 ∗ P') ∧
    heap_preserved (hb_priv_s bij') hs ∧
    heap_preserved (hb_priv_i bij') hi ∧
    ei = expr_fill K1 ei' ∧
    es = expr_fill K2 es' ∧
    hb_provs_i bij' ⊆ h_provs hi ∧
    dom _ (hb_bij bij') ⊆ h_provs hs ∧
    pp = PPInside ∧
    static_expr true ei' ∧
    ips = SMProg
 ). }
  { split!.
    { iSatMono. iFrame. iApply expr_in_bij_subst_l; [lia| |done]. iApply expr_in_bij_static. apply fd_static. }
    all: split!.
    { apply static_expr_subst_l; [|solve_length]. apply static_expr_mono. apply fd_static. }  }
  { naive_solver. }
  iSatClear.
  move => /= n' ? Hloop [ei hi fnsi] [[ips [es hs fnss]] [[pp []] P]] ?. destruct_all?; simplify_eq.
  destruct (to_val ei') eqn:?.
  - destruct ei' => //; simplify_eq/=.
    iSatStart. iIntros. iDestruct!. destruct es' => //. iSatStop.
    apply Hret; [done|]. clear Hloop Hret Hcall. eexists _, [_]. split!.
    { iSatMono. iFrame. }
  - (* TODO: remove this use of EM *)
    have [?|?]:= EM (∃ K f vs, fns !! f = None ∧ ei' = expr_fill K (Call f (Val <$> vs))).
    + destruct_all?; simplify_eq/=.
      iSatStart. iIntros!. iDestruct (expr_in_bij_fill_l with "[$]") as (???) "[??]".
      destruct_all?; simplify_eq/=. case_match => //. iDestruct!.
      rewrite big_sepL_zip_with_same_length //.
      iDestruct (big_sepL2_Val_inv_l with "[$]") as (??) "?"; subst.
      iSatStop.
      revert select (Is_true (static_expr _ _)) => /static_expr_expr_fill/=[??]//.
      apply: Hcall; [done..| | |].
      1,2: by apply Forall2_fmap_l, Forall_Forall2_diag, Forall_true.
      clear Hret. split!.
      { iSatMono. iFrame. iAccu. }
      iSatClear. move => *. setoid_subst. split!.
      apply Hloop; [done|]. split!.
      iSatMono. iIntros!. iFrame.
      iDestruct (big_sepL2_cons_inv_l with "[$]") as (???) "[??]"; subst => /=.
      by iApply (expr_in_bij_fill_2 with "[$]").
    + tstep_both.
      apply steps_impl_step_end => ?? /= Hprim.
      move: Hprim => /prim_step_inv[//|??].
      destruct_all?; simplify_eq.
      iSatStart.
      iIntros!. iDestruct (expr_in_bij_fill_l with "[$]") as (???) "[??]".
      destruct_all?; simplify_eq/=.
      revert select (Is_true (static_expr _ _)) => /static_expr_expr_fill/=[??]//.
      invert_all' @head_step; destruct_all?; simplify_eq/=.
      all: repeat (case_match; iDestruct! => //); simplify_eq; iSatStop.
      * tstep_s => ? /eval_binop_bij Hbin.
        iSatStart. iDestruct (Hbin with "[$] [$]") as (??) "?". iSatStop.
        tend. split!. apply: Hloop; [done|]. split!.
        iSatMono; iFrame.
        by iApply (expr_in_bij_fill_2 with "[$]").
      * tstep_s => l' *; simplify_eq/=.
        iSatStart.
        destruct v1 => //; simplify_eq/=; iDestruct!; simplify_eq/=.
        iDestruct (heap_bij_shared_lookup with "[$] [$]") as %?.
        iDestruct (heap_in_bij_lookup with "[$]") as (??) "#?"; [done..|].
        iSatStop.
        tend. split!; [done|]. apply: Hloop; [done|]. split!.
        iSatMono; iFrame.
        by iApply (expr_in_bij_fill_2 with "[$]").
      * tstep_s => l' *; simplify_eq/=.
        iSatStart.
        destruct v1 => //; simplify_eq/=; iDestruct!; simplify_eq/=.
        iDestruct (heap_bij_shared_lookup with "[$] [$]") as %?.
        iDestruct (heap_in_bij_alive with "[$]") as %?; [done..|].
        iSatStop. tend. split!.
        apply: Hloop; [done|]. split!.
        { iSatMono. iFrame. iSplit.
          - by iApply (expr_in_bij_fill_2 with "[$]").
          - by iApply (heap_in_bij_update with "[$] [$]"). }
        { apply heap_preserved_update; [done|]. rewrite hb_priv_s_lookup_None. naive_solver. }
        { apply heap_preserved_update; [done|]. by apply: hb_disj. }
        1: done.
        1: done.
      * tstep_s => *; simplify_eq/=.
        set (l' := (heap_fresh (dom _ (hb_bij bij')) hs)).
        eexists l'. split; [apply heap_fresh_is_fresh|] => *; simplify_eq/=. tend.
        iSatStart.
        destruct v => //; simplify_eq/=; iDestruct!; simplify_eq/=.
        iSatStop.
        split!.
        apply Hloop; [done|].
        unshelve eexists (heap_bij_share l.1 l'.1 bij' _).
        { abstract (apply: not_elem_of_weaken; [|done]; unfold heap_is_fresh in *; naive_solver). }
        split!.
        { iSatMonoBupd. iFrame.
          iMod (heap_bij_alloc_shared with "[$]") as "[$?]". { apply heap_fresh_not_in. } iModIntro.
          iSplit.
          - iApply (expr_in_bij_fill_2 with "[$]") => /=. iFrame. iPureIntro.
            unfold heap_is_fresh in *; naive_solver.
          - iApply (heap_in_bij_alloc l l'); [done|apply heap_fresh_is_fresh|done].
        }
        1: { apply heap_preserved_alloc; [|rewrite hb_priv_s_lookup_None; by move => *; simplify_map_eq].
             rewrite hb_privs_s_share. apply: heap_preserved_mono; [done|]. apply delete_subseteq. }
        1: { apply heap_preserved_alloc; [done|]. apply not_elem_of_dom. unfold heap_is_fresh in *. set_solver. }
        1: { etrans; [apply hb_provs_i_share|]. rewrite heap_alloc_provs. set_solver. }
        1: { rewrite dom_insert_L heap_alloc_provs. set_solver. }
      * tstep_s => l' *; simplify_eq/=. tend.
        iSatStart.
        destruct v => //; simplify_eq/=; iDestruct!; simplify_eq/=.
        iDestruct (heap_bij_shared_lookup with "[$] [$]") as %?.
        iDestruct (heap_in_bij_alive with "[$]") as %?; [done..|].
        iSatStop.
        split!. apply: Hloop; [done|].
        split!.
        { iSatMono. iFrame. iSplit.
          - by iApply (expr_in_bij_fill_2 with "[$]").
          - by iApply heap_in_bij_free. }
        1: { apply heap_preserved_free; [done|]. rewrite hb_priv_s_lookup_None. naive_solver. }
        1: { apply heap_preserved_free; [done|]. apply: hb_disj. naive_solver. }
        1: done.
        1: done.
      * tstep_s => *. simplify_eq/=.
        iSatStart.
        destruct v => //; simplify_eq/=; iDestruct!; simplify_eq/=.
        iSatStop.
        tend. split!. apply: Hloop; [done|]. split!.
        { iSatMono. iFrame. case_match; by iApply (expr_in_bij_fill_2 with "[$]"). }
        case_match; naive_solver.
      * tstep_s. tend. split!. apply: Hloop; [done|]. split!.
        { iSatMono. iFrame. iApply (expr_in_bij_fill_2 with "[$]"). by iApply (expr_in_bij_subst with "[$]"). }
        1: by apply static_expr_subst.
      * by tstep_s.
      * iSatStart.
        rewrite big_sepL_zip_with_same_length //.
        iDestruct (big_sepL2_Val_inv_l with "[$]") as (??) "?"; subst.
        iSatStop.
        tstep_s. left. split! => ?. tend. split!; [solve_length|].
        apply Hloop; [done|]. split!.
        { iSatMono. iFrame. iApply (expr_in_bij_fill_2 with "[$]").
          iApply expr_in_bij_subst_l; [solve_length| |done].
          iApply expr_in_bij_static. apply fd_static. }
        apply static_expr_subst_l; [|solve_length]. apply static_expr_mono. apply fd_static.
      * naive_solver.
Qed.

Lemma imp_heap_bij_imp_closed m σ:
  trefines (MS (imp_closed (imp_heap_bij m)) (SMFilter, initial_imp_heap_bij_state m σ, ICStart))
           (MS (imp_closed m) (SMFilter, σ, ICStart)).
Proof.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { simpl. exact (λ _
          '(σm1, (σf, σ1, (pp, _, r)), σc1)
          '(σm2, σ2, σc2),
           σ1 = σ2 ∧ σc1 = σc2 ∧
             ((σc1 = ICStart ∧ σf = SMFilter ∧ pp = PPOutside ∧ σm1 = σm2 ∧ σm2 = SMFilter ∧ r = True%I) ∨
              ( ((∃ e, σf = SMProgRecv e ∧ σm2 = SMProgRecv e) ∨ (σf = SMProg ∧ σm2 = SMProg)
                 ) ∧ σm1 = SMProg ∧ σc1 = ICRunning ∧ pp = PPInside))
                             ). }
  { split!. } { done. }
  move => {}n _ /= Hloop [[σm1 [[σf σ1] [[pp []] r]]] σc1] [[σm2 σ2] σc2] ?.
  destruct_all?; simplify_eq/=.
  - tstep_i. apply steps_impl_step_end => ???. invert_all' @m_step; simplify_eq/=. split!.
    tstep_s. eexists (Some (inr _)). split!. apply: steps_spec_step_end; [econs|] => ??. simplify_eq/=.
    tstep_i. apply steps_impl_step_end => ???. invert_all @m_step. split!.
    tstep_s. eexists (Some (inl _)). split!. apply: steps_spec_step_end; [econs|] => ??. simplify_eq/=.
    tstep_i => ??; simplify_eq/=.
    tstep_i. eexists ∅, (ValNum <$> vs), initial_heap_state. split!.
    { apply: (satisfiable_init (_, _)). { split; by eapply (gmap_view_auth_dfrac_valid _ (DfracOwn 1)). }
      rewrite pair_split uPred.ownM_op.
      iIntros "[$ $]". iModIntro. iSplit!.
      - iIntros (????). set_solver.
      - rewrite big_sepL2_fmap_l big_sepL2_fmap_r. iApply big_sepL2_intro; [done|].
        iIntros "!>" (?????). by simplify_eq/=.
      - by instantiate (1 := True%I). }
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
      iSatStart.
      iIntros!. iDestruct (big_sepL2_ValNum_inv_r with "[$]") as %?. subst.
      iSatStop.
      split!; [done|].
      tstep_i. apply steps_impl_step_end => ???. invert_all @m_step. split!.
      tstep_s. eexists (Some (inr _)). split!. apply: steps_spec_step_end; [econs|] => /=? ->.
      tstep_i. apply steps_impl_step_end => ???. invert_all @m_step. split!.
      tstep_s. eexists (Some (inl _)). split!. apply: steps_spec_step_end; [econs|] => /=? ->.
      tstep_i => ? <-.
      tstep_i. eexists _, [ValNum _]. split!.
      { iSatMono. iIntros!. iFrame. iSplitR; [by iPureIntro|]. instantiate (1:=True%I). done. }
      apply: Hloop; [done|]. split!.
    + destruct i as [? []]; simplify_eq/=.
      tstep_s. eexists (Some _). split!.
      apply: steps_spec_step_end; [econs|]=> /=??. destruct_all?; simplify_eq/=.
      tstep_s. eexists None. apply: steps_spec_step_end; [econs|]=> /=??. destruct_all?; simplify_eq/=.
      iSatStart. iIntros!.
      iDestruct (big_sepL2_cons_inv_r with "[$]") as ([]??) "[??]"; subst => //=; iDestruct!.
      iSatStop.
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
  pose (R := λ (b : bool) (s1 s2 : (unit * uPred heap_bijUR)), if b then s1.2 ≡ s2.2 else True).
  apply: (imp_prepost_proof R); unfold R in *.
  { destruct b.
    - constructor => ? // ?? -> //.
    - by constructor => ?. }
  { naive_solver. }
  move => n K1 K2 f fn1 vs1 h0 [] r0 ?.
  rewrite !lookup_insert_Some => ?; destruct_all?; simplify_map_eq/=.
  move => bij1 vs h1 *. split!. move => ?. destruct vs => //.
  iSatStart. iIntros!.
  iDestruct (big_sepL2_nil_inv_r with "[$]") as %?. subst.
  iSatStop.
  split!. move => Hcall Hret.
  pose (l := (heap_fresh (dom _ (hb_bij bij1)) h1)).
  pose proof (heap_fresh_not_in (dom (gset _) (hb_bij bij1)) h1) as Hf.
  tstep_s. eexists l. split!. { apply heap_fresh_is_fresh. }
  move => *; simplify_eq.
  tstep_s. tstep_s. move => ? [<-] ?.
  tstep_s.
  apply: (Hcall _ _ ([LetECtx _ _]) ([LetECtx _ _])); [done|..].
  1, 2: by simplify_map_eq. 1,2: by econs.
  eexists (heap_bij_update_const_s l.1 _ bij1), [].
  split!.
  { rewrite dom_insert_L heap_update_provs heap_alloc_provs. set_solver. }
  { etrans; [apply hb_provs_i_update_const_s|]. done. }
  { rewrite hb_priv_s_update_const_s. apply heap_preserved_insert_const.
    apply heap_preserved_update; [|by move => *; simplify_map_eq].
    apply heap_preserved_alloc; [|by move => *; simplify_map_eq].
    rewrite delete_notin; [done|].
    rewrite hb_priv_s_lookup_None => ??.
    apply Hf. by apply elem_of_dom. }
  { iSatMonoBupd. iFrame.
    iMod (heap_bij_alloc_const_s with "[$]") as "[? ?]"; [done|]. iFrame. iModIntro.
    iDestruct select (heap_in_bij _ _ _) as "Hbij".
    iSplitR "Hbij". { iAccu. } iSplit => //.
    iApply heap_in_bij_update_r; [move => *; simplify_map_eq|].
    iApply heap_in_bij_alloc_r; [move => *; simplify_map_eq|].
    iApply heap_in_bij_mono_bij; [|done]. move => ?? /=/lookup_insert_Some?. naive_solver. }
  iSatClear.
  move => ? h2 [] ? ? bij3 *. setoid_subst.
  iSatStart. iIntros!.
  iDestruct (big_sepL2_cons_inv_l with "[$]") as (???) "[??]".
  iDestruct (big_sepL2_nil_inv_l with "[$]") as %?; subst.
  iDestruct (heap_bij_const_s_lookup with "[$] [$]") as %?.
  iSatStop.
  split!.
  tstep_i.
  tstep_s.
  tstep_s. move => ?? [<-] /heap_preserved_lookup_r Hlookup.
  efeed pose proof Hlookup as Hlookup'; [done..|by apply hb_priv_s_lookup_Some|].
  simplify_map_eq.
  tstep_s.
  tstep_s => *. simplify_eq.
  tstep_s.
  apply: Hret; [done|].
  eexists (heap_bij_update_const_s (fresh (dom (gset prov) (hb_bij bij1) ∪ h_provs h1)) _ _), [ValNum 1]. split!.
  { rewrite dom_insert_L. apply union_subseteq. split; [|set_solver].
    etrans; [|done]. apply elem_of_subseteq_singleton. by apply elem_of_dom. }
  { etrans; [apply hb_provs_i_update_const_s|]. done. }
  { rewrite hb_priv_s_update_const_s. apply heap_preserved_insert_const.
    apply: heap_preserved_free; [ |by move => *; simplify_map_eq].
    apply: heap_preserved_mono; [done|]. apply delete_subseteq. }
  iSatMonoBupd. iFrame.
  iMod (heap_bij_frag_update_const_s with "[$]") as "[? ?]". iFrame. iModIntro. iSplit; [|done].
  iApply heap_in_bij_free_r; [move => *; simplify_map_eq|].
  iApply heap_in_bij_mono_bij; [|done].
  move => /=?? /lookup_insert_Some. naive_solver.
Qed.

Lemma bij_alloc_ctx_refines :
  imp_ctx_refines (<["f" := bij_alloc_opt]> ∅) (<["f" := bij_alloc]> ∅).
Proof.
  apply: imp_heap_bij_trefines_implies_ctx_refines. { set_solver. }
  apply bij_alloc_opt_refines.
Qed.
End imp_heap_bij_example.
