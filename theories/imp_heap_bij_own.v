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

Tactic Notation "iDestruct!" :=
  repeat (
     iMatchHyp (fun H P => match P with ⌜_ = _⌝%I => iDestruct H as %? end)
  || iMatchHyp (fun H P => match P with (_ ∗ _)%I => iDestruct H as "[??]" end)
  || simplify_eq/=).

Tactic Notation "iIntros!" := iIntros; iDestruct!.

Ltac iSplit_step :=
  lazymatch goal with
  | |- environments.envs_entails _ (∃ x, _)%I => iExists _
  | |- environments.envs_entails _ (_ ∗ _)%I => iSplit
  | |- environments.envs_entails _ (⌜_⌝)%I => iPureIntro
  | |- _ => split_step
  end; simpl.

Ltac original_iSplit_tac :=
  (* The outer repeat is because later split_steps may have
  instantiated evars and thus we try earlier goals again. *)
  repeat (simpl; repeat iSplit_step).

Ltac iSplit_tac :=
  original_iSplit_tac.

Tactic Notation "iSplit!" := iSplit_tac.


(* TODO: Allow also ownership of the outer heap, probably by adding a
   second gmap prov (option Z → option val) and adding an new
   heap_preserved and making sure that if hb_bij !! p2 = Some p1 then
   we have the persistent fragment {[ p1 := None ]} *)

(** * camera definition *)
Inductive heap_bij_elem :=
| HBShared (p : prov) | HBConstant (h : Z → option val) | HBChanging.
Canonical Structure heap_bij_elemO := leibnizO heap_bij_elem.

Definition heap_bijUR : ucmra := gmap_viewUR prov heap_bij_elemO.

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
  hb_iff pi ps ps' :
   hb_bij !! ps = Some (HBShared pi) →
   hb_bij !! ps' = Some (HBShared pi) →
   ps = ps'
}.

Ltac simplify_bij :=
  repeat (simplify_eq; match goal with
         | H1 : hb_bij ?bij !! ?ps1 = Some (HBShared ?pi),
             H2 : hb_bij ?bij !! ?ps2 = Some (HBShared ?pi) |- _ =>
             pose proof (hb_iff bij pi ps1 ps2 H1 H2); clear H2
         end); simplify_eq.

Global Program Instance heap_bij_empty : Empty heap_bij := HeapBij ∅ _.
Next Obligation. set_solver. Qed.

Definition hb_shared_provs (bij : heap_bij) : gset prov :=
  list_to_set (omap (λ x, if x.2 is HBShared p then Some p else None) (map_to_list (hb_bij bij))).

Global Typeclasses Opaque hb_shared_provs.

Lemma elem_of_hb_shared_provs bij p1:
  p1 ∈ hb_shared_provs bij ↔ ∃ p2, hb_bij bij !! p2 = Some (HBShared p1).
Proof.
  rewrite /hb_shared_provs elem_of_list_to_set elem_of_list_omap.
  setoid_rewrite elem_of_map_to_list'.
  split.
  - move => [[??] /= [??]]. case_match; simplify_eq/=. naive_solver.
  - move => [??]. by eexists (_, _).
Qed.

Program Definition heap_bij_add_shared (p1 p2 : prov) (bij : heap_bij)
        (H : p1 ∉ hb_shared_provs bij) :=
  HeapBij (<[p2 := HBShared p1]> (hb_bij bij)) _.
Next Obligation.
  move => ??? Hnotin ???.
  rewrite !lookup_insert_Some => ??. destruct_all?; simplify_eq/= => //. 3: by apply: hb_iff.
  all: simplify_eq; contradict Hnotin; apply elem_of_hb_shared_provs; naive_solver.
Qed.

Program Definition heap_bij_update_const (p : prov) (h : gmap loc val) (bij : heap_bij) :=
  HeapBij (<[p := HBConstant (λ o, h !! (p, o))]> (hb_bij bij)) _.
Next Obligation.
  move => ??????.
  rewrite !lookup_insert_Some => ??. destruct_all?; simplify_eq/= => //. by apply: hb_iff.
Qed.

Program Definition heap_bij_delete_prov (p : prov) (bij : heap_bij) :=
  HeapBij (delete p (hb_bij bij)) _.
Next Obligation.
  move => ?????.
  rewrite !lookup_delete_Some => ??. destruct_all?; simplify_eq/= => //. by apply: hb_iff.
Qed.

Lemma hb_shared_provs_add_shared p1 p2 bij H:
  hb_shared_provs (heap_bij_add_shared p1 p2 bij H) ⊆ {[p1]} ∪ hb_shared_provs bij.
Proof.
  move => ?/elem_of_hb_shared_provs[/=?/lookup_insert_Some?].
  set_unfold. rewrite elem_of_hb_shared_provs. naive_solver.
Qed.

Lemma hb_shared_provs_update_const p h bij:
  hb_shared_provs (heap_bij_update_const p h bij) ⊆ hb_shared_provs bij.
Proof.
  move => ?. rewrite !elem_of_hb_shared_provs /=.
  setoid_rewrite lookup_insert_Some. naive_solver.
Qed.

Definition heap_bij_auth (bij : heap_bij) : uPred heap_bijUR :=
  uPred_ownM (gmap_view_auth (DfracOwn 1) (hb_bij bij)).

Definition heap_bij_shared (p1 p2 : prov) : uPred (heap_bijUR) :=
  uPred_ownM (gmap_view_frag p2 DfracDiscarded (HBShared p1)).

Definition heap_bij_const (p : prov) (f : Z → option val) : uPred (heap_bijUR) :=
  uPred_ownM (gmap_view_frag p (DfracOwn 1) (HBConstant f)).

Lemma heap_bij_alloc_shared bij p1 p2 H:
  p2 ∉ dom (gset _) (hb_bij bij) →
  heap_bij_auth bij ==∗ heap_bij_auth (heap_bij_add_shared p1 p2 bij H) ∗ heap_bij_shared p1 p2.
Proof.
  move => ?. rewrite -uPred.ownM_op. apply uPred.bupd_ownM_update. apply gmap_view_alloc; [|done].
  by apply not_elem_of_dom.
Qed.

Lemma heap_bij_shared_lookup p1 p2 bij :
  satisfiable (heap_bij_auth bij ∗ heap_bij_shared p1 p2) →
  hb_bij bij !! p2 = Some (HBShared p1).
Proof.
  rewrite -uPred.ownM_op => /satisfiable_valid/cmra_discrete_valid/gmap_view_both_valid_L. naive_solver.
Qed.

Lemma heap_bij_alloc_const bij p h:
  p ∉ dom (gset _) (hb_bij bij) →
  heap_bij_auth bij ==∗ heap_bij_auth (heap_bij_update_const p h bij) ∗ heap_bij_const p (λ o, h !! (p, o)).
Proof.
  move => ?. rewrite -uPred.ownM_op. apply uPred.bupd_ownM_update. apply gmap_view_alloc; [|done].
  by apply not_elem_of_dom.
Qed.

Lemma heap_bij_const_lookup p f bij :
  satisfiable (heap_bij_auth bij ∗ heap_bij_const p f) →
  hb_bij bij !! p = Some (HBConstant f).
Proof.
  rewrite -uPred.ownM_op => /satisfiable_valid/cmra_discrete_valid/gmap_view_both_valid_L. naive_solver.
Qed.

Lemma heap_bij_frag_update_const bij p f h:
  heap_bij_auth bij ∗ heap_bij_const p f ==∗
  heap_bij_auth (heap_bij_update_const p h bij) ∗ heap_bij_const p (λ o, h !! (p, o)).
Proof. rewrite -!uPred.ownM_op. apply uPred.bupd_ownM_update. apply gmap_view_update. Qed.

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
  rewrite !big_sepL_zip_with. rewrite big_sepL_fmap.
  iApply big_sepL_impl; [done|].
  iIntros "!>" (?? ?) "#?". rewrite list_lookup_fmap. case_match => //=.
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

(*
Lemma ectx_in_bij_cons r Ki K Ki' K':
  ectx_in_bij r (Ki :: K) (Ki' :: K') ↔ ectx_item_in_bij r Ki Ki' ∧ ectx_in_bij r K K'.
Proof. apply Forall2_cons. Qed.

Lemma ectx_in_bij_app r Ki K Ki' K':
  ectx_in_bij r Ki Ki' →
  ectx_in_bij r K K' →
  ectx_in_bij r (Ki ++ K) (Ki' ++ K').
Proof. apply Forall2_app. Qed.

Lemma ectx_in_bij_cons_inv_l r Ki K K':
  ectx_in_bij r (Ki::K) K' →
  ∃ Ki' K'', ectx_item_in_bij r Ki Ki' ∧ ectx_in_bij r K K'' ∧ K' = Ki' :: K''.
Proof. apply Forall2_cons_inv_l. Qed.

Lemma expr_in_bij_fill_item_2 r K1 K2 e1 e2 :
  ectx_item_in_bij r K1 K2 →
  expr_in_bij r e1 e2 →
  expr_in_bij r (expr_fill_item K1 e1) (expr_fill_item K2 e2).
Proof.
  move => ??.
  destruct K1, K2 => //; simplify_eq/=; destruct_all? => //.
  rewrite !app_length /=. split_and!; [done|solve_length|].
  apply Forall_zip_with_2. apply Forall2_app; [by apply Forall2_fmap|by econs].
Qed.

Lemma expr_in_bij_fill_2 r K1 K2 e1 e2 :
  ectx_in_bij r K1 K2 →
  expr_in_bij r e1 e2 →
  expr_in_bij r (expr_fill K1 e1) (expr_fill K2 e2).
Proof.
  elim: K1 K2 e1 e2. { move => ??? /Forall2_nil_inv_l->. done. }
  move => Ki1 K1 IH ??? /(Forall2_cons_inv_l _ _)[Ki2 [K2 [?[??]]]] ?; subst => /=.
  apply: IH; [done|]. by apply expr_in_bij_fill_item_2.
Qed.
*)

Lemma expr_in_bij_fill_item_l Ki e1 e2 :
  expr_in_bij (expr_fill_item Ki e1) e2 -∗
  ∃ Ki' e', ⌜e2 = expr_fill_item Ki' e'⌝ ∗ ectx_item_in_bij Ki Ki' ∗ expr_in_bij e1 e'.
Proof.
  iIntros "He".
  destruct Ki, e2 => //=; iDestruct!; destruct_all?; simplify_eq; try case_match => //; simplify_eq. 10: {
    revert select (length _ = length _). rewrite app_length fmap_length/= => ?.
    rewrite big_sepL_zip_with big_sepL_app big_sepL_fmap /=. iDestruct select (_ ∗ _)%I as "[Hv [He Hel]]".
    iAssert (⌜∀ i, args !! i = ((Val <$> (((default inhabitant) ∘ to_val) <$> (take (length vl) args)))
                       ++ (drop (length vl) args)) !! i⌝)%I as %Hargs%list_eq. {
      iIntros (i). destruct (decide (i < length vl)) as [Hlt|].
      - move: (Hlt) => /lookup_lt_is_Some_2[??].
        have /lookup_lt_is_Some_2[a ?] : i < length args by lia.
        rewrite lookup_app_l ?fmap_length ?take_length; [|lia]. rewrite !list_lookup_fmap.
        rewrite lookup_take; [|lia].
        iDestruct (big_sepL_lookup with "Hv") as "?"; [done|]. simplify_option_eq. destruct a => //.
      - admit.
    }
    rewrite fmap_length Nat.add_0_r.
    have /lookup_lt_is_Some_2[a ?] : length vl < length args by lia. simplify_option_eq.
    iExists (CallCtx _ _ _), _.
    iSplit!. { etrans; [done|]. f_equal. by erewrite drop_S. }
    admit.
    admit.
    done.
  }
  all: (unshelve iExists _); [econs; shelve| naive_solver].
Admitted.

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
  heap_in_bij (heap_bij_add_shared l1.1 l2.1 bij H) (heap_alloc hi l1 n) (heap_alloc hs l2 n).
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
  - have ? : p1 ≠ l1.1. { contradict H. apply elem_of_hb_shared_provs. naive_solver. }
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
Definition heap_preserved (bij : heap_bij) (h : heap_state) :=
  ∀ l f, hb_bij bij !! l.1 = Some (HBConstant f) → h.(h_heap) !! l = f l.2.

Lemma heap_preserved_mono bij1 bij2 h:
  heap_preserved bij1 h →
  (∀ p f, hb_bij bij2 !! p = Some (HBConstant f) → hb_bij bij1 !! p = Some (HBConstant f)) →
  heap_preserved bij2 h.
Proof. unfold heap_preserved => Hp ????. apply: Hp. naive_solver. Qed.

Lemma heap_preserved_lookup_r bij h f l v:
  h_heap h !! l = v →
  heap_preserved bij h →
  hb_bij bij !! l.1 = Some (HBConstant f) →
  f l.2 = v.
Proof. move => Hl Hp ?. by rewrite -Hp. Qed.

Lemma heap_preserved_update l v h bij:
  heap_preserved bij h →
  (∀ f, hb_bij bij !! l.1 = Some (HBConstant f) → False) →
  heap_preserved bij (heap_update h l v).
Proof.
  move => Hp ???? /=. rewrite lookup_alter_ne; [by eapply Hp|naive_solver].
Qed.

Lemma heap_preserved_alloc l n h bij:
  heap_preserved bij h →
  (∀ f, hb_bij bij !! l.1 = Some (HBConstant f) → False) →
  heap_preserved bij (heap_alloc h l n).
Proof.
  move => Hp ? l' f /= ?. rewrite lookup_union_r; [by apply Hp|].
  apply not_elem_of_list_to_map_1 => /elem_of_list_fmap[[[??]?] [?/elem_of_list_fmap[?[??]]]]; simplify_eq/=.
  naive_solver.
Qed.

Lemma heap_preserved_free l h bij:
  heap_preserved bij h →
  (∀ f, hb_bij bij !! l.1 = Some (HBConstant f) → False) →
  heap_preserved bij (heap_free h l).
Proof.
  move => Hp ? l' f ? /=. rewrite map_filter_lookup. etrans; [|by eapply Hp].
  destruct (h_heap h !! l') => //=. case_option_guard => //. destruct l, l'; naive_solver.
Qed.

Lemma heap_preserved_add_shared p1 p2 bij H h:
  heap_preserved bij h →
  heap_preserved (heap_bij_add_shared p1 p2 bij H) h.
Proof. move => Hp l f /= /lookup_insert_Some[[??//]|[??]]. by apply Hp. Qed.

Lemma heap_preserved_update_const p bij h:
  heap_preserved (heap_bij_delete_prov p bij) h →
  heap_preserved (heap_bij_update_const p (h_heap h) bij) h.
Proof.
  move => Hp l f /= /lookup_insert_Some[[??]|[??]]; simplify_eq. 1: by destruct l.
  apply: Hp => /=. rewrite lookup_delete_Some. done.
Qed.

Definition imp_heap_bij_pre (e : imp_event) (s : unit) : prepost (imp_event * unit) heap_bijUR :=
  let ho := heap_of_event e.2 in
  pp_quant $ λ bij,
  pp_quant $ λ vsi,
  pp_quant $ λ hi,
  pp_add (heap_bij_auth bij ∗ heap_in_bij bij ho hi ∗ [∗ list] v1;v2∈vals_of_event e.2; vsi, val_in_bij v1 v2) $
  (* TODO: should we also have the following for hi? We don't need it so far... *)
  pp_prop (hb_shared_provs bij ⊆ h_provs ho) $
  pp_prop (heap_preserved bij hi) $
  pp_end ((e.1, event_set_vals_heap e.2 vsi hi), tt).

Definition imp_heap_bij_post (e : imp_event) (s : unit) : prepost (imp_event * unit) heap_bijUR :=
  let hi := heap_of_event e.2 in
  pp_quant $ λ bij,
  pp_quant $ λ vso,
  pp_quant $ λ ho,
  pp_remove (heap_bij_auth bij ∗ heap_in_bij bij ho hi ∗ [∗ list] v1;v2∈vso;vals_of_event e.2, val_in_bij v1 v2) $
  (* TODO: should we also have the following for hi? We don't need it so far... *)
  pp_prop (hb_shared_provs bij ⊆ h_provs ho) $
  pp_prop (heap_preserved bij hi) $
  pp_end ((e.1, event_set_vals_heap e.2 vso ho), tt).

Definition imp_heap_bij (m : module imp_event) : module imp_event :=
  mod_prepost imp_heap_bij_pre imp_heap_bij_post m.

Definition initial_imp_heap_bij_state (m : module imp_event) (σ : m.(m_state)) :=
  (@SMFilter imp_event, σ, (@PPOutside imp_event imp_event, tt, (True : uPred heap_bijUR)%I)).

Local Ltac split_solve :=
  match goal with
  | |- heap_preserved ?p _ => is_evar p; eassumption
  | |- event_set_vals_heap _ _ _ = event_set_vals_heap _ _ _ => reflexivity
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
      (λ ips s1 s2 s _ _ ics1 ics2, ics1 = ics2). }
  { move => ?? [] /=*; naive_solver. }
  { by rewrite left_id. }
  { by apply satisfiable_pure_1. }
  { split!. }
  all: move => [] [] [] P1 P2 ics1 ics2.
  - move => e ics' e' /= ? ? *; destruct_all?; simplify_eq/=.
    split!.
    { apply: satisfiable_mono; [done|]. iIntros!; iFrame. }
    { iIntros!. iModIntro. iFrame. }
    { by destruct e. }
  - move => e ics' e' /= ? ? *; destruct_all?; simplify_eq/=.
    split!.
    { apply: satisfiable_mono; [done|]. iIntros!; iFrame. }
    { iIntros!. iModIntro. iFrame. }
    { by destruct e. }
  - move => [? e] /= ? Hr *; destruct_all?; simplify_eq/=.
    revert select (_ ==∗ _) => Hbupd.
    all: rewrite ?heap_of_event_event_set_vals_heap; split!.
    split!.
    { apply: satisfiable_bmono; [done|]. iIntros!. iMod (Hbupd with "[$]"). iModIntro.
      iDestruct!. iDestruct (big_sepL2_length with "[$]") as %?. rewrite vals_of_event_event_set_vals_heap //.
      iFrame. }
    { iIntros. iDestruct!. iMod (Hbupd with "[$]"). iModIntro.
      iDestruct!. iDestruct (big_sepL2_length with "[$]") as %?. rewrite vals_of_event_event_set_vals_heap //.
      iFrame. }
    { by destruct e. }
    { by destruct e. }
  - move => [? e] /= *; destruct_all?; simplify_eq/=.
    revert select (_ ==∗ _) => Hbupd.
    split!.
    1: by destruct e.
    1: { etrans; [done|]. iIntros ">[??]". iMod (Hbupd with "[$]"). iModIntro. by iFrame. }
  - move => [? e] /= ? *; destruct_all?; simplify_eq/=.
    revert select (_ ==∗ _) => Hbupd.
    split!.
    all: rewrite ?heap_of_event_event_set_vals_heap; split!.
    { apply: satisfiable_bmono; [done|]. iIntros. iDestruct!. iMod (Hbupd with "[$]"). iModIntro.
      iDestruct!. iDestruct (big_sepL2_length with "[$]") as %?. rewrite vals_of_event_event_set_vals_heap //.
      iFrame. }
    { iIntros. iDestruct!. iMod (Hbupd with "[$]"). iModIntro.
      iDestruct!. iDestruct (big_sepL2_length with "[$]") as %?. rewrite vals_of_event_event_set_vals_heap //.
      iFrame. }
    1: by destruct e.
    1: by destruct e.
  - move => [? e] /= ? *; destruct_all?; simplify_eq/=.
    revert select (_ ==∗ _) => Hbupd.
    split!.
    1: by destruct e.
    1: { etrans; [done|]. iIntros ">[??]". iMod (Hbupd with "[$]"). iModIntro. by iFrame. }
Qed.

Local Ltac split_solve ::=
  match goal with
  | |- expr_fill (?K' ++ ?K) _ = expr_fill ?K _ =>
      assert_fails (has_evar K'); assert_fails (has_evar K); apply expr_fill_app
  | |- expr_fill ?K _ = expr_fill ?K _ =>
      assert_fails (has_evar K); reflexivity
  | |- Is_true (static_expr _ (expr_fill _ _)) => apply static_expr_expr_fill
  | |- _ ≡ _ => reflexivity
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
  { admit. }
  { move => ????. naive_solver. }
  move => n K1 K2 f fn1 vs1 h1 [] P1 ?? /= bij vs *.
  have ?: length vs1 = length vs.
  { apply: satisfiable_pure_2. apply: satisfiable_mono; [done|]. iIntros!. by iApply big_sepL2_length. }
  split!. move => ?. split; [lia|].
  move => Hcall Hret.
  unshelve apply: tsim_remember. { simpl. exact (λ _ '(Imp ei hi fnsi) '(ips, Imp es hs fnss, (pp, _, P')),
    ∃ bij' ei' es',
    fnsi = fns ∧ fnss = fns ∧
    (P' ==∗ heap_bij_auth bij' ∗ expr_in_bij ei' es' ∗ heap_in_bij bij' hi hs ∗ P1) ∧
    satisfiable P' ∧
    heap_preserved bij' hs ∧
    ei = expr_fill K1 ei' ∧
    es = expr_fill K2 es' ∧
    hb_shared_provs bij' ⊆ h_provs hi ∧
    pp = PPInside ∧
    static_expr true ei' ∧
    ips = SMProg
 ). }
  { split!.
    { iIntros. iModIntro. iDestruct!. iFrame.
      iApply expr_in_bij_subst_l; [lia| |done]. iApply expr_in_bij_static. apply fd_static. }
    all: split!.
    { apply static_expr_subst_l; [|solve_length]. apply static_expr_mono. apply fd_static. }  }
  { naive_solver. }
  move => /= n' ? Hloop [ei hi fnsi] [[ips [es hs fnss]] [[pp []] P]] ?. destruct_all?; simplify_eq.
  destruct (to_val ei') eqn:?.
  - destruct ei' => //; simplify_eq/=.
    have [??]: ∃ v, es' = Val v; simplify_eq/=. {
      apply: satisfiable_pure_2. apply: satisfiable_bmono; [done|]. etrans; [done|].
      iIntros ">?"; iDestruct!. destruct es' => //. naive_solver.
    }
    apply Hret; [done|]. clear Hloop Hret Hcall. eexists _, [_]. split!.
    { etrans; [done|]. iIntros ">?". iDestruct!. by iFrame. }
    all: split!.
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
      1: { etrans; [done|]. rewrite cmra_core_dup assoc -assoc. done. }
      all: split!.
      1: { by apply cmra_included_r. }
      move => *. decompose_Forall_hyps. split!.
      apply Hloop; [done|]. split!.
      1: { rewrite -!assoc. apply cmra_update_op; [done|].
           etrans. { apply cmra_update_op; [done|]. by apply cmra_update_included. }
           rewrite assoc. apply cmra_update_op; [|done].
           apply cmra_update_included. apply cmra_included_core. }
      all: split!.
      { apply: ectx_in_bij_mono; [done|]. apply cmra_core_mono. by apply cmra_included_r. }
      { apply: val_in_bij_mono; [done|]. apply cmra_core_mono. by apply cmra_included_l. }
      { apply: heap_in_bij_mono; [done|]. apply cmra_core_mono. by apply cmra_included_l. }
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
        tend. split!. apply: Hloop; [done|]. split!. 1: done. all: split!.
      * tstep_s => *; simplify_eq/=.
        destruct v1 => //; simplify_eq/=; destruct_all?; simplify_eq/=. tend.
        efeed pose proof heap_in_bij_lookup as Hl; [done|done| |done|destruct_all?].
        { apply heap_bij_shared_lookup.
          apply: cmra_valid_included; [by apply: cmra_update_valid|].
          apply: cmra_included_op_l. by apply: cmra_mono_l. }
        split!. 1: done.
        apply: Hloop; [done|]. split!. 1: done. all: split!.
      * tstep_s => l' *; simplify_eq/=.
        destruct v1 => //; simplify_eq/=; destruct_all?; simplify_eq/=. tend.
        have ? : hb_bij bij' !! l'.1 = Some (HBShared l.1). {
          apply heap_bij_shared_lookup.
          apply: cmra_valid_included; [by apply: cmra_update_valid|].
          apply: cmra_included_op_l. by apply: cmra_mono_l.
        }
        split!.
        1: { by apply: heap_in_bij_alive. }
        apply: Hloop; [done|]. split!. 1: done. all: split!.
        1: apply heap_preserved_update; [done|naive_solver].
        1: by apply heap_in_bij_update.
      * tstep_s => *; simplify_eq/=.
        set (l' := (heap_fresh (dom _ (hb_bij bij')) hs)).
        eexists l'. split; [apply heap_fresh_is_fresh|] => *; simplify_eq/=. tend.
        destruct v => //; simplify_eq/=; destruct_all?; simplify_eq/=.
        split!.
        apply Hloop; [done|].
        unshelve eexists (heap_bij_add_shared l.1 l'.1 bij' _).
        { abstract (apply: not_elem_of_weaken; [|done]; unfold heap_is_fresh in *; naive_solver). }
        split!.
        1: { etrans; [done|]. apply cmra_update_op; [|done].
             rewrite heap_bij_alloc_shared; [|apply (heap_fresh_not_in (dom _ (hb_bij bij')) hs)].
             rewrite -assoc. apply cmra_update_op; [done|].
             apply cmra_update_included, cmra_included_core. }
        all: split!.
        1: { apply heap_preserved_alloc; [|by move => *; simplify_map_eq].
             by apply heap_preserved_add_shared. }
        1: { apply: ectx_in_bij_mono; [done| ]. apply cmra_core_mono. apply cmra_included_r. }
        1: { rewrite - {1}(core_id_core (heap_bij_shared _ _)). apply cmra_core_mono. apply cmra_included_l. }
        1: unfold heap_is_fresh in *; naive_solver.
        1: { apply: (heap_in_bij_alloc l l'); [|done|apply heap_fresh_is_fresh].
             apply: heap_in_bij_mono; [done|]. apply cmra_core_mono. apply cmra_included_r. }
        1: { etrans; [apply hb_shared_provs_add_shared|]. set_solver. }
      * tstep_s => l' *; simplify_eq/=. tend.
        destruct v => //; simplify_eq/=; destruct_all?; simplify_eq/=.
        have ? : hb_bij bij' !! l'.1 = Some (HBShared l.1). {
          apply heap_bij_shared_lookup.
          apply: cmra_valid_included; [by apply: cmra_update_valid|].
          apply: cmra_included_op_l. by apply: cmra_mono_l.
        }
        split!. 1: by apply: heap_in_bij_alive. apply: Hloop; [done|].
        split!. 1: done. all: split!.
        1: apply heap_preserved_free; [done|naive_solver].
        1: by apply heap_in_bij_free.
      * tstep_s => *; simplify_eq/=. destruct v => //; simplify_eq/=. tend.
        split!. apply: Hloop; [done|]. split!. 1: done. all: split!. all: by case_match.
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
          '(σm1, (σf, σ1, (pp, _, r)), σc1)
          '(σm2, σ2, σc2),
           σ1 = σ2 ∧ σc1 = σc2 ∧ ✓ r ∧
             ((σc1 = ICStart ∧ σf = SMFilter ∧ pp = PPOutside ∧ σm1 = σm2 ∧ σm2 = SMFilter ∧ r = ε) ∨
              ( ((∃ e, σf = SMProgRecv e ∧ σm2 = SMProgRecv e) ∨ (σf = SMProg ∧ σm2 = SMProg)
                 ) ∧ σm1 = SMProg ∧ σc1 = ICRunning ∧ pp = PPInside))
                             ). }
  { split!. apply ucmra_unit_valid. } { done. }
  move => {}n _ /= Hloop [[σm1 [[σf σ1] [[pp []] r]]] σc1] [[σm2 σ2] σc2] ?.
  destruct_all?; simplify_eq/=.
  - tstep_i. apply steps_impl_step_end => ???. invert_all' @m_step; simplify_eq/=. split!.
    tstep_s. eexists (Some (inr _)). split!. apply: steps_spec_step_end; [econs|] => ??. simplify_eq/=.
    tstep_i. apply steps_impl_step_end => ???. invert_all @m_step. split!.
    tstep_s. eexists (Some (inl _)). split!. apply: steps_spec_step_end; [econs|] => ??. simplify_eq/=.
    tstep_i => ??; simplify_eq/=.
    tstep_i. eexists ∅, (ValNum <$> vs), initial_heap_state, ε. split!.
    1: { rewrite !right_id. by apply gmap_view_auth_dfrac_valid. }
    1: { apply Forall2_fmap. apply Forall_Forall2_diag. by apply Forall_true. }
    apply: Hloop; [done|]. split!.
    1: { rewrite !right_id. by apply gmap_view_auth_dfrac_valid. }
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
      tstep_i. eexists _, [ValNum _]. split!.
      1: by apply: cmra_update_valid.
      1: done. 1: econs; [done|econs]. 1: done. 1: done.
      apply: Hloop; [done|]. split!.
      1: by apply: cmra_update_valid.
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
  pose (R := λ (b : bool) (s1 s2 : unit), True).
  apply: (imp_prepost_proof R); unfold R in *.
  (* { constructor. { move => [??]. naive_solver. } *)
  (*   { move => [??] [??] [??] [??] [??]. split; [by etrans|]. etrans; [done|]. *)
  (*     by apply: heap_preserved_mono. } } *)
  { naive_solver. }
  move => n K1 K2 f fn1 vs1 h0 [] r0 ? ?.
  rewrite !lookup_insert_Some => ?; destruct_all?; simplify_map_eq/=.
  move => bij1 ? h1 *. split!. move => ?. split!; [solve_length|].
  move => Hcall Hret.
  pose (l := (heap_fresh (dom _ (hb_bij bij1)) h1)).
  have Hf := heap_fresh_not_in (dom _ (hb_bij bij1)) h1.
  tstep_s. eexists l. split!. { apply heap_fresh_is_fresh. }
  move => *; simplify_eq.
  tstep_s. tstep_s. move => ? [<-] ?.
  tstep_s.
  apply: (Hcall _ _ ([LetECtx _ _]) ([LetECtx _ _])); [done|..].
  1, 2: by simplify_map_eq. 1,2: by econs.
  eexists (heap_bij_update_const l.1 _ bij1), [].
  split!.
  { rewrite -!assoc. etrans.
    { apply cmra_update_op; [|done]. apply (heap_bij_alloc_const _ l.1). set_solver. }
    rewrite -assoc. apply cmra_update_op; [done|].
    rewrite comm -assoc. done. }
  { etrans; [apply hb_shared_provs_update_const|]. done. }
  { econs. }
  { apply: heap_in_bij_update_r; [|move => *; simplify_map_eq].
    apply: heap_in_bij_alloc_r; [|move => *; simplify_map_eq].
    apply: heap_in_bij_mono_bij; [done|]. move => ?? /=/lookup_insert_Some?. naive_solver. }
  { apply heap_preserved_update_const.
    apply heap_preserved_update; [|move => *; simplify_map_eq].
    apply heap_preserved_alloc; [|move => *; simplify_map_eq].
    apply: heap_preserved_mono; [done|]. move => ?? /=/lookup_delete_Some?. naive_solver. }
  { apply cmra_included_l. }
  move => ? h2 [] ? bij3 ? h3 *. decompose_Forall_hyps.
  split!.
  tstep_i.
  tstep_s.
  tstep_s. move => ?? [<-] /heap_preserved_lookup_r Hlookup.
  eassert (hb_bij bij3 !! l.1 = Some (HBConstant _)). {
    apply heap_bij_const_lookup. apply: cmra_valid_included; [done|].
    rewrite -assoc. apply cmra_mono_l. apply cmra_included_op_r. etrans; [|done].
    apply cmra_included_r.
  }
  efeed pose proof Hlookup as Hlookup'; [done..|].
  simplify_map_eq.
  tstep_s.
  tstep_s => *. simplify_eq.
  tstep_s.
  apply: Hret; [done|].
  eexists (heap_bij_update_const _ _ _), [ValNum 1]. split!.
  { etrans. { by apply: cmra_update_op; [|by apply cmra_update_included]. }
    rewrite assoc comm !assoc.
    apply: cmra_update_op; [|done]. apply: cmra_update_op; [|done].
    rewrite comm. etrans; [apply heap_bij_frag_update_const|]. apply cmra_update_op_l. }
  all: split!.
  { etrans; [apply hb_shared_provs_update_const|]. done. }
  1: by econs.
  { apply heap_in_bij_free_r. {
      apply: heap_in_bij_mono_bij; [done|].
      move => /=?? /lookup_insert_Some. naive_solver. }
    move => ??. simplify_map_eq. }
  { apply heap_preserved_update_const.
    apply: heap_preserved_free; [ |move => *; simplify_map_eq].
    apply: heap_preserved_mono; [done|]. move => ?? /lookup_delete_Some; naive_solver.
  }
Qed.

Lemma bij_alloc_ctx_refines :
  imp_ctx_refines (<["f" := bij_alloc_opt]> ∅) (<["f" := bij_alloc]> ∅).
Proof.
  apply: imp_heap_bij_trefines_implies_ctx_refines. { set_solver. }
  apply bij_alloc_opt_refines.
Qed.
End imp_heap_bij_example.
