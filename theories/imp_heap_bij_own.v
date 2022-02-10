Require Export iris.algebra.cmra.
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

Section updates.
  Context {A : cmra}.
  Lemma cmra_update_included (x y : A) :
    x ≼ y → y ~~> x.
  Proof. move => [? ->]. apply cmra_update_op_l. Qed.
End updates.

Section total_updates.
  Local Set Default Proof Using "Type*".
  Context {A : ucmra}.
  Context `{CmraTotal A} `{CmraDiscrete A}.
  Lemma ucmra_discrete_update_valid (x y : A) :
    x ~~> y → ✓ x → ✓ y.
  Proof.
    move => /cmra_discrete_update Hv. have := (Hv (@ε A (ucmra_unit A))).
    rewrite comm left_id comm left_id. naive_solver.
  Qed.
End total_updates.

Section included.
  Context {A : cmra}.
  Implicit Types (x y z : A).
  Lemma cmra_included_op_l x y z : x ≼ y → x ≼ y ⋅ z.
  Proof. intros ?. etrans; [done|]. apply cmra_included_l. Qed.
  Lemma cmra_included_op_r x y z : x ≼ y → x ≼ z ⋅ y.
  Proof. intros ?. etrans; [done|]. apply cmra_included_r. Qed.
End included.


Section prepost.
Context {R : Type} {A : cmra}.

Definition pp_update (P x : A) (pp : A → prepost R) : prepost R :=
  pp_quant $ λ y,
  pp_prop (x ~~> P ⋅ y) $
  pp y.

Definition pp_own (P x : A) (pp : A → prepost R) : prepost R :=
  pp_prop (✓ (P ⋅ x)) $
  pp (P ⋅ x).
End prepost.


(** * camera definition *)
Inductive heap_bij_elem :=
| HBShared (p : prov) | HBConstant (h : Z → option val) | HBChanging.
Canonical Structure heap_bij_elemO := leibnizO heap_bij_elem.

Definition heap_bijUR : cmra := gmap_viewUR prov heap_bij_elemO.
(* Eval simpl in cmra_car heap_bijR. *)

(** * imp_heap_bij_own *)
Record heap_bij := HeapBij {
  hb_bij : gmap prov heap_bij_elem;
  hb_iff p1 p2 p1' p2' :
   hb_bij !! p2 = Some (HBShared p1) →
   hb_bij !! p2' = Some (HBShared p1') →
   p1 = p1' ↔ p2 = p2'
}.

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
  move => ??? Hnotin ????.
  rewrite !lookup_insert_Some => ??. destruct_all?; simplify_eq/= => //. 3: by apply: hb_iff.
  all: split => ?; simplify_eq; contradict Hnotin; apply elem_of_hb_shared_provs; naive_solver.
Qed.

Program Definition heap_bij_update_const (p : prov) (h : gmap loc val) (bij : heap_bij) :=
  HeapBij (<[p := HBConstant (λ o, h !! (p, o))]> (hb_bij bij)) _.
Next Obligation.
  move => ???????.
  rewrite !lookup_insert_Some => ??. destruct_all?; simplify_eq/= => //. by apply: hb_iff.
Qed.

Program Definition heap_bij_delete_prov (p : prov) (bij : heap_bij) :=
  HeapBij (delete p (hb_bij bij)) _.
Next Obligation.
  move => ??????.
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

(* Global Instance heap_bij_subseteq : SubsetEq heap_bij := *)
  (* λ bij1 bij2, ∀ p1 p2, hb_bij bij1 !! p2 = Some (HBShared p1) → hb_bij bij2 !! p2 = Some (HBShared p1). *)

Definition heap_bij_auth (bij : heap_bij) : heap_bijUR :=
  gmap_view_auth (DfracOwn 1) (hb_bij bij).

Definition heap_bij_shared (p1 p2 : prov) : heap_bijUR :=
  gmap_view_frag p2 DfracDiscarded (HBShared p1).

Definition heap_bij_const (p : prov) (f : Z → option val) : heap_bijUR :=
  gmap_view_frag p (DfracOwn 1) (HBConstant f).

Lemma heap_bij_alloc_shared bij p1 p2 H:
  p2 ∉ dom (gset _) (hb_bij bij) →
  heap_bij_auth bij ~~> heap_bij_auth (heap_bij_add_shared p1 p2 bij H) ⋅ heap_bij_shared p1 p2.
Proof. move => ?. apply gmap_view_alloc; [|done]. by apply not_elem_of_dom. Qed.

Lemma heap_bij_shared_lookup p1 p2 bij :
  ✓ (heap_bij_auth bij ⋅ heap_bij_shared p1 p2) →
  hb_bij bij !! p2 = Some (HBShared p1).
Proof. move => /gmap_view_both_valid_L. naive_solver. Qed.

Lemma heap_bij_alloc_const bij p h:
  p ∉ dom (gset _) (hb_bij bij) →
  heap_bij_auth bij ~~> heap_bij_auth (heap_bij_update_const p h bij) ⋅ heap_bij_const p (λ o, h !! (p, o)).
Proof. move => ?. apply gmap_view_alloc; [|done]. by apply not_elem_of_dom. Qed.

Lemma heap_bij_const_lookup p f bij :
  ✓ (heap_bij_auth bij ⋅ heap_bij_const p f) →
  hb_bij bij !! p = Some (HBConstant f).
Proof. move => /gmap_view_both_valid_L. naive_solver. Qed.

Lemma heap_bij_frag_update_const bij p f h:
  heap_bij_auth bij ⋅ heap_bij_const p f ~~>
  heap_bij_auth (heap_bij_update_const p h bij) ⋅ heap_bij_const p (λ o, h !! (p, o)).
Proof. apply gmap_view_update. Qed.

(** ** val_in_bij *)
Definition val_in_bij (r : heap_bijUR) (v1 v2 : val) : Prop :=
  match v1, v2 with
  | ValNum n1, ValNum n2 => n1 = n2
  | ValBool b1, ValBool b2 => b1 = b2
  | ValLoc l1, ValLoc l2 => heap_bij_shared l1.1 l2.1 ≼ r /\ l1.2 = l2.2
  | _, _ => False
  end.

Lemma val_in_bij_mono r r' v1 v2:
  val_in_bij r v1 v2 →
  core r ≼ r' →
  val_in_bij r' v1 v2.
Proof.
  destruct v1, v2 => //=. move => [??] ?. split; [|done].
  rewrite -(core_id_core (heap_bij_shared _ _)).
  etrans; [|done]. by apply cmra_core_mono.
Qed.

(** ** expr_in_bij *)
Fixpoint expr_in_bij (r : heap_bijUR) (e1 e2 : expr) {struct e1} : Prop :=
  match e1, e2 with
  | Var v, Var v' => v = v'
  | Val v, Val v' => val_in_bij r v v'
  | BinOp e1 o e2, BinOp e1' o' e2' => o = o' ∧ expr_in_bij r e1 e1' ∧ expr_in_bij r e2 e2'
  | Load e, Load e' => expr_in_bij r e e'
  | Store e1 e2, Store e1' e2' => expr_in_bij r e1 e1' ∧ expr_in_bij r e2 e2'
  | Alloc e, Alloc e' => expr_in_bij r e e'
  | Free e, Free e' => expr_in_bij r e e'
  | If e e1 e2, If e' e1' e2' => expr_in_bij r e e' ∧ expr_in_bij r e1 e1' ∧ expr_in_bij r e2 e2'
  | LetE v e1 e2, LetE v' e1' e2' => v = v' ∧ expr_in_bij r e1 e1' ∧ expr_in_bij r e2 e2'
  | Call f args, Call f' args' => f = f' ∧ length args = length args' ∧
                                   Forall id (zip_with (expr_in_bij r) args args')
  | UbE, UbE => True
  | ReturnExt b e, ReturnExt b' e' => b = b' ∧ expr_in_bij r e e'
  | Waiting b, Waiting b' => b = b'
  | _, _ => False
  end.

Lemma Forall2_bij_val_inv_l r vl el :
  Forall2 (expr_in_bij r) (Val <$> vl) el →
  ∃ vl', el = Val <$> vl' ∧ Forall2 (val_in_bij r) vl vl'.
Proof.
  elim: vl el; csimpl. { move => ? /Forall2_nil_inv_l->. by eexists []. }
  move => ?? IH ? /(Forall2_cons_inv_l _ _)[v' [?[?[/IH[?[??]]?]]]]; subst.
  destruct v' => //. eexists (_::_). split; [done|]. by econs.
Qed.

Lemma Forall2_bij_val_inv_r r vl el :
  Forall2 (expr_in_bij r) el (Val <$> vl) →
  ∃ vl', el = Val <$> vl' ∧ Forall2 (val_in_bij r) vl' vl.
Proof.
  elim: vl el; csimpl. { move => ? /Forall2_nil_inv_r->. by eexists []. }
  move => ?? IH ? /(Forall2_cons_inv_r _ _ _ _) [v' [?[?[/IH[?[??]] ?]]]]; subst.
  destruct v' => //. eexists (_::_). split; [done|]. by econs.
Qed.

Lemma expr_in_bij_mono r r' e1 e2:
  expr_in_bij r e1 e2 →
  core r ≼ r' →
  expr_in_bij r' e1 e2.
Proof.
  elim: e1 e2 => //=*; repeat case_match => //; try naive_solver (eauto using val_in_bij_mono).
  destruct_all?; simplify_eq. split!.
  revert select (Forall id _). generalize dependent args.
  revert select (Forall _ _). elim. { by case. }
  move => ????? []//=??? *; decompose_Forall_hyps. econs; naive_solver.
Qed.

Lemma expr_in_bij_subst r x v e v' e':
  expr_in_bij r e e' →
  val_in_bij r v v' →
  expr_in_bij r (subst x v e) (subst x v' e').
Proof.
  elim: e e' => //= *; repeat (case_match => //); simplify_eq/=; repeat case_bool_decide => //; try naive_solver.
  destruct_all?. rewrite !fmap_length. split!.
  revert select (Forall _ _). generalize dependent args.
  revert select (Forall _ _). elim. { by case. }
  move => ????? []//=??? /(Forall_cons_1 _ _)[??]. econs; naive_solver.
Qed.

Lemma expr_in_bij_subst_l r xs vs e vs' e':
  expr_in_bij r e e' →
  Forall2 (val_in_bij r) vs vs' →
  length xs = length vs →
  expr_in_bij r (subst_l xs vs e) (subst_l xs vs' e').
Proof.
  move => He Hall. elim: Hall xs e e' He. { by case. }
  move => ?????? IH []//=??????. apply: IH; [|lia]. by apply expr_in_bij_subst.
Qed.

Lemma expr_in_bij_static r e:
  static_expr false e →
  expr_in_bij r e e.
Proof.
  elim: e => //=; try naive_solver. { by case. }
  move => ?? IH Hb. split!.
  elim: IH Hb => //=; econs; naive_solver.
Qed.

(** ** ectx_in_bij *)
Definition ectx_item_in_bij (r : heap_bijUR) (Ki Ki' : expr_ectx) : Prop :=
  match Ki, Ki' with
  | BinOpLCtx op e2, BinOpLCtx op' e2' => op = op' ∧ expr_in_bij r e2 e2'
  | BinOpRCtx v1 op, BinOpRCtx v1' op' => op = op' ∧ val_in_bij r v1 v1'
  | LoadCtx, LoadCtx => True
  | StoreLCtx e2, StoreLCtx e2' => expr_in_bij r e2 e2'
  | StoreRCtx v1, StoreRCtx v1' => val_in_bij r v1 v1'
  | AllocCtx, AllocCtx => True
  | FreeCtx, FreeCtx => True
  | IfCtx e2 e3, IfCtx e2' e3' => expr_in_bij r e2 e2' ∧ expr_in_bij r e3 e3'
  | LetECtx v e2, LetECtx v' e2' => v = v' ∧ expr_in_bij r e2 e2'
  | CallCtx f vl el, CallCtx f' vl' el' => f = f' ∧ Forall2 (val_in_bij r) vl vl' ∧
                                            Forall2 (expr_in_bij r) el el'
  | ReturnExtCtx b, ReturnExtCtx b' => b = b'
  | _, _ => False
  end.

Definition ectx_in_bij (r : heap_bijUR) (K1 K2 : list expr_ectx) : Prop :=
  Forall2 (ectx_item_in_bij r) K1 K2.

Lemma ectx_item_in_bij_mono r r' K1 K2:
  ectx_item_in_bij r K1 K2 →
  core r ≼ r' →
  ectx_item_in_bij r' K1 K2.
Proof.
  destruct K1, K2 => //=; try naive_solver (eauto using expr_in_bij_mono, val_in_bij_mono).
  move => [?[??]] ?. split_and!; [done|..].
  all: apply: Forall2_impl; [done|]; eauto using expr_in_bij_mono, val_in_bij_mono.
Qed.

Lemma ectx_in_bij_mono r r' K1 K2:
  ectx_in_bij r K1 K2 →
  core r ≼ r' →
  ectx_in_bij r' K1 K2.
Proof. move => ??. apply: Forall2_impl; [done|]. move => *; by apply: ectx_item_in_bij_mono.  Qed.

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

Lemma expr_in_bij_fill_item_l r Ki e1 e2 :
  expr_in_bij r (expr_fill_item Ki e1) e2 →
  ∃ Ki' e', e2 = expr_fill_item Ki' e' ∧ ectx_item_in_bij r Ki Ki' ∧ expr_in_bij r e1 e'.
Proof.
  destruct Ki, e2 => //= *; destruct_all?; simplify_eq; try case_match => //; simplify_eq. 10: {
    revert select (Forall _ _) => /Forall_zip_with_1 Hall.
    move: (Hall ltac:(done)) => /Forall2_app_inv_l[?[?[Hv[/(Forall2_cons_inv_l _ _)[?[?[?[??]]]]?]]]]. simplify_eq.
    move: Hv => /Forall2_bij_val_inv_l[?[??]]. simplify_eq.
    by eexists (CallCtx _ _ _), _.
  }
  all: (unshelve eexists _); [econs; shelve| naive_solver].
Qed.

Lemma expr_in_bij_fill_l r K e1 e2 :
  expr_in_bij r (expr_fill K e1) e2 →
  ∃ K' e', e2 = expr_fill K' e' ∧ ectx_in_bij r K K' ∧ expr_in_bij r e1 e'.
Proof.
  elim: K e1 e2 => /=. { move => *. eexists [], _. split!. econs. }
  move => Ki K IH e1 e2 /IH[K'[?[?[?/expr_in_bij_fill_item_l?]]]].
  destruct_all?; simplify_eq. eexists (_ :: _), _ => /=. split_and!; [done| |done].
  by econs.
Qed.

Lemma eval_binop_bij o v1 v2 v1' v2' v r:
  eval_binop o v1 v2 = Some v →
  val_in_bij r v1' v1 →
  val_in_bij r v2' v2 →
  ∃ v', eval_binop o v1' v2' = Some v' ∧
       val_in_bij r v' v.
Proof.
  destruct o, v1, v2, v1', v2' => //= *; destruct_all?; simplify_eq. all: split!.
  lia.
Qed.

(** *** heap_in_bij *)
Definition heap_in_bij (bij : heap_bij) (r : heap_bijUR) (h h' : heap_state) : Prop :=
  ∀ p1 p2 o,
  hb_bij bij !! p2 = Some (HBShared p1) →

  (is_Some (h.(h_heap) !! (p1, o)) ↔ is_Some (h'.(h_heap) !! (p2, o)))
  /\
  ∀ v1 v2,
  h.(h_heap)  !! (p1, o) = Some v1 →
  h'.(h_heap) !! (p2, o) = Some v2 →
  val_in_bij r v1 v2.

Lemma heap_in_bij_mono bij r r' h h':
  heap_in_bij bij r h h' →
  core r ≼ r' →
  heap_in_bij bij r' h h'.
Proof.
  move => Hbij ? ????. split; [by apply Hbij|].
  move => ????. apply: val_in_bij_mono; [|done].
  by eapply Hbij.
Qed.

Lemma heap_in_bij_mono_bij bij bij' r h h':
  heap_in_bij bij r h h' →
  (∀ p1 p2, hb_bij bij' !! p2 = Some (HBShared p1) → hb_bij bij !! p2 = Some (HBShared p1)) →
  heap_in_bij bij' r h h'.
Proof. unfold heap_in_bij => Hp ?????. apply: Hp. naive_solver. Qed.

Lemma heap_in_bij_alive bij r h1 h2 l1 l2:
  heap_in_bij bij r h1 h2 →
  heap_alive h2 l2 →
  hb_bij bij !! l2.1 = Some (HBShared l1.1) →
  l1.2 = l2.2 →
  heap_alive h1 l1.
Proof.
  move => ? Hbij ??. destruct l1 as [p1 ?], l2 as [p2 o]; simplify_eq/=.
  unfold heap_in_bij, heap_alive in *. naive_solver.
Qed.

Lemma heap_in_bij_lookup bij r h1 h2 l1 l2 v:
  h_heap h2 !! l2 = Some v →
  heap_in_bij bij r h1 h2 →
  hb_bij bij !! l2.1 = Some (HBShared l1.1) →
  l1.2 = l2.2 →
  ∃ v', h_heap h1 !! l1 = Some v' ∧ val_in_bij r v' v.
Proof.
  move => ? Hbij ??. destruct l1 as [p1 ?], l2 as [p2 o]; simplify_eq/=.
  have [[? H2]?]:= Hbij _ _ o ltac:(done).
  have [??]:= H2 ltac:(done).
  naive_solver.
Qed.

Lemma heap_in_bij_update bij r h1 h2 l1 l2 v1 v2:
  heap_in_bij bij r h1 h2 →
  val_in_bij r v1 v2 →
  hb_bij bij !! l2.1 = Some (HBShared l1.1) →
  l1.2 = l2.2 →
  heap_in_bij bij r (heap_update h1 l1 v1) (heap_update h2 l2 v2).
Proof.
  move => Hbij ???. destruct l1 as [p1 ?], l2 as [p2 o]; simplify_eq/=.
  move => p1' p2' o' /=?. have : p1 = p1' ↔ p2 = p2' by apply: hb_iff.
  split.
  - rewrite !lookup_alter_is_Some. by apply Hbij.
  - move => ?? /lookup_alter_Some[[?[?[??]]]|[??]] /lookup_alter_Some[[?[?[??]]]|[??]]; simplify_eq.
    all: try by eapply Hbij. all: naive_solver.
Qed.

Lemma heap_in_bij_update_r bij r h1 h2 l2 v2:
  heap_in_bij bij r h1 h2 →
  (∀ p, hb_bij bij !! l2.1 = Some (HBShared p) → False) →
  heap_in_bij bij r h1 (heap_update h2 l2 v2).
Proof.
  move => Hbij Hin ? ??? /=.
  rewrite !lookup_alter_ne. 1: by apply Hbij.
  naive_solver.
Qed.

Lemma heap_in_bij_alloc l1 l2 hi hs n bij r H:
  heap_in_bij bij r hi hs →
  heap_is_fresh hi l1 →
  heap_is_fresh hs l2 →
  heap_in_bij (heap_bij_add_shared l1.1 l2.1 bij H) r (heap_alloc hi l1 n) (heap_alloc hs l2 n).
Proof.
  move => /= Hbij [Hi1 ?] [Hi2 ?]  p1 p2 o /= /lookup_insert_Some[[??]|[??]]; simplify_eq.
  - destruct l1 as [p1 ?], l2 as [p2 ?]; simplify_eq/=.
    rewrite !lookup_union_l'.
    2: { apply eq_None_ne_Some => ??. apply Hi2. by apply: (heap_wf _ (_, _)). }
    2: { apply eq_None_ne_Some => ??. apply Hi1. by apply: (heap_wf _ (_, _)). }
    split.
    + rewrite !list_to_map_lookup_is_Some. f_equiv => ?. rewrite !elem_of_list_fmap.
      f_equiv => ?. naive_solver.
    + move => ?? /(elem_of_list_to_map_2 _ _ _)/elem_of_list_fmap[?[??]].
      move => /(elem_of_list_to_map_2 _ _ _)/elem_of_list_fmap[?[??]]. by simplify_eq/=.
  -
    have ? : p1 ≠ l1.1. { contradict H. apply elem_of_hb_shared_provs. naive_solver. }
    (* have ? : p2 ≠ l2.1 by contradict H2; set_unfold; left; left; eexists (_, _); naive_solver. *)
    have [Hbij1 Hbij2]:= Hbij p1 p2 o ltac:(set_solver).
    rewrite !lookup_union_r.
    2, 3: apply not_elem_of_list_to_map_1;
        move => /elem_of_list_fmap[[[??]?] [?/elem_of_list_fmap[?[??]]]]; simplify_eq/=.
    split; [done|] => *. apply: val_in_bij_mono; [naive_solver|]. apply cmra_included_core.
Qed.

Lemma heap_in_bij_alloc_r l2 hi hs n bij r:
  heap_in_bij bij r hi hs →
  (∀ p, hb_bij bij !! l2.1 = Some (HBShared p) → False) →
  heap_in_bij bij r hi (heap_alloc hs l2 n).
Proof.
  move => /= Hbij Hin ???? /=. rewrite lookup_union_r. 1: by apply Hbij.
  apply not_elem_of_list_to_map_1.
  move => /elem_of_list_fmap[[??][?/elem_of_list_fmap[?[??]]]]; simplify_eq/=.
  naive_solver.
Qed.

Lemma heap_in_bij_free r hi hs l1 l2 bij:
  heap_in_bij bij r hi hs →
  hb_bij bij !! l2.1 = Some (HBShared l1.1) →
  heap_in_bij bij r (heap_free hi l1) (heap_free hs l2).
Proof.
  move => Hbij Hin p1 p2 o /=?.
  have [Hbij1 Hbij2]:= Hbij p1 p2 o ltac:(done).
  have ?: p1 = l1.1 ↔ p2 = l2.1 by apply: hb_iff.
  split.
  - rewrite !map_filter_lookup /=. destruct (h_heap hi !! (p1, o)), (h_heap hs !! (p2, o)) => //=.
    all: repeat case_option_guard => //; naive_solver.
  - move => ??. rewrite !map_filter_lookup => /bind_Some[?[??]] /bind_Some[?[??]].
    repeat case_option_guard => //; naive_solver.
Qed.

Lemma heap_in_bij_free_r l2 hi hs bij r:
  heap_in_bij bij r hi hs →
  (∀ p, hb_bij bij !! l2.1 = Some (HBShared p) → False) →
  heap_in_bij bij r hi (heap_free hs l2).
Proof.
  move => /= Hbij Hin ???? /=. rewrite map_filter_lookup_true. 1: by apply Hbij.
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

Definition imp_heap_bij_pre (e : imp_event) (s : heap_bijUR) : prepost (imp_event * heap_bijUR) :=
  let ho := heap_of_event e.2 in
  pp_quant $ λ bij,
  pp_quant $ λ vsi,
  pp_quant $ λ hi,
  pp_quant $ λ r',
  pp_own (heap_bij_auth bij ⋅ r') s $ λ y,
  (* TODO: should we also have the following for hi? We don't need it so far... *)
  pp_prop (hb_shared_provs bij ⊆ h_provs ho) $
  pp_prop (Forall2 (val_in_bij r') (vals_of_event e.2) vsi) $
  pp_prop (heap_in_bij bij r' ho hi) $
  pp_prop (heap_preserved bij hi) $
  pp_end ((e.1, event_set_vals_heap e.2 vsi hi), y).

Definition imp_heap_bij_post (e : imp_event) (s : heap_bijUR) : prepost (imp_event * heap_bijUR) :=
  let hi := heap_of_event e.2 in
  pp_quant $ λ bij,
  pp_quant $ λ vso,
  pp_quant $ λ ho,
  pp_quant $ λ r',
  pp_update (heap_bij_auth bij ⋅ r') s $ λ y,
  (* TODO: should we also have the following for hi? We don't need it so far... *)
  pp_prop (hb_shared_provs bij ⊆ h_provs ho) $
  pp_prop (Forall2 (val_in_bij r') vso (vals_of_event e.2)) $
  pp_prop (heap_in_bij bij r' ho hi) $
  pp_prop (heap_preserved bij hi) $
  pp_end ((e.1, event_set_vals_heap e.2 vso ho), y).

Definition imp_heap_bij (m : module imp_event) : module imp_event :=
  mod_prepost imp_heap_bij_pre imp_heap_bij_post m.

Definition initial_imp_heap_bij_state (m : module imp_event) (σ : m.(m_state)) :=
  (@SMFilter imp_event, σ, (@PPOutside imp_event imp_event, @ε heap_bijUR _)).

Local Ltac split_solve :=
  match goal with
  | |- heap_in_bij ?p _ _ _ => is_evar p; eassumption
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
      (λ ips r1 r2 r ics1 ics2,
          ics1 = ics2 ∧
            ✓ r ∧
       ((ips = SPNone ∧
          r ≡ r1 ⋅ r2) ∨
        ((ips = SPLeft ∧
          r ~~> r1 ⋅ r2) ∨
         (ips = SPRight ∧
          r ~~> r1 ⋅ r2)))). }
  { move => ?? [] /=*; naive_solver. }
  { split!. 1: apply ucmra_unit_valid. 1: by rewrite left_id.  }
  all: move => r1 r2 r ics1 ics2.
  - move => e ics' e' /= ? [? [Hvalid [[? Hequiv]|[?|?]]]] *; destruct_all?; simplify_eq/=.
    split!.
    { apply: cmra_valid_included; [done|]. apply cmra_mono_l.
      rewrite Hequiv. by apply cmra_included_l. }
    all: split!.
    1: by destruct e.
    1: by rewrite Hequiv assoc.
  - move => e ics' e' /= ? [? [Hvalid [[? Hequiv]|[?|?]]]] *; destruct_all?; simplify_eq/=.
    split!.
    { apply: cmra_valid_included; [done|]. apply cmra_mono_l.
      rewrite Hequiv. by apply cmra_included_r. }
    all: split!.
    1: by destruct e.
    1: by rewrite (comm _ r1) -(assoc _ _ r2) (comm _ r2) Hequiv.
  - move => [? e] /= [? [Hvalid [?|[[? Hr]|?]]]] *; destruct_all?; simplify_eq/=.
    revert select (_ ~~> _) => Hupdate. rewrite Hupdate in Hr.
    split!.
    1: { apply: cmra_valid_included; [by apply: ucmra_discrete_update_valid|].
         apply cmra_mono_r. by apply cmra_included_l. }
    all: rewrite ?heap_of_event_event_set_vals_heap; split!.
    1: { rewrite vals_of_event_event_set_vals_heap //. by apply: Forall2_length. }
    1: done.
    all: split!.
    1: { rewrite comm -assoc (comm _ r2) assoc. done. }
    1: by destruct e.
    1: by destruct e.
  - move => [? e] /= [? [Hvalid [?|[[? Hr]|?]]]] *; destruct_all?; simplify_eq/=.
    revert select (_ ~~> _) => Hupdate. rewrite Hupdate in Hr.
    split!.
    1: by destruct e.
    3: done.
    1: { rewrite assoc. done. }
    1: { apply: cmra_valid_included; [by apply: ucmra_discrete_update_valid|].
         apply cmra_mono_r. by apply cmra_included_r. }
  - move => [? e] /= [? [Hvalid [?|[?|[? Hr]]]]] *; destruct_all?; simplify_eq/=.
    revert select (_ ~~> _) => Hupdate. rewrite Hupdate in Hr.
    split!.
    1: { apply: cmra_valid_included; [by apply: ucmra_discrete_update_valid|].
         rewrite comm. apply cmra_mono_l. by apply cmra_included_l. }
    all: rewrite ?heap_of_event_event_set_vals_heap; split!.
    1: { rewrite vals_of_event_event_set_vals_heap //. by apply: Forall2_length. }
    1: done.
    all: split!.
    1: { rewrite -assoc (comm _ r1) assoc comm. done. }
    1: by destruct e.
    1: by destruct e.
  - move => [? e] /= [? [Hvalid [?|[?|[? Hr]]]]] *; destruct_all?; simplify_eq/=.
    revert select (_ ~~> _) => Hupdate. rewrite Hupdate in Hr.
    split!.
    1: by destruct e.
    3: done.
    1: { rewrite (comm _ r1) assoc comm. done. }
    1: { apply: cmra_valid_included. 1: by apply: ucmra_discrete_update_valid.
         apply cmra_mono_l. by apply cmra_included_r. }
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

Lemma imp_heap_bij_imp_refl fns:
  trefines (MS imp_module (initial_imp_state fns))
           (MS (imp_heap_bij imp_module)
               (initial_imp_heap_bij_state imp_module (initial_imp_state fns))).
Proof.
  pose (R := λ (b : bool) (r1 r2 : heap_bijUR), r1 ≼ r2).
  apply: (imp_prepost_proof R); unfold R in *.
  { move => ? ?. naive_solver. }
  move => n K1 K2 f fn1 vs1 h1 r0 ?? /= bij *.
  split!. move => ?. split; [solve_length|].
  move => Hcall Hret.
  unshelve apply: tsim_remember. { simpl. exact (λ _ '(Imp ei hi fnsi) '(ips, Imp es hs fnss, (pp, r')),
    ∃ bij' ei' es' rvs,
    fnsi = fns ∧ fnss = fns ∧
    r' ~~> heap_bij_auth bij' ⋅ core rvs ⋅ r0 ∧
    ✓ r' ∧
    heap_preserved bij' hs ∧
    ei = expr_fill K1 ei' ∧
    es = expr_fill K2 es' ∧
    expr_in_bij (core rvs) ei' es' ∧
    heap_in_bij bij' (core rvs) hi hs ∧
    hb_shared_provs bij' ⊆ h_provs hi ∧
    pp = PPInside ∧
    static_expr true ei' ∧
    ips = SMProg
 ). }
  { split!.
    { apply cmra_update_op; [|done]. apply cmra_update_op; [done|]. apply cmra_update_included.
      apply cmra_included_core. }
    all: split!.
    { apply expr_in_bij_subst_l; [| |solve_length].
      - apply expr_in_bij_static. apply fd_static.
      - apply: Forall2_impl; [done|]. move => ???. by apply: val_in_bij_mono. }
    { by apply: heap_in_bij_mono. }
    { apply static_expr_subst_l; [|solve_length]. apply static_expr_mono. apply fd_static. }  }
  { naive_solver. }
  move => /= n' ? Hloop [ei hi fnsi] [[ips [es hs fnss]] [pp r]] ?. destruct_all?; simplify_eq.
  destruct (to_val ei') eqn:?.
  - destruct ei' => //; simplify_eq/=. destruct es' => //; simplify_eq/=.
    apply Hret; [done|]. clear Hloop Hret Hcall. split!.
    1: done. all: split!.
    1: { by econs; [|done]. }
    1: done.
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
          apply: cmra_valid_included; [by apply: ucmra_discrete_update_valid|].
          apply: cmra_included_op_l. by apply: cmra_mono_l. }
        split!. 1: done.
        apply: Hloop; [done|]. split!. 1: done. all: split!.
      * tstep_s => l' *; simplify_eq/=.
        destruct v1 => //; simplify_eq/=; destruct_all?; simplify_eq/=. tend.
        have ? : hb_bij bij' !! l'.1 = Some (HBShared l.1). {
          apply heap_bij_shared_lookup.
          apply: cmra_valid_included; [by apply: ucmra_discrete_update_valid|].
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
          apply: cmra_valid_included; [by apply: ucmra_discrete_update_valid|].
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
          '(σm1, (σf, σ1, (pp, r)), σc1)
          '(σm2, σ2, σc2),
           σ1 = σ2 ∧ σc1 = σc2 ∧ ✓ r ∧
             ((σc1 = ICStart ∧ σf = SMFilter ∧ pp = PPOutside ∧ σm1 = σm2 ∧ σm2 = SMFilter ∧ r = ε) ∨
              ( ((∃ e, σf = SMProgRecv e ∧ σm2 = SMProgRecv e) ∨ (σf = SMProg ∧ σm2 = SMProg)
                 ) ∧ σm1 = SMProg ∧ σc1 = ICRunning ∧ pp = PPInside))
                             ). }
  { split!. apply ucmra_unit_valid. } { done. }
  move => {}n _ /= Hloop [[σm1 [[σf σ1] [pp r]]] σc1] [[σm2 σ2] σc2] ?. destruct_all?; simplify_eq/=.
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
      1: by apply: ucmra_discrete_update_valid.
      1: done. 1: econs; [done|econs]. 1: done. 1: done.
      apply: Hloop; [done|]. split!.
      1: by apply: ucmra_discrete_update_valid.
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
  pose (R := λ (b : bool) (r1 r2 : heap_bijUR), r1 ≼ r2).
  apply: (imp_prepost_proof R); unfold R in *.
  (* { constructor. { move => [??]. naive_solver. } *)
  (*   { move => [??] [??] [??] [??] [??]. split; [by etrans|]. etrans; [done|]. *)
  (*     by apply: heap_preserved_mono. } } *)
  { move => [??] [??]. naive_solver. }
  move => n K1 K2 f fn1 vs1 h0 r0 ?.
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
  move => ? h2 r2 ? bij3 ? h3 *. decompose_Forall_hyps.
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
