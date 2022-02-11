Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.filter.
Require Import refframe.product.
Require Import refframe.seq_product.
Require Import refframe.link.
Require Import refframe.prepost.
Require Import refframe.proof_techniques.
Require Import refframe.imp.

(** * imp_heap_bij *)
Record heap_bij := HeapBij {
  hb_bij : gset (prov * prov);
  hb_env : gset prov;
  hb_prog : gset prov;
  hb_disj_env : hb_env ## set_map snd hb_bij;
  hb_disj_prog : hb_prog ## set_map snd hb_bij;
  hb_disj_priv : hb_prog ## hb_env;
  hb_iff p1 p2 p1' p2' : (p1, p2) ∈ hb_bij → (p1', p2') ∈ hb_bij → p1 = p1' ↔ p2 = p2'
}.

Global Program Instance imp_heap_bij_empty : Empty heap_bij :=
  HeapBij ∅ ∅ ∅ _ _ _ _.
Solve Obligations with set_solver.

Definition hb_provs_right (bij : heap_bij) : gset prov :=
  (set_map snd (hb_bij bij) ∪ hb_env bij ∪ hb_prog bij).

Definition heap_bij_extend (p : player) (bij bij' : heap_bij) :=
  hb_bij bij ⊆ hb_bij bij' ∧
  (if p is Env then hb_env bij ⊆ hb_env bij' else hb_env bij = hb_env bij') ∧
  (if p is Prog then hb_prog bij ⊆ hb_prog bij' else hb_prog bij = hb_prog bij').

Global Instance heap_bij_extend_preorder p : PreOrder (heap_bij_extend p).
Proof.
  unfold heap_bij_extend. constructor.
  - move => *. destruct p;set_solver.
  - move => *. destruct p;set_solver.
Qed.
Global Typeclasses Opaque heap_bij_extend.

Program Definition heap_bij_add_loc (p1 p2 : prov) (bij : heap_bij)
        (H : p1 ∉ set_map (D:=gset _) fst (hb_bij bij)) (_ : p2 ∉ hb_provs_right bij) :=
  HeapBij ({[ (p1, p2 )]} ∪ hb_bij bij) (hb_env bij) (hb_prog bij) _ _ _ _.
Next Obligation.
  move => ?????. rewrite set_map_union_L. apply disjoint_union_r. split; [|apply hb_disj_env].
  rewrite set_map_singleton_L disjoint_singleton_r. set_solver.
Qed.
Next Obligation.
  move => ?????. rewrite set_map_union_L. apply disjoint_union_r. split; [|apply hb_disj_prog].
  rewrite set_map_singleton_L disjoint_singleton_r. set_solver.
Qed.
Next Obligation. move => *. apply hb_disj_priv. Qed.
Next Obligation.
  move => ??? Hl Hr??????. set_unfold.
  destruct_all?; simplify_eq => //.
  - split => ?;  [contradict Hl | contradict Hr; left; left]; eexists (_,_); naive_solver.
  - split => ?;  [contradict Hl | contradict Hr; left; left]; eexists (_,_); naive_solver.
  - by apply: hb_iff.
Qed.

Program Definition heap_bij_add_prog (p2 : prov) (bij : heap_bij) (_ : p2 ∉ hb_provs_right bij) :=
  HeapBij (hb_bij bij) (hb_env bij) ({[ p2 ]} ∪ hb_prog bij) _ _ _ _.
Next Obligation. move => ???. apply: hb_disj_env. Qed.
Next Obligation.
  move => ???. apply disjoint_union_l. split; [|apply hb_disj_prog].
  rewrite disjoint_singleton_l. set_solver.
Qed.
Next Obligation.
  move => ???. apply disjoint_union_l. split; [|apply hb_disj_priv].
  rewrite disjoint_singleton_l. set_solver.
Qed.
Next Obligation. move => ????. apply: hb_iff. Qed.

(** ** val_in_bij *)
Definition val_in_bij (bij : gset (prov * prov)) (v1 v2 : val) : Prop :=
  match v1, v2 with
  | ValNum n1, ValNum n2 => n1 = n2
  | ValBool b1, ValBool b2 => b1 = b2
  | ValLoc l1, ValLoc l2 => (l1.1, l2.1) ∈ bij /\ l1.2 = l2.2
  | _, _ => False
  end.

Lemma val_in_bij_mono bij bij' v1 v2:
  val_in_bij bij v1 v2 →
  bij ⊆ bij' →
  val_in_bij bij' v1 v2.
Proof. destruct v1, v2 => //=. set_solver. Qed.

(** ** expr_in_bij *)
Fixpoint expr_in_bij (bij : gset (prov * prov)) (e1 e2 : expr) {struct e1} : Prop :=
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
Definition ectx_item_in_bij (bij : gset (prov * prov)) (Ki Ki' : expr_ectx) : Prop :=
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

Definition ectx_in_bij (bij : gset (prov * prov)) (K1 K2 : list expr_ectx) : Prop :=
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
Definition heap_in_bij (bij : gset (prov * prov)) (h h' : heap_state) : Prop :=
  ∀ p1 p2 o,
  (p1, p2) ∈ bij →

  (is_Some (h.(h_heap) !! (p1, o)) ↔ is_Some (h'.(h_heap) !! (p2, o)))
  /\
  ∀ v1 v2,
  h.(h_heap)  !! (p1, o) = Some v1 →
  h'.(h_heap) !! (p2, o) = Some v2 →
  val_in_bij bij v1 v2.

Lemma heap_in_bij_alive bij h1 h2 l1 l2:
  heap_in_bij bij h1 h2 →
  heap_alive h2 l2 →
  (l1.1, l2.1) ∈ bij →
  l1.2 = l2.2 →
  heap_alive h1 l1.
Proof.
  move => ? Hbij ??. destruct l1 as [p1 ?], l2 as [p2 o]; simplify_eq/=.
  unfold heap_in_bij, heap_alive in *. naive_solver.
Qed.

Lemma heap_in_bij_lookup bij h1 h2 l1 l2 v:
  h_heap h2 !! l2 = Some v →
  heap_in_bij bij h1 h2 →
  (l1.1, l2.1) ∈ bij →
  l1.2 = l2.2 →
  ∃ v', h_heap h1 !! l1 = Some v' ∧ val_in_bij bij v' v.
Proof.
  move => ? Hbij ??. destruct l1 as [p1 ?], l2 as [p2 o]; simplify_eq/=.
  have [[? H2]?]:= Hbij _ _ o ltac:(done).
  have [??]:= H2 ltac:(done).
  naive_solver.
Qed.

Lemma heap_in_bij_update bij h1 h2 l1 l2 v1 v2:
  heap_in_bij (hb_bij bij) h1 h2 →
  val_in_bij (hb_bij bij) v1 v2 →
  (l1.1, l2.1) ∈ (hb_bij bij) →
  l1.2 = l2.2 →
  heap_in_bij (hb_bij bij) (heap_update h1 l1 v1) (heap_update h2 l2 v2).
Proof.
  move => Hbij ???. destruct l1 as [p1 ?], l2 as [p2 o]; simplify_eq/=.
  move => p1' p2' o' /=?. have : p1 = p1' ↔ p2 = p2' by apply: hb_iff.
  split.
  - rewrite !lookup_alter_is_Some. by apply Hbij.
  - move => ?? /lookup_alter_Some[[?[?[??]]]|[??]] /lookup_alter_Some[[?[?[??]]]|[??]]; simplify_eq.
    all: try by eapply Hbij. all: naive_solver.
Qed.

Lemma heap_in_bij_update_r bij h1 h2 l2 v2:
  heap_in_bij bij h1 h2 →
  l2.1 ∉ set_map (D:=gset _) snd bij →
  heap_in_bij bij h1 (heap_update h2 l2 v2).
Proof.
  move => Hbij Hin ? ??? /=.
  rewrite !lookup_alter_ne. 1: by apply Hbij.
  contradict Hin; subst => /=. apply elem_of_map.
  eexists (_, _). naive_solver.
Qed.

Lemma heap_in_bij_alloc l1 l2 hi hs n bij H1 H2:
  heap_in_bij (hb_bij bij) hi hs →
  heap_is_fresh hi l1 →
  heap_is_fresh hs l2 →
  heap_in_bij (hb_bij (heap_bij_add_loc l1.1 l2.1 bij H1 H2)) (heap_alloc hi l1 n) (heap_alloc hs l2 n).
Proof.
  move => /= Hbij [Hi1 ?] [Hi2 ?] p1 p2 o /= /elem_of_union[?|?].
  - set_unfold; simplify_eq. destruct l1 as [p1 ?], l2 as [p2 ?]; simplify_eq/=.
    rewrite !lookup_union_l'.
    2: { apply eq_None_ne_Some => ??. apply Hi2. by apply: (heap_wf _ (_, _)). }
    2: { apply eq_None_ne_Some => ??. apply Hi1. by apply: (heap_wf _ (_, _)). }
    split.
    + rewrite !list_to_map_lookup_is_Some. f_equiv => ?. rewrite !elem_of_list_fmap. f_equiv => ?. naive_solver.
    + move => ?? /(elem_of_list_to_map_2 _ _ _)/elem_of_list_fmap[?[??]].
      move => /(elem_of_list_to_map_2 _ _ _)/elem_of_list_fmap[?[??]]. by simplify_eq/=.
  - have ? : p1 ≠ l1.1 by contradict H1; set_unfold; eexists (_, _); naive_solver.
    have ? : p2 ≠ l2.1 by contradict H2; set_unfold; left; left; eexists (_, _); naive_solver.
    have [Hbij1 Hbij2]:= Hbij p1 p2 o ltac:(set_solver).
    rewrite !lookup_union_r.
    2, 3: apply not_elem_of_list_to_map_1;
        move => /elem_of_list_fmap[[[??]?] [?/elem_of_list_fmap[?[??]]]]; simplify_eq/=.
    split; [done|] => *. apply: val_in_bij_mono; [naive_solver|]. set_solver.
Qed.

Lemma heap_in_bij_alloc_r l2 hi hs n bij:
  heap_in_bij bij hi hs →
  l2.1 ∉ set_map (D:=gset _) snd bij →
  heap_in_bij bij hi (heap_alloc hs l2 n).
Proof.
  move => /= Hbij Hin ???? /=. rewrite lookup_union_r. 1: by apply Hbij.
  apply not_elem_of_list_to_map_1. contradict Hin.
  move: Hin => /elem_of_list_fmap[[??][?/elem_of_list_fmap[?[??]]]]; simplify_eq/=.
  apply elem_of_map. eexists (_, _). naive_solver.
Qed.

Lemma heap_in_bij_free hi hs l1 l2 bij:
  heap_in_bij (hb_bij bij) hi hs →
  (l1.1, l2.1) ∈ hb_bij bij →
  heap_in_bij (hb_bij bij) (heap_free hi l1) (heap_free hs l2).
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

Lemma heap_in_bij_free_r hi hs l2 bij:
  heap_in_bij bij hi hs →
  l2.1 ∉ set_map (D:=gset _) snd bij →
  heap_in_bij bij hi (heap_free hs l2).
Proof.
  move => /= Hbij Hin ???? /=. rewrite map_filter_lookup_true. 1: by apply Hbij.
  move => ??. contradict Hin. apply elem_of_map. eexists (_, _). naive_solver.
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

Lemma heap_preserved_bij_env p1 p2 l v he hp bij:
  (p1, p2) ∈ hb_bij bij →
  l.1 = p2 →
  heap_preserved (hb_env bij) he hp →
  heap_preserved (hb_env bij) he (heap_update hp l v).
Proof.
  move => ???. apply heap_preserved_update_r; [done|].
  move => ?. have := hb_disj_env bij. apply; [done|]. apply elem_of_map. by eexists (_, _).
Qed.

Lemma heap_preserved_bij_env_free p1 p2 l he hp bij:
  (p1, p2) ∈ hb_bij bij →
  l.1 = p2 →
  heap_preserved (hb_env bij) he hp →
  heap_preserved (hb_env bij) he (heap_free hp l).
Proof.
  move => ?? Hp p o /=?. rewrite map_filter_lookup. etrans; [by apply Hp|].
  destruct (h_heap hp !! (p, o)) => //=. case_option_guard => //.
  exfalso. have := hb_disj_env bij. apply; [done|]. apply elem_of_map. eexists (_, _). naive_solver.
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

Record imp_heap_bij_state := ImpHeapBij {
  ihb_bij : heap_bij;
  (* last seen heap *)
  ihb_heap : heap_state;
}.
Add Printing Constructor imp_heap_bij_state.

Definition imp_heap_bij_pre (e : imp_event) (s : imp_heap_bij_state) : prepost (imp_event * imp_heap_bij_state) unitUR :=
  let ho := heap_of_event e.2 in
  pp_quant $ λ bij',
  pp_quant $ λ vsi,
  pp_quant $ λ hi,
  pp_prop (heap_bij_extend Env s.(ihb_bij) bij') $
  (* TODO: should we also have the following for hi? We don't need it so far... *)
  pp_prop (set_map fst (hb_bij bij') ⊆ h_provs ho) $
  pp_prop (Forall2 (val_in_bij (hb_bij bij')) (vals_of_event e.2) vsi) $
  pp_prop (heap_in_bij (hb_bij bij') ho hi) $
  pp_prop (heap_preserved (hb_prog bij') s.(ihb_heap) hi) $
  pp_end ((e.1, event_set_vals_heap e.2 vsi hi), ImpHeapBij bij' hi).

Definition imp_heap_bij_post (e : imp_event) (s : imp_heap_bij_state) : prepost (imp_event * imp_heap_bij_state) unitUR :=
  let hi := heap_of_event e.2 in
  pp_quant $ λ bij',
  pp_quant $ λ vso,
  pp_quant $ λ ho,
  pp_prop (heap_bij_extend Prog s.(ihb_bij) bij') $
  (* TODO: should we also have the following for hi? We don't need it so far... *)
  pp_prop (set_map fst (hb_bij bij') ⊆ h_provs ho) $
  pp_prop (Forall2 (val_in_bij (hb_bij bij')) vso (vals_of_event e.2)) $
  pp_prop (heap_in_bij (hb_bij bij') ho hi) $
  pp_prop (heap_preserved (hb_env bij') s.(ihb_heap) hi) $
  pp_end ((e.1, event_set_vals_heap e.2 vso ho), ImpHeapBij bij' hi).

Definition imp_heap_bij (m : module imp_event) : module imp_event :=
  mod_prepost imp_heap_bij_pre imp_heap_bij_post m.

Definition initial_imp_heap_bij_state (m : module imp_event) (σ : m.(m_state)) :=
  (@SMFilter imp_event, σ, (@PPOutside imp_event imp_event, ImpHeapBij ∅ initial_heap_state, tt)).

Local Ltac split_solve :=
  match goal with
  | |- heap_in_bij ?p _ _ => is_evar p; eassumption
  | |- event_set_vals_heap _ _ _ = event_set_vals_heap _ _ _ => reflexivity
  | |- heap_bij_extend ?p ?a ?b =>
      assert_fails (has_evar p); assert_fails (has_evar a); assert_fails (has_evar b); by etrans
  | |- ?a ⊆ ?b =>
      assert_fails (has_evar a); assert_fails (has_evar b); etrans; [eassumption|]
  | |- ?a ⊆ ?b =>
      assert_fails (has_evar a); assert_fails (has_evar b); etrans; [|eassumption]
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
          hb_bij bij1 ⊆ bijm ∧
          hb_bij bij2 ⊆ bijm ∧
          hb_bij bij ⊆ bijm ∧
       ((ips = SPNone ∧ bijm = hb_bij bij ∧
          hb_env bij1 ⊆ hb_env bij ∪ hb_prog bij2 ∧
          hb_env bij2 ⊆ hb_env bij ∪ hb_prog bij1 ∧
          hb_prog bij = hb_prog bij1 ∪ hb_prog bij2 ∧
          hb_prog bij1 ## hb_prog bij2 ∧
          heap_preserved (hb_prog bij1) hi1 hi ∧
          heap_preserved (hb_prog bij2) hi2 hi) ∨
        ((ips = SPLeft ∧ bijm = hb_bij bij1 ∧
          hb_env bij1 = hb_env bij ∪ hb_prog bij2 ∧
          hb_env bij2 ⊆ hb_env bij ∪ hb_prog bij1 ∧
          hb_prog bij ⊆ hb_prog bij1 ∪ hb_prog bij2 ∧
          hb_prog bij2 ## hb_env bij ∧
          heap_preserved (hb_env bij) hi hi1 ∧
          heap_preserved (hb_prog bij2) hi2 hi1) ∨
         (ips = SPRight ∧ bijm = hb_bij bij2 ∧
          hb_env bij1 ⊆ hb_env bij ∪ hb_prog bij2 ∧
          hb_env bij2 = hb_env bij ∪ hb_prog bij1 ∧
          hb_prog bij ⊆ hb_prog bij1 ∪ hb_prog bij2 ∧
          hb_prog bij1 ## hb_env bij ∧
          heap_preserved (hb_env bij) hi hi2 ∧
          heap_preserved (hb_prog bij1) hi1 hi2)))). }
  { move => ?? [] /=*; naive_solver. }
  { done. } { done. }
  { split!. all: set_solver. }
  all: move => [bij1 hi1] [bij2 hi2] [bij hi] [] [] ics1 ics2.
  - move => e ics' e' /= *. unfold heap_bij_extend in *; destruct_all?; simplify_eq/=.
    unshelve split!. 1: econstructor. all: shelve_unifiable. all: split!. all: split!.
    1: { set_unfold; naive_solver. }
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
    1: by destruct e.
    1: { set_unfold; naive_solver. }
    1: { set_unfold; naive_solver. }
    1: { apply: disjoint_mono; [apply hb_disj_priv| |done]. set_unfold; naive_solver. }
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
  - move => e ics' e' /= *. unfold heap_bij_extend in *; destruct_all?; simplify_eq/=.
    unshelve split!. 1: econstructor. all: shelve_unifiable. all: split!. all: split!.
    1: { set_unfold; naive_solver. }
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
    1: by destruct e.
    1: { set_unfold; naive_solver. }
    1: { set_unfold; naive_solver. }
    1: { apply: disjoint_mono; [apply hb_disj_priv| |done]. set_unfold; naive_solver. }
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
  - move => [? e] /= *. unfold heap_bij_extend in *; destruct_all?; simplify_eq/=.
    unshelve split!. 1: econstructor. all: shelve_unifiable.
    all: split!; rewrite ?heap_of_event_event_set_vals_heap; split!. all: split!.
    1: { set_unfold; naive_solver. }
    1: { rewrite vals_of_event_event_set_vals_heap //. by apply: Forall2_length. }
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
    1: { set_unfold; naive_solver. }
    1: { set_unfold; naive_solver. }
    1: { apply: disjoint_mono; [apply hb_disj_priv|done|]. set_unfold; naive_solver. }
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
    1: by destruct e.
    1: by destruct e.
  - move => [? e] /= *. unfold heap_bij_extend in *; destruct_all?; simplify_eq/=.
    unshelve split!. 1: econstructor. all: shelve_unifiable.
    all: split!; rewrite ?heap_of_event_event_set_vals_heap; split!. all: split!.
    1: by destruct e.
    1: { set_unfold; naive_solver. }
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
    1: { set_unfold; naive_solver. }
    1: { set_unfold; naive_solver. }
    1: { apply: disjoint_mono; [apply hb_disj_priv|done|]. set_unfold; naive_solver. }
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
  - move => [? e] /= *. unfold heap_bij_extend in *; destruct_all?; simplify_eq/=.
    unshelve split!. 1: econstructor. all: shelve_unifiable.
    all: split!; rewrite ?heap_of_event_event_set_vals_heap; split!. all: split!.
    1: { set_unfold; naive_solver. }
    1: { rewrite vals_of_event_event_set_vals_heap //. by apply: Forall2_length. }
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
    1: { set_unfold; naive_solver. }
    1: { set_unfold; naive_solver. }
    1: { apply: disjoint_mono; [apply hb_disj_priv|done|]. set_unfold; naive_solver. }
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
    1: by destruct e.
    1: by destruct e.
  - move => [? e] /= *. unfold heap_bij_extend in *; destruct_all?; simplify_eq/=.
    unshelve split!. 1: econstructor. all: shelve_unifiable.
    all: split!; rewrite ?heap_of_event_event_set_vals_heap; split!. all: split!.
    1: by destruct e.
    1: { set_unfold; naive_solver. }
    1: { apply: heap_preserved_mono; [done|]. set_unfold; naive_solver. }
    1: { set_unfold; naive_solver. }
    1: { set_unfold; naive_solver. }
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
  pose (R := λ (b : bool) '(ImpHeapBij bij1 h1) '(ImpHeapBij bij2 h2),
          (hb_prog bij1 = ∅ → hb_prog bij2 = ∅) ∧ hb_bij bij1 ⊆ hb_bij bij2).
  apply: (imp_prepost_proof R); unfold R in *.
  { constructor. { move => [??]. naive_solver. }
    { move => [??] [??] [??] [??] [??]. split. naive_solver. by etrans. } }
  { move => [??] [??]. naive_solver. }
  move => n K1 K2 f fn1 vs1 h1 [bij0 ?] [] ??? /= bij1 *.
  split!. move => ?. split; [solve_length|].
  move => Hcall Hret.
  unshelve apply: tsim_remember. { simpl. exact (λ _ '(Imp ei hi fnsi) '(ips, Imp es hs fnss, (pp, ImpHeapBij bij he, _)),
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
    { apply static_expr_subst_l; [|solve_length]. apply static_expr_mono. apply fd_static. }  }
  { naive_solver. }
  move => /= n' ? Hloop [ei hi fnsi] [[ips [es hs fnss]] [[pp [bij he]] []]] ?.
  destruct_all?; simplify_eq.
  destruct (to_val ei') eqn:?.
  - destruct ei' => //; simplify_eq/=. destruct es' => //; simplify_eq/=.
    apply Hret; [done|]. clear Hloop Hret Hcall. split!.
    { unfold heap_bij_extend. split!; [done..|]. bij_solver. }
    all: split!. by econs. done.
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
  move => {}n _ /= Hloop [[σm1 [[σf σ1] [[pp [bij hi]] []]]] σc1] [[σm2 σ2] σc2] ?.
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
  pose (R := λ (b : bool) '(ImpHeapBij bij1 h1) '(ImpHeapBij bij2 h2),
          hb_prog bij1 ⊆ hb_prog bij2 ∧ heap_preserved (hb_prog bij1) h1 h2).
  apply: (imp_prepost_proof R); unfold R in *.
  { constructor. { move => [??]. naive_solver. }
    { move => [??] [??] [??] [??] [??]. split; [by etrans|]. etrans; [done|].
      by apply: heap_preserved_mono. } }
  { move => [??] [??]. naive_solver. }
  move => n K1 K2 f fn1 vs1 h0 [bij0 ?] [] ? ?.
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
  { unfold heap_bij_extend. split!. set_solver. }
  { apply heap_in_bij_update_r; [|set_solver]. apply heap_in_bij_alloc_r; [done|set_solver]. }
  { apply heap_preserved_update_r; [|set_solver]. apply heap_preserved_alloc_r; [set_solver|done]. }
  { bij_solver. }
  { etrans; [apply: heap_preserved_mono; [done|bij_solver]|].
    apply heap_preserved_update_r; [|bij_solver].
    apply heap_preserved_alloc_r; [bij_solver|done]. }
  move => ? h2 [bij2 h3] [??] bij4 ? h4 *. decompose_Forall_hyps.
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
