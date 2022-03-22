Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.filter.
Require Import refframe.product.
Require Import refframe.seq_product.
Require Import refframe.link.
Require Import refframe.prepost.
Require Import refframe.proof_techniques.

Local Open Scope Z_scope.

(** * C-like language language *)
Declare Scope loc_scope.
Delimit Scope loc_scope with L.
Open Scope loc_scope.

Definition prov : Set := Z.
Definition loc : Set := (prov * Z).

Definition shift_loc (l : loc) (z : Z) : loc := (l.1, l.2 + z).
Notation "l +ₗ z" := (shift_loc l%L z%Z) (at level 50, left associativity) : loc_scope.
Global Typeclasses Opaque shift_loc.

Lemma shift_loc_0 l :
  l +ₗ 0 = l.
Proof. rewrite /shift_loc. destruct l => /=. f_equal. lia. Qed.

Inductive binop : Set :=
| AddOp | ShiftOp | EqOp | LeOp | LtOp.

Inductive val := | ValNum (z : Z) | ValBool (b : bool) | ValLoc (l : loc).
Global Instance val_inhabited : Inhabited val := populate (ValNum 0).
Coercion ValNum : Z >-> val.
Global Instance val_eq_dec : EqDecision val.
Proof. solve_decision. Qed.

Definition val_to_Z (v : val) : option Z :=
  match v with
  | ValNum z => Some z
  | _ => None
  end.
Definition val_to_bool (v : val) : option bool :=
  match v with
  | ValBool b => Some b
  | _ => None
  end.
Definition val_to_loc (v : val) : option loc :=
  match v with
  | ValLoc l => Some l
  | _ => None
  end.

Section expr.
Local Unset Elimination Schemes.
Inductive expr : Set :=
| Var (v : string)
| Val (v : val)
| BinOp (e1 : expr) (o : binop) (e2 : expr)
| Load (e : expr)
| Store (e1 e2 : expr)
(* TODO: Do we want to have Alloca instead of Alloc, i.e. an alloc
that is automatically freed on function return? *)
| Alloc (e : expr)
| Free (e : expr)
| If (e e1 e2 : expr)
| LetE (v : string) (e1 e2 : expr)
| Call (f : string) (args : list expr)
| UbE
(* Returning to the context, insert automatically during execution. *)
| ReturnExt (can_return_further : bool) (e : expr)
| Waiting (can_return : bool)
.
End expr.
Lemma expr_ind (P : expr → Prop) :
  (∀ (x : string), P (Var x)) →
  (∀ (v : val), P (Val v)) →
  (∀ (e1 : expr) (op : binop) (e2 : expr), P e1 → P e2 → P (BinOp e1 op e2)) →
  (∀ (e : expr), P e → P (Load e)) →
  (∀ (e1 e2 : expr), P e1 → P e2 → P (Store e1 e2)) →
  (∀ (e : expr), P e → P (Alloc e)) →
  (∀ (e : expr), P e → P (Free e)) →
  (∀ (e1 e2 e3 : expr), P e1 → P e2 → P e3 → P (If e1 e2 e3)) →
  (∀ (v : string) (e1 e2 : expr), P e1 → P e2 → P (LetE v e1 e2)) →
  (∀ (f : string) (args : list expr), Forall P args → P (Call f args)) →
  (P UbE) →
  (∀ (can_return_further : bool) (e : expr), P e → P (ReturnExt can_return_further e)) →
  (∀ (can_return : bool), P (Waiting can_return)) →
  ∀ (e : expr), P e.
Proof.
  move => *. generalize dependent P => P. match goal with | e : expr |- _ => revert e end.
  fix FIX 1. move => [ ^e] => ????????? Hcall ???.
  10: { apply Hcall. apply Forall_true => ?. by apply: FIX. }
  all: auto.
Qed.

Global Instance val_inj : Inj (=) (=) Val.
Proof. move => ?? []. done. Qed.

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

(** substitution *)
Fixpoint subst (x : string) (v : val) (e : expr) : expr :=
  match e with
  | Var y => if bool_decide (x = y) then Val v else Var y
  | Val v => Val v
  | BinOp e1 o e2 => BinOp (subst x v e1) o (subst x v e2)
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  | Alloc e => Alloc (subst x v e)
  | Free e => Free (subst x v e)
  | If e e1 e2 => If (subst x v e) (subst x v e1) (subst x v e2)
  | LetE y e1 e2 => LetE y (subst x v e1) (if bool_decide (x ≠ y) then subst x v e2 else e2)
  | Call f args => Call f (subst x v <$> args)
  | UbE => UbE
  | ReturnExt b e => ReturnExt b (subst x v e)
  | Waiting b => Waiting b
  end.
Fixpoint subst_l (xs : list string) (vs : list val) (e : expr) : expr :=
  match xs, vs with
  | x::xs', v::vs' => subst_l xs' vs' (subst x v e)
  | _,_ => e
  end.

Fixpoint subst_map (x : gmap string val) (e : expr) : expr :=
  match e with
  | Var y => if x !! y is Some v then Val v else Var y
  | Val v => Val v
  | BinOp e1 o e2 => BinOp (subst_map x e1) o (subst_map x e2)
  | Load e => Load (subst_map x e)
  | Store e1 e2 => Store (subst_map x e1) (subst_map x e2)
  | Alloc e => Alloc (subst_map x e)
  | Free e => Free (subst_map x e)
  | If e e1 e2 => If (subst_map x e) (subst_map x e1) (subst_map x e2)
  | LetE y e1 e2 => LetE y (subst_map x e1) (subst_map (delete y x) e2)
  | Call f args => Call f (subst_map x <$> args)
  | UbE => UbE
  | ReturnExt b e => ReturnExt b (subst_map x e)
  | Waiting b => Waiting b
  end.

Lemma subst_map_empty e :
  subst_map ∅ e = e.
Proof.
  elim: e => /=; try by move => *; simplify_map_eq; congruence.
  - move => *. rewrite delete_empty. congruence.
  - move => ?? /Forall_lookup IH. f_equal.
    apply list_eq => ?. apply option_eq => ?.
    rewrite !list_lookup_fmap !fmap_Some.
    naive_solver congruence.
Qed.

Lemma subst_subst_map x v e xs :
  subst_map (<[x:=v]> xs) e = subst_map xs (subst x v e).
Proof.
  elim: e xs => //=; try by move => *; congruence.
  - move => ??. case_bool_decide; simplify_map_eq => //.
  - move => ??? H1 H2 xs. rewrite H1. case_bool_decide; subst. 2: by rewrite delete_insert_delete.
    by rewrite delete_insert_ne // H2.
  - move => ?? /Forall_lookup IH ?. f_equal. apply list_eq => ?. apply option_eq => ?.
    rewrite !list_lookup_fmap !fmap_Some. setoid_rewrite fmap_Some.
    naive_solver congruence.
Qed.

Lemma subst_l_subst_map xs vs e :
  length xs = length vs →
  subst_l xs vs e = subst_map (list_to_map (zip xs vs)) e.
Proof.
  elim: xs vs e. { case => //=. move => ??. by rewrite subst_map_empty. }
  move => ?? IH [|??] //= e [?]. by rewrite subst_subst_map IH.
Qed.

(** evaluation contexts *)
Inductive expr_ectx :=
| BinOpLCtx (op : binop) (e2 : expr)
| BinOpRCtx (v1 : val) (op : binop)
| LoadCtx
| StoreLCtx (e2 : expr)
| StoreRCtx (v1 : val)
| AllocCtx
| FreeCtx
| IfCtx (e2 e3 : expr)
| LetECtx (v : string) (e2 : expr)
| CallCtx (f : string) (vl : list val) (el : list expr)
| ReturnExtCtx (can_return_further : bool)
.

Definition expr_fill_item (Ki : expr_ectx) (e : expr) : expr :=
  match Ki with
  | BinOpLCtx op e2 => BinOp e op e2
  | BinOpRCtx v1 op => BinOp (Val v1) op e
  | LoadCtx => Load e
  | StoreLCtx e2 => Store e e2
  | StoreRCtx v1 => Store (Val v1) e
  | AllocCtx => Alloc e
  | FreeCtx => Free e
  | IfCtx e2 e3 => If e e2 e3
  | LetECtx v e2 => LetE v e e2
  | CallCtx f vl el => Call f ((Val <$> vl) ++ e :: el)
  | ReturnExtCtx b => ReturnExt b e
  end.

Global Instance expr_fill_item_inj Ki : Inj (=) (=) (expr_fill_item Ki).
Proof. destruct Ki => ??? //=; by simplify_eq/=. Qed.

Lemma list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2 :
  to_val e1 = None → to_val e2 = None →
  (Val <$> vl1) ++ e1 :: el1 = (Val <$> vl2) ++ e2 :: el2 →
  vl1 = vl2 ∧ e1 = e2 ∧ el1 = el2.
Proof.
  revert vl2; induction vl1; destruct vl2; intros H1 H2; inversion 1.
  - done.
  - subst. by inversion H1.
  - subst. by inversion H2.
  - destruct (IHvl1 vl2); auto. split; f_equal; auto.
Qed.

Lemma list_expr_val_inv vl1 vl2 e2 el2 :
  (Val <$> vl1) = (Val <$> vl2) ++ e2 :: el2 →
  is_Some (to_val e2).
Proof. revert vl2; induction vl1; destruct vl2 => //?; simplify_eq/=; naive_solver. Qed.

Lemma fill_item_val Ki e : is_Some (to_val (expr_fill_item Ki e)) → is_Some (to_val e).
Proof. destruct Ki => //=; move => [??] //. Qed.

Lemma expr_fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  expr_fill_item Ki1 e1 = expr_fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1, Ki2 => //= *; simplify_eq => //.
  efeed pose proof list_expr_val_eq_inv; [| |done|]; naive_solver.
Qed.

Definition expr_fill (K : list expr_ectx) (e : expr) : expr :=
  foldl (flip expr_fill_item) e K.

Lemma expr_fill_app K1 K2 e:
  expr_fill (K2 ++ K1) e = expr_fill K1 (expr_fill K2 e).
Proof. apply foldl_app. Qed.

Lemma fill_val K e : is_Some (to_val (expr_fill K e)) → is_Some (to_val e).
Proof.
  elim/rev_ind: K e => //?? IH e. rewrite expr_fill_app /= => ?.
  apply IH. by apply: fill_item_val.
Qed.

Lemma expr_fill_Waiting_inj K1 K2 b1 b2 :
  expr_fill K1 (Waiting b1) = expr_fill K2 (Waiting b2) → K1 = K2 ∧ b1 = b2.
Proof.
  elim/rev_ind: K1 K2.
  - move => K2. destruct K2 as [|Ki] using rev_ind; [naive_solver|] => /=.
    rewrite expr_fill_app => /=. destruct Ki; naive_solver.
  - move => Ki1 K1 IH K2. destruct K2 as [|Ki2 K2 IHK] using rev_ind => /=.
    { rewrite expr_fill_app => /=. destruct Ki1; naive_solver. }
    rewrite !expr_fill_app /= => Heq.
    have ? : Ki1 = Ki2. {
      apply: expr_fill_item_no_val_inj; [..|done].
      all: apply eq_None_not_Some => /fill_val /=[??]//.
    } subst.
    naive_solver.
Qed.

Fixpoint static_expr (allow_loc : bool) (e : expr) : bool :=
  match e with
  | Var v => true
  | Val v => allow_loc || (if v is ValLoc _ then false else true)
  | BinOp e1 o e2 => static_expr allow_loc e1 && static_expr allow_loc e2
  | Load e1 => static_expr allow_loc e1
  | Store e1 e2 => static_expr allow_loc e1 && static_expr allow_loc e2
  | Alloc e1 => static_expr allow_loc e1
  | Free e1 => static_expr allow_loc e1
  | If e e1 e2 => static_expr allow_loc e && static_expr allow_loc e1 && static_expr allow_loc e2
  | LetE v e1 e2 => static_expr allow_loc e1 && static_expr allow_loc e2
  | Call f args => forallb (static_expr allow_loc) args
  | UbE => true
  | ReturnExt can_return_further e => false
  | Waiting can_return => false
  end.

Lemma static_expr_subst x v e:
  static_expr true e →
  static_expr true (subst x v e).
Proof.
  elim: e => //= *; try naive_solver.
  - by case_bool_decide.
  - case_bool_decide; naive_solver.
  - apply forallb_True, Forall_forall => ? /elem_of_list_fmap[?[??]]. subst.
    revert select (Forall _ _) => /Forall_forall.
    revert select (Is_true (forallb _ _)) => /forallb_True/Forall_forall. naive_solver.
Qed.

Lemma static_expr_subst_l xs vs e:
  static_expr true e →
  length xs = length vs →
  static_expr true (subst_l xs vs e).
Proof.
  elim: xs vs e. { by case. }
  move => ?? IH [//|??] /=???. apply IH; [|lia].
  by apply static_expr_subst.
Qed.

Lemma static_expr_expr_fill bl K e:
  static_expr bl (expr_fill K e) ↔ static_expr bl (expr_fill K (Var "")) ∧ static_expr bl e.
Proof.
  elim/rev_ind: K e => /=. { naive_solver. }
  move => Ki K IH e. rewrite !expr_fill_app/=.
  destruct Ki => //=; rewrite ?forallb_app/=; naive_solver.
Qed.

Lemma static_expr_mono e:
  static_expr false e →
  static_expr true e.
Proof.
  elim: e => //=; try naive_solver.
  move => ?? IH /forallb_True.
  elim: IH => // *. decompose_Forall_hyps; naive_solver.
Qed.

Record fndef : Type := {
  fd_args : list string;
  fd_body : expr;
  fd_static : static_expr false fd_body;
}.

(** ** heap *)
Record heap_state : Set := Heap {
  h_heap : gmap loc val;
  h_provs' : gmap prov unit; (* We need to use gmap because gset does not live in Set *)
  heap_wf' : bool_decide (set_map fst (dom (gset _) h_heap) ⊆ dom (gset _) h_provs');
}.
Add Printing Constructor heap_state.

Definition h_provs (h : heap_state) : gset prov := dom _ (h_provs' h).

Lemma heap_state_eq h1 h2:
  h1 = h2 ↔ h1.(h_heap) = h2.(h_heap) ∧ h1.(h_provs') = h2.(h_provs').
Proof. split; [naive_solver|]. destruct h1, h2 => /= -[??]; subst. f_equal. apply proof_irrel. Qed.

Lemma heap_wf h l:
  is_Some (h_heap h !! l) → l.1 ∈ h_provs h.
Proof.
  move => ?. have /bool_decide_unpack := heap_wf' h. apply.
  apply elem_of_map. eexists l. split; [done|]. by apply elem_of_dom.
Qed.

Program Definition initial_heap_state : heap_state :=
  Heap ∅ ∅ _.
Next Obligation. apply bool_decide_spec. set_solver. Qed.

Definition heap_alive (h : heap_state) (l : loc) : Prop :=
  is_Some (h.(h_heap) !! l).

Definition heap_is_fresh (h : heap_state) (l : loc) : Prop :=
  l.1 ∉ h_provs h ∧ l.2 = 0.

Definition heap_fresh (ps : gset prov) (h : heap_state) : loc :=
  (fresh (ps ∪ h_provs h), 0).

Program Definition heap_update (h : heap_state) (l : loc) (v : val) : heap_state :=
  Heap (alter (λ _, v) l h.(h_heap)) h.(h_provs') _.
Next Obligation.
  move => ???. apply bool_decide_spec. move => ? /elem_of_map[?[?/elem_of_dom]].
  rewrite lookup_alter_is_Some. subst. apply heap_wf.
Qed.

Lemma heap_update_provs h l v :
  h_provs (heap_update h l v) = h_provs h.
Proof. done. Qed.

Program Definition heap_alloc (h : heap_state) (l : loc) (n : Z) : heap_state :=
  Heap (list_to_map ((λ z, (l +ₗ z, ValNum 0)) <$> seqZ 0 n) ∪ h.(h_heap)) (gset_to_gmap tt ({[l.1]} ∪ h_provs h)) _.
Next Obligation.
  move => ???. apply bool_decide_spec. move => ? /elem_of_map[?[?/elem_of_dom]]. subst.
  rewrite dom_gset_to_gmap. move => [? /lookup_union_Some_raw[Hl|[? Hh]]]; apply elem_of_union; [left|right; by apply heap_wf].
  move: Hl => /(elem_of_list_to_map_2 _ _ _)/elem_of_list_fmap. set_solver.
Qed.

Lemma heap_alloc_provs h l n :
  h_provs (heap_alloc h l n) = {[l.1]} ∪ h_provs h.
Proof. by rewrite /h_provs /= dom_gset_to_gmap. Qed.

Program Definition heap_free (h : heap_state) (l : loc) : heap_state :=
  Heap (filter (λ '(l', v), l'.1 ≠ l.1) h.(h_heap)) h.(h_provs') _.
Next Obligation.
  move => ??. apply bool_decide_spec. move => ? /elem_of_map[?[?/elem_of_dom]]. subst.
  rewrite map_filter_lookup => -[?/bind_Some[?[??]]]. by apply heap_wf.
Qed.

Lemma heap_free_provs h l :
  h_provs (heap_free h l) = h_provs h.
Proof. done. Qed.

Program Definition heap_merge (h1 h2 : heap_state) : heap_state :=
  Heap (h_heap h1 ∪ h_heap h2) (h_provs' h1 ∪ h_provs' h2) _.
Next Obligation.
  move => ??. apply bool_decide_spec. move => ? /elem_of_map[?[?/elem_of_dom]]. subst.
  move => /lookup_union_is_Some[/heap_wf?|/heap_wf?]; set_solver.
Qed.

Lemma heap_merge_provs h1 h2 :
  h_provs (heap_merge h1 h2) = h_provs h1 ∪ h_provs h2.
Proof. by rewrite /h_provs/= dom_union_L. Qed.

Program Definition heap_restrict (h : heap_state) (P : prov → Prop) `{!∀ x, Decision (P x)} : heap_state :=
  Heap (filter (λ x, P x.1.1) h.(h_heap)) h.(h_provs') _.
Next Obligation.
  move => ???. apply bool_decide_spec. move => ? /elem_of_map[?[?/elem_of_dom]]. subst.
  rewrite map_filter_lookup => -[?/bind_Some[?[??]]]. by apply heap_wf.
Qed.

Lemma heap_restrict_provs h (P : prov → Prop) `{!∀ x, Decision (P x)} :
  h_provs (heap_restrict h P) = h_provs h.
Proof. done. Qed.

Program Definition heap_add_provs (h : heap_state) (p : gset prov) : heap_state :=
  Heap (h_heap h) (gset_to_gmap tt (p ∪ h_provs h)) _.
Next Obligation.
  move => ??. apply bool_decide_spec. move => ? /elem_of_map[?[?/elem_of_dom]] ?. subst.
  rewrite dom_gset_to_gmap. apply: union_subseteq_r. by apply heap_wf.
Qed.

Lemma heap_add_provs_provs h p :
  h_provs (heap_add_provs h p) = p ∪ h_provs h.
Proof. by rewrite /h_provs/= dom_gset_to_gmap. Qed.

Lemma heap_fresh_is_fresh ps h:
  heap_is_fresh h (heap_fresh ps h).
Proof.
  split; [|done] => /=.
  match goal with | |- context [fresh ?X] => pose proof (is_fresh X) as H; revert H; move: {1 3}(X) => l Hl end.
  set_solver.
Qed.

Lemma heap_fresh_not_in ps h:
  (heap_fresh ps h).1 ∉ ps.
Proof.
  unfold heap_fresh => /=.
  match goal with | |- context [fresh ?X] => pose proof (is_fresh X) as H; revert H; move: {1 3}(X) => l Hl end.
  set_solver.
Qed.

Lemma heap_alive_alloc h l l' n :
  l.1 = l'.1 →
  l'.2 ≤ l.2 < l'.2 + n →
  heap_alive (heap_alloc h l' n) l.
Proof.
  destruct l as [p o], l' as [p' o'].
  move => ??. simplify_eq/=. rewrite /heap_alive/=/shift_loc/=.
  apply lookup_union_is_Some. left. apply list_to_map_lookup_is_Some.
  eexists 0. apply elem_of_list_fmap. eexists (o - o').
  split; [do 2 f_equal; lia|]. apply elem_of_seqZ. lia.
Qed.

Lemma heap_alive_update h l l' v :
  heap_alive h l →
  heap_alive (heap_update h l' v) l.
Proof. move => ?. rewrite /heap_alive/=. by apply lookup_alter_is_Some. Qed.

Lemma heap_free_update h l l' v :
  l'.1 = l.1 →
  heap_free (heap_update h l' v) l = heap_free h l.
Proof.
  move => ?. apply heap_state_eq => /=. split; [|done].
  apply map_filter_strong_ext_1 => l'' ?. destruct l'', l', l; simplify_eq/=.
  split => -[?]; rewrite lookup_alter_ne //; congruence.
Qed.

Lemma heap_free_alloc h l n :
  l.1 ∉ h_provs h →
  heap_free (heap_alloc h l n) l = heap_add_provs h {[l.1]}.
Proof.
  move => Hin.
  apply heap_state_eq => /=. split; [|done].
  rewrite map_filter_union.
  2: { apply map_disjoint_list_to_map_l. rewrite Forall_fmap. apply Forall_forall.
       move => ?? /=. apply eq_None_not_Some. by move => /heap_wf/=. }
  rewrite (map_filter_id _ (h_heap h)).
  2: { move => [??] ? /(mk_is_Some _ _) /heap_wf/=Hwf ?. subst. naive_solver. }
  rewrite map_filter_empty_iff_2 ?left_id_L //.
  move => ?? /(elem_of_list_to_map_2 _ _ _)/elem_of_list_fmap[?[??]]. simplify_eq/=. by apply.
Qed.

(** ** state *)
Record imp_state := Imp {
  st_expr : expr;
  st_heap : heap_state;
  st_fns : gmap string fndef;
}.
Add Printing Constructor imp_state.

Definition initial_imp_state (fns : gmap string fndef) : imp_state :=
  Imp (Waiting false) initial_heap_state fns.

(** ** imp_event *)
Inductive imp_ev : Type :=
| EICall (fn : string) (args: list val) (h : heap_state)
| EIReturn (ret: val) (h : heap_state).

Definition imp_event := io_event imp_ev.

Definition vals_of_event (e : imp_ev) : list val :=
  match e with
  | EICall f vs h => vs
  | EIReturn v h => [v]
  end.

Definition heap_of_event (e : imp_ev) : heap_state :=
  match e with
  | EICall f vs h => h
  | EIReturn v h => h
  end.

Definition event_set_vals_heap (e : imp_ev) (vs : list val) (h : heap_state) : imp_ev :=
  match e with
  | EICall f vs' h' => EICall f vs h
  | EIReturn v' h' => EIReturn (vs !!! 0%nat) h
  end.

Lemma heap_of_event_event_set_vals_heap e vs h :
  heap_of_event (event_set_vals_heap e vs h) = h.
Proof. by destruct e. Qed.

Lemma vals_of_event_event_set_vals_heap e vs h :
  length vs = length (vals_of_event e) →
  vals_of_event (event_set_vals_heap e vs h) = vs.
Proof. destruct e => //=. destruct vs as [|? [|]] => //. Qed.

Lemma event_set_vals_heap_idemp e vs1 h1 vs2 h2:
  event_set_vals_heap (event_set_vals_heap e vs1 h1) vs2 h2 = event_set_vals_heap e vs2 h2.
Proof. by destruct e. Qed.
(** ** step *)
Definition eval_binop (op : binop) (v1 v2 : val) : option val :=
  match op with
  | AddOp => z1 ← val_to_Z v1; z2 ← val_to_Z v2; Some (ValNum (z1 + z2))
  | ShiftOp => l ← val_to_loc v1; z ← val_to_Z v2; Some (ValLoc (l +ₗ z))
  | EqOp =>
      match v1 with
      | ValNum z1 => z2 ← val_to_Z v2; Some (ValBool (bool_decide (z1 = z2)))
      | ValBool b1 => b2 ← val_to_bool v2; Some (ValBool (bool_decide (b1 = b2)))
      | _ => None
      end
  | LeOp => z1 ← val_to_Z v1; z2 ← val_to_Z v2; Some (ValBool (bool_decide (z1 ≤ z2)))
  | LtOp => z1 ← val_to_Z v1; z2 ← val_to_Z v2; Some (ValBool (bool_decide (z1 < z2)))
  end.

(* TODO: alternative idea: Define semantics as state → itree moduleE state
   Then put an itree forever around it after adding the evaluation context
This way one can reuse infrastructure
*)
Inductive head_step : imp_state → option imp_event → (imp_state → Prop) → Prop :=
| BinOpS v1 op v2 h fns:
  head_step (Imp (BinOp (Val v1) op (Val v2)) h fns) None (λ σ',
    ∃ v, eval_binop op v1 v2 = Some v ∧ σ' = Imp (Val v) h fns)
| LoadS v1 h fns:
  head_step (Imp (Load (Val v1)) h fns) None (λ σ',
    ∃ l v, v1 = ValLoc l ∧ h.(h_heap) !! l = Some v ∧ σ' = Imp (Val v) h fns)
| StoreS v1 v h fns:
  head_step (Imp (Store (Val v1) (Val v)) h fns) None (λ σ',
    ∃ l, v1 = ValLoc l ∧ heap_alive h l ∧ σ' = Imp (Val v) (heap_update h l v) fns)
| AllocS h fns l v:
  heap_is_fresh h l →
  head_step (Imp (Alloc (Val v)) h fns) None (λ σ',
    ∃ z, v = ValNum z ∧ 0 < z ∧ σ' = Imp (Val (ValLoc l)) (heap_alloc h l z) fns)
| FreeS h fns v:
  head_step (Imp (Free (Val v)) h fns) None (λ σ',
    ∃ l, v = ValLoc l ∧ heap_alive h l ∧ σ' = Imp (Val (ValNum 0)) (heap_free h l) fns)
| IfS v fns e1 e2 h:
  head_step (Imp (If (Val v) e1 e2) h fns) None (λ σ,
       ∃ b, val_to_bool v = Some b ∧ σ = Imp (if b then e1 else e2) h fns)
| LetS x v e fns h:
  head_step (Imp (LetE x (Val v) e) h fns) None (λ σ, σ = Imp (subst x v e) h fns)
| UbES fns h:
  head_step (Imp UbE h fns) None (λ σ, False)
| VarES fns h v: (* unbound variable *)
  head_step (Imp (Var v) h fns) None (λ σ, False)
| CallInternalS f fn fns vs h:
  fns !! f = Some fn →
  head_step (Imp (Call f (Val <$> vs)) h fns) None (λ σ,
   length vs = length fn.(fd_args) ∧
   σ = Imp (subst_l fn.(fd_args) vs fn.(fd_body)) h fns)
| CallExternalS f fns vs h:
  fns !! f = None →
  head_step (Imp (Call f (Val <$> vs)) h fns) (Some (Outgoing, EICall f vs h)) (λ σ, σ = Imp (Waiting true) h fns)
| ReturnS fns v b h:
  head_step (Imp (ReturnExt b (Val v)) h fns) (Some (Outgoing, EIReturn v h)) (λ σ, σ = (Imp (Waiting b) h fns))
| RecvCallS fns f fn vs b h h':
  fns !! f = Some fn →
  head_step (Imp (Waiting b) h fns) (Some (Incoming, EICall f vs h')) (λ σ,
    σ = (Imp (if bool_decide (length vs = length fn.(fd_args)) then
                ReturnExt b (subst_l fn.(fd_args) vs fn.(fd_body))
              else
                UbE) h' fns))
| RecvReturnS fns v h h':
  head_step (Imp (Waiting true) h fns) (Some (Incoming, EIReturn v h')) (λ σ, σ = (Imp (Val v) h' fns))
.

Definition sub_redexes_are_values (e : expr) :=
  ∀ K e', e = expr_fill K e' → to_val e' = None → K = [].

Lemma sub_redexes_are_values_item e :
  (∀ Ki e', e = expr_fill_item Ki e' → is_Some (to_val e')) →
  sub_redexes_are_values e.
Proof.
  move => Hitem. elim/rev_ind => //= ?? IH?.
  rewrite expr_fill_app /= => /Hitem/fill_val[??].
  naive_solver.
Qed.

Ltac solve_sub_redexes_are_values := apply sub_redexes_are_values_item; case; naive_solver.

Global Instance expr_fill_inj K : Inj (=) (=) (expr_fill K).
Proof. induction K as [|Ki K IH]; rewrite /Inj; naive_solver. Qed.

Lemma val_head_stuck e1 h σ1 κ Pσ : head_step (Imp e1 h σ1) κ Pσ → to_val e1 = None.
Proof. by inversion 1. Qed.

Lemma head_ctx_step_val Ki e h σ1 κ Pσ :
  head_step (Imp (expr_fill_item Ki e) h σ1) κ Pσ → is_Some (to_val e).
Proof. destruct Ki; inversion 1; simplify_eq => //; by apply: list_expr_val_inv. Qed.

Lemma head_fill_step_val K e h σ1 κ Pσ :
  to_val e = None →
  head_step (Imp (expr_fill K e) h σ1) κ Pσ →
  K = [].
Proof.
  elim/rev_ind: K => //=????. rewrite expr_fill_app /= => /head_ctx_step_val /fill_val[??].
  naive_solver.
Qed.

Lemma step_by_val K K' e1' e1_redex h σ1 κ Pσ :
  expr_fill K e1' = expr_fill K' e1_redex →
  to_val e1' = None →
  head_step (Imp e1_redex h σ1) κ Pσ →
  ∃ K'', K' = K'' ++ K.
Proof.
  assert (fill_val : ∀ K e, is_Some (to_val (expr_fill K e)) → is_Some (to_val e)).
  { intros K''. induction K'' as [|Ki K'' IH]=> e //=. by intros ?%IH%fill_item_val. }
  assert (fill_not_val : ∀ K e, to_val e = None → to_val (expr_fill K e) = None).
  { intros ? e. rewrite !eq_None_not_Some. eauto. }

  intros Hfill Hred Hstep; revert K' Hfill.
  induction K as [|Ki K IH] using rev_ind=> /= K' Hfill; eauto using app_nil_r.
  destruct K' as [|Ki' K' _] using @rev_ind; simplify_eq/=.
  { rewrite expr_fill_app in Hstep. apply head_ctx_step_val in Hstep.
    apply fill_val in Hstep. by apply not_eq_None_Some in Hstep. }
  rewrite !expr_fill_app /= in Hfill.
  assert (Ki = Ki') as ->.
  { eapply expr_fill_item_no_val_inj, Hfill; eauto using val_head_stuck. }
  simplify_eq. destruct (IH K') as [K'' ->]; auto.
  exists K''. by rewrite assoc.
Qed.

Inductive prim_step : imp_state → option imp_event → (imp_state → Prop) → Prop :=
  Ectx_step K e e' fns κ Pσ h:
    e = expr_fill K e' →
    head_step (Imp e' h fns) κ Pσ →
    prim_step (Imp e h fns) κ (λ σ, ∃ e2 h2 fns2, Pσ (Imp e2 h2 fns2) ∧ σ = Imp (expr_fill K e2) h2 fns2).

Lemma prim_step_inv K e fns κ h Pσ:
  prim_step (Imp (expr_fill K e) h fns) κ Pσ →
  to_val e = None →
  ∃ K' e' Pσ', e = expr_fill K' e' ∧ head_step (Imp e' h fns) κ Pσ' ∧
      Pσ = (λ σ, ∃ e2 h2 fns2, Pσ' (Imp e2 h2 fns2) ∧ σ = Imp (expr_fill (K' ++ K) e2) h2 fns2).
Proof.
  inversion 1; simplify_eq => ?.
  revert select (expr_fill _ _ = expr_fill _ _) => Heq. move: (Heq) => /step_by_val Hg.
  have [//|? ?]:= Hg _ _ _ _ _ ltac:(done). subst.
  rewrite expr_fill_app in Heq. naive_solver.
Qed.

Lemma prim_step_inv_head K e fns h κ Pσ:
  prim_step (Imp (expr_fill K e) h fns) κ Pσ →
  sub_redexes_are_values e →
  to_val e = None →
  ∃ Pσ', head_step (Imp e h fns) κ Pσ' ∧
      Pσ = (λ σ, ∃ e2 h2 fns2, Pσ' (Imp e2 h2 fns2) ∧ σ = Imp (expr_fill K e2) h2 fns2).
Proof.
  move => Hprim Hsub ?.
  move: Hprim => /prim_step_inv[|?[?[?[?[Hstep ?]]]]]. { done. } subst.
  have ->:= Hsub _ _ ltac:(done). 2: { by apply: val_head_stuck. }
  naive_solver.
Qed.

Definition imp_module := Mod prim_step.

Global Instance imp_vis_no_all: VisNoAll imp_module.
Proof. move => *. invert_all' @m_step; invert_all head_step; naive_solver. Qed.

(** * tstep *)
(** ** ImpExprFill *)
Class ImpExprFill (e : expr) (K : list expr_ectx) (e' : expr) := {
    imp_expr_fill_proof : e = expr_fill K e'
}.
Global Hint Mode ImpExprFill ! - - : tstep.

Lemma imp_expr_fill_end e :
  ImpExprFill e [] e.
Proof. done. Qed.
Global Hint Resolve imp_expr_fill_end | 100 : tstep.

Lemma imp_expr_fill_expr_fill e K K' e' `{!ImpExprFill e K' e'} :
  ImpExprFill (expr_fill K e) (K' ++ K) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply imp_expr_fill_proof. Qed.
Global Hint Resolve imp_expr_fill_expr_fill : tstep.

Lemma imp_expr_fill_BinOpL e1 e2 op K e' `{!ImpExprFill e1 K e'} :
  ImpExprFill (BinOp e1 op e2) (K ++ [BinOpLCtx op e2]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply imp_expr_fill_proof. Qed.
Global Hint Resolve imp_expr_fill_BinOpL : tstep.

Lemma imp_expr_fill_BinOpR (v1 : val) e2 op K e' `{!ImpExprFill e2 K e'} :
  ImpExprFill (BinOp (Val v1) op e2) (K ++ [BinOpRCtx v1 op]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply imp_expr_fill_proof. Qed.
Global Hint Resolve imp_expr_fill_BinOpR : tstep.

Lemma imp_expr_fill_Load e1 K e' `{!ImpExprFill e1 K e'} :
  ImpExprFill (Load e1) (K ++ [LoadCtx]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply imp_expr_fill_proof. Qed.
Global Hint Resolve imp_expr_fill_Load : tstep.

Lemma imp_expr_fill_StoreL e1 e2 K e' `{!ImpExprFill e1 K e'} :
  ImpExprFill (Store e1 e2) (K ++ [StoreLCtx e2]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply imp_expr_fill_proof. Qed.
Global Hint Resolve imp_expr_fill_StoreL : tstep.

Lemma imp_expr_fill_StoreR (v1 : val) e2 K e' `{!ImpExprFill e2 K e'} :
  ImpExprFill (Store (Val v1) e2) (K ++ [StoreRCtx v1]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply imp_expr_fill_proof. Qed.
Global Hint Resolve imp_expr_fill_StoreR : tstep.

Lemma imp_expr_fill_Alloc e1 K e' `{!ImpExprFill e1 K e'} :
  ImpExprFill (Alloc e1) (K ++ [AllocCtx]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply imp_expr_fill_proof. Qed.
Global Hint Resolve imp_expr_fill_Alloc : tstep.

Lemma imp_expr_fill_Free e1 K e' `{!ImpExprFill e1 K e'} :
  ImpExprFill (Free e1) (K ++ [FreeCtx]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply imp_expr_fill_proof. Qed.
Global Hint Resolve imp_expr_fill_Free : tstep.

Lemma imp_expr_fill_If e e2 e3 K e' `{!ImpExprFill e K e'} :
  ImpExprFill (If e e2 e3) (K ++ [IfCtx e2 e3]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply imp_expr_fill_proof. Qed.
Global Hint Resolve imp_expr_fill_If : tstep.

Lemma imp_expr_fill_LetE v e1 e2 K e' `{!ImpExprFill e1 K e'} :
  ImpExprFill (LetE v e1 e2) (K ++ [LetECtx v e2]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply imp_expr_fill_proof. Qed.
Global Hint Resolve imp_expr_fill_LetE : tstep.

Lemma imp_expr_fill_ReturnExt b e K e' `{!ImpExprFill e K e'} :
  ImpExprFill (ReturnExt b e) (K ++ [ReturnExtCtx b]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply imp_expr_fill_proof. Qed.
Global Hint Resolve imp_expr_fill_ReturnExt : tstep.

(** ** instances *)
(* This pattern of using ImpExprFill at each rule is quite expensive
but we don't care at the moment. *)
Lemma imp_step_UbE_s fns h e K `{!ImpExprFill e K UbE}:
  TStepS imp_module (Imp e h fns) (λ G, G None (λ G', True)).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. eexists _, _. split; [done|] => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?. naive_solver.
Qed.
Global Hint Resolve imp_step_UbE_s : tstep.

Lemma imp_step_Var_s fns h e K v `{!ImpExprFill e K (Var v)}:
  TStepS imp_module (Imp e h fns) (λ G, G None (λ G', True)).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. eexists _, _. split; [done|] => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?. naive_solver.
Qed.
Global Hint Resolve imp_step_Var_s : tstep.

Lemma imp_step_Waiting_i fns h K e b `{!ImpExprFill e K (Waiting b)}:
  TStepI imp_module (Imp e h fns) (λ G,
    (∀ f fn vs h', fns !! f = Some fn →
      G true (Some (Incoming, EICall f vs h')) (λ G',  G'
          (Imp (expr_fill K (
           if bool_decide (length vs = length (fd_args fn)) then
             ReturnExt b ((subst_l fn.(fd_args) vs fn.(fd_body)))
           else
             UbE)) h' fns))) ∧
    ∀ v h', b → G true (Some (Incoming, EIReturn v h')) (λ G', G' (Imp (expr_fill K (Val v)) h' fns))
   ).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  invert_all head_step.
  - naive_solver.
  - naive_solver.
Qed.
Global Hint Resolve imp_step_Waiting_i : tstep.

Lemma imp_step_Waiting_s fns h e K b `{!ImpExprFill e K (Waiting b)}:
  TStepS imp_module (Imp e h fns) (λ G,
    (∃ f fn vs h', fns !! f = Some fn ∧
      G (Some (Incoming, EICall f vs h')) (λ G', G'
          (Imp (expr_fill K (if bool_decide (length vs = length (fd_args fn)) then
                               ReturnExt b ((subst_l fn.(fd_args) vs fn.(fd_body)))
                             else
                               UbE)) h' fns))) ∨
    ∃ v h', b ∧ G (Some (Incoming, EIReturn v h')) (λ G', G' (Imp (expr_fill K (Val v)) h' fns))
   ).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. destruct_all!; (split!; [done|]) => /= ??. 2: destruct b => //.
  all: apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?; destruct_all?; simplify_eq; done.
Qed.
Global Hint Resolve imp_step_Waiting_s : tstep.

Lemma imp_step_ReturnExt_i fns h e K b (v : val) `{!ImpExprFill e K (ReturnExt b (Val v))}:
  TStepI imp_module (Imp e h fns) (λ G,
    (G true (Some (Outgoing, EIReturn v h)) (λ G', G' (Imp (expr_fill K (Waiting b)) h fns)))).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  invert_all head_step.
  naive_solver.
Qed.
Global Hint Resolve imp_step_ReturnExt_i : tstep.

Lemma imp_step_ReturnExt_s fns h e K b (v : val) `{!ImpExprFill e K (ReturnExt b (Val v))}:
  TStepS imp_module (Imp e h fns) (λ G,
    (G (Some (Outgoing, EIReturn v h)) (λ G', G' (Imp (expr_fill K (Waiting b)) h fns)))).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct_all?; simplify_eq. done.
Qed.
Global Hint Resolve imp_step_ReturnExt_s : tstep.

Lemma imp_step_Call_i fns h e K f vs `{!ImpExprFill e K (imp.Call f (Val <$> vs))}:
  TStepI imp_module (Imp e h fns) (λ G,
    (∀ fn, fns !! f = Some fn → G true None (λ G', length vs = length fn.(fd_args) ∧
         G' (Imp (expr_fill K (subst_l fn.(fd_args) vs fn.(fd_body))) h fns))) ∧
    (fns !! f = None → G true (Some (Outgoing, EICall f vs h)) (λ G',
           G' (Imp (expr_fill K (Waiting true)) h fns)))).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]]. {
    apply sub_redexes_are_values_item; case; try naive_solver.
    move => /= ??? e' [_ Heq]. by apply: list_expr_val_inv.
  } { done. } subst.
  invert_all head_step.
  - naive_solver.
  - naive_solver.
Qed.
Global Hint Resolve imp_step_Call_i : tstep.

Lemma imp_step_Call_s fns h e K f vs `{!ImpExprFill e K (imp.Call f (Val <$> vs))}:
  TStepS imp_module (Imp e h fns) (λ G,
    (∃ fn, fns !! f = Some fn ∧ G None (λ G', length vs = length fn.(fd_args) → G'
             (Imp (expr_fill K (subst_l fn.(fd_args) vs fn.(fd_body))) h fns))) ∨
    (fns !! f = None ∧ G (Some (Outgoing, EICall f vs h)) (λ G',
           G' (Imp (expr_fill K (Waiting true)) h fns)))).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. destruct_all?; (split!; [done|]); move => /= ??.
  all: apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  all: destruct_all?; simplify_eq; naive_solver.
Qed.
Global Hint Resolve imp_step_Call_s : tstep.

Lemma imp_step_Binop_i fns h e K (v1 v2 : val) op `{!ImpExprFill e K (BinOp (Val v1) op (Val v2))}:
  TStepI imp_module (Imp e h fns) (λ G,
    (G true None (λ G', ∃ v', eval_binop op v1 v2 = Some v' ∧ G' (Imp (expr_fill K (Val v')) h fns)))).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  invert_all head_step.
  naive_solver.
Qed.
Global Hint Resolve imp_step_Binop_i | 10 : tstep.

Lemma imp_step_Binop_s fns h e K (v1 v2 : val) op `{!ImpExprFill e K (BinOp (Val v1) op (Val v2))}:
  TStepS imp_module (Imp e h fns) (λ G,
    (G None (λ G', ∀ v', eval_binop op v1 v2 = Some v' → G' (Imp (expr_fill K (Val v')) h fns)))).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct_all?; simplify_eq. naive_solver.
Qed.
Global Hint Resolve imp_step_Binop_s | 10 : tstep.

Lemma imp_step_BinopAdd_i fns h e K n1 n2 `{!ImpExprFill e K (BinOp (Val (ValNum n1)) AddOp (Val (ValNum n2)))}:
  TStepI imp_module (Imp e h fns) (λ G,
    (G true None (λ G', G' (Imp (expr_fill K (Val (ValNum (n1 + n2)))) h fns)))).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. tstep_i => ???. split! => ?. naive_solver.
Qed.
Global Hint Resolve imp_step_BinopAdd_i | 5 : tstep.

Lemma imp_step_BinopAdd_s fns h e K (v1 v2 : val) `{!ImpExprFill e K (BinOp (Val v1) AddOp (Val v2))}:
  TStepS imp_module (Imp e h fns) (λ G,
    (G None (λ G', ∀ n1 n2, v1 = ValNum n1 → v2 = ValNum n2 → G' (Imp (expr_fill K (Val (ValNum (n1 + n2)))) h fns)))).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??. tstep_s. split! => ? /bind_Some[?[? /bind_Some[?[??]]]].
  destruct v1, v2 => //. simplify_eq/=. naive_solver.
Qed.
Global Hint Resolve imp_step_BinopAdd_s | 5 : tstep.

Lemma imp_step_BinopShift_i fns h e K l z `{!ImpExprFill e K (BinOp (Val (ValLoc l)) ShiftOp (Val (ValNum z)))}:
  TStepI imp_module (Imp e h fns) (λ G,
    (G true None (λ G', G' (Imp (expr_fill K (Val (ValLoc (l +ₗ z)))) h fns)))).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. tstep_i => ???. split! => ?. naive_solver.
Qed.
Global Hint Resolve imp_step_BinopShift_i | 5 : tstep.

Lemma imp_step_BinopShift_s fns h e K (v1 v2 : val) `{!ImpExprFill e K (BinOp (Val v1) ShiftOp (Val v2))}:
  TStepS imp_module (Imp e h fns) (λ G,
    (G None (λ G', ∀ l z, v1 = ValLoc l → v2 = ValNum z → G' (Imp (expr_fill K (Val (ValLoc (l +ₗ z)))) h fns)))).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??. tstep_s. split! => ? /bind_Some[?[? /bind_Some[?[??]]]].
  destruct v1, v2 => //. simplify_eq/=. naive_solver.
Qed.
Global Hint Resolve imp_step_BinopShift_s | 5 : tstep.

Lemma imp_step_Load_i fns h e K l `{!ImpExprFill e K (Load (Val (ValLoc l)))}:
  TStepI imp_module (Imp e h fns) (λ G,
    (G true None (λ G', ∃ v', h.(h_heap) !! l = Some v' ∧ G' (Imp (expr_fill K (Val v')) h fns)))).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  invert_all head_step.
  naive_solver.
Qed.
Global Hint Resolve imp_step_Load_i : tstep.

Lemma imp_step_Load_s fns h e K v `{!ImpExprFill e K (Load (Val v))}:
  TStepS imp_module (Imp e h fns) (λ G,
    (G None (λ G', ∀ l v', v = ValLoc l → h.(h_heap) !! l = Some v' → G' (Imp (expr_fill K (Val v')) h fns)))).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct_all?; simplify_eq. naive_solver.
Qed.
Global Hint Resolve imp_step_Load_s : tstep.

Lemma imp_step_Store_i fns h e K l v `{!ImpExprFill e K (Store (Val (ValLoc l)) (Val v))}:
  TStepI imp_module (Imp e h fns) (λ G,
    (G true None (λ G', heap_alive h l ∧ G' (Imp (expr_fill K (Val v)) (heap_update h l v) fns)))).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  invert_all head_step.
  naive_solver.
Qed.
Global Hint Resolve imp_step_Store_i : tstep.

Lemma imp_step_Store_s fns h e K v1 v `{!ImpExprFill e K (Store (Val v1) (Val v))}:
  TStepS imp_module (Imp e h fns) (λ G,
    (G None (λ G', ∀ l, v1 = ValLoc l → heap_alive h l → G'
      (Imp (expr_fill K (Val v)) (heap_update h l v) fns)))).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct_all?; simplify_eq. naive_solver.
Qed.
Global Hint Resolve imp_step_Store_s : tstep.

Lemma imp_step_Alloc_i fns h e K n `{!ImpExprFill e K (Alloc (Val (ValNum n)))}:
  TStepI imp_module (Imp e h fns) (λ G, ∀ l, heap_is_fresh h l →
    (G true None (λ G', 0 < n ∧ G' (Imp (expr_fill K (Val (ValLoc l))) (heap_alloc h l n) fns)))).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  invert_all head_step.
  naive_solver.
Qed.
Global Hint Resolve imp_step_Alloc_i : tstep.

Lemma imp_step_Alloc_s fns h e K v `{!ImpExprFill e K (Alloc (Val v))}:
  TStepS imp_module (Imp e h fns) (λ G,
    (G None (λ G', ∃ l, heap_is_fresh h l ∧ (∀ n, v = ValNum n → 0 < n → G' (Imp (expr_fill K (Val (ValLoc l))) (heap_alloc h l n) fns))))).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ?[?[??]].
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct_all?; simplify_eq. naive_solver.
Qed.
Global Hint Resolve imp_step_Alloc_s : tstep.

Lemma imp_step_Free_i fns h e K l `{!ImpExprFill e K (Free (Val (ValLoc l)))}:
  TStepI imp_module (Imp e h fns) (λ G,
    (G true None (λ G', heap_alive h l ∧ G' (Imp (expr_fill K (Val (ValNum 0))) (heap_free h l) fns)))).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  invert_all head_step.
  naive_solver.
Qed.
Global Hint Resolve imp_step_Free_i : tstep.

Lemma imp_step_Free_s fns h e K v `{!ImpExprFill e K (Free (Val v))}:
  TStepS imp_module (Imp e h fns) (λ G,
    (G None (λ G', ∀ l, v = ValLoc l → heap_alive h l → G' (Imp (expr_fill K (Val 0)) (heap_free h l) fns)))).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct_all?; simplify_eq. naive_solver.
Qed.
Global Hint Resolve imp_step_Free_s : tstep.

Lemma imp_step_LetE_i fns h e K x v e1 `{!ImpExprFill e K (LetE x (Val v) e1)}:
  TStepI imp_module (Imp e h fns) (λ G,
    (G true None (λ G', G' (Imp (expr_fill K (subst x v e1)) h fns)))).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  invert_all head_step.
  naive_solver.
Qed.
Global Hint Resolve imp_step_LetE_i : tstep.

Lemma imp_step_LetE_s fns h e K x v e1 `{!ImpExprFill e K (LetE x (Val v) e1)}:
  TStepS imp_module (Imp e h fns) (λ G,
    (G None (λ G', G' (Imp (expr_fill K (subst x v e1)) h fns)))).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct_all?; simplify_eq. naive_solver.
Qed.
Global Hint Resolve imp_step_LetE_s : tstep.

Lemma imp_step_If_i fns h b K e1 e2 `{!ImpExprFill e K (If (Val (ValBool b)) e1 e2)}:
  TStepI imp_module (Imp e h fns) (λ G,
    (G true None (λ G', G' (Imp (expr_fill K (if b then e1 else e2)) h fns)))).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  invert_all head_step.
  naive_solver.
Qed.
Global Hint Resolve imp_step_If_i | 10 : tstep.

Lemma imp_step_If_s fns h v K e1 e2 `{!ImpExprFill e K (If (Val v) e1 e2)}:
  TStepS imp_module (Imp e h fns) (λ G,
    (G None (λ G', ∀ b, v = ValBool b → G' (Imp (expr_fill K (if b then e1 else e2)) h fns)))).
Proof.
  destruct ImpExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct_all?; simplify_eq. destruct v => //. naive_solver.
Qed.
Global Hint Resolve imp_step_If_s | 10 : tstep.

(** * proof technique for prepost *)
Lemma imp_prepost_proof {S} {M : ucmra} R `{!∀ b, PreOrder (R b)} i o fns1 fns2 s0 (r0 : uPred M):
  (* R true: public transition relation, R false: private transition relation *)
  (∀ s r s' r', R true (s, r) (s', r') → R false (s, r) (s', r')) →
  (∀ n K1 K2 f fn1 vs1 h1 s1 r1,
      R false (s0, r0) (s1, r1) →
      fns1 !! f = Some fn1 →
      pp_to_all (i (Incoming, EICall f vs1 h1) s1) (λ '(e', s2) r2, ∀ r2',
      satisfiable (r1 ∗ r2 ∗ r2') →
      ∃ vs2 h2 fn2, e' = (Incoming, EICall f vs2 h2) ∧ fns2 !! f = Some fn2 ∧ (
        length vs2 = length (fd_args fn2) →
          length vs1 = length (fd_args fn1) ∧ (
      (* Call *)
      (∀ n' f K1' K2' es1 es2 vs1' vs2' h1' h2' b s3 r3,
         n' ⊆ n →
         fns1 !! f = None →
         fns2 !! f = None →
         Forall2 (λ e v, e = Val v) es1 vs1' →
         Forall2 (λ e v, e = Val v) es2 vs2' →
         pp_to_ex (o (Outgoing, EICall f vs2' h2') s3) (λ '(e''', s4) r4, ∃ r4',
            e''' = (Outgoing, EICall f vs1' h1') ∧ R false (s1, r1) (s4, r4') ∧
            satisfiable (r4' ∗ r4 ∗ r3) ∧
           ∀ v1'' h1'' s5 r5, R true (s4, r4') (s5, r5) →
                   pp_to_all (i (Incoming, EIReturn v1'' h1'') s5) (λ '(e''''', s6) r6, ∀ r6',
                     satisfiable (r5 ∗ r6 ∗ r6') →
            ∃ v2'' h2'', e''''' = (Incoming, EIReturn v2'' h2'') ∧
          Imp (expr_fill K1 (expr_fill K1' (Val v1''))) h1'' fns1
              ⪯{imp_module, mod_prepost i o imp_module, n', true}
          (SMProg, Imp (expr_fill K2 (expr_fill K2' (Val v2''))) h2'' fns2, (PPInside, s6, r6')))) →

          Imp (expr_fill K1 (expr_fill K1' (Call f es1))) h1' fns1
              ⪯{imp_module, mod_prepost i o imp_module, n', b}
          (SMProg, Imp (expr_fill K2 (expr_fill K2' (Call f es2))) h2' fns2, (PPInside, s3, r3))) →
      (* Return *)
      (∀ n' v1 v2 h1' h2' b s3 r3,
         n' ⊆ n →
         pp_to_ex (o (Outgoing, EIReturn v2 h2') s3) (λ '(e''', s4) r4, ∃ r4',
               e''' = (Outgoing, EIReturn v1 h1') ∧ R true (s1, r1) (s4, r4') ∧ satisfiable (r4' ∗ r4 ∗ r3)) →
          Imp (expr_fill K1 (Val v1)) h1' fns1
              ⪯{imp_module, mod_prepost i o imp_module, n', b}
          (SMProg, Imp (expr_fill K2 (Val v2)) h2' fns2, (PPInside, s3, r3))) →
      Imp (expr_fill K1 (subst_l fn1.(fd_args) vs1 fn1.(fd_body))) h1 fns1
          ⪯{imp_module, mod_prepost i o imp_module, n, false}
          (SMProg, Imp (expr_fill K2 (subst_l fn2.(fd_args) vs2 fn2.(fd_body))) h2 fns2, (PPInside, s2, r2')))))) →
  trefines (MS imp_module (initial_imp_state fns1))
           (MS (mod_prepost (S:=S) i o imp_module)
               (SMFilter, initial_imp_state fns2, (PPOutside, s0, r0))).
Proof.
  move => HR Hc.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember_call.
  { simpl. exact (λ d b '((Imp ei1 hi1 fnsi1), (ips1, Imp es1 hs1 fnss1, (pp1, s1, r1)))
                    '((Imp ei2 hi2 fnsi2), (ips2, Imp es2 hs2 fnss2, (pp2, s2, r2))),
    ∃ Ki Ks,
      fnsi2 = fns1 ∧
      fnss2 = fns2 ∧
      ei2 = expr_fill Ki (Waiting (bool_decide (d ≠ 0%nat))) ∧
      es2 = expr_fill Ks (Waiting (bool_decide (d ≠ 0%nat))) ∧
      pp2 = PPOutside ∧
      ips2 = SMFilter ∧
      R b (s1, r1) (s2, r2) ∧
      if b then
        ei2 = ei1 ∧
        es2 = es1
      else
        True
                 ). }
  { simpl. exact (λ  '(Imp ei1 hi1 fnsi1) '(ips1, Imp es1 hs1 fnss1, (pp1, s1, r1))
                     '(Imp ei2 hi2 fnsi2) '(ips2, Imp es2 hs2 fnss2, (pp2, s2, r2)),
    ∃ Ki b v,
      fnsi2 = fnsi1 ∧
      fnss2 = fnss1 ∧
      ei1 = expr_fill Ki (Waiting b) ∧
      es2 = es1 ∧
      ei2 = expr_fill Ki (Val v) ∧
      ips2 = SMFilter ∧
      hs2 = hs1 ∧
      pp2 = PPRecv1 (Incoming, EIReturn v hi2) ∧
      s2 = s1 ∧
      r2 = r1). }
  { move => ??? *. destruct_all?. repeat case_match; naive_solver. }
  { move => /= *. destruct_all?. repeat case_match. naive_solver. }
  { move => /=. eexists [], []. split!. }
  move => /= n [ei hi fnsi] [[ips [es hs fnss]] [[pp {}s] r]] d ? ? Hstay Hcall Hret. destruct_all!; simplify_eq.
  tstep_i. split => *.
  - tstep_s. split!.
    tstep_s. apply: pp_to_all_mono. { by eapply (Hc n (ReturnExtCtx _ :: Ki) (ReturnExtCtx _ :: Ks)). }
    move => -[??] ? Hcall' ??. move: Hcall' => /(_ _ ltac:(done))[?[?[?[?[? Hcall']]]]]. simplify_eq/=.
    tstep_s. left. split!. repeat case_bool_decide (_ = _); try by tstep_s. 2: naive_solver.
    have [//|? {}Hcall'] := Hcall'. apply: tsim_mono_b. apply: Hcall'.
    + move => n' f K1' K2' es1 es2 vs1' vs2' ???????? Hall1 Hall2 ?.
      have ?: es1 = Val <$> vs1'. { clear -Hall1. elim: Hall1; naive_solver. } subst.
      have ?: es2 = Val <$> vs2'. { clear -Hall2. elim: Hall2; naive_solver. } subst.
      tstep_i. split => *; simplify_eq. rewrite orb_true_r. tstep_s. right. split!.
      tstep_s. apply: pp_to_ex_mono; [done|].
      move => [??] ? /= [?[?[?[??]]]]. simplify_eq. split!; [done|].
      apply Hcall; [done| |]. { split!; [done..|]. by etrans. }
      move => [ei2 hi2 fnsi2] [[ips2 [es2 hs2 fnss2]] [[pp2 {}s2] r2]].
      move => [ei3 hi3 fnsi3] [[ips3 [es3 hs3 fnss3]] [[pp3 {}s3] r3]] ??.
      destruct_all?; simplify_eq.
      tstep_s. apply: pp_to_all_mono; [naive_solver|].
      move => [??] ? Hsim ??. move: Hsim => /(_ _ ltac:(done))?. destruct_all?. simplify_eq/=.
      tstep_s. right. split!.
      repeat match goal with | H : expr_fill _ _ = expr_fill _ _ |- _ => apply expr_fill_Waiting_inj in H end.
      destruct_all?; simplify_eq.
      by rewrite !expr_fill_app.
    + move => *. tstep_s. tstep_i. rewrite orb_true_r. tstep_s. apply: pp_to_ex_mono; [done|].
      move => [??] ? [?[?[??]]] /=. subst. split!; [done|]. apply: tsim_mono; [|done].
      apply: Hstay; [done|]. split!; [done..|]. naive_solver.
  - tstep_s. split!.
    apply: Hret; [done|naive_solver| |].
    + by split!.
    + by split!.
Qed.
(** * closing *)
(*
module imp_event:
Incoming, Call f vs h -> Outgoing, Call f' vs' h' → Incoming, Return v h' -> Outgoing, Return v' h''


module imp_closed_event:
Start f vs            -> Call f' vs' v                                     -> Return v'
*)

Inductive imp_closed_event : Type :=
| EICStart (f : string) (args: list Z)
| EICCall (f : string) (args: list Z) (ret : Z)
| EICEnd (ret : val)
.

Inductive imp_closed_state :=
| ICStart
| ICRecvStart (f : string) (vs : list Z)
| ICRunning
| ICRecvCall1 (f : string) (args : list val) (h : heap_state)
| ICRecvCall2 (f : string) (args : list Z) (h : heap_state)
| ICRecvRet (v : Z) (h : heap_state)
| ICRecvEnd1 (v : val)
| ICRecvEnd2 (v : Z)
| ICEnd.

Inductive imp_closed_step :
  imp_closed_state → option (imp_event + imp_closed_event) → (imp_closed_state → Prop) → Prop :=
| ICStartS f vs:
  imp_closed_step ICStart (Some (inr (EICStart f vs))) (λ σ, σ = ICRecvStart f vs)
| ICRecvStartS f vs:
  imp_closed_step (ICRecvStart f vs)
                  (Some (inl (Incoming, EICall f (ValNum <$> vs) initial_heap_state))) (λ σ, σ = ICRunning)
| ICRunningS f vs h:
  imp_closed_step ICRunning (Some (inl (Outgoing, EICall f vs h))) (λ σ, σ = ICRecvCall1 f vs h)
| ICRecvCall1S f vs h:
  imp_closed_step (ICRecvCall1 f vs h) None (λ σ,
         ∃ vs', vs = ValNum <$> vs' ∧ σ = ICRecvCall2 f vs' h)
| ICRecvCall2S f vs rv h:
  imp_closed_step (ICRecvCall2 f vs h)
                  (Some (inr (EICCall f vs rv))) (λ σ, σ = ICRecvRet rv h)
| ICRecvRetS v h:
  imp_closed_step (ICRecvRet v h)
                  (Some (inl (Incoming, EIReturn (ValNum v) h))) (λ σ, σ = ICRunning)
| ICRunningEndS v h:
  imp_closed_step ICRunning (Some (inl (Outgoing, EIReturn v h))) (λ σ, σ = ICRecvEnd1 v)
| ICRecvEnd1EndS v:
  imp_closed_step (ICRecvEnd1 v) None (λ σ, ∃ v', v = ValNum v' ∧ σ = ICRecvEnd2 v')
| ICEndS v:
  imp_closed_step (ICRecvEnd2 v) (Some (inr (EICEnd v))) (λ σ, σ = ICEnd)
.

Definition imp_closed_filter_module : module (imp_event + imp_closed_event) :=
  Mod imp_closed_step.

Global Instance imp_closed_filter_module_vis_no_all : VisNoAll imp_closed_filter_module.
Proof. move => ????. invert_all @m_step; naive_solver. Qed.

Definition imp_closed (m : module imp_event) : module imp_closed_event :=
  mod_seq_map m imp_closed_filter_module.

(** * syntactic linking *)
Definition imp_link (fns1 fns2 : gmap string fndef) : gmap string fndef :=
  fns1 ∪ fns2.

Definition imp_ctx_refines (fnsi fnss : gmap string fndef) :=
  ∀ C, trefines (MS (imp_closed imp_module) (SMFilter, initial_imp_state (imp_link fnsi C), ICStart))
                (MS (imp_closed imp_module) (SMFilter, initial_imp_state (imp_link fnss C), ICStart)).

(** * semantic linking *)
Definition imp_prod_filter (fns1 fns2 : gset string) : seq_product_state → list seq_product_state → imp_ev → seq_product_state → list seq_product_state → imp_ev → Prop :=
  λ p cs e p' cs' e',
    e' = e ∧
    match e with
    | EICall f vs h =>
        p' = (if bool_decide (f ∈ fns1) then SPLeft else if bool_decide (f ∈ fns2) then SPRight else SPNone) ∧
        (cs' = p::cs) ∧
        p ≠ p'
    | EIReturn v h =>
        cs = p'::cs' ∧
        p ≠ p'
    end.
Arguments imp_prod_filter _ _ _ _ _ _ _ _ /.

Definition imp_prod (fns1 fns2 : gset string) (m1 m2 : module imp_event) : module imp_event :=
  mod_link (imp_prod_filter fns1 fns2) m1 m2.

Lemma imp_prod_trefines m1 m1' m2 m2' σ1 σ1' σ2 σ2' σ ins1 ins2 `{!VisNoAll m1} `{!VisNoAll m2}:
  trefines (MS m1 σ1) (MS m1' σ1') →
  trefines (MS m2 σ2) (MS m2' σ2') →
  trefines (MS (imp_prod ins1 ins2 m1 m2) (σ, σ1, σ2))
           (MS (imp_prod ins1 ins2 m1' m2') (σ, σ1', σ2')).
Proof. move => ??. by apply mod_link_trefines. Qed.

Inductive imp_link_prod_combine_ectx :
  nat → bool → bool → mod_link_state imp_ev → list seq_product_state → list expr_ectx → list expr_ectx → list expr_ectx → Prop :=
| IPCENil:
  imp_link_prod_combine_ectx 0 false false MLFNone [] [] [] []
| IPCENoneToLeft n cs K Kl Kr bl br:
  imp_link_prod_combine_ectx n bl br MLFNone cs K Kl Kr →
  imp_link_prod_combine_ectx (S n) bl br MLFLeft (SPNone :: cs)
                             (ReturnExtCtx (bl || br)::K) (ReturnExtCtx bl::Kl) Kr
| IPCENoneToRight n cs K Kl Kr bl br:
  imp_link_prod_combine_ectx n bl br MLFNone cs K Kl Kr →
  imp_link_prod_combine_ectx (S n) bl br MLFRight (SPNone :: cs)
                             (ReturnExtCtx (bl || br)::K) Kl (ReturnExtCtx br::Kr)
| IPCELeftToRight n cs K Kl Kl' Kr bl br:
  imp_link_prod_combine_ectx n bl br MLFLeft cs K Kl Kr →
  static_expr true (expr_fill Kl' (Var "")) →
  imp_link_prod_combine_ectx (S n) true br MLFRight (SPLeft :: cs)
                             (Kl' ++ K) (Kl' ++ Kl) (ReturnExtCtx br::Kr)
| IPCELeftToNone n cs K Kl Kl' Kr bl br:
  imp_link_prod_combine_ectx n bl br MLFLeft cs K Kl Kr →
  static_expr true (expr_fill Kl' (Var "")) →
  imp_link_prod_combine_ectx (S n) true br MLFNone (SPLeft :: cs)
                             (Kl' ++ K) (Kl' ++ Kl) Kr
| IPCERightToLeft n cs K Kl Kr' Kr bl br:
  imp_link_prod_combine_ectx n bl br MLFRight cs K Kl Kr →
  static_expr true (expr_fill Kr' (Var "")) →
  imp_link_prod_combine_ectx (S n) bl true MLFLeft (SPRight :: cs)
                             (Kr' ++ K) (ReturnExtCtx bl::Kl) (Kr' ++ Kr)
| IPCERightToNone n cs K Kl Kr' Kr bl br:
  imp_link_prod_combine_ectx n bl br MLFRight cs K Kl Kr →
  static_expr true (expr_fill Kr' (Var "")) →
  imp_link_prod_combine_ectx (S n) bl true MLFNone (SPRight :: cs)
                             (Kr' ++ K) Kl (Kr' ++ Kr)
.

Definition imp_link_prod_inv (bv : bool) (fns1 fns2 : gmap string fndef) (σ1 : imp_module.(m_state)) (σ2 : mod_link_state imp_ev * list seq_product_state * imp_state * imp_state) : Prop :=
  let 'Imp e1 h1 fns1' := σ1 in
  let '(σf, cs, Imp el hl fnsl, Imp er hr fnsr) := σ2 in
  ∃ n K Kl Kr e1' el' er' bl br,
  fns1' = fns1 ∪ fns2 ∧
  fnsl = fns1 ∧
  fnsr = fns2 ∧
  imp_link_prod_combine_ectx n bl br σf cs K Kl Kr ∧
  e1 = expr_fill K e1' ∧
  el = expr_fill Kl el' ∧
  er = expr_fill Kr er' ∧
  match σf with
  | MLFLeft => e1' = el' ∧ static_expr true el' ∧ er' = Waiting br ∧ h1 = hl
              ∧ (if bv then to_val el' = None else True)
  | MLFRight => e1' = er' ∧ static_expr true er' ∧ el' = Waiting bl ∧ h1 = hr
               ∧ (if bv then to_val er' = None else True)
  | MLFNone => e1' = Waiting (bl || br) ∧ el' = Waiting bl ∧ er' = Waiting br
  | _ => False
  end.

Lemma imp_link_refines_prod fns1 fns2:
  fns1 ##ₘ fns2 →
  trefines (MS imp_module (initial_imp_state (imp_link fns1 fns2)))
           (MS (imp_prod (dom _ fns1) (dom _ fns2) imp_module imp_module)
               (MLFNone, [], initial_imp_state fns1, initial_imp_state fns2)).
Proof.
  move => Hdisj.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { exact: (λ _, imp_link_prod_inv true fns1 fns2). }
  { split!. 1: by econs. all: done. } { done. }
  move => /= {}n _ Hloop [e1 h1 fns1'] [[[ipfs cs] [el hl fnsl]] [er hr fnsr]] [m [K [Kl [Kr ?]]]].
  have {}Hloop : ∀ σi σs,
            imp_link_prod_inv false fns1 fns2 σi σs
            → σi ⪯{imp_module, imp_prod (dom (gset string) fns1) (dom (gset string) fns2) imp_module imp_module, n, true} σs. {
    clear -Hloop. move => [e1 h1 fns1'] [[[ipfs cs] [el hl fnsl]] [er hr fnsr]].
    move => [m [K [Kl [Kr [e1' [el' [er' [bl [br [?[?[?[HK[?[?[? Hm]]]]]]]]]]]]]]]]; simplify_eq.
    elim/lt_wf_ind: m ipfs h1 hl hr cs K Kl Kr e1' el' er' bl br HK Hm => m IHm.
    move => ipfs h1 hl hr cs K Kl Kr e1' el' er' bl br HK Hmatch.
    case_match; destruct_all?; simplify_eq/=.
    - destruct (to_val el') eqn:?; [ |apply: Hloop; naive_solver].
      destruct el'; simplify_eq/=.
      inversion HK; clear HK; simplify_eq/=.
      * tstep_i. tstep_s. split!; [done..|] => /=. split!.
        apply: Hloop; [done|]. by split!.
      * tstep_s. split!.
        tstep_s. split!.
        rewrite !expr_fill_app. apply: IHm; [|done|]; [lia|]. split!. by apply static_expr_expr_fill.
    - destruct (to_val er') eqn:?; [ |apply: Hloop; naive_solver].
      destruct er'; simplify_eq/=.
      inversion HK; clear HK; simplify_eq/=.
      * tstep_i. tstep_s. split!. apply: Hloop; [done|]. by split!.
      * tstep_s. split!.
        tstep_s. split!.
        rewrite !expr_fill_app. apply: IHm; [|done|]; [lia|]. split!. by apply static_expr_expr_fill.
    - apply: Hloop; naive_solver.
  }
  destruct_all?; simplify_eq/=. case_match; destruct_all?; simplify_eq.
  - tstep_both. apply: steps_impl_step_end => ?? /prim_step_inv[//|?[?[?[?[??]]]]].
    simplify_eq. revert select (Is_true (static_expr _ _)) => /static_expr_expr_fill/=[??]//.
    rewrite -expr_fill_app.
    invert_all head_step => //.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply static_expr_expr_fill.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply static_expr_expr_fill.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply static_expr_expr_fill.
    + tstep_s => *. split!; [done..|] => /= *; simplify_eq.
      split!; [done..|] => /= *; simplify_eq. tend. split!.
      apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply static_expr_expr_fill.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply static_expr_expr_fill.
    + tstep_s => b ?. subst. tend. split!. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      apply static_expr_expr_fill. split!. destruct b; naive_solver.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      apply static_expr_expr_fill. split!. by apply static_expr_subst.
    + tstep_s. done.
    + tstep_s. done.
    + revert select ((_ ∪ _) !! _ = Some _) => /lookup_union_Some_raw[?|[??]].
      * tstep_s. left. split!. tend. split!.
        apply: Hloop. rewrite !expr_fill_app. split!; [done..|].
        apply static_expr_expr_fill. split!. apply static_expr_subst_l; [|done].
        apply static_expr_mono. apply fd_static.
      * tstep_s. right. simpl_map_decide. split!.
        tstep_s. left. split!. case_bool_decide.
        2: { tstep_s. done. }
        tend. split!. apply: Hloop. split!; [by econs|done..|].
        apply static_expr_subst_l; [|done]. apply static_expr_mono. apply fd_static.
    + revert select ((_ ∪ _) !! _ = None) => /lookup_union_None[??].
      tstep_s. right. simpl_map_decide. split!; [done|]. tend. split!.
      apply: Hloop. split!; [by econs|done..].
  - tstep_both. apply: steps_impl_step_end => ?? /prim_step_inv[//|?[?[?[?[??]]]]].
    simplify_eq. revert select (Is_true (static_expr _ _)) => /static_expr_expr_fill/=[??]//.
    rewrite -expr_fill_app.
    invert_all head_step => //.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply static_expr_expr_fill.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply static_expr_expr_fill.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply static_expr_expr_fill.
    + tstep_s => *. split!; [done..|] => /= *; simplify_eq.
      split!; [done..|] => /= *; simplify_eq. tend. split!.
      apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply static_expr_expr_fill.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply static_expr_expr_fill.
    + tstep_s => b ?. subst. tend. split!. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      apply static_expr_expr_fill. split!. destruct b; naive_solver.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      apply static_expr_expr_fill. split!. by apply static_expr_subst.
    + tstep_s. done.
    + tstep_s. done.
    + revert select ((_ ∪ _) !! _ = Some _) => /lookup_union_Some_raw[?|[??]].
      * have ? : fns2 !! f = None by apply: map_disjoint_Some_l.
        tstep_s. right. simpl_map_decide. split!.
        tstep_s. left. split!. case_bool_decide.
        2: { by tstep_s. }
        tend. split!. apply: Hloop. split!; [by econs|done..|].
        apply static_expr_subst_l; [|done]. apply static_expr_mono. apply fd_static.
      * tstep_s. left. split! => /= ?. tend. split!.
        apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
        apply static_expr_expr_fill. split!. apply static_expr_subst_l; [|done].
        apply static_expr_mono. apply fd_static.
    + revert select ((_ ∪ _) !! _ = None) => /lookup_union_None[??].
      tstep_s. right. simpl_map_decide. split!;[done|] => /=. tend. split!; [done..|].
      apply: Hloop. split!; [by econs|rewrite ?orb_true_r; done..].
  - tstep_i. split.
    + move => f fn vs h' /lookup_union_Some_raw[?|[??]].
      * have ?: fns2 !! f = None by apply: map_disjoint_Some_l.
        tstep_s. eexists (EICall _ _ _) => /=. simpl. simpl_map_decide. split!.
        tstep_s. split!. case_bool_decide. 2: { tstep_s. naive_solver. }
        apply Hloop. split!; [by econs|done..| ].
        apply static_expr_subst_l; [|done]. apply static_expr_mono. apply fd_static.
      * tstep_s. eexists (EICall _ _ _) => /=. simpl. simpl_map_decide. split!.
        tstep_s. split!. case_bool_decide. 2: { tstep_s. naive_solver. }
        apply Hloop. split!; [by econs|done..| ].
        apply static_expr_subst_l; [|done]. apply static_expr_mono. apply fd_static.
    + move => v h' ?.
      revert select (imp_link_prod_combine_ectx _ _ _ _ _ _ _ _) => HK.
      inversion HK; clear HK; simplify_eq/= => //.
      * tstep_s. eexists (EIReturn _ _) => /=. split!.
        tstep_s. split!.
        apply Hloop. rewrite !expr_fill_app. split!; [done..|].
        by apply static_expr_expr_fill.
      * tstep_s. eexists (EIReturn _ _) => /=. split!.
        tstep_s. split!.
        apply Hloop. rewrite !expr_fill_app. split!; [done..|].
        by apply static_expr_expr_fill.
Qed.

Lemma imp_prod_refines_link fns1 fns2:
  fns1 ##ₘ fns2 →
  trefines (MS (imp_prod (dom _ fns1) (dom _ fns2) imp_module imp_module)
               (MLFNone, [], initial_imp_state fns1, initial_imp_state fns2))
           (MS imp_module (initial_imp_state (imp_link fns1 fns2))).
Proof.
  move => Hdisj.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { exact: (λ _, flip (imp_link_prod_inv false fns1 fns2)). }
  { split!. 1: by econs. all: done. } { done. }
  move => /= {}n _ Hloop [[[ipfs cs] [el hl fnsl]] [er hr fnsr]] [e1 h1 fns1'] [m [K [Kl [Kr ?]]]].
  destruct_all?; simplify_eq/=. case_match; destruct_all?; simplify_eq.
  - destruct (to_val el') eqn:?.
    + destruct el'; simplify_eq/=.
      revert select (imp_link_prod_combine_ectx _ _ _ _ _ _ _ _) => HK.
      inversion HK; clear HK; simplify_eq/=.
      * tstep_i => *; destruct_all?; simplify_eq. tstep_s. split!.
        apply: Hloop; [done|]. by split!.
      * tstep_i => *; destruct_all?; simplify_eq/=.
        tstep_i; split => *; simplify_eq.
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..|].
        by apply static_expr_expr_fill.
    + tstep_both. apply: steps_impl_step_end => ?? /prim_step_inv[//|?[?[?[?[??]]]]] *.
      simplify_eq. revert select (Is_true (static_expr _ _)) => /static_expr_expr_fill/=[??]//.
      rewrite -expr_fill_app.
      invert_all head_step => //; destruct_all?; simplify_eq.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply static_expr_expr_fill.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply static_expr_expr_fill.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply static_expr_expr_fill.
      * tstep_s => *. split!; [done..|] => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply static_expr_expr_fill.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply static_expr_expr_fill.
      * tstep_s => b ?. subst. tend. split!. apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply static_expr_expr_fill. split!. destruct b; naive_solver.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply static_expr_expr_fill. split!. by apply static_expr_subst.
      * by tstep_s.
      * by tstep_s.
      * tstep_s. left. split!; [apply lookup_union_Some; naive_solver|] => ?. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..|].
        apply static_expr_expr_fill. split!. apply static_expr_subst_l; [|done].
        apply static_expr_mono. apply fd_static.
      * move => *. destruct_all?; simplify_eq/=. repeat case_bool_decide => //.
        -- have [??] : is_Some (fns2 !! f) by apply elem_of_dom.
           tstep_s. left. split!; [apply lookup_union_Some; naive_solver|] => ?. tend. split!.
           tstep_i. split => *; simplify_eq. case_bool_decide => //.
           apply: Hloop; [done|]. split!; [by econs|done..|].
           apply static_expr_subst_l; [|done]. apply static_expr_mono. apply fd_static.
        -- tstep_s. right. split!; [apply lookup_union_None;split!;by apply not_elem_of_dom| done|].
           tend. split!. apply: Hloop; [done|]. split!; [by econs|done..].
  - destruct (to_val er') eqn:?.
    + destruct er'; simplify_eq/=.
      revert select (imp_link_prod_combine_ectx _ _ _ _ _ _ _ _) => HK.
      inversion HK; clear HK; simplify_eq/=.
      * tstep_i => *; destruct_all?; simplify_eq. tstep_s. split!.
        apply: Hloop; [done|]. by split!.
      * tstep_i => *; destruct_all?; simplify_eq/=.
        tstep_i; split => *; simplify_eq.
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..|].
        by apply static_expr_expr_fill.
    + tstep_both. apply: steps_impl_step_end => ?? /prim_step_inv[//|?[?[?[?[??]]]]] *.
      simplify_eq. revert select (Is_true (static_expr _ _)) => /static_expr_expr_fill/=[??]//.
      rewrite -expr_fill_app.
      invert_all head_step => //; destruct_all?; simplify_eq.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply static_expr_expr_fill.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply static_expr_expr_fill.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply static_expr_expr_fill.
      * tstep_s => *. split!;[done..|] => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply static_expr_expr_fill.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply static_expr_expr_fill.
      * tstep_s => b ?. subst. tend. split!. apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply static_expr_expr_fill. split!. destruct b; naive_solver.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply static_expr_expr_fill. split!. by apply static_expr_subst.
      * by tstep_s.
      * by tstep_s.
      * tstep_s. left. split!; [apply lookup_union_Some; naive_solver|] => ?. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..|].
        apply static_expr_expr_fill. split!. apply static_expr_subst_l; [|done].
        apply static_expr_mono. apply fd_static.
      * move => *. destruct_all?; simplify_eq/=. repeat case_bool_decide => //.
        -- have [??] : is_Some (fns1 !! f) by apply elem_of_dom.
           tstep_s. left. split!; [apply lookup_union_Some; naive_solver|] => ?.
           tend. split!.
           tstep_i. split => *; invert_all imp_prod_filter. case_bool_decide => //.
           apply: Hloop; [done|]. split!; [by econs|done..|].
           apply static_expr_subst_l; [|done]. apply static_expr_mono. apply fd_static.
        -- tstep_s. right. split!; [apply lookup_union_None;split!;by apply not_elem_of_dom|done|].
           tend. split!. apply: Hloop; [done|]. split!; [by econs|rewrite ?orb_true_r; done..].
  - tstep_i => *.
    repeat match goal with | x : imp_ev |- _ => destruct x end; simplify_eq/=; destruct_all?; simplify_eq/=.
    + tstep_s. left. repeat case_bool_decide => //.
      all: revert select (_ ∈ dom _ _) => /elem_of_dom[??]; split!;
               [rewrite lookup_union_Some //; naive_solver |].
      * case_bool_decide. 2: { by tstep_s. }
        tstep_i. split => *; destruct_all?; simplify_eq/=. case_bool_decide => //.
        apply: Hloop; [done|]. split!; [by econs|done..|]. apply static_expr_subst_l; [|done].
        apply static_expr_mono. apply fd_static.
      * case_bool_decide. 2: { by tstep_s. }
        tstep_i. split => *; destruct_all?; simplify_eq/=. case_bool_decide => //.
        apply: Hloop; [done|]. split!; [by econs|done..|]. apply static_expr_subst_l; [|done].
        apply static_expr_mono. apply fd_static.
    + tstep_s. right.
      revert select (imp_link_prod_combine_ectx _ _ _ _ _ _ _ _) => HK.
      inversion HK; clear HK; simplify_eq; rewrite ?orb_true_r.
      * split!. tstep_i. split => *; destruct_all?; simplify_eq/=.
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done|done..|].
        by apply static_expr_expr_fill.
      * split!. tstep_i. split => *; destruct_all?; simplify_eq/=.
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done|done..|].
        by apply static_expr_expr_fill.
Qed.

Lemma imp_trefines_implies_ctx_refines fnsi fnss :
  dom (gset _) fnsi = dom (gset _) fnss →
  trefines (MS imp_module (initial_imp_state fnsi)) (MS imp_module (initial_imp_state fnss)) →
  imp_ctx_refines fnsi fnss.
Proof.
  move => Hdom Href C. rewrite /imp_link map_difference_union_r (map_difference_union_r fnss).
  apply mod_seq_map_trefines. { apply _. } { apply _. }
  etrans. { apply imp_link_refines_prod. apply map_disjoint_difference_r'. }
  etrans. 2: { apply imp_prod_refines_link. apply map_disjoint_difference_r'. }
  rewrite !dom_difference_L Hdom.
  apply imp_prod_trefines; [apply _..| |].
  - apply: Href.
  - erewrite map_difference_eq_dom_L => //. apply _.
Qed.
