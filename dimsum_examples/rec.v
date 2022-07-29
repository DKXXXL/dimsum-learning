From dimsum.core Require Export proof_techniques link prepost.
From dimsum.core Require Import axioms.

Local Open Scope Z_scope.

(** * Rec, a "C-like" language *)
(** ** Locations *)
Declare Scope loc_scope.
Delimit Scope loc_scope with L.
Open Scope loc_scope.

Definition prov : Set := Z.
Definition loc : Set := (prov * Z).

Definition offset_loc (l : loc) (z : Z) : loc := (l.1, l.2 + z).
Notation "l +ₗ z" := (offset_loc l%L z%Z) (at level 50, left associativity) : loc_scope.
Global Typeclasses Opaque offset_loc.

Lemma offset_loc_0 l :
  l +ₗ 0 = l.
Proof. rewrite /offset_loc. destruct l => /=. f_equal. lia. Qed.

Lemma offset_loc_assoc l n1 n2 :
  l +ₗ n1 +ₗ n2 = l +ₗ (n1 + n2).
Proof. rewrite /offset_loc. destruct l => /=. f_equal. lia. Qed.

Global Instance offset_loc_inj_r l : Inj eq eq (λ i, l +ₗ i).
Proof. move => ??. rewrite /offset_loc /= => ?. simplify_eq. lia. Qed.

Global Instance offset_loc_inj_r2 l i : Inj eq eq (λ j, l +ₗ i +ₗ j).
Proof. move => ??. rewrite /offset_loc /= => ?. simplify_eq. lia. Qed.

Lemma offset_loc_S l i :
  l +ₗ S i = l +ₗ 1 +ₗ i.
Proof. rewrite /offset_loc /=. f_equal. lia. Qed.

Lemma offset_loc_add_sub l i j:
  i = - j →
  l +ₗ i +ₗ j = l.
Proof. destruct l. rewrite /offset_loc /= => ?. f_equal. lia. Qed.

(** ** Syntax *)
Inductive binop : Set :=
| AddOp | OffsetOp | EqOp | LeOp | LtOp.

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
| If (e e1 e2 : expr)
| LetE (v : string) (e1 e2 : expr)
| Call (f : string) (args : list expr)
(* expressions only appearing at runtime: *)
| AllocA (ls : list (string * Z)) (e : expr)
| FreeA (ls : list (loc * Z)) (e : expr)
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
  (∀ (e1 e2 e3 : expr), P e1 → P e2 → P e3 → P (If e1 e2 e3)) →
  (∀ (v : string) (e1 e2 : expr), P e1 → P e2 → P (LetE v e1 e2)) →
  (∀ (f : string) (args : list expr), Forall P args → P (Call f args)) →
  (∀ ls (e : expr), P e → P (AllocA ls e)) →
  (∀ ls (e : expr), P e → P (FreeA ls e)) →
  (∀ (can_return_further : bool) (e : expr), P e → P (ReturnExt can_return_further e)) →
  (∀ (can_return : bool), P (Waiting can_return)) →
  ∀ (e : expr), P e.
Proof.
  move => *. generalize dependent P => P. match goal with | e : expr |- _ => revert e end.
  fix FIX 1. move => [ ^e] => ??????? Hcall ????.
  8: { apply Hcall. apply Forall_true => ?. by apply: FIX. }
  all: auto.
Qed.

Global Instance val_inj : Inj (=) (=) Val.
Proof. move => ?? []. done. Qed.

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

Fixpoint assigned_vars (e : expr) : list string :=
  match e with
  | Var v => []
  | Val v => []
  | BinOp e1 o e2 => assigned_vars e1 ++ assigned_vars e2
  | Load e => assigned_vars e
  | Store e1 e2 => assigned_vars e1 ++ assigned_vars e2
  | If e e1 e2 => assigned_vars e ++ assigned_vars e1 ++ assigned_vars e2
  | LetE v e1 e2 => [v] ++ assigned_vars e1 ++ assigned_vars e2
  | Call f args => mjoin (assigned_vars <$> args)
  | AllocA _ e => assigned_vars e
  | FreeA _ e => assigned_vars e
  | ReturnExt can_return_further e => assigned_vars e
  | Waiting can_return => []
  end.

(** ** Substitution *)
Fixpoint subst (x : string) (v : val) (e : expr) : expr :=
  match e with
  | Var y => if bool_decide (x = y) then Val v else Var y
  | Val v => Val v
  | BinOp e1 o e2 => BinOp (subst x v e1) o (subst x v e2)
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  | If e e1 e2 => If (subst x v e) (subst x v e1) (subst x v e2)
  | LetE y e1 e2 => LetE y (subst x v e1) (if bool_decide (x ≠ y) then subst x v e2 else e2)
  | Call f args => Call f (subst x v <$> args)
  | AllocA ls e => AllocA ls (subst x v e)
  | FreeA ls e => FreeA ls (subst x v e)
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
  | If e e1 e2 => If (subst_map x e) (subst_map x e1) (subst_map x e2)
  | LetE y e1 e2 => LetE y (subst_map x e1) (subst_map (delete y x) e2)
  | Call f args => Call f (subst_map x <$> args)
  | AllocA ls e => AllocA ls (subst_map x e)
  | FreeA ls e => FreeA ls (subst_map x e)
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

Lemma subst_map_subst x v e xs :
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

Lemma subst_map_subst_map e xs ys:
  subst_map (xs ∪ ys) e = subst_map ys (subst_map xs e).
Proof.
  revert e. induction xs using map_ind => e.
  { by rewrite left_id_L subst_map_empty. }
  rewrite -insert_union_l !subst_map_subst. naive_solver.
Qed.

Lemma subst_subst_map x v e xs :
  subst_map (xs ∪ <[x:=v]> ∅) e = subst x v (subst_map xs e).
Proof. by rewrite subst_map_subst_map subst_map_subst subst_map_empty. Qed.

Lemma subst_subst_map_delete x v e xs :
  subst_map (<[x:=v]> xs) e = subst x v (subst_map (delete x xs) e).
Proof.
  rewrite -subst_subst_map -insert_union_r; [|by simplify_map_eq].
  by rewrite right_id_L insert_delete_insert.
Qed.

Lemma subst_l_subst_map xs vs e :
  length xs = length vs →
  subst_l xs vs e = subst_map (list_to_map (zip xs vs)) e.
Proof.
  elim: xs vs e. { case => //=. move => ??. by rewrite subst_map_empty. }
  move => ?? IH [|??] //= e [?]. by rewrite subst_map_subst IH.
Qed.

(** ** Evaluation contexts *)
Inductive expr_ectx :=
| BinOpLCtx (op : binop) (e2 : expr)
| BinOpRCtx (v1 : val) (op : binop)
| LoadCtx
| StoreLCtx (e2 : expr)
| StoreRCtx (v1 : val)
| IfCtx (e2 e3 : expr)
| LetECtx (v : string) (e2 : expr)
| CallCtx (f : string) (vl : list val) (el : list expr)
| FreeACtx (ls : list (loc * Z))
| ReturnExtCtx (can_return_further : bool)
.

Definition expr_fill_item (Ki : expr_ectx) (e : expr) : expr :=
  match Ki with
  | BinOpLCtx op e2 => BinOp e op e2
  | BinOpRCtx v1 op => BinOp (Val v1) op e
  | LoadCtx => Load e
  | StoreLCtx e2 => Store e e2
  | StoreRCtx v1 => Store (Val v1) e
  | IfCtx e2 e3 => If e e2 e3
  | LetECtx v e2 => LetE v e e2
  | CallCtx f vl el => Call f ((Val <$> vl) ++ e :: el)
  | FreeACtx ls => FreeA ls e
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
  exploit list_expr_val_eq_inv; [| |done|]; naive_solver.
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

(** ** Static expressions *)
(** Static expressions correspond to the surface syntax of the language. *)
Fixpoint is_static_expr (allow_loc : bool) (e : expr) : bool :=
  match e with
  | Var v => true
  | Val v => allow_loc || (if v is ValLoc _ then false else true)
  | BinOp e1 o e2 => is_static_expr allow_loc e1 && is_static_expr allow_loc e2
  | Load e1 => is_static_expr allow_loc e1
  | Store e1 e2 => is_static_expr allow_loc e1 && is_static_expr allow_loc e2
  | If e e1 e2 => is_static_expr allow_loc e && is_static_expr allow_loc e1 && is_static_expr allow_loc e2
  | LetE v e1 e2 => is_static_expr allow_loc e1 && is_static_expr allow_loc e2
  | Call f args => forallb (is_static_expr allow_loc) args
  | AllocA _ e => allow_loc && is_static_expr allow_loc e
  | FreeA _ e => allow_loc && is_static_expr allow_loc e
  | ReturnExt can_return_further e => false
  | Waiting can_return => false
  end.

Lemma is_static_expr_forallb vs:
  forallb (is_static_expr true) (Val <$> vs).
Proof. by apply forallb_True, Forall_fmap, Forall_true. Qed.

Lemma is_static_expr_subst x v e:
  is_static_expr true e →
  is_static_expr true (subst x v e).
Proof.
  elim: e => //= *; try naive_solver.
  - by case_bool_decide.
  - case_bool_decide; naive_solver.
  - apply forallb_True, Forall_forall => ? /elem_of_list_fmap[?[??]]. subst.
    revert select (Forall _ _) => /Forall_forall.
    revert select (Is_true (forallb _ _)) => /forallb_True/Forall_forall. naive_solver.
Qed.

Lemma is_static_expr_subst_l xs vs e:
  is_static_expr true e →
  is_static_expr true (subst_l xs vs e).
Proof.
  elim: xs vs e. { by case. }
  move => ?? IH [//|??] /=??. apply IH.
  by apply is_static_expr_subst.
Qed.

Lemma is_static_expr_expr_fill bl K e:
  is_static_expr bl (expr_fill K e) ↔ is_static_expr bl (expr_fill K (Var "")) ∧ is_static_expr bl e.
Proof.
  elim/rev_ind: K e => /=. { naive_solver. }
  move => Ki K IH e. rewrite !expr_fill_app/=.
  destruct Ki => //=; rewrite ?forallb_app/=; naive_solver.
Qed.

Lemma is_static_expr_mono e:
  is_static_expr false e →
  is_static_expr true e.
Proof.
  elim: e => //=; try naive_solver.
  move => ?? IH /forallb_True.
  elim: IH => // *. decompose_Forall_hyps; naive_solver.
Qed.

(** ** fndef *)
Record fndef : Type := {
  fd_args : list string;
  fd_vars : list (string * Z);
  fd_body : expr;
  fd_static : is_static_expr false fd_body;
}.

Lemma fndef_eq fn1 fn2 :
  fn1 = fn2 ↔ fd_args fn1 = fd_args fn2 ∧ fd_vars fn1 = fd_vars fn2 ∧ fd_body fn1 = fd_body fn2.
Proof. split; [naive_solver|]. destruct fn1, fn2 => /= -[?[??]]. subst. f_equal. apply proof_irrel. Qed.

(** ** heap *)
Record heap_state : Set := Heap {
  h_heap : gmap loc val;
  h_provs : gset prov;
  heap_wf l : is_Some (h_heap !! l) → l.1 ∈ h_provs;
}.
Add Printing Constructor heap_state.

Lemma heap_state_eq h1 h2:
  h1 = h2 ↔ h1.(h_heap) = h2.(h_heap) ∧ h1.(h_provs) = h2.(h_provs).
Proof. split; [naive_solver|]. destruct h1, h2 => /= -[??]; subst. f_equal. apply AxProofIrrelevance. Qed.

Global Program Instance heap_empty : Empty heap_state :=
  Heap ∅ ∅ _.
Next Obligation. move => ?. rewrite lookup_empty => -[??]. done. Qed.

Definition h_block (h : heap_state) (p : prov) : gmap Z val :=
  gmap_curry (h_heap h) !!! p.

Lemma h_block_lookup h p z:
  h_block h p !! z = h_heap h !! (p, z).
Proof.
  rewrite /h_block -lookup_gmap_curry /=.
  apply option_eq => ?.
  rewrite bind_Some lookup_total_alt. simpl.
  destruct (gmap_curry (h_heap h) !! p); naive_solver.
Qed.

Definition zero_block (l: loc) (n: Z) : gmap Z val :=
  gmap_curry (list_to_map ((λ z : Z, (l +ₗ z, ValNum 0%Z)) <$> seqZ 0 n)) !!! l.1.

Lemma zero_block_lookup_Some l k i x:
  l.2 = 0%Z →
  zero_block l k !! i = Some x ↔ x = ValNum 0 ∧ (0 ≤ i < k)%Z.
Proof.
  move => Hl. rewrite /zero_block lookup_total_gmap_curry -elem_of_list_to_map.
  2: { eapply NoDup_fmap_fst; last first.
       { eapply NoDup_fmap_2, NoDup_seqZ.
         intros z1 z2; injection 1. lia. }
       intros ? y1 y2 [? []]%elem_of_list_fmap_2 [? []]%elem_of_list_fmap_2.
       by simplify_eq. }
  rewrite elem_of_list_fmap. setoid_rewrite elem_of_seqZ.
  destruct l; naive_solver lia.
Qed.

Lemma zero_block_insert_zero l (k: Z) i:
  l.2 = 0%Z →
  (0 ≤ i < k)%Z →
  <[i:=ValNum 0%Z]> (zero_block l k) = zero_block l k.
Proof.
  move => ??. apply map_eq => j.
  destruct (decide (i = j)); simplify_map_eq => //.
  symmetry. by apply zero_block_lookup_Some.
Qed.


Definition heap_alive (h : heap_state) (l : loc) : Prop :=
  is_Some (h.(h_heap) !! l).

Definition heap_range (h : heap_state) (l : loc) (a : Z) : Prop :=
  ∀ l', l'.1 = l.1 → is_Some (h.(h_heap) !! l') ↔ l.2 ≤ l'.2 < l.2 + a.

Definition heap_is_fresh (h : heap_state) (l : loc) : Prop :=
  l.1 ∉ h_provs h ∧ l.2 = 0.

Definition heap_fresh (ps : gset prov) (h : heap_state) : loc :=
  (fresh (ps ∪ h_provs h), 0).

Program Definition heap_update (h : heap_state) (l : loc) (v : val) : heap_state :=
  Heap (alter (λ _, v) l h.(h_heap)) h.(h_provs) _.
Next Obligation. move => ????. rewrite lookup_alter_is_Some. apply heap_wf. Qed.

Program Definition heap_update_big (h : heap_state) (m : gmap loc val) : heap_state :=
  Heap (map_union_weak m h.(h_heap)) (h.(h_provs)) _.
Next Obligation. move => ???. rewrite map_lookup_imap. move => [? /bind_Some[?[??]]]. by apply heap_wf. Qed.

Lemma heap_update_big_empty h :
  heap_update_big h ∅ = h.
Proof.
  apply heap_state_eq => /=. split!. etrans; [|apply map_imap_Some].
  apply map_imap_ext => ? /=. by rewrite lookup_empty.
Qed.

Lemma heap_update_big_update h l v m:
  heap_update_big (heap_update h l v) m = heap_update_big h (m ∪ (<[l := v]> $ ∅)).
Proof.
  apply heap_state_eq => /=. split!. apply map_eq => i. apply option_eq => v'. rewrite !map_lookup_imap.
  rewrite !bind_Some. setoid_rewrite lookup_alter_Some.
  split => ?; destruct!.
  - split!. destruct (m !! i) eqn:?.
    + by erewrite lookup_union_Some_l.
    + rewrite lookup_union_r //=. by simplify_map_eq.
  - split!. rewrite lookup_union_l' //. by simplify_map_eq.
  - destruct (decide (l = i)); subst; split!.
    + destruct (m !! i) eqn:?.
      * by erewrite lookup_union_Some_l.
      * rewrite lookup_union_r //=. by simplify_map_eq.
    + rewrite lookup_union_l' //. by simplify_map_eq.
Qed.


Definition heap_alloc_h (h : gmap loc val) (l : loc) (n : Z) : gmap loc val :=
  (list_to_map ((λ z, (l +ₗ z, ValNum 0)) <$> seqZ 0 n) ∪ h).

Lemma heap_alloc_h_lookup h n (l l' : loc):
  l.1 = l'.1 →
  l.2 ≤ l'.2 < l.2 + n →
  heap_alloc_h h l n !! l' = Some (ValNum 0).
Proof.
  destruct l as [p o], l' as [p' o'] => /=??; subst. apply lookup_union_Some_l.
  apply elem_of_list_to_map_1.
  { rewrite -list_fmap_compose. apply NoDup_fmap; [|apply NoDup_seqZ].
    move => ??/=. rewrite /offset_loc/= => ?. naive_solver lia. }
  apply elem_of_list_fmap. eexists (o' - o). rewrite elem_of_seqZ /offset_loc /=.
  split; [do 2 f_equal; lia | naive_solver lia].
Qed.
(* must be Opaque, otherwise simpl takes ages to figure out that it cannot reduce heap_alloc_h. *)
Global Opaque heap_alloc_h.


Program Definition heap_alloc (h : heap_state) (l : loc) (n : Z) : heap_state :=
  Heap (heap_alloc_h h.(h_heap) l n) ({[l.1]} ∪ h_provs h) _.
Next Obligation.
  move => ????. move => [? /lookup_union_Some_raw[Hl|[? Hh]]]; apply elem_of_union; [left|right; by apply heap_wf].
  move: Hl => /(elem_of_list_to_map_2 _ _ _)/elem_of_list_fmap. set_solver.
Qed.

Program Definition heap_free (h : heap_state) (l : loc) : heap_state :=
  Heap (filter (λ '(l', v), l'.1 ≠ l.1) h.(h_heap)) h.(h_provs) _.
Next Obligation. move => ???. rewrite map_filter_lookup => -[?/bind_Some[?[??]]]. by apply heap_wf. Qed.

Program Definition heap_merge (h1 h2 : heap_state) : heap_state :=
  Heap (h_heap h1 ∪ h_heap h2) (h_provs h1 ∪ h_provs h2) _.
Next Obligation. move => ???. move => /lookup_union_is_Some[/heap_wf?|/heap_wf?]; set_solver. Qed.

Program Definition heap_restrict (h : heap_state) (P : prov → Prop) `{!∀ x, Decision (P x)} : heap_state :=
  Heap (filter (λ x, P x.1.1) h.(h_heap)) h.(h_provs) _.
Next Obligation. move => ????. rewrite map_filter_lookup => -[?/bind_Some[?[??]]]. by apply heap_wf. Qed.

Program Definition heap_add_provs (h : heap_state) (p : gset prov) : heap_state :=
  Heap (h_heap h) (p ∪ h_provs h) _.
Next Obligation. move => ????. apply: union_subseteq_r. by apply heap_wf. Qed.

Fixpoint heap_fresh_list (xs : list Z) (ps : gset prov) (h : heap_state) : list loc :=
  match xs with
  | [] => []
  | x::xs' =>
      let l := heap_fresh ps h in
      l::heap_fresh_list xs' ps (heap_alloc h l x)
  end.

Fixpoint heap_alloc_list (xs : list Z) (ls : list loc) (h h' : heap_state) : Prop :=
  match xs with
  | [] => ls = [] ∧ h' = h
  | x::xs' => ∃ l ls', ls = l::ls' ∧ heap_is_fresh h l ∧ heap_alloc_list xs' ls' (heap_alloc h l x) h'
  end.

Fixpoint heap_free_list (xs : list (loc * Z)) (h h' : heap_state) : Prop :=
  match xs with
  | [] => h' = h
  | x::xs' => heap_range h x.1 x.2 ∧ heap_free_list xs' (heap_free h x.1) h'
  end.

Lemma heap_alloc_list_length xs ls h h' :
  heap_alloc_list xs ls h h' →
  length xs = length ls.
Proof. elim: xs ls h h'. { case; naive_solver. } move => /= ??? [|??] ??; naive_solver. Qed.

Lemma heap_alloc_list_offset_zero vs ls h1 h2 i l:
  heap_alloc_list vs ls h1 h2 →
  ls !! i = Some l →
  l.2 = 0%Z.
Proof.
  induction vs as [|v vs IHvs] in i, ls, h1, h2 |-*; destruct ls; simpl; try naive_solver.
  intros (? & ? & ? & Hf & ?) Hlook. simplify_eq.
  destruct i; last by eauto.
  injection Hlook as ->. by destruct Hf.
Qed.

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
Opaque heap_fresh.

Lemma heap_alloc_list_fresh xs ps h:
  ∃ h', heap_alloc_list xs (heap_fresh_list xs ps h) h h'.
Proof.
  elim: xs ps h. { case; naive_solver. }
  move => a ? IH //= ps h. exploit IH => -[??].
  split!; [|done]. by apply heap_fresh_is_fresh.
Qed.

Global Transparent heap_alloc_h. (* TODO: remove this *)
Lemma heap_alive_alloc h l l' n :
  l.1 = l'.1 →
  l'.2 ≤ l.2 < l'.2 + n →
  heap_alive (heap_alloc h l' n) l.
Proof.
  destruct l as [p o], l' as [p' o'].
  move => ??. simplify_eq/=. rewrite /heap_alive/=/heap_alloc_h/offset_loc/=.
  apply lookup_union_is_Some. left. apply list_to_map_lookup_is_Some.
  eexists 0. apply elem_of_list_fmap. eexists (o - o').
  split; [do 2 f_equal; lia|]. apply elem_of_seqZ. lia.
Qed.
Global Opaque heap_alloc_h.

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

Lemma h_block_heap_alloc h l n:
  heap_is_fresh h l →
  (h_block (heap_alloc h l n) l.1) = zero_block l n.
Proof.
  intros Hfresh.
  rewrite /h_block /heap_alloc /zero_block /=.
  eapply map_leibniz, map_equiv_iff; intros i.
  rewrite !lookup_total_gmap_curry.
  assert (h_heap h !! (l.1, i) = None) as Hlook.
  { rewrite /heap_is_fresh in Hfresh.
    destruct lookup eqn: Hlook; last done.
    destruct l; simpl in *.
    exfalso. eapply Hfresh, (heap_wf _ (p, i)); eauto.
  }
  rewrite lookup_union; rewrite Hlook; clear Hlook.
  destruct lookup; done.
Qed.

Lemma h_block_heap_update hs l v:
  h_block (heap_update hs l v) l.1 = alter (λ _, v) l.2 (h_block hs l.1).
Proof.
  rewrite /h_block/=. apply map_eq => i.
  rewrite !lookup_total_gmap_curry.
  destruct (decide (i = l.2)); simplify_map_eq.
  - rewrite lookup_total_gmap_curry -?surjective_pairing. by simplify_map_eq.
  - rewrite !lookup_alter_ne ?lookup_total_gmap_curry //. destruct l. naive_solver.
Qed.

(** *** heap_preserved *)
Definition heap_preserved (m : gmap prov (gmap Z val)) (h : heap_state) :=
  ∀ l h', m !! l.1 = Some h' → h.(h_heap) !! l = h' !! l.2.

Lemma heap_preserved_mono m1 m2 h:
  heap_preserved m1 h →
  m2 ⊆ m1 →
  heap_preserved m2 h.
Proof. unfold heap_preserved => Hp Hsub ???. apply: Hp. by eapply map_subseteq_spec. Qed.

Lemma heap_preserved_lookup_r m h h' l v:
  h_heap h !! l = v →
  heap_preserved m h →
  m !! l.1 = Some h' →
  h' !! l.2 = v.
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

Lemma heap_preserved_insert_const p m h:
  heap_preserved (delete p m) h →
  heap_preserved (<[p := h_block h p]> m) h.
Proof.
  move => Hp l f /= /lookup_insert_Some[[??]|[??]]; simplify_eq.
  - rewrite h_block_lookup. by destruct l.
  - apply: Hp => /=. rewrite lookup_delete_Some. done.
Qed.

(** ** state *)
Record rec_state := Rec {
  st_expr : expr;
  st_heap : heap_state;
  st_fns : gmap string fndef;
}.
Add Printing Constructor rec_state.

Definition rec_init (fns : gmap string fndef) : rec_state :=
  Rec (Waiting false) ∅ fns.

(** ** rec_event *)
Inductive rec_ev : Type :=
| ERCall (fn : string) (args: list val) (h : heap_state)
| ERReturn (ret: val) (h : heap_state).

Global Instance rec_ev_inhabited : Inhabited rec_ev := populate (ERReturn inhabitant ∅).

Definition rec_event := io_event rec_ev.

Definition vals_of_event (e : rec_ev) : list val :=
  match e with
  | ERCall f vs h => vs
  | ERReturn v h => [v]
  end.

Definition heap_of_event (e : rec_ev) : heap_state :=
  match e with
  | ERCall f vs h => h
  | ERReturn v h => h
  end.

Definition event_set_vals_heap (e : rec_ev) (vs : list val) (h : heap_state) : rec_ev :=
  match e with
  | ERCall f vs' h' => ERCall f vs h
  | ERReturn v' h' => ERReturn (vs !!! 0%nat) h
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

Global Instance event_set_vals_heap_split_assume_inj e : SplitAssumeInj2 (=) (=) (=) (event_set_vals_heap e).
Proof. done. Qed.

(** ** Operational semantics *)
Definition eval_binop (op : binop) (v1 v2 : val) : option val :=
  match op with
  | AddOp => z1 ← val_to_Z v1; z2 ← val_to_Z v2; Some (ValNum (z1 + z2))
  | OffsetOp => l ← val_to_loc v1; z ← val_to_Z v2; Some (ValLoc (l +ₗ z))
  | EqOp =>
      match v1 with
      | ValNum z1 => z2 ← val_to_Z v2; Some (ValBool (bool_decide (z1 = z2)))
      | ValBool b1 => b2 ← val_to_bool v2; Some (ValBool (bool_decide (b1 = b2)))
      | _ => None
      end
  | LeOp => z1 ← val_to_Z v1; z2 ← val_to_Z v2; Some (ValBool (bool_decide (z1 ≤ z2)))
  | LtOp => z1 ← val_to_Z v1; z2 ← val_to_Z v2; Some (ValBool (bool_decide (z1 < z2)))
  end.

Inductive head_step : rec_state → option rec_event → (rec_state → Prop) → Prop :=
| BinOpS v1 op v2 h fns:
  head_step (Rec (BinOp (Val v1) op (Val v2)) h fns) None (λ σ',
    ∃ v, eval_binop op v1 v2 = Some v ∧ σ' = Rec (Val v) h fns)
| LoadS v1 h fns:
  head_step (Rec (Load (Val v1)) h fns) None (λ σ',
    ∃ l v, v1 = ValLoc l ∧ h.(h_heap) !! l = Some v ∧ σ' = Rec (Val v) h fns)
| StoreS v1 v h fns:
  head_step (Rec (Store (Val v1) (Val v)) h fns) None (λ σ',
    ∃ l, v1 = ValLoc l ∧ heap_alive h l ∧ σ' = Rec (Val v) (heap_update h l v) fns)
| IfS v fns e1 e2 h:
  head_step (Rec (If (Val v) e1 e2) h fns) None (λ σ,
       ∃ b, val_to_bool v = Some b ∧ σ = Rec (if b then e1 else e2) h fns)
| LetS x v e fns h:
  head_step (Rec (LetE x (Val v) e) h fns) None (λ σ, σ = Rec (subst x v e) h fns)
| VarES fns h v: (* unbound variable *)
  head_step (Rec (Var v) h fns) None (λ σ, False)
| AllocAS h h' fns ls xs e:
  heap_alloc_list xs.*2 ls h h' →
  head_step (Rec (AllocA xs e) h fns) None (λ σ',
    Forall (λ x, 0 < x) xs.*2 ∧ σ' = Rec (FreeA (zip ls xs.*2) (subst_l xs.*1 (ValLoc <$> ls) e)) h' fns)
| FreeAS h fns ls v:
  head_step (Rec (FreeA ls (Val v)) h fns) None (λ σ',
    ∃ h', heap_free_list ls h h' ∧ σ' = Rec (Val v) h' fns)
| CallInternalS f fn fns vs h:
  fns !! f = Some fn →
  head_step (Rec (Call f (Val <$> vs)) h fns) None (λ σ,
   length vs = length fn.(fd_args) ∧
   σ = Rec (AllocA fn.(fd_vars) (subst_l fn.(fd_args) vs fn.(fd_body))) h fns)
| CallExternalS f fns vs h:
  fns !! f = None →
  head_step (Rec (Call f (Val <$> vs)) h fns) (Some (Outgoing, ERCall f vs h)) (λ σ, σ = Rec (Waiting true) h fns)
| ReturnS fns v b h:
  head_step (Rec (ReturnExt b (Val v)) h fns) (Some (Outgoing, ERReturn v h)) (λ σ, σ = (Rec (Waiting b) h fns))
| RecvCallS fns f fn vs b h h':
  fns !! f = Some fn →
  head_step (Rec (Waiting b) h fns) (Some (Incoming, ERCall f vs h')) (λ σ,
    σ = (Rec (ReturnExt b (Call f (Val <$> vs))) h' fns))
| RecvReturnS fns v h h':
  head_step (Rec (Waiting true) h fns) (Some (Incoming, ERReturn v h')) (λ σ, σ = (Rec (Val v) h' fns))
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

Lemma val_head_stuck e1 h σ1 κ Pσ : head_step (Rec e1 h σ1) κ Pσ → to_val e1 = None.
Proof. by inversion 1. Qed.

Lemma head_ctx_step_val Ki e h σ1 κ Pσ :
  head_step (Rec (expr_fill_item Ki e) h σ1) κ Pσ → is_Some (to_val e).
Proof. destruct Ki; inversion 1; simplify_eq => //; by apply: list_expr_val_inv. Qed.

Lemma head_fill_step_val K e h σ1 κ Pσ :
  to_val e = None →
  head_step (Rec (expr_fill K e) h σ1) κ Pσ →
  K = [].
Proof.
  elim/rev_ind: K => //=????. rewrite expr_fill_app /= => /head_ctx_step_val /fill_val[??].
  naive_solver.
Qed.

Lemma step_by_val K K' e1' e1_redex h σ1 κ Pσ :
  expr_fill K e1' = expr_fill K' e1_redex →
  to_val e1' = None →
  head_step (Rec e1_redex h σ1) κ Pσ →
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

Inductive prim_step : rec_state → option rec_event → (rec_state → Prop) → Prop :=
  Ectx_step K e e' fns κ Pσ h:
    e = expr_fill K e' →
    head_step (Rec e' h fns) κ Pσ →
    prim_step (Rec e h fns) κ (λ σ, ∃ e2 h2 fns2, Pσ (Rec e2 h2 fns2) ∧ σ = Rec (expr_fill K e2) h2 fns2).

Lemma prim_step_inv K e fns κ h Pσ:
  prim_step (Rec (expr_fill K e) h fns) κ Pσ →
  to_val e = None →
  ∃ K' e' Pσ', e = expr_fill K' e' ∧ head_step (Rec e' h fns) κ Pσ' ∧
      Pσ = (λ σ, ∃ e2 h2 fns2, Pσ' (Rec e2 h2 fns2) ∧ σ = Rec (expr_fill (K' ++ K) e2) h2 fns2).
Proof.
  inversion 1; simplify_eq => ?.
  revert select (expr_fill _ _ = expr_fill _ _) => Heq. move: (Heq) => /step_by_val Hg.
  have [//|? ?]:= Hg _ _ _ _ _ ltac:(done). subst.
  rewrite expr_fill_app in Heq. naive_solver.
Qed.

Lemma prim_step_inv_head K e fns h κ Pσ:
  prim_step (Rec (expr_fill K e) h fns) κ Pσ →
  sub_redexes_are_values e →
  to_val e = None →
  ∃ Pσ', head_step (Rec e h fns) κ Pσ' ∧
      Pσ = (λ σ, ∃ e2 h2 fns2, Pσ' (Rec e2 h2 fns2) ∧ σ = Rec (expr_fill K e2) h2 fns2).
Proof.
  move => Hprim Hsub ?.
  move: Hprim => /prim_step_inv[|?[?[?[?[Hstep ?]]]]]. { done. } subst.
  have ->:= Hsub _ _ ltac:(done). 2: { by apply: val_head_stuck. }
  naive_solver.
Qed.

Definition rec_trans := ModTrans prim_step.
Definition rec_mod (fns : gmap string fndef) := Mod rec_trans (rec_init fns).

Global Instance rec_vis_no_all: VisNoAng rec_trans.
Proof. move => *. inv_all @m_step; inv_all head_step; naive_solver. Qed.

(** * Deeply embedded static expressions  *)
Inductive static_val := | StaticValNum (z : Z) | StaticValBool (b : bool).
Global Instance static_val_eqdec : EqDecision static_val.
Proof. solve_decision. Qed.

Definition static_val_to_val (v : static_val) : val :=
  match v with
  | StaticValNum z => ValNum z
  | StaticValBool b => ValBool b
  end.

Definition val_to_static_val (v : val) : static_val :=
  match v with
  | ValNum z => StaticValNum z
  | ValBool b => StaticValBool b
  | ValLoc _ => StaticValNum 0
  end.

Section static_expr.
Local Unset Elimination Schemes.
Inductive static_expr : Set :=
| SVar (v : string)
| SVal (v : static_val)
| SBinOp (e1 : static_expr) (o : binop) (e2 : static_expr)
| SLoad (e : static_expr)
| SStore (e1 e2 : static_expr)
| SIf (e e1 e2 : static_expr)
| SLetE (v : string) (e1 e2 : static_expr)
| SCall (f : string) (args : list static_expr)
.
End static_expr.
Lemma static_expr_ind (P : static_expr → Prop) :
  (∀ (x : string), P (SVar x)) →
  (∀ (v : static_val), P (SVal v)) →
  (∀ (e1 : static_expr) (op : binop) (e2 : static_expr), P e1 → P e2 → P (SBinOp e1 op e2)) →
  (∀ (e : static_expr), P e → P (SLoad e)) →
  (∀ (e1 e2 : static_expr), P e1 → P e2 → P (SStore e1 e2)) →
  (∀ (e1 e2 e3 : static_expr), P e1 → P e2 → P e3 → P (SIf e1 e2 e3)) →
  (∀ (v : string) (e1 e2 : static_expr), P e1 → P e2 → P (SLetE v e1 e2)) →
  (∀ (f : string) (args : list static_expr), Forall P args → P (SCall f args)) →
  ∀ (e : static_expr), P e.
Proof.
  move => *. generalize dependent P => P. match goal with | e : static_expr |- _ => revert e end.
  fix FIX 1. move => [ ^e] => ??????? Hcall.
  8: { apply Hcall. apply Forall_true => ?. by apply: FIX. }
  all: auto.
Qed.

Fixpoint static_expr_to_expr (e : static_expr) : expr :=
  match e with
  | SVar v => Var v
  | SVal v => Val (static_val_to_val v)
  | SBinOp e1 o e2 => BinOp (static_expr_to_expr e1) o (static_expr_to_expr e2)
  | SLoad e => Load (static_expr_to_expr e)
  | SStore e1 e2 => Store (static_expr_to_expr e1) (static_expr_to_expr e2)
  | SIf e e1 e2 => If (static_expr_to_expr e) (static_expr_to_expr e1) (static_expr_to_expr e2)
  | SLetE v e1 e2 => LetE v (static_expr_to_expr e1) (static_expr_to_expr e2)
  | SCall f args => Call f (static_expr_to_expr <$> args)
  end.

Lemma static_expr_is_static e :
  is_static_expr false (static_expr_to_expr e).
Proof.
  elim: e => //=; try naive_solver.
  - by case.
  - move => _ ?. elim => //=. naive_solver.
Qed.

Fixpoint expr_to_static_expr (e : expr) : static_expr :=
  match e with
  | Var v => SVar v
  | Val v => SVal (val_to_static_val v)
  | BinOp e1 o e2 => SBinOp (expr_to_static_expr e1) o (expr_to_static_expr e2)
  | Load e => SLoad (expr_to_static_expr e)
  | Store e1 e2 => SStore (expr_to_static_expr e1) (expr_to_static_expr e2)
  | If e e1 e2 => SIf (expr_to_static_expr e) (expr_to_static_expr e1) (expr_to_static_expr e2)
  | LetE v e1 e2 => SLetE v (expr_to_static_expr e1) (expr_to_static_expr e2)
  | Call f args => SCall f (expr_to_static_expr <$> args)
  | _ => SVar ""
  end.

Lemma static_expr_to_expr_to_static_expr e :
  is_static_expr false e →
  static_expr_to_expr (expr_to_static_expr e) = e.
Proof.
  elim: e => //=; try (move => *; f_equal; naive_solver).
  - by case.
  - move => f args Hall Hargs. f_equal.
    elim: Hall Hargs => // ??; csimpl => *. f_equal; naive_solver.
Qed.

Record static_fndef : Type := {
  sfd_args : list string;
  sfd_vars : list (string * Z);
  sfd_body : static_expr;
}.

Program Definition static_fndef_to_fndef (fn : static_fndef) : fndef := {|
   fd_args := fn.(sfd_args);
   fd_vars := fn.(sfd_vars);
   fd_body := static_expr_to_expr fn.(sfd_body);
|}.
Next Obligation. move => ?. apply static_expr_is_static. Qed.

Definition fndef_to_static_fndef (fn : fndef) : static_fndef := {|
   sfd_args := fn.(fd_args);
   sfd_vars := fn.(fd_vars);
   sfd_body := expr_to_static_expr fn.(fd_body);
|}.

Definition rec_static_init (fns : gmap string static_fndef) : rec_state :=
  rec_init (static_fndef_to_fndef <$> fns).

Definition rec_static_mod (fns : gmap string static_fndef) := Mod rec_trans (rec_static_init fns).

Lemma static_fndef_to_fndef_to_static_fndef fn :
  static_fndef_to_fndef (fndef_to_static_fndef fn) = fn.
Proof. apply fndef_eq. split_and!; [done..|] => /=. apply static_expr_to_expr_to_static_expr. apply fd_static. Qed.

(** * tstep *)
(** ** AsVals *)
Class AsVals (es : list expr) (vs : list val) (es' : option (expr * list expr)) := {
  as_vals : es = (Val <$> vs) ++ from_option (λ '(e, es), e :: es) [] es'
}.
Global Hint Mode AsVals ! - ! : typeclass_instances.

Lemma as_vals_nil :
  AsVals [] [] None.
Proof. done. Qed.
Global Hint Resolve as_vals_nil : typeclass_instances.

Lemma as_vals_cons v es vs es' :
  AsVals es vs es' → AsVals (Val v :: es) (v :: vs) es'.
Proof. move => [->]. done. Qed.
Global Hint Resolve as_vals_cons : typeclass_instances.

Lemma as_vals_expr_cons e es:
  AsVals (e :: es) [] (Some (e, es)).
Proof. done. Qed.
Global Hint Resolve as_vals_expr_cons | 50 : typeclass_instances.

Lemma as_vals_fmap vs :
  AsVals (Val <$> vs) vs None.
Proof. constructor. rewrite right_id_L. done. Qed.
Global Hint Resolve as_vals_fmap : typeclass_instances.


(** ** RecExprFill *)
Class RecExprFill (e : expr) (K : list expr_ectx) (e' : expr) := {
    rec_expr_fill_proof : e = expr_fill K e'
}.
Global Hint Mode RecExprFill ! - - : typeclass_instances.

Lemma rec_expr_fill_end e :
  RecExprFill e [] e.
Proof. done. Qed.
Global Hint Resolve rec_expr_fill_end | 100 : typeclass_instances.

Lemma rec_expr_fill_expr_fill e K K' e' `{!RecExprFill e K' e'} :
  RecExprFill (expr_fill K e) (K' ++ K) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply rec_expr_fill_proof. Qed.
Global Hint Resolve rec_expr_fill_expr_fill : typeclass_instances.

Lemma rec_expr_fill_BinOpL e1 e2 op K e' `{!RecExprFill e1 K e'} :
  RecExprFill (BinOp e1 op e2) (K ++ [BinOpLCtx op e2]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply rec_expr_fill_proof. Qed.
Global Hint Resolve rec_expr_fill_BinOpL : typeclass_instances.

Lemma rec_expr_fill_BinOpR (v1 : val) e2 op K e' `{!RecExprFill e2 K e'} :
  RecExprFill (BinOp (Val v1) op e2) (K ++ [BinOpRCtx v1 op]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply rec_expr_fill_proof. Qed.
Global Hint Resolve rec_expr_fill_BinOpR : typeclass_instances.

Lemma rec_expr_fill_Load e1 K e' `{!RecExprFill e1 K e'} :
  RecExprFill (Load e1) (K ++ [LoadCtx]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply rec_expr_fill_proof. Qed.
Global Hint Resolve rec_expr_fill_Load : typeclass_instances.

Lemma rec_expr_fill_StoreL e1 e2 K e' `{!RecExprFill e1 K e'} :
  RecExprFill (Store e1 e2) (K ++ [StoreLCtx e2]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply rec_expr_fill_proof. Qed.
Global Hint Resolve rec_expr_fill_StoreL : typeclass_instances.

Lemma rec_expr_fill_StoreR (v1 : val) e2 K e' `{!RecExprFill e2 K e'} :
  RecExprFill (Store (Val v1) e2) (K ++ [StoreRCtx v1]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply rec_expr_fill_proof. Qed.
Global Hint Resolve rec_expr_fill_StoreR : typeclass_instances.

Lemma rec_expr_fill_FreeA e1 K e' ls `{!RecExprFill e1 K e'} :
  RecExprFill (FreeA ls e1) (K ++ [FreeACtx ls]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply rec_expr_fill_proof. Qed.
Global Hint Resolve rec_expr_fill_FreeA : typeclass_instances.

Lemma rec_expr_fill_If e e2 e3 K e' `{!RecExprFill e K e'} :
  RecExprFill (If e e2 e3) (K ++ [IfCtx e2 e3]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply rec_expr_fill_proof. Qed.
Global Hint Resolve rec_expr_fill_If : typeclass_instances.

Lemma rec_expr_fill_LetE v e1 e2 K e' `{!RecExprFill e1 K e'} :
  RecExprFill (LetE v e1 e2) (K ++ [LetECtx v e2]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply rec_expr_fill_proof. Qed.
Global Hint Resolve rec_expr_fill_LetE : typeclass_instances.

Lemma rec_expr_fill_Call e K e' f es vs es' `{!AsVals es vs (Some (e, es')) } `{!RecExprFill e K e'} :
  RecExprFill (Call f es) (K ++ [CallCtx f vs es']) e'.
Proof.
  destruct AsVals0, RecExprFill0. subst.
  constructor => /=. rewrite expr_fill_app /=. done.
Qed.
Global Hint Resolve rec_expr_fill_Call : typeclass_instances.

Lemma rec_expr_fill_ReturnExt b e K e' `{!RecExprFill e K e'} :
  RecExprFill (ReturnExt b e) (K ++ [ReturnExtCtx b]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply rec_expr_fill_proof. Qed.
Global Hint Resolve rec_expr_fill_ReturnExt : typeclass_instances.

(** ** instances *)
(* This pattern of using RecExprFill at each rule is quite expensive
but we don't care at the moment. *)
Lemma rec_step_Var_s fns h e K v `{!RecExprFill e K (Var v)}:
  TStepS rec_trans (Rec e h fns) (λ G, G None (λ G', True)).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. eexists _, _. split; [done|] => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?. naive_solver.
Qed.
Global Hint Resolve rec_step_Var_s : typeclass_instances.

Lemma rec_step_Waiting_i fns h K e b `{!RecExprFill e K (Waiting b)}:
  TStepI rec_trans (Rec e h fns) (λ G,
    (∀ f fn vs h', fns !! f = Some fn →
      G true (Some (Incoming, ERCall f vs h')) (λ G',  G'
          (Rec (expr_fill K (ReturnExt b (Call f (Val <$> vs)))) h' fns))) ∧
    ∀ v h', b → G true (Some (Incoming, ERReturn v h')) (λ G', G' (Rec (expr_fill K (Val v)) h' fns))
   ).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  - naive_solver.
  - naive_solver.
Qed.
Global Hint Resolve rec_step_Waiting_i : typeclass_instances.

Lemma rec_step_Waiting_s fns h e K b `{!RecExprFill e K (Waiting b)}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (∃ f fn vs h', fns !! f = Some fn ∧
      G (Some (Incoming, ERCall f vs h')) (λ G', G'
          (Rec (expr_fill K (ReturnExt b (Call f (Val <$> vs)))) h' fns))) ∨
    ∃ v h', b ∧ G (Some (Incoming, ERReturn v h')) (λ G', G' (Rec (expr_fill K (Val v)) h' fns))
   ).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. destruct!; (split!; [done|]) => /= ??. 2: destruct b => //.
  all: apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?; destruct!; done.
Qed.
Global Hint Resolve rec_step_Waiting_s : typeclass_instances.

Lemma rec_step_ReturnExt_i fns h e K b (v : val) `{!RecExprFill e K (ReturnExt b (Val v))}:
  TStepI rec_trans (Rec e h fns) (λ G,
    (G true (Some (Outgoing, ERReturn v h)) (λ G', G' (Rec (expr_fill K (Waiting b)) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  naive_solver.
Qed.
Global Hint Resolve rec_step_ReturnExt_i : typeclass_instances.

Lemma rec_step_ReturnExt_s fns h e K b (v : val) `{!RecExprFill e K (ReturnExt b (Val v))}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (G (Some (Outgoing, ERReturn v h)) (λ G', G' (Rec (expr_fill K (Waiting b)) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct!. done.
Qed.
Global Hint Resolve rec_step_ReturnExt_s : typeclass_instances.

Lemma rec_step_Call_i fns h e K f vs es `{!RecExprFill e K (rec.Call f es)} `{!AsVals es vs None}:
  TStepI rec_trans (Rec e h fns) (λ G,
    (∀ fn, fns !! f = Some fn → G true None (λ G', length vs = length fn.(fd_args) ∧
         G' (Rec (expr_fill K (AllocA fn.(fd_vars) (subst_l fn.(fd_args) vs fn.(fd_body)))) h fns))) ∧
    (fns !! f = None → G true (Some (Outgoing, ERCall f vs h)) (λ G',
           G' (Rec (expr_fill K (Waiting true)) h fns)))).
Proof.
  destruct AsVals0, RecExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[Hstep ?]]. {
    apply sub_redexes_are_values_item; case; try naive_solver.
    move => /= ??? e' [_ Heq]. rewrite right_id_L in Heq. by apply: list_expr_val_inv.
  } { done. } subst.
  rewrite right_id_L in Hstep. inv Hstep.
  - naive_solver.
  - naive_solver.
Qed.
Global Hint Resolve rec_step_Call_i : typeclass_instances.

Lemma rec_step_Call_s fns h e K f vs `{!RecExprFill e K (rec.Call f es)} `{!AsVals es vs None}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (∃ fn, fns !! f = Some fn ∧ G None (λ G', length vs = length fn.(fd_args) → G'
             (Rec (expr_fill K (AllocA fn.(fd_vars) (subst_l fn.(fd_args) vs fn.(fd_body)))) h fns))) ∨
    (fns !! f = None ∧ G (Some (Outgoing, ERCall f vs h)) (λ G',
           G' (Rec (expr_fill K (Waiting true)) h fns)))).
Proof.
  destruct AsVals0, RecExprFill0; subst. rewrite right_id_L.
  constructor => ? HG. destruct!; (split!; [done|]); move => /= ??.
  all: apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  all: destruct!; naive_solver.
Qed.
Global Hint Resolve rec_step_Call_s : typeclass_instances.

Lemma rec_step_Binop_i fns h e K (v1 v2 : val) op `{!RecExprFill e K (BinOp (Val v1) op (Val v2))}:
  TStepI rec_trans (Rec e h fns) (λ G,
    (G true None (λ G', ∃ v', eval_binop op v1 v2 = Some v' ∧ G' (Rec (expr_fill K (Val v')) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  naive_solver.
Qed.
Global Hint Resolve rec_step_Binop_i | 10 : typeclass_instances.

Lemma rec_step_Binop_s fns h e K (v1 v2 : val) op `{!RecExprFill e K (BinOp (Val v1) op (Val v2))}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (G None (λ G', ∀ v', eval_binop op v1 v2 = Some v' → G' (Rec (expr_fill K (Val v')) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct!. naive_solver.
Qed.
Global Hint Resolve rec_step_Binop_s | 10 : typeclass_instances.

Lemma rec_step_BinopAdd_i fns h e K n1 n2 `{!RecExprFill e K (BinOp (Val (ValNum n1)) AddOp (Val (ValNum n2)))}:
  TStepI rec_trans (Rec e h fns) (λ G,
    (G true None (λ G', G' (Rec (expr_fill K (Val (ValNum (n1 + n2)))) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. tstep_i => ???. split! => ?. naive_solver.
Qed.
Global Hint Resolve rec_step_BinopAdd_i | 5 : typeclass_instances.

Lemma rec_step_BinopAdd_s fns h e K (v1 v2 : val) `{!RecExprFill e K (BinOp (Val v1) AddOp (Val v2))}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (G None (λ G', ∀ n1 n2, v1 = ValNum n1 → v2 = ValNum n2 → G' (Rec (expr_fill K (Val (ValNum (n1 + n2)))) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??. tstep_s. split! => ? /bind_Some[?[? /bind_Some[?[??]]]].
  destruct v1, v2 => //. simplify_eq/=. naive_solver.
Qed.
Global Hint Resolve rec_step_BinopAdd_s | 5 : typeclass_instances.

Lemma rec_step_BinopOffset_i fns h e K l z `{!RecExprFill e K (BinOp (Val (ValLoc l)) OffsetOp (Val (ValNum z)))}:
  TStepI rec_trans (Rec e h fns) (λ G,
    (G true None (λ G', G' (Rec (expr_fill K (Val (ValLoc (l +ₗ z)))) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. tstep_i => ???. split! => ?. naive_solver.
Qed.
Global Hint Resolve rec_step_BinopOffset_i | 5 : typeclass_instances.

Lemma rec_step_BinopOffset_s fns h e K (v1 v2 : val) `{!RecExprFill e K (BinOp (Val v1) OffsetOp (Val v2))}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (G None (λ G', ∀ l z, v1 = ValLoc l → v2 = ValNum z → G' (Rec (expr_fill K (Val (ValLoc (l +ₗ z)))) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??. tstep_s. split! => ? /bind_Some[?[? /bind_Some[?[??]]]].
  destruct v1, v2 => //. simplify_eq/=. naive_solver.
Qed.
Global Hint Resolve rec_step_BinopOffset_s | 5 : typeclass_instances.

Lemma rec_step_Load_i fns h e K l `{!RecExprFill e K (Load (Val (ValLoc l)))}:
  TStepI rec_trans (Rec e h fns) (λ G,
    (G true None (λ G', ∃ v', h.(h_heap) !! l = Some v' ∧ G' (Rec (expr_fill K (Val v')) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  naive_solver.
Qed.
Global Hint Resolve rec_step_Load_i : typeclass_instances.

Lemma rec_step_Load_s fns h e K v `{!RecExprFill e K (Load (Val v))}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (G None (λ G', ∀ l v', v = ValLoc l → h.(h_heap) !! l = Some v' → G' (Rec (expr_fill K (Val v')) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct!. naive_solver.
Qed.
Global Hint Resolve rec_step_Load_s : typeclass_instances.

Lemma rec_step_Store_i fns h e K l v `{!RecExprFill e K (Store (Val (ValLoc l)) (Val v))}:
  TStepI rec_trans (Rec e h fns) (λ G,
    (G true None (λ G', heap_alive h l ∧ G' (Rec (expr_fill K (Val v)) (heap_update h l v) fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  naive_solver.
Qed.
Global Hint Resolve rec_step_Store_i : typeclass_instances.

Lemma rec_step_Store_s fns h e K v1 v `{!RecExprFill e K (Store (Val v1) (Val v))}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (G None (λ G', ∀ l, v1 = ValLoc l → heap_alive h l → G'
      (Rec (expr_fill K (Val v)) (heap_update h l v) fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct!. naive_solver.
Qed.
Global Hint Resolve rec_step_Store_s : typeclass_instances.

Lemma rec_step_AllocA_i fns h e K e' vs `{!RecExprFill e K (AllocA vs e')}:
  TStepI rec_trans (Rec e h fns) (λ G, ∀ ls h', heap_alloc_list vs.*2 ls h h' →
    (G true None (λ G', Forall (λ z, 0 < z) vs.*2 ∧
           G' (Rec (expr_fill K (FreeA (zip ls vs.*2) (subst_l vs.*1 (ValLoc <$> ls) e'))) h' fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  naive_solver.
Qed.
Global Hint Resolve rec_step_AllocA_i : typeclass_instances.

Lemma rec_step_Alloc_s fns h e e' K vs `{!RecExprFill e K (AllocA vs e')}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (G None (λ G', ∃ ls h', heap_alloc_list vs.*2 ls h h' ∧
      (Forall (λ z, 0 < z) vs.*2 → G' (Rec (expr_fill K (FreeA (zip ls vs.*2) (subst_l vs.*1 (ValLoc <$> ls) e'))) h' fns))))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ?[?[?[??]]].
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct!. naive_solver.
Qed.
Global Hint Resolve rec_step_Alloc_s : typeclass_instances.

Lemma rec_step_FreeA_i fns h e K v ls `{!RecExprFill e K (FreeA ls (Val v))}:
  TStepI rec_trans (Rec e h fns) (λ G,
    (G true None (λ G', ∃ h', heap_free_list ls h h' ∧ G' (Rec (expr_fill K (Val v)) h' fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  naive_solver.
Qed.
Global Hint Resolve rec_step_FreeA_i : typeclass_instances.

Lemma rec_step_FreeA_s fns h e K ls v `{!RecExprFill e K (FreeA ls (Val v))}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (G None (λ G', ∀ h', heap_free_list ls h h' → G' (Rec (expr_fill K (Val v)) h' fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct!. naive_solver.
Qed.
Global Hint Resolve rec_step_FreeA_s : typeclass_instances.

Lemma rec_step_LetE_i fns h e K x v e1 `{!RecExprFill e K (LetE x (Val v) e1)}:
  TStepI rec_trans (Rec e h fns) (λ G,
    (G true None (λ G', G' (Rec (expr_fill K (subst x v e1)) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  naive_solver.
Qed.
Global Hint Resolve rec_step_LetE_i : typeclass_instances.

Lemma rec_step_LetE_s fns h e K x v e1 `{!RecExprFill e K (LetE x (Val v) e1)}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (G None (λ G', G' (Rec (expr_fill K (subst x v e1)) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct!. naive_solver.
Qed.
Global Hint Resolve rec_step_LetE_s : typeclass_instances.

Lemma rec_step_If_i fns h b K e1 e2 `{!RecExprFill e K (If (Val (ValBool b)) e1 e2)}:
  TStepI rec_trans (Rec e h fns) (λ G,
    (G true None (λ G', G' (Rec (expr_fill K (if b then e1 else e2)) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  naive_solver.
Qed.
Global Hint Resolve rec_step_If_i | 10 : typeclass_instances.

Lemma rec_step_If_s fns h v K e1 e2 `{!RecExprFill e K (If (Val v) e1 e2)}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (G None (λ G', ∀ b, v = ValBool b → G' (Rec (expr_fill K (if b then e1 else e2)) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct!. destruct v => //. naive_solver.
Qed.
Global Hint Resolve rec_step_If_s | 10 : typeclass_instances.

(** * Proof techniques *)
Definition rec_proof_call (n : trace_index) (fns1 fns2 : gmap string fndef) :=
  (∀ n' f es1' es2' K1' K2' es1 es2 vs1' vs2' h1' h2' b,
      RecExprFill es1' K1' (Call f es1) →
      RecExprFill es2' K2' (Call f es2) →
      n' ⊆ n →
      Forall2 (λ e v, e = Val v) es1 vs1' →
      Forall2 (λ e v, e = Val v) es2 vs2' →
      vs1' = vs2' →
      h1' = h2' →
      (∀ v'' h'',
          Rec (expr_fill K1' (Val v'')) h'' fns1
              (* TODO: it possible to make it b instead of false? *)
              ⪯{rec_trans, rec_trans, n', false}
              Rec (expr_fill K2' (Val v'')) h'' fns2) →
      Rec es1' h1' fns1
          ⪯{rec_trans, rec_trans, n', b}
      Rec es2' h2' fns2).

Lemma rec_proof fns1 fns2:
  (∀ f, fns1 !! f = None ↔ fns2 !! f = None) →
  (∀ n K1 K2 f fn1 vs h,
      fns1 !! f = Some fn1 →
      ∃ fn2, fns2 !! f = Some fn2 ∧ length (fd_args fn1) = length (fd_args fn2) ∧ (
        length vs = length (fd_args fn1) →
      (* Call *)
      rec_proof_call n fns1 fns2 →
      (* Return *)
      (∀ n' v1' v2' h1' h2' b,
         n' ⊆ n →
         v1' = v2' →
         h1' = h2' →
         Rec (expr_fill K1 (Val v1')) h1' fns1
             ⪯{rec_trans, rec_trans, n', b}
         Rec (expr_fill K2 (Val v2')) h2' fns2) →

       Rec (expr_fill K1 (AllocA fn1.(fd_vars) $ subst_l fn1.(fd_args) vs (fd_body fn1))) h fns1
           ⪯{rec_trans, rec_trans, n, false}
       Rec (expr_fill K2 (AllocA fn2.(fd_vars) $ subst_l fn2.(fd_args) vs (fd_body fn2))) h fns2)) →

  trefines (rec_mod fns1) (rec_mod fns2).
Proof.
  move => Hf Hc.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember. { simpl. exact (λ n' '(Rec e1 h1 fns1') '(Rec e2 h2 fns2'),
     ∃ K1 K2 b,
       fns1' = fns1 ∧
       fns2' = fns2 ∧
       h1 = h2 ∧
       e1 = expr_fill K1 (Waiting b) ∧
       e2 = expr_fill K2 (Waiting b) ∧
       ∀ v' h',
         b →
         Rec (expr_fill K1 (Val v')) h' fns1
             ⪯{rec_trans, rec_trans, n', false}
         Rec (expr_fill K2 (Val v')) h' fns2

  ). } { eexists [], []. split!. }
  { move => /= ?? [???] [???] *. destruct!. split!; [done..|].
    move => ???. apply: tsim_mono; [naive_solver|done]. }
  move => /= n1 ? IH [???] [???] ?. destruct!.
  tstep_both. split!.
  2: { move => *. tstep_s. right. split!; [done|]. tend. apply: tsim_mono_b. naive_solver. }
  move => f fn1 vs h ?.
  have [fn2 ?] : is_Some (fns2 !! f). { apply not_eq_None_Some. naive_solver. }
  tstep_s. left. split!; [done..|]. tstep_s. left. split!. move => ?. tend.
  have ? : length (fd_args fn1) = length (fd_args fn2).
  { move: (Hc n0 [] [] f fn1 [] h). naive_solver. }
  tstep_i. split!; [|naive_solver]. move => ??. simplify_eq/=. split; [congruence|].
  unshelve eapply tsim_remember. { simpl. exact (λ n' '(Rec e1 h1 fns1') '(Rec e2 h2 fns2'),
     ∃ K1 K2 f vs fn1 fn2,
       fns1' = fns1 ∧
       fns2' = fns2 ∧
       h1 = h2 ∧
       fns1 !! f = Some fn1 ∧
       fns2 !! f = Some fn2 ∧
       e1 = expr_fill K1 (AllocA fn1.(fd_vars) $ subst_l (fd_args fn1) vs (fd_body fn1)) ∧
       e2 = expr_fill K2 (AllocA fn2.(fd_vars) $ subst_l (fd_args fn2) vs (fd_body fn2)) ∧
       length vs = length (fd_args fn1) ∧
       ∀ v' h',
         Rec (expr_fill K1 (Val v')) h' fns1
             ⪯{rec_trans, rec_trans, n', false}
         Rec (expr_fill K2 (Val v')) h' fns2

  ). }
  { eexists (ReturnExtCtx _ :: _), (ReturnExtCtx _ :: _). split!; [try done; congruence..|].
    move => ??. tstep_both. tstep_s. split!; [done|]. tend.
    apply IH; [done|]. by split!. }
  { move => /= ?? [???] [???] *. destruct!. split!; [done..|].
    move => ??. apply: tsim_mono; [naive_solver|]. by apply ti_lt_impl_le. }
  move => n2 ? IH2 [???] [???] ?. destruct!.
  exploit Hc; [done|]. move => [?[?[?]]]. simplify_eq.
  apply; [lia|..].
  - move => n' f' ?? ?? es1 es2 vs1' vs2' ??? [?][?] ? Hall1 Hall2 ???.
    have ?: es1 = Val <$> vs1'. { clear -Hall1. elim: Hall1; naive_solver. } subst.
    have ?: es2 = Val <$> vs2'. { clear -Hall2. elim: Hall2; naive_solver. } subst.
    tstep_both. split.
    + move => fn1' ?. tstep_s. left.
      have [fn2' ?] : is_Some (fns2 !! f'). { apply not_eq_None_Some. naive_solver. }
      have ? : length (fd_args fn1') = length (fd_args fn2').
      { move: (Hc n0 [] [] f' fn1' [] h). naive_solver. }
      split! => ?. tend. split; [lia|].
      apply IH2; [done|]. split!; [done..|lia|done].
    + move => ?. tstep_s. right. split!; [naive_solver|done|]. tend.
      apply IH; [etrans; [done|]; etrans; [|done]; apply ti_le_S|]. split!; [done..|].
      naive_solver.
  - move => *. subst. apply: tsim_mono; [|done]. apply tsim_mono_b_false. naive_solver.
Qed.

Lemma rec_prepost_proof {S} {M : ucmra} R `{!∀ b, PreOrder (R b)} i o fns1 fns2 (s0 : S) (r0 : uPred M):
  (* R true: public transition relation, R false: private transition relation *)
  (∀ s r s' r', R true (s, r) (s', r') → R false (s, r) (s', r')) →
  (∀ n K1 K2 f fn1 vs1 h1 s1 r1,
      R false (s0, r0) (s1, r1) →
      fns1 !! f = Some fn1 →
      pp_to_all (i (Incoming, ERCall f vs1 h1) s1) (λ '(e', s2) r2, ∀ r2',
      satisfiable (r1 ∗ r2 ∗ r2') →
      ∃ vs2 h2 fn2, e' = (Incoming, ERCall f vs2 h2) ∧ fns2 !! f = Some fn2 ∧ (
        length vs2 = length (fd_args fn2) →
          length vs1 = length (fd_args fn1) ∧ (
      (* Call *)
      (∀ n' f K1' K2' es1 es2 vs1' vs2' h1' h2' b s3 r3,
         n' ⊆ n →
         fns1 !! f = None →
         fns2 !! f = None →
         Forall2 (λ e v, e = Val v) es1 vs1' →
         Forall2 (λ e v, e = Val v) es2 vs2' →
         pp_to_ex (o (Outgoing, ERCall f vs2' h2') s3) (λ '(e''', s4) r4, ∃ r4',
            e''' = (Outgoing, ERCall f vs1' h1') ∧ R false (s1, r1) (s4, r4') ∧
            satisfiable (r4' ∗ r4 ∗ r3) ∧
           ∀ v1'' h1'' s5 r5, R true (s4, r4') (s5, r5) →
                   pp_to_all (i (Incoming, ERReturn v1'' h1'') s5) (λ '(e''''', s6) r6, ∀ r6',
                     satisfiable (r5 ∗ r6 ∗ r6') →
            ∃ v2'' h2'', e''''' = (Incoming, ERReturn v2'' h2'') ∧
          Rec (expr_fill K1' (Val v1'')) h1'' fns1
              ⪯{rec_trans, prepost_trans i o rec_trans, n', true}
          (SMProg, Rec (expr_fill K2' (Val v2'')) h2'' fns2, (PPInside, s6, r6')))) →

          Rec (expr_fill K1' (Call f es1)) h1' fns1
              ⪯{rec_trans, prepost_trans i o rec_trans, n', b}
          (SMProg, Rec (expr_fill K2' (Call f es2)) h2' fns2, (PPInside, s3, r3))) →
      (* Return *)
      (∀ n' v1 v2 h1' h2' b s3 r3,
         n' ⊆ n →
         pp_to_ex (o (Outgoing, ERReturn v2 h2') s3) (λ '(e''', s4) r4, ∃ r4',
               e''' = (Outgoing, ERReturn v1 h1') ∧ R true (s1, r1) (s4, r4') ∧ satisfiable (r4' ∗ r4 ∗ r3)) →
          Rec (expr_fill K1 (Val v1)) h1' fns1
              ⪯{rec_trans, prepost_trans i o rec_trans, n', b}
          (SMProg, Rec (expr_fill K2 (Val v2)) h2' fns2, (PPInside, s3, r3))) →
      Rec (expr_fill K1 (AllocA fn1.(fd_vars) $ subst_l fn1.(fd_args) vs1 fn1.(fd_body))) h1 fns1
          ⪯{rec_trans, prepost_trans i o rec_trans, n, false}
          (SMProg, Rec (expr_fill K2 (AllocA fn2.(fd_vars) $  subst_l fn2.(fd_args) vs2 fn2.(fd_body))) h2 fns2, (PPInside, s2, r2')))))) →
  trefines (rec_mod fns1) (prepost_mod i o (rec_mod fns2) s0 r0).
Proof.
  move => HR Hc.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember_call.
  { simpl. exact (λ d b '((Rec ei1 hi1 fnsi1), (ips1, Rec es1 hs1 fnss1, (pp1, s1, r1)))
                    '((Rec ei2 hi2 fnsi2), (ips2, Rec es2 hs2 fnss2, (pp2, s2, r2))),
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
  { simpl. exact (λ  '(Rec ei1 hi1 fnsi1) '(ips1, Rec es1 hs1 fnss1, (pp1, s1, r1))
                     '(Rec ei2 hi2 fnsi2) '(ips2, Rec es2 hs2 fnss2, (pp2, s2, r2)),
    ∃ Ki b v,
      fnsi2 = fnsi1 ∧
      fnss2 = fnss1 ∧
      ei1 = expr_fill Ki (Waiting b) ∧
      es2 = es1 ∧
      ei2 = expr_fill Ki (Val v) ∧
      ips2 = SMFilter ∧
      hs2 = hs1 ∧
      pp2 = PPRecv1 (Incoming, ERReturn v hi2) ∧
      s2 = s1 ∧
      r2 = r1). }
  { move => ??? *. destruct!. repeat case_match; naive_solver. }
  { move => /= *. destruct!. repeat case_match. naive_solver. }
  { move => /=. eexists [], []. split!. }
  move => /= n [ei hi fnsi] [[ips [es hs fnss]] [[pp {}s] r]] d ? ? Hstay Hcall Hret. destruct!.
  tstep_i. split => *.
  - tstep_s. split!.
    tstep_s. apply: pp_to_all_mono. { by eapply (Hc n (ReturnExtCtx _ :: Ki) (ReturnExtCtx _ :: Ks)). }
    move => -[??] ? Hcall' ??. move: Hcall' => /(_ _ ltac:(done))[?[?[?[?[? Hcall']]]]]. simplify_eq/=.
    tstep_s. left. split!. tstep_s. left. split!. move => ?.
    tstep_i. split; [|naive_solver]. move => ??. simplify_eq. split; [naive_solver|].
    have [//|? {}Hcall'] := Hcall'. apply: tsim_mono_b. apply: Hcall'.
    + move => n' f K1' K2' es1 es2 vs1' vs2' ???????? Hall1 Hall2 ?.
      have ?: es1 = Val <$> vs1'. { clear -Hall1. elim: Hall1; naive_solver. } subst.
      have ?: es2 = Val <$> vs2'. { clear -Hall2. elim: Hall2; naive_solver. } subst.
      tstep_i. split => *; simplify_eq. tstep_s. right. split!.
      tstep_s. apply: pp_to_ex_mono; [done|].
      move => [??] ? /= [?[?[?[??]]]]. simplify_eq. split!; [done|].
      apply Hcall; [done| |]. { split!; [done..|]. by etrans. }
      move => [ei2 hi2 fnsi2] [[ips2 [es2 hs2 fnss2]] [[pp2 {}s2] r2]].
      move => [ei3 hi3 fnsi3] [[ips3 [es3 hs3 fnss3]] [[pp3 {}s3] r3]] ??.
      destruct!.
      tstep_s. apply: pp_to_all_mono; [naive_solver|].
      move => [??] ? Hsim ??. move: Hsim => /(_ _ ltac:(done))?. destruct!/=.
      tstep_s. right. split!.
      repeat match goal with | H : expr_fill _ _ = expr_fill _ _ |- _ => apply expr_fill_Waiting_inj in H end.
      destruct!. done.
    + move => *. tstep_s. tstep_i. tstep_s. apply: pp_to_ex_mono; [done|].
      move => [??] ? [?[?[??]]] /=. subst. split!; [done|]. apply: tsim_mono; [|done].
      apply: Hstay; [done|]. split!; [done..|]. naive_solver.
  - tstep_s. split!.
    apply: Hret; [done|naive_solver| |].
    + by split!.
    + by split!.
Qed.
(** * closing *)
(**
module rec_event:
Incoming, Call f vs h -> Outgoing, Call f' vs' h' → Incoming, Return v h' -> Outgoing, Return v' h''


module rec_closed_event:
Start f vs            -> Call f' vs' v                                     -> Return v'
*)

Inductive rec_closed_event : Type :=
| ERCStart (f : string) (args: list Z)
| ERCCall (f : string) (args: list Z) (ret : Z)
| ERCEnd (ret : val)
.

Inductive rec_closed_state :=
| RCStart
| RCRecvStart (f : string) (vs : list Z)
| RCRunning
| RCRecvCall1 (f : string) (args : list val) (h : heap_state)
| RCRecvCall2 (f : string) (args : list Z) (h : heap_state)
| RCRecvRet (v : Z) (h : heap_state)
| RCRecvEnd1 (v : val)
| RCRecvEnd2 (v : Z)
| RCEnd.

Inductive rec_closed_step :
  rec_closed_state → option (sm_event rec_event rec_closed_event) → (rec_closed_state → Prop) → Prop :=
| RCStartS f vs:
  rec_closed_step RCStart (Some (SMEEmit (ERCStart f vs))) (λ σ, σ = RCRecvStart f vs)
| RCRecvStartS f vs:
  rec_closed_step (RCRecvStart f vs)
                  (Some (SMEReturn (Some (Incoming, ERCall f (ValNum <$> vs) ∅)))) (λ σ, σ = RCRunning)
| RCRunningS f vs h:
  rec_closed_step RCRunning (Some (SMERecv (Outgoing, ERCall f vs h))) (λ σ, σ = RCRecvCall1 f vs h)
| RCRecvCall1S f vs h:
  rec_closed_step (RCRecvCall1 f vs h) None (λ σ,
         ∃ vs', vs = ValNum <$> vs' ∧ σ = RCRecvCall2 f vs' h)
| RCRecvCall2S f vs rv h:
  rec_closed_step (RCRecvCall2 f vs h)
                  (Some (SMEEmit (ERCCall f vs rv))) (λ σ, σ = RCRecvRet rv h)
| RCRecvRetS v h:
  rec_closed_step (RCRecvRet v h)
                  (Some (SMEReturn (Some (Incoming, ERReturn (ValNum v) h)))) (λ σ, σ = RCRunning)
| RCRunningEndS v h:
  rec_closed_step RCRunning (Some (SMERecv (Outgoing, ERReturn v h))) (λ σ, σ = RCRecvEnd1 v)
| RCRecvEnd1EndS v:
  rec_closed_step (RCRecvEnd1 v) None (λ σ, ∃ v', v = ValNum v' ∧ σ = RCRecvEnd2 v')
| RCEndS v:
  rec_closed_step (RCRecvEnd2 v) (Some (SMEEmit (ERCEnd v))) (λ σ, σ = RCEnd)
.

Definition rec_closed_filter_trans : mod_trans (sm_event rec_event rec_closed_event) :=
  ModTrans rec_closed_step.

Definition rec_closed_filter : module (sm_event rec_event rec_closed_event) :=
  Mod rec_closed_filter_trans RCStart.

Global Instance rec_closed_filter_vis_no_all : VisNoAng rec_closed_filter_trans.
Proof. move => ????. inv_all @m_step; naive_solver. Qed.

Definition rec_closed (m : module rec_event) : module rec_closed_event :=
  seq_map_mod m rec_closed_filter SMFilter.

(** * Linking *)
(** ** Syntactic linking *)
Definition rec_syn_link (fns1 fns2 : gmap string fndef) : gmap string fndef :=
  fns1 ∪ fns2.

Definition rec_ctx_refines (fnsi fnss : gmap string fndef) :=
  ∀ C, trefines (rec_closed (rec_mod (rec_syn_link fnsi C)))
                (rec_closed (rec_mod (rec_syn_link fnss C))).

(** ** Semantic linking *)
Definition rec_link_filter (fns1 fns2 : gset string) : seq_product_case → list seq_product_case → rec_ev → seq_product_case → list seq_product_case → rec_ev → bool → Prop :=
  λ p cs e p' cs' e' ok,
    e' = e ∧
    ok = true ∧
    match e with
    | ERCall f vs h =>
        p' = (if bool_decide (f ∈ fns1) then SPLeft else if bool_decide (f ∈ fns2) then SPRight else SPNone) ∧
        (cs' = p::cs) ∧
        p ≠ p'
    | ERReturn v h =>
        cs = p'::cs' ∧
        p ≠ p'
    end.
Arguments rec_link_filter _ _ _ _ _ _ _ _ /.

Definition rec_link_trans (fns1 fns2 : gset string) (m1 m2 : mod_trans rec_event) : mod_trans rec_event :=
  link_trans (rec_link_filter fns1 fns2) m1 m2.

Definition rec_link (fns1 fns2 : gset string) (m1 m2 : module rec_event) : module rec_event :=
  Mod (rec_link_trans fns1 fns2 m1.(m_trans) m2.(m_trans)) (MLFNone, [], m1.(m_init), m2.(m_init)).

Lemma rec_link_trefines m1 m1' m2 m2' fns1 fns2 `{!VisNoAng m1.(m_trans)} `{!VisNoAng m2.(m_trans)}:
  trefines m1 m1' →
  trefines m2 m2' →
  trefines (rec_link fns1 fns2 m1 m2) (rec_link fns1 fns2 m1' m2').
Proof. move => ??. by apply link_mod_trefines. Qed.

(** ** Relating semantic and syntactic linking *)
Inductive rec_link_combine_ectx :
  nat → bool → bool → link_case rec_ev → list seq_product_case → list expr_ectx → list expr_ectx → list expr_ectx → Prop :=
| RPCENil:
  rec_link_combine_ectx 0 false false MLFNone [] [] [] []
| RPCENoneToLeft n cs K Kl Kr bl br:
  rec_link_combine_ectx n bl br MLFNone cs K Kl Kr →
  rec_link_combine_ectx (S n) bl br MLFLeft (SPNone :: cs)
                             (ReturnExtCtx (bl || br)::K) (ReturnExtCtx bl::Kl) Kr
| RPCENoneToRight n cs K Kl Kr bl br:
  rec_link_combine_ectx n bl br MLFNone cs K Kl Kr →
  rec_link_combine_ectx (S n) bl br MLFRight (SPNone :: cs)
                             (ReturnExtCtx (bl || br)::K) Kl (ReturnExtCtx br::Kr)
| RPCELeftToRight n cs K Kl Kl' Kr bl br:
  rec_link_combine_ectx n bl br MLFLeft cs K Kl Kr →
  is_static_expr true (expr_fill Kl' (Var "")) →
  rec_link_combine_ectx (S n) true br MLFRight (SPLeft :: cs)
                             (Kl' ++ K) (Kl' ++ Kl) (ReturnExtCtx br::Kr)
| RPCELeftToNone n cs K Kl Kl' Kr bl br:
  rec_link_combine_ectx n bl br MLFLeft cs K Kl Kr →
  is_static_expr true (expr_fill Kl' (Var "")) →
  rec_link_combine_ectx (S n) true br MLFNone (SPLeft :: cs)
                             (Kl' ++ K) (Kl' ++ Kl) Kr
| RPCERightToLeft n cs K Kl Kr' Kr bl br:
  rec_link_combine_ectx n bl br MLFRight cs K Kl Kr →
  is_static_expr true (expr_fill Kr' (Var "")) →
  rec_link_combine_ectx (S n) bl true MLFLeft (SPRight :: cs)
                             (Kr' ++ K) (ReturnExtCtx bl::Kl) (Kr' ++ Kr)
| RPCERightToNone n cs K Kl Kr' Kr bl br:
  rec_link_combine_ectx n bl br MLFRight cs K Kl Kr →
  is_static_expr true (expr_fill Kr' (Var "")) →
  rec_link_combine_ectx (S n) bl true MLFNone (SPRight :: cs)
                             (Kr' ++ K) Kl (Kr' ++ Kr)
.

Definition rec_link_inv (bv : bool) (fns1 fns2 : gmap string fndef) (σ1 : rec_trans.(m_state)) (σ2 : link_case rec_ev * list seq_product_case * rec_state * rec_state) : Prop :=
  let 'Rec e1 h1 fns1' := σ1 in
  let '(σf, cs, Rec el hl fnsl, Rec er hr fnsr) := σ2 in
  ∃ n K Kl Kr e1' el' er' bl br,
  fns1' = fns1 ∪ fns2 ∧
  fnsl = fns1 ∧
  fnsr = fns2 ∧
  rec_link_combine_ectx n bl br σf cs K Kl Kr ∧
  e1 = expr_fill K e1' ∧
  el = expr_fill Kl el' ∧
  er = expr_fill Kr er' ∧
  match σf with
  | MLFLeft => e1' = el' ∧ is_static_expr true el' ∧ er' = Waiting br ∧ h1 = hl
              ∧ (if bv then to_val el' = None else True)
  | MLFRight => e1' = er' ∧ is_static_expr true er' ∧ el' = Waiting bl ∧ h1 = hr
               ∧ (if bv then to_val er' = None else True)
  | MLFNone => e1' = Waiting (bl || br) ∧ el' = Waiting bl ∧ er' = Waiting br
  | _ => False
  end.


Lemma rec_syn_link_refines_link fns1 fns2:
  fns1 ##ₘ fns2 →
  trefines (rec_mod (rec_syn_link fns1 fns2))
           (rec_link (dom fns1) (dom fns2) (rec_mod fns1) (rec_mod fns2)).
Proof.
  move => Hdisj.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { exact: (λ _, rec_link_inv true fns1 fns2). }
  { split!. 1: by econs. all: done. } { done. }
  move => /= {}n _ Hloop [e1 h1 fns1'] [[[ipfs cs] [el hl fnsl]] [er hr fnsr]] [m [K [Kl [Kr ?]]]].
  have {}Hloop : ∀ σi σs,
            rec_link_inv false fns1 fns2 σi σs
            → σi ⪯{rec_trans, rec_link_trans (dom fns1) (dom fns2) rec_trans rec_trans, n, true} σs. {
    clear -Hloop. move => [e1 h1 fns1'] [[[ipfs cs] [el hl fnsl]] [er hr fnsr]].
    move => [m [K [Kl [Kr [e1' [el' [er' [bl [br [?[?[?[HK[?[?[? Hm]]]]]]]]]]]]]]]]; simplify_eq.
    elim/lt_wf_ind: m ipfs h1 hl hr cs K Kl Kr e1' el' er' bl br HK Hm => m IHm.
    move => ipfs h1 hl hr cs K Kl Kr e1' el' er' bl br HK Hmatch.
    case_match; destruct!/=.
    - destruct (to_val el') eqn:?; [ |apply: Hloop; naive_solver].
      destruct el'; simplify_eq/=.
      inversion HK; clear HK; simplify_eq/=.
      * tstep_i. tstep_s. split!; [done..|] => /=. split!.
        apply: Hloop; [done|]. by split!.
      * tstep_s. split!.
        tstep_s. split!.
        rewrite !expr_fill_app. apply: IHm; [|done|]; [lia|]. split!. by apply is_static_expr_expr_fill.
    - destruct (to_val er') eqn:?; [ |apply: Hloop; naive_solver].
      destruct er'; simplify_eq/=.
      inversion HK; clear HK; simplify_eq/=.
      * tstep_i. tstep_s. split!. apply: Hloop; [done|]. by split!.
      * tstep_s. split!.
        tstep_s. split!.
        rewrite !expr_fill_app. apply: IHm; [|done|]; [lia|]. split!. by apply is_static_expr_expr_fill.
    - apply: Hloop; naive_solver.
  }
  destruct!/=. case_match; destruct!.
  - tstep_both. apply: steps_impl_step_end => ?? /prim_step_inv[//|?[?[?[?[??]]]]].
    simplify_eq. revert select (Is_true (is_static_expr _ _)) => /is_static_expr_expr_fill/=[??]//.
    rewrite -expr_fill_app.
    inv_all head_step => //.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply is_static_expr_expr_fill.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply is_static_expr_expr_fill.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply is_static_expr_expr_fill.
    + tstep_s => b ?. subst. tend. split!. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      apply is_static_expr_expr_fill. split!. destruct b; naive_solver.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      apply is_static_expr_expr_fill. split!. by apply is_static_expr_subst.
    + tstep_s. done.
    + tstep_s => *. split!; [done..|] => /= *; simplify_eq. tend. split!.
      apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      apply is_static_expr_expr_fill. split!. by apply is_static_expr_subst_l.
    + tstep_s => *. tend. split!; [done..|].
      apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply is_static_expr_expr_fill.
    + revert select ((_ ∪ _) !! _ = Some _) => /lookup_union_Some_raw[?|[??]].
      * tstep_s. left. split!. tend. split!.
        apply: Hloop. rewrite !expr_fill_app. split!; [done..|].
        apply is_static_expr_expr_fill. split!. apply is_static_expr_subst_l.
        apply is_static_expr_mono. apply fd_static.
      * tstep_s. right. simpl_map_decide. split!.
        tstep_s. left. split!. tstep_s. left. split! => ?. tend.
        split!. apply: Hloop. split!; [by econs|done..|].
        apply is_static_expr_subst_l. apply is_static_expr_mono. apply fd_static.
    + revert select ((_ ∪ _) !! _ = None) => /lookup_union_None[??].
      tstep_s. right. simpl_map_decide. split!; [done|]. tend. split!.
      apply: Hloop. split!; [by econs|done..].
  - tstep_both. apply: steps_impl_step_end => ?? /prim_step_inv[//|?[?[?[?[??]]]]].
    simplify_eq. revert select (Is_true (is_static_expr _ _)) => /is_static_expr_expr_fill/=[??]//.
    rewrite -expr_fill_app.
    inv_all head_step => //.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply is_static_expr_expr_fill.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply is_static_expr_expr_fill.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply is_static_expr_expr_fill.
    + tstep_s => b ?. subst. tend. split!. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      apply is_static_expr_expr_fill. split!. destruct b; naive_solver.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      apply is_static_expr_expr_fill. split!. by apply is_static_expr_subst.
    + tstep_s. done.
    + tstep_s => *. split!; [done..|] => /= *; simplify_eq. tend. split!.
      apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      apply is_static_expr_expr_fill. split!. by apply is_static_expr_subst_l.
    + tstep_s => *. tend. split!; [done..|].
      apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply is_static_expr_expr_fill.
    + revert select ((_ ∪ _) !! _ = Some _) => /lookup_union_Some_raw[?|[??]].
      * have ? : fns2 !! f = None by apply: map_disjoint_Some_l.
        tstep_s. right. simpl_map_decide. split!.
        tstep_s. left. split!. tstep_s. left. split! => ?.
        tend. split!. apply: Hloop. split!; [by econs|done..|].
        apply is_static_expr_subst_l. apply is_static_expr_mono. apply fd_static.
      * tstep_s. left. split! => /= ?. tend. split!.
        apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
        apply is_static_expr_expr_fill. split!. apply is_static_expr_subst_l.
        apply is_static_expr_mono. apply fd_static.
    + revert select ((_ ∪ _) !! _ = None) => /lookup_union_None[??].
      tstep_s. right. simpl_map_decide. split!;[done|] => /=. tend. split!; [done..|].
      apply: Hloop. split!; [by econs|rewrite ?orb_true_r; done..].
  - tstep_i. split.
    + move => f fn vs h' /lookup_union_Some_raw[?|[??]].
      * have ?: fns2 !! f = None by apply: map_disjoint_Some_l.
        tstep_s. eexists (ERCall _ _ _) => /=. simpl. simpl_map_decide. split!.
        tstep_s. split!.
        apply Hloop. split!; [by econs|done..| ]. apply is_static_expr_forallb.
      * tstep_s. eexists (ERCall _ _ _) => /=. simpl. simpl_map_decide. split!.
        tstep_s. split!.
        apply Hloop. split!; [by econs|done..| ]. apply is_static_expr_forallb.
    + move => v h' ?.
      revert select (rec_link_combine_ectx _ _ _ _ _ _ _ _) => HK.
      inversion HK; clear HK; simplify_eq/= => //.
      * tstep_s. eexists (ERReturn _ _) => /=. split!.
        tstep_s. split!.
        apply Hloop. rewrite !expr_fill_app. split!; [done..|].
        by apply is_static_expr_expr_fill.
      * tstep_s. eexists (ERReturn _ _) => /=. split!.
        tstep_s. split!.
        apply Hloop. rewrite !expr_fill_app. split!; [done..|].
        by apply is_static_expr_expr_fill.
Qed.

Lemma rec_link_refines_syn_link fns1 fns2:
  fns1 ##ₘ fns2 →
  trefines (rec_link (dom fns1) (dom fns2) (rec_mod fns1) (rec_mod fns2))
           (rec_mod (rec_syn_link fns1 fns2)).
Proof.
  move => Hdisj.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { exact: (λ _, flip (rec_link_inv false fns1 fns2)). }
  { split!. 1: by econs. all: done. } { done. }
  move => /= {}n _ Hloop [[[ipfs cs] [el hl fnsl]] [er hr fnsr]] [e1 h1 fns1'] [m [K [Kl [Kr ?]]]].
  destruct!/=. case_match; destruct!.
  - destruct (to_val el') eqn:?.
    + destruct el'; simplify_eq/=.
      revert select (rec_link_combine_ectx _ _ _ _ _ _ _ _) => HK.
      inversion HK; clear HK; simplify_eq/=.
      * tstep_i => *; destruct!. tstep_s. split!.
        apply: Hloop; [done|]. by split!.
      * tstep_i => *; destruct!/=.
        tstep_i; split => *; simplify_eq.
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..|].
        by apply is_static_expr_expr_fill.
    + tstep_both. apply: steps_impl_step_end => ?? /prim_step_inv[//|?[?[?[?[??]]]]] *.
      simplify_eq. revert select (Is_true (is_static_expr _ _)) => /is_static_expr_expr_fill/=[??]//.
      rewrite -expr_fill_app.
      inv_all/= head_step => //; destruct!.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply is_static_expr_expr_fill.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply is_static_expr_expr_fill.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply is_static_expr_expr_fill.
      * tstep_s => b ?. subst. tend. split!. apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply is_static_expr_expr_fill. split!. destruct b; naive_solver.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply is_static_expr_expr_fill. split!. by apply is_static_expr_subst.
      * by tstep_s.
      * tstep_s => *. split!; [done..|] => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply is_static_expr_expr_fill. split!. by apply is_static_expr_subst_l.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply is_static_expr_expr_fill.
      * tstep_s. left. split!; [apply lookup_union_Some; naive_solver|] => ?. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..|].
        apply is_static_expr_expr_fill. split!. apply is_static_expr_subst_l.
        apply is_static_expr_mono. apply fd_static.
      * move => *. destruct!/=. repeat case_bool_decide => //.
        -- tend. split!. tstep_i. split => *; simplify_eq.
           apply: Hloop; [done|]. split!; [by econs|done..|]. apply is_static_expr_forallb.
        -- tstep_s. right. split!; [apply lookup_union_None;split!;by apply not_elem_of_dom| done|].
           tend. split!. apply: Hloop; [done|]. split!; [by econs|done..].
  - destruct (to_val er') eqn:?.
    + destruct er'; simplify_eq/=.
      revert select (rec_link_combine_ectx _ _ _ _ _ _ _ _) => HK. inv/= HK.
      * tstep_i => *; destruct!. tstep_s. split!.
        apply: Hloop; [done|]. by split!.
      * tstep_i => *; destruct!/=.
        tstep_i; split => *; simplify_eq.
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..|].
        by apply is_static_expr_expr_fill.
    + tstep_both. apply: steps_impl_step_end => ?? /prim_step_inv[//|?[?[?[?[??]]]]] *.
      simplify_eq. revert select (Is_true (is_static_expr _ _)) => /is_static_expr_expr_fill/=[??]//.
      rewrite -expr_fill_app.
      inv_all/= head_step => //; destruct!.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply is_static_expr_expr_fill.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply is_static_expr_expr_fill.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply is_static_expr_expr_fill.
      * tstep_s => b ?. subst. tend. split!. apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply is_static_expr_expr_fill. split!. destruct b; naive_solver.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply is_static_expr_expr_fill. split!. by apply is_static_expr_subst.
      * by tstep_s.
      * tstep_s => *. split!; [done..|] => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply is_static_expr_expr_fill. split!. by apply is_static_expr_subst_l.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply is_static_expr_expr_fill.
      * tstep_s. left. split!; [apply lookup_union_Some; naive_solver|] => ?. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..|].
        apply is_static_expr_expr_fill. split!. apply is_static_expr_subst_l.
        apply is_static_expr_mono. apply fd_static.
      * move => *. destruct!/=. repeat case_bool_decide => //.
        -- tend. split!. tstep_i. split => *; simplify_eq.
           apply: Hloop; [done|]. split!; [by econs|done..|]. apply is_static_expr_forallb.
        -- tstep_s. right. split!; [apply lookup_union_None;split!;by apply not_elem_of_dom|done|].
           tend. split!. apply: Hloop; [done|]. split!; [by econs|rewrite ?orb_true_r; done..].
  - tstep_i => *.
    repeat match goal with | x : rec_ev |- _ => destruct x end; simplify_eq/=; destruct!/=.
    + tstep_s. left. repeat case_bool_decide => //.
      all: revert select (_ ∈ dom _) => /elem_of_dom[??]; split!;
               [rewrite lookup_union_Some //; naive_solver |].
      * tstep_i. split => *; destruct!/=.
        apply: Hloop; [done|]. split!; [by econs|done..|]. apply is_static_expr_forallb.
      * tstep_i. split => *; destruct!/=.
        apply: Hloop; [done|]. split!; [by econs|done..|]. apply is_static_expr_forallb.
    + tstep_s. right.
      revert select (rec_link_combine_ectx _ _ _ _ _ _ _ _) => HK.
      inversion HK; clear HK; simplify_eq; rewrite ?orb_true_r.
      * split!. tstep_i. split => *; destruct!/=.
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done|done..|].
        by apply is_static_expr_expr_fill.
      * split!. tstep_i. split => *; destruct!/=.
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done|done..|].
        by apply is_static_expr_expr_fill.
Qed.

Lemma rec_trefines_implies_ctx_refines fnsi fnss :
  dom fnsi = dom fnss →
  trefines (rec_mod fnsi) (rec_mod fnss) →
  rec_ctx_refines fnsi fnss.
Proof.
  move => Hdom Href C. rewrite /rec_syn_link map_difference_union_r (map_difference_union_r fnss).
  apply seq_map_mod_trefines. { apply _. } { apply _. }
  etrans. { apply rec_syn_link_refines_link. apply map_disjoint_difference_r'. }
  etrans. 2: { apply rec_link_refines_syn_link. apply map_disjoint_difference_r'. }
  rewrite !dom_difference_L Hdom.
  apply rec_link_trefines; [apply _..| |].
  - apply: Href.
  - erewrite map_difference_eq_dom_L => //. apply _.
Qed.

(** ** Commuting and associativity of semantic linking (WIP) *)
(*
(* TODO: track a stack of this and compute every thing from it (also keep an optional event) *)
Inductive rec_prod_assoc_state :=
| IPA1 | IPA2 | IPA3 | IPANone.

(* Inductive rec_prod_assoc_stack (m1 m2 m3 : module rec_event) : *)
(*   link_case rec_ev → list seq_product_case → link_case rec_ev → list seq_product_case → *)
(*   link_case rec_ev → list seq_product_case → link_case rec_ev → list seq_product_case → Prop := *)
(* | IPASNil : *)
(*   rec_prod_assoc_stack m1 m2 m3 MLFNone [] MLFNone [] MLFNone [] MLFNone [] *)
(* | IPASNil : *)
(*   rec_prod_assoc_stack m1 m2 m3 MLFNone [] MLFNone [] MLFNone [] MLFNone [] *)
(* . *)

Definition rec_prod_assoc_inv (fns1 fns2 fns3 : gset string) (m1 m2 m3 : module rec_event)
  (σ1 : link_case rec_ev * list seq_product_case * m1.(m_state) *
          (link_case rec_ev * list seq_product_case * m2.(m_state) * m3.(m_state)))
  (σ2 : link_case rec_ev * list seq_product_case * (link_case rec_ev * list seq_product_case * m1.(m_state) * m2.(m_state)) * m3.(m_state)) : Prop :=
  let '(σfi1, csi1, σi1, (σfi2, csi2, σi2, σi3)) := σ1 in
  let '(σfs1, css1, (σfs2, css2, σs1, σs2), σs3) := σ2 in
  ∃ ipacur,
  σi1 = σs1 ∧
  σi2 = σs2 ∧
  σi3 = σs3 ∧
  match ipacur with
  | IPA1 => False
  | IPA2 => False
  | IPA3 => False
  | IPANone => σfi1 = MLFNone ∧ σfi2 = MLFNone ∧ σfs1 = MLFNone ∧ σfs2 = MLFNone
  end.
  (* rec_prod_assoc_stack m1 m2 m3 σfi1 csi1 σfi2 csi2 σfs1 css1 σfs2 css2. *)


Lemma rec_prod_assoc1 fns1 fns2 fns3 m1 m2 m3 σ1 σ2 σ3:
  fns1 ## fns2 →
  trefines (MS (rec_link fns1 (fns2 ∪ fns3) m1 (rec_link fns2 fns3 m2 m3))
              (initial_rec_link_state m1 (rec_link _ _ m2 m3) σ1
                  (initial_rec_link_state m2 m3 σ2 σ3)))
           (MS (rec_link (fns1 ∪ fns2) fns3 (rec_link fns1 fns2 m1 m2) m3)
               (initial_rec_link_state (rec_link _ _ m1 m2) m3
                  (initial_rec_link_state m1 m2 σ1 σ2) σ3)
           ).
Proof.
  move => Hdisj12.
  apply tsim_implies_trefines => n /=.
  unshelve apply: tsim_remember. { exact: (λ _, rec_prod_assoc_inv fns1 fns2 fns3 m1 m2 m3). }
  { eexists IPANone. split!. } { done. }
  move => ?? IH [[[??]?][[[??]?]?]] [[[??][[[??]?]?]]?] /= ?. destruct!.
  (* revert select (rec_prod_assoc_stack _ _ _ _ _ _ _ _ _ _ _) => Hstack. inversion Hstack; simplify_eq. *)
  case_match; destruct!.
  tstep_i => *. case_match; destruct!.
  tstep_s. split!; [repeat case_bool_decide; set_solver|].
  case_bool_decide => /=.
  - rewrite bool_decide_true; [|set_solver].
    tstep_s. split!; [repeat case_bool_decide; set_solver|].
    rewrite bool_decide_true /=; [|set_solver].
    apply IH; [done|]. split!.
  repeat case_bool_decide => /=.

  set_unfold; naive_solver.
  set_unfold; naive_solver.

set_unfold; naive_solver.
try by exfalso; set_unfold; naive_solver.
  - tstep_s. split!; [repeat case_bool_decide; set_solver|].
    apply IH; [done|]. split!.
  tstep_i.
*)
