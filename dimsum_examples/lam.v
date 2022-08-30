From dimsum.core Require Export proof_techniques link prepost.
From dimsum.core Require Import axioms.

Local Open Scope Z_scope.

(** * Lam, a higher-order functional language with closures*)

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

(** ** function id*)
Definition fid : Set := string*option Z.

(** ** Syntax *)
Inductive binop : Set :=
| AddOp  | OffsetOp | EqOp | LeOp | LtOp.

Inductive val := 
  | ValNum (z : Z) 
  | ValBool (b : bool) 
  | ValLoc (l : loc)
  | ValFid (id: fid)
.

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
Definition val_to_fid (v:val ) : option fid := 
  match v with 
  | ValFid f => Some f 
  | _ => None 
  end. 

Section expr.
Local Unset Elimination Schemes.
Inductive expr : Set :=
| Var (v : string)
| Val (v : val)
| BinOp (e1 : expr) (o : binop) (e2 : expr)
| NewRef (e1:expr) (e2: expr)
| Load (e : expr)
| Store (e1 e2 : expr)
| If (e e1 e2 : expr)
| LetE (v : string) (e1 e2 : expr)
| FixE (f:string) (args:list string) (e:expr)
| App (e :expr) (args : list expr)
(* Returning to the context, insert automatically during execution. *)
| ReturnExt (e : expr)
| ReturnInt (e:expr) (* Needed because we want to generate closures of same name as linking*)
| Waiting 

.
End expr.

Lemma expr_ind (P : expr → Prop) :
  (∀ (x : string), P (Var x)) →
  (∀ (v : val), P (Val v)) →
  (∀ (e1 : expr) (op : binop) (e2 : expr), P e1 → P e2 → P (BinOp e1 op e2)) →
  (∀ (e1 e2:expr), P e1 →P e2→ P (NewRef e1 e2)) →
  (∀ (e : expr), P e → P (Load e)) →
  (∀ (e1 e2 : expr), P e1 → P e2 → P (Store e1 e2)) →
  (∀ (e1 e2 e3 : expr), P e1 → P e2 → P e3 → P (If e1 e2 e3)) →
  (∀ (v : string) (e1 e2 : expr), P e1 → P e2 → P (LetE v e1 e2)) →
  (∀ (f:string) (args:list string) (e:expr), P e →P( FixE f args e))→
  (∀ (e :expr ) (args : list expr), P e → Forall P args → P (App e args)) →
  (∀ (e : expr), P e → P (ReturnExt  e)) →
  (∀ (e : expr), P e → P (ReturnInt  e)) →
  (P Waiting ) →
  ∀ (e : expr), P e.
Proof.
  move => *. generalize dependent P => P. match goal with | e : expr |- _ => revert e end.
  fix FIX 1. move => [ ^e] => ????????? Happ ???. 
  10: { apply Happ. auto. apply Forall_true => ?. by apply: FIX. }
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
  | NewRef e1 e2 => assigned_vars e1 ++ assigned_vars e2
  | Load e => assigned_vars e
  | Store e1 e2 => assigned_vars e1 ++ assigned_vars e2
  | If e e1 e2 => assigned_vars e ++ assigned_vars e1 ++ assigned_vars e2
  | LetE v e1 e2 => [v] ++ assigned_vars e1 ++ assigned_vars e2
  | FixE f args e => [f] ++ args ++ assigned_vars e
  | App e args => assigned_vars e ++ mjoin (assigned_vars <$> args)
  | ReturnExt e => assigned_vars e
  | ReturnInt e => assigned_vars e
  | Waiting  => []
  end.

(** ** Substitution *)
Fixpoint subst (x : string) (v : val) (e : expr) : expr :=
  match e with
  | Var y => if bool_decide (x = y) then Val v else Var y
  | Val v => Val v
  | BinOp e1 o e2 => BinOp (subst x v e1) o (subst x v e2)
  | NewRef e1 e2 => NewRef (subst x v e1) (subst x v e2)
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  | If e e1 e2 => If (subst x v e) (subst x v e1) (subst x v e2)
  | LetE y e1 e2 => LetE y (subst x v e1) (if bool_decide (x ≠ y) then subst x v e2 else e2)
  | FixE f args e => FixE f args (if bool_decide (x ∈ f::args) then e else subst x v e)
  | App e args => App (subst x v e) (subst x v <$> args)
  | ReturnExt e => ReturnExt (subst x v e)
  | ReturnInt e => ReturnInt (subst x v e)
  | Waiting  => Waiting 
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
  | NewRef e1 e2 => NewRef (subst_map x e1) (subst_map x e2)
  | Load e => Load (subst_map x e)
  | Store e1 e2 => Store (subst_map x e1) (subst_map x e2)
  | If e e1 e2 => If (subst_map x e) (subst_map x e1) (subst_map x e2)
  | LetE y e1 e2 => LetE y (subst_map x e1) (subst_map (delete y x) e2)
  | FixE f args e =>
      let newx := foldl (λ m k, delete k m) x (f::args) in  
      FixE f args (subst_map newx e)
  | App e args => App (subst_map x e) (subst_map x <$> args)
  | ReturnExt e => ReturnExt (subst_map x e)
  | ReturnInt e => ReturnInt (subst_map x e)
  | Waiting  => Waiting 
  end.

Lemma subst_map_empty e :
  subst_map ∅ e = e.
Proof.
  intros.
  induction e; simpl; 
  try rewrite IHe1; try rewrite IHe2; try rewrite IHe3; try rewrite IHe; auto.
  rewrite delete_empty. rewrite IHe2. reflexivity.
  rewrite delete_empty. f_equal. 
    induction args; simpl; auto.
    rewrite delete_empty; auto.
    f_equal. induction args.
    - reflexivity.
    - simpl. inversion H; subst. rewrite H2. apply IHargs in H3. f_equal.
     unfold fmap in H3. auto.
     Qed.

Lemma foldl_cons:
∀ {A B : Type} (f : A → B → A) (a : A) (l : list B) (x : B),
 (foldl f (f a x) l) =foldl f a (x:: l) .
intros. simpl. reflexivity.
Qed.

Lemma foldl_delete xs x v l: 
x ∈ l →foldl
  (λ (m : gmap string val) (k : string),
     delete k m) (<[x:=v]> xs) l =
foldl
  (λ (m : gmap string val) (k : string),
     delete k m) xs l.
Proof. 
  generalize dependent xs.
   induction l; intros. rewrite elem_of_nil in H; contradiction.
   rewrite elem_of_cons in H. destruct H.
   simpl. subst. rewrite delete_insert_delete. reflexivity.
   assert (x=a \/ x≠a). apply AxClassic.
   destruct H0; subst.
    simpl. rewrite delete_insert_delete. reflexivity.
   simpl. rewrite delete_insert_ne. naive_solver. naive_solver. 
  Qed.
   
  Lemma foldl_delete_notin xs x v l: 
  x ∉ l →foldl
    (λ (m : gmap string val) (k : string),
       delete k m) (<[x:=v]> xs) l =
       <[x:=v]> (foldl
    (λ (m : gmap string val) (k : string),
       delete k m) xs l).
    Proof.
      intros. generalize dependent xs.
      induction l; simpl. reflexivity.
      rewrite not_elem_of_cons in H.
      destruct H. intros.
      rewrite delete_insert_ne.
      naive_solver. naive_solver.
    Qed.


Lemma subst_map_subst x v e xs :
  subst_map (<[x:=v]> xs) e = subst_map xs (subst x v e).
Proof.
  (*TODO: use fmap_cons*)
  generalize dependent xs.
  induction e; intros; simpl; 
  try rewrite IHe1; try rewrite IHe2; try rewrite IHe3; try rewrite IHe;auto.
  - case_bool_decide; simplify_map_eq; auto.
  - case_bool_decide. f_equal. rewrite delete_insert_ne. rewrite IHe2. reflexivity. auto.
  subst. rewrite delete_insert_delete. reflexivity.
  - f_equal. case_bool_decide. f_equal. 
  assert (foldl (λ (m : gmap string val) (k : string), delete k m)(delete f (<[x:=v]> xs)) args = 
        foldl (λ (m : gmap string val) (k : string), delete k m)  (<[x:=v]> xs) (f::args)).
  apply (foldl_cons (λ (m : gmap string val) 
  (k : string), delete k m) (<[x:=v]> xs) args f).
  rewrite H0.  
  assert (foldl (λ (m : gmap string val) (k : string), delete k m)(delete f (xs)) args = 
  foldl (λ (m : gmap string val) (k : string), delete k m)  (xs) (f::args)).
  apply (foldl_cons (λ (m : gmap string val) 
  (k : string), delete k m) ( xs) args f). rewrite H1.
  remember (f::args) as l. apply foldl_delete. naive_solver. rewrite delete_insert_ne. rewrite foldl_delete_notin.
  assert (foldl (λ (m : gmap string val) (k : string), delete k m)(delete f (xs)) args = 
  foldl (λ (m : gmap string val) (k : string), delete k m)  (xs) (f::args)).
  apply (foldl_cons (λ (m : gmap string val) 
  (k : string), delete k m) ( xs) args f). auto. rewrite not_elem_of_cons in H. destruct H. auto. rewrite not_elem_of_cons in H. destruct H;auto.
  - f_equal. induction args. reflexivity. simpl. f_equal. inversion H; subst; auto. inversion H; subst.
  apply IHargs in H3. unfold fmap in H3. auto.
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
| NewRefLCtx (e2:expr)
| NewRefRCtx (v1:val)
| LoadCtx
| StoreLCtx (e2 : expr)
| StoreRCtx (v1 : val)
| IfCtx (e2 e3 : expr)
| LetECtx (v : string) (e2: expr)
| AppLCtx (el: list expr)
| AppRCtx (v1: val) (arg1: list val) (arg2: list expr)
| ReturnExtCtx 
| ReturnIntCtx 
.


Definition expr_fill_item (Ki : expr_ectx) (e : expr) : expr :=
  match Ki with
  | BinOpLCtx op e2 => BinOp e op e2
  | BinOpRCtx v1 op => BinOp (Val v1) op e
  | NewRefLCtx e2=> NewRef e e2
  | NewRefRCtx v1 => NewRef (Val v1) e
  | LoadCtx => Load e
  | StoreLCtx e2 => Store e e2
  | StoreRCtx v1 => Store (Val v1) e
  | IfCtx e2 e3 => If e e2 e3
  | LetECtx v e2 => LetE v e e2
  | AppLCtx el => App e el
  | AppRCtx v vl el => App (Val v) ((Val<$> vl) ++ e::el)
  | ReturnExtCtx => ReturnExt e
  | ReturnIntCtx => ReturnInt e
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
Proof. destruct Ki => //= ; move => [??] //. Qed.

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

Lemma expr_fill_Waiting_inj K1 K2 :
  expr_fill K1 (Waiting) = expr_fill K2 (Waiting) → K1 = K2.
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
Fixpoint is_static_expr (allow_loc_closid: bool)  (e : expr) : bool :=
  match e with
  | Var y => true
  | Val v => 
    (match v with 
    | ValLoc _ => allow_loc_closid
    | ValFid (_, Some _) => allow_loc_closid 
    | _ => true
    end)
  | BinOp e1 o e2 => is_static_expr allow_loc_closid e1 && is_static_expr allow_loc_closid e2
  | NewRef e1 e2 => is_static_expr allow_loc_closid e1 && is_static_expr allow_loc_closid e2
  | Load e => is_static_expr allow_loc_closid e
  | Store e1 e2 => is_static_expr allow_loc_closid e1 && is_static_expr allow_loc_closid e2
  | If e e1 e2 => 
      is_static_expr allow_loc_closid e && is_static_expr allow_loc_closid e1 && is_static_expr allow_loc_closid e2
  | LetE y e1 e2 => is_static_expr allow_loc_closid e1 && is_static_expr allow_loc_closid e2
  | FixE f args e => is_static_expr allow_loc_closid e
  | App e args => is_static_expr allow_loc_closid e && forallb (is_static_expr allow_loc_closid) args
  | ReturnExt e => false
  | ReturnInt e => false
  | Waiting => false
  end.

Lemma is_static_expr_value v: 
   is_static_expr true  (Val v).
Proof.
  simpl. destruct v; auto. destruct id; destruct o;auto.
Qed.

Lemma is_static_expr_forallb vs:
  forallb (is_static_expr true) (Val <$> vs).
Proof.
  by apply forallb_True, Forall_fmap, Forall_true, is_static_expr_value. 
Qed.  

(*For is_static_expr_subst. Is this a proven lemma?*)
Lemma Forall_implication {A:Type}(P Q:A -> Prop) args: 
  Forall (λ x, P x) args -> Forall (λ x, ((P x) -> (Q x))) args -> Forall (λ x, Q x) args.
  Proof.
    induction args; intros. constructor.
    constructor; inversion H; inversion H0; subst; eauto.
  Qed. 

Lemma is_static_expr_subst x v e:
  is_static_expr true e →
  is_static_expr true (subst x v e).
Proof.
  elim: e; intros; try naive_solver; simpl.
  - case_bool_decide.  apply is_static_expr_value. auto.
  - case_bool_decide; naive_solver.
  - case_bool_decide; naive_solver.  
  - simpl in H1. apply andb_prop_elim in H1. destruct H1. apply andb_prop_intro.
  split. eauto. apply forallb_True, Forall_fmap. apply forallb_True in H2.
  apply Forall_implication with (λ x : expr, is_static_expr true x); auto.
Qed.

Lemma is_static_expr_subst_l xs vs e:
  is_static_expr true e →
  is_static_expr true (subst_l xs vs e).
Proof.
  elim: xs vs e. { by case. }
  move => ?? IH [//|??] /=??. apply IH.
  by apply is_static_expr_subst.
Qed.

Lemma is_static_expr_expr_fill blc K e:
  is_static_expr blc (expr_fill K e) ↔ is_static_expr blc (expr_fill K (Var "")) ∧ is_static_expr blc e.
Proof.
  elim/rev_ind: K e => /=. { naive_solver. }
  move => Ki K IH e. rewrite !expr_fill_app/=.
  destruct Ki => //=; rewrite ?forallb_app/=; naive_solver.
Qed.

Lemma is_static_expr_val v: is_static_expr true (Val v).
Proof.
  destruct v; auto.
  destruct id; destruct o; auto.
Qed.




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
  - split!. rewrite lookup_union_l //. by simplify_map_eq.
  - destruct (decide (l = i)); subst; split!.
    + destruct (m !! i) eqn:?.
      * by erewrite lookup_union_Some_l.
      * rewrite lookup_union_r //=. by simplify_map_eq.
    + rewrite lookup_union_l //. by simplify_map_eq.
Qed.

(* Note: different from Rec. alloc not necessarily store 0*)
Definition heap_alloc_h (h : gmap loc val) (l : loc) (v:val) (n : Z) : gmap loc val :=
  (list_to_map ((λ z, (l +ₗ z, v)) <$> seqZ 0 n) ∪ h).

Lemma heap_alloc_h_lookup h n v(l l' : loc):
  l.1 = l'.1 →
  l.2 ≤ l'.2 < l.2 + n →
  heap_alloc_h h l v n !! l' = Some v.
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


Program Definition heap_alloc (h : heap_state) (l : loc) (v:val) (n : Z) : heap_state :=
  Heap (heap_alloc_h h.(h_heap) l v n) ({[l.1]} ∪ h_provs h) _.
Next Obligation.
  move => ?????. move => [? /lookup_union_Some_raw[Hl|[? Hh]]]; apply elem_of_union; [left|right; by apply heap_wf].
  move: Hl => /(elem_of_list_to_map_2 _ _ _)/elem_of_list_fmap. set_solver.
Qed.

Definition heap_alloc_prop (h h':heap_state) (l:loc) (v:val) (n:Z):Prop:=
  n=0 \/ (heap_is_fresh h l /\ h' = heap_alloc h l v n).


(* ** removed*)
(*
Program Definition heap_free (h : heap_state) (l : loc) : heap_state :=
  Heap (filter (λ '(l', v), l'.1 ≠ l.1) h.(h_heap)) h.(h_provs) _.
Next Obligation. move => ???. rewrite map_filter_lookup => -[?/bind_Some[?[??]]]. by apply heap_wf. Qed.
*)

Program Definition heap_merge (h1 h2 : heap_state) : heap_state :=
  Heap (h_heap h1 ∪ h_heap h2) (h_provs h1 ∪ h_provs h2) _.
Next Obligation. move => ???. move => /lookup_union_is_Some[/heap_wf?|/heap_wf?]; set_solver. Qed.


Program Definition heap_restrict (h : heap_state) (P : prov → Prop) `{!∀ x, Decision (P x)} : heap_state :=
  Heap (filter (λ x, P x.1.1) h.(h_heap)) h.(h_provs) _.
Next Obligation. move => ????. rewrite map_filter_lookup => -[?/bind_Some[?[??]]]. by apply heap_wf. Qed.

Program Definition heap_add_provs (h : heap_state) (p : gset prov) : heap_state :=
  Heap (h_heap h) (p ∪ h_provs h) _.
Next Obligation. move => ????. apply: union_subseteq_r. by apply heap_wf. Qed.

(* ** Removed since Lam does not do list allocations*)
(*
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
*)

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

(* ** Removed since Lam does not do list allocations*)
(*
Lemma heap_alloc_list_fresh xs ps h:
  ∃ h', heap_alloc_list xs (heap_fresh_list xs ps h) h h'.
Proof.
  elim: xs ps h. { case; naive_solver. }
  move => a ? IH //= ps h. efeed pose proof IH as Hx. destruct Hx.
  split!; [|done]. by apply heap_fresh_is_fresh.
Qed.
*)

Global Transparent heap_alloc_h. (* TODO: remove this *)
Lemma heap_alive_alloc h l l' v n :
  l.1 = l'.1 →
  l'.2 ≤ l.2 < l'.2 + n →
  heap_alive (heap_alloc h l' v n) l.
Proof.
  destruct l as [p o], l' as [p' o'].
  move => ??. simplify_eq/=. rewrite /heap_alive/=/heap_alloc_h/offset_loc/=.
  apply lookup_union_is_Some. left. apply list_to_map_lookup_is_Some.
  eexists v. apply elem_of_list_fmap. eexists (o - o').
  split. f_equal. f_equal;lia. apply elem_of_seqZ. lia.
Qed.
Global Opaque heap_alloc_h.

Lemma heap_alive_update h l l' v :
  heap_alive h l →
  heap_alive (heap_update h l' v) l.
Proof. move => ?. rewrite /heap_alive/=. by apply lookup_alter_is_Some. Qed.

(* Removed as Lam does not support free*)
(*
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
*)

(* ** Lemma is wrong, since Lam might allocate non-zero containing blocks*)
(*
Lemma h_block_heap_alloc h l v n:
  heap_is_fresh h l →
  (h_block (heap_alloc h l v n) l.1) = zero_block l n.
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
*)

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

Lemma heap_preserved_alloc l v n h m:
  heap_preserved m h →
  m !! l.1 = None →
  heap_preserved m (heap_alloc h l v n).
Proof.
  move => Hp ? l' f /= ?. rewrite lookup_union_r; [by apply Hp|].
  apply not_elem_of_list_to_map_1 => /elem_of_list_fmap[[[??]?] [?/elem_of_list_fmap[?[??]]]]; simplify_eq/=.
Qed.

(* ** Removed*)
(*
Lemma heap_preserved_free l h m:
  heap_preserved m h →
  m !! l.1 = None →
  heap_preserved m (heap_free h l).
Proof.
  move => Hp ? l' f ? /=. rewrite map_filter_lookup. etrans; [|by eapply Hp].
  destruct (h_heap h !! l') => //=. case_option_guard => //. destruct l, l'; naive_solver.
Qed.
*)

Lemma heap_preserved_insert_const p m h:
  heap_preserved (delete p m) h →
  heap_preserved (<[p := h_block h p]> m) h.
Proof.
  move => Hp l f /= /lookup_insert_Some[[??]|[??]]; simplify_eq.
  - rewrite h_block_lookup. by destruct l.
  - apply: Hp => /=. rewrite lookup_delete_Some. done.
Qed.



(** ** fndef *)
Record fndef : Type := {
  fd_args : list string;
  fd_body : expr;
  fd_static : is_static_expr true fd_body;
}.

Lemma fndef_eq fn1 fn2 :
  fn1 = fn2 ↔ fd_args fn1 = fd_args fn2 ∧ fd_body fn1 = fd_body fn2.
Proof. split; [naive_solver|]. destruct fn1, fn2 => /=. move => [??]. subst. f_equal. apply proof_irrel. Qed.


Definition fns_state:= gmap fid fndef.
Definition empty_fns_state: fns_state := ∅.
Definition fns_fresh (fns:fns_state) (f:fid):= f ∉ dom fns.
Definition fns_alive (fns:fns_state) (f:fid):= f ∈ dom fns.
Definition fns_add (fns:fns_state) (f :fid) (v:fndef) := <[f:=v]>fns.
Definition fns_lookup (fns:fns_state) (f:fid) := fns !!f.
Add Printing Constructor fndef.

(** ** state *)
Record lam_state := Lam {
  st_expr : expr;
  st_stack: list string;
  st_heap : heap_state;
  st_fns : fns_state;
}.
Add Printing Constructor lam_state.

Definition lam_init (fns : gmap fid fndef) : lam_state :=
  Lam (Waiting) [] ∅ fns.

(** ** rec_event *)
Inductive lam_ev : Type :=
| ELCall (id : fid) (args: list val) (h:heap_state)
| ELReturn (ret: val) (h:heap_state).

Global Instance lam_ev_inhabited : Inhabited lam_ev := populate (ELReturn inhabitant ∅).

Definition lam_event := io_event lam_ev.


Definition vals_of_event (e : lam_ev) : list val :=
  match e with
  | ELCall f vs h => vs
  | ELReturn v h => [v]
  end.

Definition heap_of_event (e : lam_ev) : heap_state :=
  match e with
  | ELCall f vs h => h
  | ELReturn v h => h
  end.



Definition event_set_vals_heap (e : lam_ev) (vs : list val) (h : heap_state) : lam_ev :=
  match e with
  | ELCall f vs' h' => ELCall f vs h
  | ELReturn v' h' => ELReturn (vs !!! 0%nat) h
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


(* get first component of fns key to produce gset*)
Definition get_string_set_from_fid_set (s:gmap fid fndef):gset string:=
  set_map(λ f:fid, f.1) (dom s).

Lemma insert_get_string_set_unchanged hd m n e: 
  hd ∈ get_string_set_from_fid_set m →
  get_string_set_from_fid_set (fns_add m (hd,n) e) = get_string_set_from_fid_set m .
Proof.
  unfold get_string_set_from_fid_set, fns_add.
  intros. set_solver.
Qed.

Lemma elem_get_string_set_union s m1 m2: 
  (s∈get_string_set_from_fid_set (m1 ∪ m2))↔
  (s∈get_string_set_from_fid_set m1 \/ s∈get_string_set_from_fid_set m2).
Proof.
  unfold get_string_set_from_fid_set, fns_add.
  intros. set_solver. 
Qed.


Lemma lookup_disjoint_none_left m1 m2 key payload: 
get_string_set_from_fid_set m1## get_string_set_from_fid_set m2→key∈get_string_set_from_fid_set m2→
m1!!(key,payload)=None.
Proof.
  intros.  unfold get_string_set_from_fid_set in *. 
  symmetry in H.
  remember (not_elem_of_disjoint _ _ _ H0 H). clear Heqn.
  destruct (m1!!(key,payload)) eqn:K; auto.
  unfold not in n.
  assert (key ∈ ((set_map (λ f : fid, f.1) (dom m1)):gset string)).
  rewrite elem_of_map. exists (key,payload). split!. rewrite elem_of_dom. auto. apply n in H1.
  inversion H1.
Qed.

Lemma lookup_disjoint_none_right m1 m2 key payload: 
get_string_set_from_fid_set m1## get_string_set_from_fid_set m2→key∈get_string_set_from_fid_set m1→
m2!!(key,payload)=None.
Proof.
  intros. unfold get_string_set_from_fid_set in *.
  remember (not_elem_of_disjoint _ _ _ H0 H). clear Heqn.
  destruct (m2!!(key,payload)) eqn:K; auto.
  unfold not in n.
  assert (key ∈ ((set_map (λ f : fid, f.1) (dom m2)):gset string)).
  rewrite elem_of_map. exists (key,payload). split!. rewrite elem_of_dom. auto. apply n in H1.
  inversion H1.
Qed.


Lemma lookup_get_string_disjoint_union_left m1 m2 s o: 
  get_string_set_from_fid_set m1 ## get_string_set_from_fid_set m2 →
  s ∈ get_string_set_from_fid_set m1 →
  (m1 ∪ m2) !! (s, o) = m1 !! (s, o).
Proof.
  intros.
  remember (lookup_disjoint_none_right _ _ _ o H H0).
  clear Heqe.
  apply lookup_union_l; auto.
Qed.


Lemma lookup_get_string_disjoint_union_right m1 m2 s o: 
  get_string_set_from_fid_set m1 ## get_string_set_from_fid_set m2 →
  s ∈ get_string_set_from_fid_set m2 →
  (m1 ∪ m2) !! (s, o) = m2 !! (s, o).
Proof.
  intros.
  remember (lookup_disjoint_none_left _ _ _ o H H0).
  clear Heqe.
  apply lookup_union_r; auto.
Qed.

Lemma get_string_sets_disjoint_implies_sets_disjoint m1 m2:
  get_string_set_from_fid_set m1 ## get_string_set_from_fid_set m2 → 
  m1 ##ₘ m2.
Proof.
  unfold get_string_set_from_fid_set.
  intros.
  apply map_disjoint_dom_2.
  set_solver.
Qed.

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

Inductive head_step : lam_state → option lam_event → (lam_state → Prop) → Prop :=
| BinOpS v1 op v2 lis h fns: (* v1 binop v2*)
  head_step (Lam (BinOp (Val v1) op (Val v2)) lis h fns) None (λ σ',
    ∃ v, eval_binop op v1 v2 = Some v ∧ σ' = Lam (Val v) lis h fns)
| NewRefS v v' l lis h h' fns: (* ref v n *)
  (∀n, v' = ValNum n →heap_alloc_prop h h' l v n) →
  head_step (Lam (NewRef (Val v) (Val v')) lis h fns) None 
  (λ σ', ∃n, ValNum n = v' /\n>0 /\ σ' = Lam (Val (ValLoc l)) lis h' fns) 
| LoadS v lis h fns: (* !v *)
  head_step (Lam (Load (Val v)) lis h fns) None 
  (λ σ', ∃l v', v = ValLoc l ∧ h.(h_heap)!!l = Some v' ∧ σ' = Lam (Val v') lis h fns)
| StoreS v v' lis h fns: (* v1 <- v2 *)
  head_step (Lam (Store (Val v) (Val v')) lis h fns) None 
  (λ σ', ∃l, ValLoc l = v ∧ heap_alive h l ∧ σ'= Lam (Val v') lis (heap_update h l v') fns)
| IfS v e1 e2 lis h fns: (* if v then e1 else e2 *)
  head_step (Lam (If (Val v) e1 e2) lis h fns) None 
  (λ σ', ∃ b, ValBool b = v ∧ σ' = Lam (if b then e1 else e2) lis h fns)
| LetS x v e lis h fns: (* let x = v in e *)
  head_step (Lam (LetE x (Val v) e) lis h fns) None 
  (λ σ', σ'= Lam (subst x v e) lis h fns)
| FixS f args e n hd tl h fns: (* fix f [args] = e *)
  let updated_body := subst f (ValFid (hd,Some n)) e in
  fns !! (hd, Some n)= None → 
  head_step (Lam (FixE f args e) (hd::tl) h  fns) None 
  (λ σ', ∃ H, let fn_entry := {|fd_args:= args; fd_body:= updated_body;fd_static:= H|} in 
  σ' = Lam (Val (ValFid (hd, Some n))) (hd::tl) h (fns_add fns (hd, Some n) fn_entry) ) 
| VarS x lis h fns: (* unbound variable *)
  head_step (Lam (Var x) lis h fns) None 
  (λ σ', False)
| RecvCallS f args h' lis h fns: (* Call?(f, args, h') *)
  f.1∈get_string_set_from_fid_set fns →
  head_step (Lam Waiting lis h fns) (Some (Incoming, ELCall f args h'))
  (λ σ', 
  σ' = Lam (ReturnExt (App (Val (ValFid f)) (Val <$> args))) lis h' fns)
| CallInternalS f args lis h fns: (* App (Val(ValFid f)) (Val <$> args) *)
  f.1 ∈ get_string_set_from_fid_set fns→
  head_step (Lam (App (Val(ValFid f)) (Val <$> args)) lis h fns) None
  (λ σ', ∃fn, fns!!f = Some fn /\ length args = length fn.(fd_args) ∧ 
    σ' = Lam (ReturnInt (subst_l fn.(fd_args) args fn.(fd_body))) ((fst f)::lis) h fns)
| CallExternalS f args lis h fns: (* Call! f args h*)
  f.1∉get_string_set_from_fid_set fns →
  head_step (Lam (App (Val (ValFid f)) (Val <$> args)) lis h fns) (Some (Outgoing, ELCall f args h)) 
  (λ σ', σ' = Lam (Waiting) lis h fns)
| ReturnInternalS v hd tl h fns: (* returning internal, i.e. popping the stack*)
  head_step (Lam (ReturnInt (Val v)) (hd::tl) h fns) None
  (λ σ',  σ' = Lam (Val v) tl h fns)
| ReturnExternalS v s h fns: (* Ret!(v, h)*)
  head_step (Lam (ReturnExt (Val v)) s h fns) (Some (Outgoing, ELReturn v h))
  (λ σ',  σ' = Lam (Waiting) s h fns)
| RecvReturnS v h' hd tl h fns: (* Ret?(v, h')*) (* should s be hd::tl?*)
  head_step (Lam (Waiting) (hd::tl) h fns) (Some (Incoming, ELReturn v h'))
  (λ σ', σ' = Lam (Val v) (hd::tl) h' fns)
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

Lemma val_head_stuck e lis h fns κ Pσ : head_step (Lam e lis h fns) κ Pσ → to_val e = None.
Proof. by inversion 1. Qed.

Lemma head_ctx_step_val Ki e lis h fns κ Pσ :
  head_step (Lam (expr_fill_item Ki e) lis h fns) κ Pσ → is_Some (to_val e).
Proof. destruct Ki; inversion 1; simplify_eq => //; by apply: list_expr_val_inv. Qed.

Lemma head_fill_step_val K e lis h fns κ Pσ :
  to_val e = None →
  head_step (Lam (expr_fill K e) lis h fns) κ Pσ →
  K = [].
Proof.
  elim/rev_ind: K => //=????. rewrite expr_fill_app /= => /head_ctx_step_val /fill_val[??].
  naive_solver.
Qed.

Lemma step_by_val K K' e1' e1_redex lis h fns κ Pσ :
  expr_fill K e1' = expr_fill K' e1_redex →
  to_val e1' = None →
  head_step (Lam e1_redex lis h fns) κ Pσ →
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

Inductive prim_step : lam_state → option lam_event → (lam_state → Prop) → Prop :=
  Ectx_step e K e' lis h fns κ Pσ:
    e = expr_fill K e' →
    head_step (Lam e' lis h fns) κ Pσ →
    prim_step (Lam e lis h fns) κ (λ σ, ∃ e2 lis2 h2 fns2, Pσ (Lam e2 lis2 h2 fns2) ∧ σ = Lam (expr_fill K e2) lis2 h2 fns2).

Lemma prim_step_inv K e lis h fns κ Pσ:
  prim_step (Lam (expr_fill K e) lis h fns) κ Pσ →
  to_val e = None →
  ∃ K' e' Pσ', e = expr_fill K' e' ∧ head_step (Lam e' lis h fns) κ Pσ' ∧
      Pσ = (λ σ, ∃ e2 lis2 h2 fns2, Pσ' (Lam e2 lis2 h2 fns2) ∧ σ = Lam (expr_fill (K' ++ K) e2) lis2 h2 fns2).
Proof.
  inversion 1; simplify_eq => eNone.
  revert select (expr_fill _ _ = expr_fill _ _) => Heq. move: (Heq) => /step_by_val Hg.
  apply (Hg lis h fns κ Pσ0 eNone) in H7 as M. 
  destruct M. exists x, e', Pσ0. subst.
  split.
  rewrite expr_fill_app in Heq. naive_solver. split;naive_solver.
Qed.
  

Lemma prim_step_inv_head K e lis h fns κ Pσ:
  prim_step (Lam (expr_fill K e) lis h fns) κ Pσ →
  sub_redexes_are_values e →
  to_val e = None →
  ∃ Pσ', head_step (Lam e lis h fns) κ Pσ' ∧
      Pσ = (λ σ, ∃ e2 lis2 h2 fns2, Pσ' (Lam e2 lis2 h2 fns2) ∧ σ = Lam (expr_fill K e2) lis2 h2 fns2).
Proof.
  move => Hprim Hsub ?.
  move: Hprim => /prim_step_inv[|?[?[?[?[Hstep ?]]]]]. { done. } subst.
  have ->:= Hsub _ _ ltac:(done). 2: { by apply: val_head_stuck. }
  naive_solver.
Qed.

Definition lam_trans := ModTrans  prim_step.
Definition lam_mod (fns : gmap fid fndef) := Mod lam_trans (lam_init fns).

(* ** RHS set is singleton or empty*)
Global Instance lam_vis_no_all: VisNoAng lam_trans.
Proof.
move => *. inv_all @m_step  ; inversion H0; subst; inv_all head_step ; naive_solver.
Qed.

(** * Deeply embedded static expressions  *)
Inductive static_val := | StaticValNum (z : Z) | StaticValBool (b : bool) | StaticValFid (f:string).
Global Instance static_val_eqdec : EqDecision static_val.
Proof. solve_decision. Qed.

Definition static_val_to_val (v : static_val) : val :=
  match v with
  | StaticValNum z => ValNum z
  | StaticValBool b => ValBool b
  | StaticValFid f => ValFid (f,None)
  end.

Definition val_to_static_val (v : val) : static_val :=
  match v with
  | ValNum z => StaticValNum z
  | ValBool b => StaticValBool b
  | ValFid (f,None) => StaticValFid f
  | _  => StaticValNum 0
  end.

Section static_expr.
Local Unset Elimination Schemes.
Inductive static_expr : Set :=
| SVar (v : string)
| SVal (v : static_val)
| SBinOp (e1 : static_expr) (o : binop) (e2 : static_expr)
| SNewRef (e1 :static_expr) (e2 : static_expr)
| SLoad (e : static_expr)
| SStore (e1 e2 : static_expr)
| SIf (e e1 e2 : static_expr)
| SLetE (v : string) (e1 e2 : static_expr)
| SFixE (f:string) (args: list string) (e:static_expr)
| SApp (f: static_expr) (args : list static_expr)
.

End static_expr.
Lemma static_expr_ind (P : static_expr → Prop) :
  (∀ (x : string), P (SVar x)) →
  (∀ (v : static_val), P (SVal v)) →
  (∀ (e1 : static_expr) (op : binop) (e2 : static_expr), P e1 → P e2 → P (SBinOp e1 op e2)) →
  (∀ (e1 e2 : static_expr), P e1 → P e2 → P (SNewRef e1 e2)) →
  (∀ (e : static_expr), P e → P (SLoad e)) →
  (∀ (e1 e2 : static_expr), P e1 → P e2 → P (SStore e1 e2)) →
  (∀ (e1 e2 e3 : static_expr), P e1 → P e2 → P e3 → P (SIf e1 e2 e3)) →
  (∀ (v : string) (e1 e2 : static_expr), P e1 → P e2 → P (SLetE v e1 e2)) →
  (∀ (f:string) (args: list string) (e:static_expr), P e → P (SFixE f args e)) →
  (∀ (f : static_expr) (args : list static_expr), P f → Forall P args → P (SApp f args)) →
  ∀ (e : static_expr), P e.
Proof.
  move => *. generalize dependent P => P. match goal with | e : static_expr |- _ => revert e end.
  fix FIX 1. move => [ ^e] => ????????? Hcall.
  10: { apply Hcall. by apply:FIX. apply Forall_true => ?. by apply: FIX. }
  all: auto.
Qed.

Fixpoint static_expr_to_expr (e : static_expr) : expr :=
  match e with
  | SVar v => Var v
  | SVal v => Val (static_val_to_val v)
  | SBinOp e1 o e2 => BinOp (static_expr_to_expr e1) o (static_expr_to_expr e2)
  | SNewRef e1 e2 => NewRef (static_expr_to_expr e1) (static_expr_to_expr e2)
  | SLoad e => Load (static_expr_to_expr e)
  | SStore e1 e2 => Store (static_expr_to_expr e1) (static_expr_to_expr e2)
  | SIf e e1 e2 => If (static_expr_to_expr e) (static_expr_to_expr e1) (static_expr_to_expr e2)
  | SLetE v e1 e2 => LetE v (static_expr_to_expr e1) (static_expr_to_expr e2)
  | SFixE f args e => FixE f args (static_expr_to_expr e)
  | SApp f args => App (static_expr_to_expr f) (static_expr_to_expr <$> args)
  end.

Lemma static_expr_is_static e :
  is_static_expr false  (static_expr_to_expr e).
Proof.
  elim: e => //=; try naive_solver.
  - case; auto. 
  - move => ? ? ?. elim => //=; naive_solver.
Qed.

Fixpoint expr_to_static_expr (e : expr) : static_expr :=
  match e with
  | Var v => SVar v
  | Val v => SVal (val_to_static_val v)
  | BinOp e1 o e2 => SBinOp (expr_to_static_expr e1) o (expr_to_static_expr e2)
  | NewRef e1 e2 => SNewRef (expr_to_static_expr e1) (expr_to_static_expr e2)
  | Load e => SLoad (expr_to_static_expr e)
  | Store e1 e2 => SStore (expr_to_static_expr e1) (expr_to_static_expr e2)
  | If e e1 e2 => SIf (expr_to_static_expr e) (expr_to_static_expr e1) (expr_to_static_expr e2)
  | LetE v e1 e2 => SLetE v (expr_to_static_expr e1) (expr_to_static_expr e2)
  | FixE f args e => SFixE f args (expr_to_static_expr e)
  | App f args => SApp (expr_to_static_expr f) (expr_to_static_expr <$> args)
  | _ => SVar ""
  end.

Lemma static_expr_to_expr_to_static_expr e :
  is_static_expr false e →
  static_expr_to_expr (expr_to_static_expr e) = e.
Proof.
  elim: e => //=; try (move => *; f_equal; naive_solver).
  - intros[]; auto; simpl. naive_solver. destruct id eqn:K; destruct o; naive_solver.
  - move => f args Hall Hargs. f_equal. 
  intros. apply andb_prop_elim in H. destruct H.
  f_equal. naive_solver. rewrite -list_fmap_compose.
  (* TODO improve this proof*)
  rewrite forallb_True in H0.
  apply (Forall_implication _ (λ H:expr ,static_expr_to_expr (expr_to_static_expr H) = H)  _) in H0; auto.
  rewrite <-list_fmap_id.
  apply Forall_fmap_ext_1.
  remember (@Forall_iff expr (λ x : expr, static_expr_to_expr (expr_to_static_expr x) = x)
  args (λ x : expr, (static_expr_to_expr ∘ expr_to_static_expr) x = id x)) as L.
  naive_solver.
  Qed.
  
Record static_fndef : Type := {
  sfd_args : list string;
  sfd_body : static_expr;
}.

Lemma static_expr_monotone e: is_static_expr false e → is_static_expr true e.
Proof.
  induction e;try  naive_solver. destruct v;auto. destruct id,o;auto.
  simpl. intros. induction args. simpl. naive_solver. simpl. simpl in H0. inversion H. naive_solver.
Qed.
  
Program Definition static_fndef_to_fndef (fn : static_fndef) : fndef := {|
   fd_args := fn.(sfd_args);
   fd_body := static_expr_to_expr fn.(sfd_body);
|}.
Next Obligation. move => ?. apply static_expr_monotone. apply static_expr_is_static. Qed.

Definition fndef_to_static_fndef (fn : fndef) : static_fndef := {|
   sfd_args := fn.(fd_args);
   sfd_body := expr_to_static_expr fn.(fd_body);
|}.

Definition lam_static_init (fns : gmap fid static_fndef) : lam_state :=
  lam_init (static_fndef_to_fndef <$> fns).

Definition lam_static_mod (fns : gmap fid static_fndef) := Mod lam_trans (lam_static_init fns).

(* **Lemma removed since incorrect! Due to changes in static proposition in fndef*)
(*
Lemma static_fndef_to_fndef_to_static_fndef fn :
  static_fndef_to_fndef (fndef_to_static_fndef fn) = fn.
Proof. apply fndef_eq. split_and!; [done..|] => /=. apply static_expr_to_expr_to_static_expr. apply fd_static. Qed.
*)

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


(** ** LamExprFill *)
Class LamExprFill (e : expr) (K : list expr_ectx) (e' : expr) := {
    lam_expr_fill_proof : e = expr_fill K e'
}.
Global Hint Mode LamExprFill ! - - : typeclass_instances.

Lemma lam_expr_fill_end e :
  LamExprFill e [] e.
Proof. done. Qed.
Global Hint Resolve lam_expr_fill_end | 100 : typeclass_instances.

Lemma lam_expr_fill_expr_fill e K K' e' `{!LamExprFill e K' e'} :
  LamExprFill (expr_fill K e) (K' ++ K) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply lam_expr_fill_proof. Qed.
Global Hint Resolve lam_expr_fill_expr_fill : typeclass_instances.

Lemma lam_expr_fill_BinOpL e1 e2 op K e' `{!LamExprFill e1 K e'} :
LamExprFill (BinOp e1 op e2) (K ++ [BinOpLCtx op e2]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply lam_expr_fill_proof. Qed.
Global Hint Resolve lam_expr_fill_BinOpL : typeclass_instances.

Lemma lam_expr_fill_BinOpR (v1 : val) e2 op K e' `{!LamExprFill e2 K e'} :
  LamExprFill (BinOp (Val v1) op e2) (K ++ [BinOpRCtx v1 op]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply lam_expr_fill_proof. Qed.
Global Hint Resolve lam_expr_fill_BinOpR : typeclass_instances.

Lemma lam_expr_fill_NewRefL e1 e2 K e' `{!LamExprFill e1 K e'} :
  LamExprFill (NewRef e1 e2) (K ++ [NewRefLCtx e2]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply lam_expr_fill_proof. Qed.
Global Hint Resolve lam_expr_fill_NewRefL : typeclass_instances.

Lemma lam_expr_fill_NewRefR (v1 : val) e2 K e' `{!LamExprFill e2 K e'} :
  LamExprFill (NewRef (Val v1) e2) (K ++ [NewRefRCtx v1]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply lam_expr_fill_proof. Qed.
Global Hint Resolve lam_expr_fill_NewRefR : typeclass_instances.

Lemma lam_expr_fill_Load e1 K e' `{!LamExprFill e1 K e'} :
  LamExprFill (Load e1) (K ++ [LoadCtx]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply lam_expr_fill_proof. Qed.
Global Hint Resolve lam_expr_fill_Load : typeclass_instances.

Lemma lam_expr_fill_StoreL e1 e2 K e' `{!LamExprFill e1 K e'} :
  LamExprFill (Store e1 e2) (K ++ [StoreLCtx e2]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply lam_expr_fill_proof. Qed.
Global Hint Resolve lam_expr_fill_StoreL : typeclass_instances.

Lemma lam_expr_fill_StoreR (v1 : val) e2 K e' `{!LamExprFill e2 K e'} :
  LamExprFill (Store (Val v1) e2) (K ++ [StoreRCtx v1]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply lam_expr_fill_proof. Qed.
Global Hint Resolve lam_expr_fill_StoreR : typeclass_instances.

Lemma lam_expr_fill_If e e2 e3 K e' `{!LamExprFill e K e'} :
  LamExprFill (If e e2 e3) (K ++ [IfCtx e2 e3]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply lam_expr_fill_proof. Qed.
Global Hint Resolve lam_expr_fill_If : typeclass_instances.

Lemma lam_expr_fill_LetE v e1 e2 K e' `{!LamExprFill e1 K e'} :
  LamExprFill (LetE v e1 e2) (K ++ [LetECtx v e2]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply lam_expr_fill_proof. Qed.
Global Hint Resolve lam_expr_fill_LetE : typeclass_instances.

Lemma lam_expr_fill_AppL e1 e2 K e' `{!LamExprFill e1 K e'} :
  LamExprFill (App e1 e2) (K ++ [AppLCtx e2]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply lam_expr_fill_proof. Qed.
Global Hint Resolve lam_expr_fill_AppL : typeclass_instances.

Lemma lam_expr_fill_AppR e K e' f es vs es' `{!AsVals es vs (Some (e, es')) } `{!LamExprFill e K e'} :
  LamExprFill (App (Val f) es) (K ++ [AppRCtx f vs es']) e'.
Proof.
  destruct AsVals0, LamExprFill0. subst.
  constructor => /=. rewrite expr_fill_app /=. done.
Qed.
Global Hint Resolve lam_expr_fill_AppR : typeclass_instances.

Lemma lam_expr_fill_ReturnExt e K e' `{!LamExprFill e K e'} :
  LamExprFill (ReturnExt e) (K ++ [ReturnExtCtx]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply lam_expr_fill_proof. Qed.
Global Hint Resolve lam_expr_fill_ReturnExt : typeclass_instances.

Lemma lam_expr_fill_ReturnInt e K e' `{!LamExprFill e K e'} :
  LamExprFill (ReturnInt e) (K ++ [ReturnIntCtx]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply lam_expr_fill_proof. Qed.
Global Hint Resolve lam_expr_fill_ReturnInt : typeclass_instances.

(** ** instances *)

(* This pattern of using LamExprFill at each rule is quite expensive
but we don't care at the moment. *)
(* ** TODO recheck all angelic and demonic non-determinism,
especially those that have to do with the heap
TODO: newrefi newrefs fixi fixs apps*)

(*Var_i not needed since this is undefined behavior on implementation side. 
Only an undefined behavior specification can be refined by it*)
Lemma lam_step_Var_s fns s h e K v `{!LamExprFill e K (Var v)}:
  TStepS lam_trans (Lam e s h fns) (λ G, G None (λ G', True)).
Proof.
  destruct LamExprFill0; subst.
  constructor. intros.
  eexists _, _.  split; [done|] => /= ??.
  eapply steps_spec_step_end. econs. done. econs. intros ?  ?. simpl in H0. naive_solver.
Qed.
Global Hint Resolve lam_step_Var_s : typeclass_instances.

Lemma lam_step_Binop_i fns s h e K (v1 v2 : val) op `{!LamExprFill e K (BinOp (Val v1) op (Val v2))}:
  TStepI lam_trans (Lam e  s h fns) (λ G,
    (G true None (λ G', ∃ v', eval_binop op v1 v2 = Some v' ∧ G' (Lam (expr_fill K (Val v')) s h fns)))).
Proof.
  destruct LamExprFill0; subst.
  econs. intros. apply steps_impl_step_end. intros. apply prim_step_inv_head in H0. destruct H0 as [?[??]]. subst.
  inversion H0; simplify_eq. naive_solver. solve_sub_redexes_are_values. reflexivity.
Qed.
Global Hint Resolve lam_step_Binop_i | 10 : typeclass_instances.

Lemma lam_step_Binop_s fns s h e K  (v1 v2 : val) op `{!LamExprFill e K (BinOp (Val v1) op (Val v2))}:
  TStepS lam_trans (Lam e  s h fns) (λ G,
    (G None (λ G', ∀ v', eval_binop op v1 v2 = Some v' → G' (Lam (expr_fill K (Val v')) s h fns)))).
Proof.
  destruct LamExprFill0; subst. constructor. intros.  split!. exact H.
  intros. eapply steps_spec_step_end. econs. auto. constructor. intros.
  naive_solver.
Qed.
Global Hint Resolve lam_step_Binop_s | 10 : typeclass_instances.

(* can be removed?*)
Lemma lam_step_BinopAdd_i fns s h e K n1 n2 `{!LamExprFill e K (BinOp (Val (ValNum n1)) AddOp (Val (ValNum n2)))}:
  TStepI lam_trans (Lam e s h fns) (λ G,
    (G true None (λ G', G' (Lam (expr_fill K (Val (ValNum (n1 + n2)))) s h fns)))).
Proof.
  destruct LamExprFill0; subst.
  constructor. intros. tstep_i. intros. naive_solver.
Qed. 
Global Hint Resolve lam_step_BinopAdd_i | 5 : typeclass_instances.

Lemma lam_step_BinopAdd_s fns s h e K (v1 v2 : val) `{!LamExprFill e K (BinOp (Val v1) AddOp (Val v2))}:
  TStepS lam_trans (Lam e s h fns) (λ G,
    (G None (λ G', ∀ n1 n2, v1 = ValNum n1 → v2 = ValNum n2 → G' (Lam (expr_fill K (Val (ValNum (n1 + n2)))) s h fns)))).
Proof.
  destruct LamExprFill0; subst.
  constructor =>  ? HG. split!. exact HG. intros. tstep_s. split! => ? /bind_Some[?[? /bind_Some[?[??]]]].
  destruct v1,v2; naive_solver.
Qed. 
Global Hint Resolve lam_step_BinopAdd_s | 5 : typeclass_instances.

Lemma lam_step_BinopOffset_i fns s h e K l z `{!LamExprFill e K (BinOp (Val (ValLoc l)) OffsetOp (Val (ValNum z)))}:
  TStepI lam_trans (Lam e s h fns) (λ G,
    (G true None (λ G', G' (Lam (expr_fill K (Val (ValLoc (l +ₗ z)))) s h fns)))).
Proof.
  destruct LamExprFill0; subst.
  constructor. intros. tstep_i. intros. split!. naive_solver.
Qed. 
Global Hint Resolve lam_step_BinopOffset_i | 5 : typeclass_instances.

Lemma lam_step_BinopOffset_s fns s h e K (v1 v2 : val) `{!LamExprFill e K (BinOp (Val v1) OffsetOp (Val v2))}:
  TStepS lam_trans (Lam e s h fns) (λ G,
    (G None (λ G', ∀ l z, v1 = ValLoc l → v2 = ValNum z → G' (Lam (expr_fill K (Val (ValLoc(l+ₗz)))) s h fns)))).
Proof.
  destruct LamExprFill0; subst.
  constructor =>  ? HG. split!. exact HG. intros. tstep_s. split! => ? /bind_Some[?[? /bind_Some[?[??]]]].
  destruct v1,v2; naive_solver.
Qed. 
Global Hint Resolve lam_step_BinopOffset_i | 5 : typeclass_instances.

(* ** TO VERIFY*)
Lemma lam_step_Newref_i fns s h e K v n `{!LamExprFill e K (NewRef (Val v)  (Val (ValNum n)))}:
  TStepI lam_trans (Lam e  s h fns) (λ G, ∀l h', heap_alloc_prop h h' l v n→
  (G true None (λ G',n>0/\ ( G' (Lam (expr_fill K (Val (ValLoc l))) s h' fns))))).
Proof.
  destruct LamExprFill0; subst.
  econs. intros. apply steps_impl_step_end. intros. apply prim_step_inv_head in H0. destruct H0 as [?[??]]. subst.
  inversion H0; simplify_eq. 
  eexists true,  _. 
  split!. apply H. apply H8. reflexivity.  intros. simpl in H1. destruct!. naive_solver.   
  solve_sub_redexes_are_values. reflexivity. 
Qed.
Global Hint Resolve lam_step_Newref_i | 10 : typeclass_instances.


Lemma lam_step_Newref_s fns s h e K v v' `{!LamExprFill e K (NewRef (Val v)  (Val v'))}:
  TStepS lam_trans (Lam e s h fns) (λ G, (G None (λ G', ∃ l h', 
  (∀n, ValNum n = v'→heap_alloc_prop h h' l v n/\(n>0→ G' (Lam (expr_fill K (Val (ValLoc l))) s h' fns)))))).
Proof.
  destruct LamExprFill0; subst.
  econs. intros. destruct!.   split!; [done|]. move => ? /=. intros. destruct!. eapply steps_spec_step_end. econs. 
  done. econs. intros. symmetry in H1. apply H0 in H1. destruct!. exact H2. naive_solver. 
Qed. 
Global Hint Resolve lam_step_Newref_s | 10 : typeclass_instances.


Lemma lam_step_Load_i fns s h e K l `{!LamExprFill e K (Load (Val (ValLoc l)))}:
  TStepI lam_trans (Lam e s h fns) (λ G,
    (G true None (λ G', ∃ v', h.(h_heap) !! l = Some v' ∧ G' (Lam (expr_fill K (Val v')) s h fns)))).
Proof.
  destruct LamExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  naive_solver.
Qed.
Global Hint Resolve lam_step_Load_i : typeclass_instances.

Lemma lam_step_Load_s fns s h e K v `{!LamExprFill e K (Load (Val v))}:
  TStepS lam_trans (Lam e s h fns) (λ G,
    (G None (λ G', ∀ l v', v = ValLoc l → h.(h_heap) !! l = Some v' → G' (Lam (expr_fill K (Val v'))  s h fns)))).
Proof.
  destruct LamExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct!. naive_solver.
Qed.
Global Hint Resolve lam_step_Load_s : typeclass_instances.

Lemma lam_step_Store_i fns s h e K l v `{!LamExprFill e K (Store (Val (ValLoc l)) (Val v))}:
  TStepI lam_trans (Lam e s h fns) (λ G,
    (G true None (λ G', heap_alive h l ∧ G' (Lam (expr_fill K (Val v)) s (heap_update h l v) fns)))).
Proof.
  destruct LamExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  naive_solver.
Qed.
Global Hint Resolve lam_step_Store_i : typeclass_instances.

Lemma lam_step_Store_s fns s h e K v1 v `{!LamExprFill e K (Store (Val v1) (Val v))}:
  TStepS lam_trans (Lam e  s h fns) (λ G,
    (G None (λ G', ∀ l, v1 = ValLoc l → heap_alive h l → G'
      (Lam (expr_fill K (Val v)) s (heap_update h l v) fns)))).
Proof.
  destruct LamExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct!. naive_solver.
Qed.
Global Hint Resolve lam_step_Store_s : typeclass_instances.

Lemma lam_step_If_i fns s h b K e1 e2 `{!LamExprFill e K (If (Val (ValBool b)) e1 e2)}:
  TStepI lam_trans (Lam e s h fns) (λ G,
    (G true None (λ G', G' (Lam (expr_fill K (if b then e1 else e2)) s h fns)))).
Proof.
  destruct LamExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  naive_solver.
Qed.
Global Hint Resolve lam_step_If_i | 10 : typeclass_instances.

Lemma lam_step_If_s fns s h v K e1 e2 `{!LamExprFill e K (If (Val v) e1 e2)}:
  TStepS lam_trans (Lam e s h fns) (λ G,
    (G None (λ G', ∀ b, v = ValBool b → G' (Lam (expr_fill K (if b then e1 else e2)) s h fns)))).
Proof.
  destruct LamExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct!. naive_solver.
Qed.
Global Hint Resolve lam_step_If_s | 10 : typeclass_instances.

Lemma lam_step_LetE_i fns s h e K x v e1 `{!LamExprFill e K (LetE x (Val v) e1)}:
  TStepI lam_trans (Lam e s h fns) (λ G,
    (G true None (λ G', G' (Lam (expr_fill K (subst x v e1)) s h fns)))).
Proof.
  destruct LamExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  naive_solver.
Qed.
Global Hint Resolve lam_step_LetE_i : typeclass_instances.

Lemma lam_step_LetE_s fns s h e K x v e1 `{!LamExprFill e K (LetE x (Val v) e1)}:
  TStepS lam_trans (Lam e s h fns) (λ G,
    (G None (λ G', G' (Lam (expr_fill K (subst x v e1)) s h fns)))).
Proof.
  destruct LamExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct!. naive_solver.
Qed.
Global Hint Resolve lam_step_LetE_s : typeclass_instances.

(* ** Not sure*)

Lemma lam_step_Fix_i fns hd tl h e K f args body`{!LamExprFill e K (FixE f args body)}:
  TStepI lam_trans (Lam e  (hd::tl) h fns) (λ G, ∀ n, 
  fns!!(hd,Some n)= None→ (G true None (λ G',  ∃ H,
  let updated_body := subst f (ValFid (hd,Some n)) body in
  let fn_entry := {|fd_args:= args; fd_body:= updated_body;fd_static:= H|} in 
  G' (Lam (expr_fill K (Val (ValFid (hd,Some n)))) (hd::tl) h 
  (fns_add fns (hd, Some n) fn_entry) )))).
Proof.
  destruct LamExprFill0; subst.
  econs. intros. apply steps_impl_step_end. intros. apply prim_step_inv_head in H0. destruct H0 as [?[??]]. subst.
  inversion H0; simplify_eq. naive_solver. solve_sub_redexes_are_values. reflexivity. 
Qed.
Global Hint Resolve lam_step_Fix_i | 10 : typeclass_instances.

Lemma lam_step_Fix_s fns hd tl h e K f args body`{!LamExprFill e K (FixE f args body)}:
  TStepS lam_trans (Lam e  (hd::tl) h fns) (λ G,  (G None 
  (λ G',  ∃n, fns!!(hd,Some n)= None/\∀ H, 
  let updated_body := subst f (ValFid (hd,Some n)) body in
  let fn_entry := {|fd_args:= args; fd_body:= updated_body;fd_static:= H|} in 
  G' (Lam (expr_fill K (Val (ValFid (hd,Some n)))) (hd::tl) h 
  (fns_add fns (hd, Some n) fn_entry) )))).
Proof.
  destruct LamExprFill0; subst.
  econs. intros.  split!; [done|].  intros. simpl in H0. destruct H0.
  eapply steps_spec_step_end. econs. 
  done. econs. destruct H0.  done. intros. naive_solver.
Qed. 
Global Hint Resolve lam_step_Fix_s | 10 : typeclass_instances.


Lemma lam_step_App_i fns s h e K f vs es `{!LamExprFill e K (App (Val (ValFid f)) es)} `{!AsVals es vs None}:
  TStepI lam_trans (Lam e s h fns) (λ G,
          (f.1 ∈get_string_set_from_fid_set fns → G true None (λ G', ∃ fn, fns !! f = Some fn /\ length vs = length fn.(fd_args) ∧
            G' (Lam (expr_fill (ReturnIntCtx::K) ( (subst_l fn.(fd_args) vs fn.(fd_body)))) (f.1::s) h fns))) ∧
          (f.1 ∉ get_string_set_from_fid_set fns → G true (Some (Outgoing, ELCall  f vs h)) (λ G',
            G' (Lam (expr_fill K Waiting) s  h fns)))
    ).
Proof.
  destruct AsVals0, LamExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[Hstep ?]]. {
    apply sub_redexes_are_values_item; case; try naive_solver.
    move => /= ??? e' [_ Heq]. rewrite right_id_L in Heq. by apply: list_expr_val_inv.
  } { done. } subst.
  rewrite right_id_L in Hstep. inv Hstep.
  - destruct!; split!. auto. auto. simpl. intros. destruct!.  naive_solver.
  - naive_solver.
Qed.
Global Hint Resolve lam_step_App_i : typeclass_instances.

(* Not sure*)
(* TODO*)
Lemma lam_step_App_s fns s h e K v  vs `{!LamExprFill e K (App (Val v) es)} `{!AsVals es vs None}:
  TStepS lam_trans (Lam e s h fns) (λ G,( ∃f , ValFid f = v /\f.1 ∈get_string_set_from_fid_set fns /\ 
  G  None (λ G',  (∀ fn, fns !! f = Some fn →length vs = length fn.(fd_args) →
  G' (Lam (expr_fill (ReturnIntCtx:: K) ((subst_l fn.(fd_args) vs fn.(fd_body)))) (f.1::s) h fns)))) \/
  ∃ f, G  (Some (Outgoing, ELCall  f vs h)) (λ G', 
  ValFid f = v /\ f.1 ∉ get_string_set_from_fid_set fns/\ G' (Lam (expr_fill K Waiting) s  h fns))).
Proof.
  destruct AsVals0, LamExprFill0; subst. rewrite right_id_L.
  econs. intros. destruct!. eexists _,_ . split. exact H2.
  intros. simpl in H0. eapply steps_spec_step_end. 
  econs. naive_solver.  apply CallInternalS. exact H. intros. simpl in H1.
  destruct!.  auto.
  eexists _,_. split. exact H. intros. destruct H0 as [?[??]].
  subst. eapply steps_spec_step_end. econs. auto. econs. auto. 
  intros. naive_solver. 
Qed.
Global Hint Resolve lam_step_App_s : typeclass_instances.


Lemma lam_step_Waiting_i fns s h K e `{!LamExprFill e K Waiting}:
  TStepI lam_trans (Lam e s h fns) (λ G,
    (∀ f vs h' , f.1∈get_string_set_from_fid_set fns → 
      G true (Some (Incoming, ELCall f vs h')) (λ G', 
      G' (Lam (expr_fill K (ReturnExt (App (Val (ValFid f)) (Val<$> vs)))) s h' fns))) ∧
       ∀ v h',  (∃ hd tl, hd::tl= s)→G true (Some (Incoming, ELReturn v h')) (λ G', G' (Lam (expr_fill K (Val v)) s h' fns))
   ).
Proof.
  destruct LamExprFill0; subst.
  constructor => G HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  - naive_solver.
  - naive_solver. 
Qed.
Global Hint Resolve lam_step_Waiting_i : typeclass_instances.

Lemma lam_step_Waiting_s fns s h e K `{!LamExprFill e K Waiting}:
  TStepS lam_trans (Lam e s h fns) (λ G,
    (∃ f vs h' , f.1∈get_string_set_from_fid_set fns∧
      G (Some (Incoming, ELCall f vs h')) (λ G',  (
      G' (Lam (expr_fill (ReturnExtCtx:: K) (App (Val (ValFid f)) (Val<$> vs))) s h' fns)))) ∨
          ∃ v h',  (∃ hd tl, hd::tl= s)/\ G (Some (Incoming, ELReturn v h')) (λ G', G' (Lam (expr_fill K (Val v)) s h' fns))
   ).
Proof.
  destruct LamExprFill0; subst.
  constructor => ? HG. destruct!. split!. exact H0. intros.
  eapply steps_spec_step_end. econs. auto. econs. auto. 
  simpl. intros. naive_solver.
  eexists _,_. split. naive_solver. eauto.
  intros. eapply steps_spec_step_end. econs. auto. econs. naive_solver. 
Qed.
Global Hint Resolve lam_step_Waiting_s : typeclass_instances.


Lemma rec_step_ReturnExt_i fns s h e K  (v : val) `{!LamExprFill e K (ReturnExt (Val v))}:
  TStepI lam_trans (Lam e s h fns) (λ G,
    (G true (Some (Outgoing, ELReturn v h)) (λ G', G' (Lam (expr_fill K Waiting) s h fns)))).
Proof.
  destruct LamExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  naive_solver.
Qed.
Global Hint Resolve rec_step_ReturnExt_i : typeclass_instances.


Lemma lam_step_ReturnExt_s fns s h e K  (v : val) `{!LamExprFill e K (ReturnExt (Val v))}:
  TStepS lam_trans (Lam e s h fns) (λ G,
    (G (Some (Outgoing, ELReturn v h)) (λ G', G' (Lam (expr_fill K Waiting) s h fns)))).
Proof.
  destruct LamExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct!. done.
Qed.
Global Hint Resolve lam_step_ReturnExt_s : typeclass_instances.


Lemma rec_step_ReturnInt_i fns hd tl h e K  (v : val) `{!LamExprFill e K (ReturnInt (Val v))}:
  TStepI lam_trans (Lam e (hd::tl) h fns) (λ G,
  G true None  (λ G', G' (Lam (expr_fill K (Val v)) tl h fns))).
Proof.
  destruct LamExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  naive_solver.
Qed.
Global Hint Resolve rec_step_ReturnInt_i : typeclass_instances.

(* ** Need an additional rule for returnInt but with empty stack?*)
Lemma lam_step_ReturnInt_s fns hd tl h e K  (v : val) `{!LamExprFill e K (ReturnInt (Val v))}:
  TStepS lam_trans (Lam e (hd::tl) h fns) (λ G,
    (G None (λ G', G' (Lam (expr_fill K (Val v)) tl h fns)))).
Proof.
  destruct LamExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct!. done.
Qed.
Global Hint Resolve lam_step_ReturnInt_s : typeclass_instances.



(*
(** * Proof techniques *)
Definition rec_proof_call (n : trace_index) (fns1 fns2 : gmap string fndef) :=
  (∀ n' f es1' es2' K1' K2' es1 es2 vs1' vs2' h1' h2' b,
      LamExprFill es1' K1' (Call f es1) →
      LamExprFill es2' K2' (Call f es2) →
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
  efeed pose proof Hc as Hp; [done|]. move: Hp => [?[?[? Hp]]]. simplify_eq.
  eapply Hp; [lia|..].
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
*)


(** * closing *)
(**
module rec_event:
Incoming, Call f vs h -> Outgoing, Call f' vs' h' → Incoming, Return v h' -> Outgoing, Return v' h''


module rec_closed_event:
Start f vs            -> Call f' vs' v                                     -> Return v'
*)

(* ** TODO Ask michael*)
(*
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
  *)

(** * Linking *)
(** ** Syntactic linking *)
Definition lam_syn_link (fns1 fns2 : gmap fid fndef) : gmap fid fndef :=
  fns1 ∪ fns2.

(* ** removed as rec/lam_closed not defined*)
(*
Definition lam_ctx_refines (fnsi fnss : gmap string fndef) :=
  ∀ C, trefines (rec_closed (rec_mod (rec_syn_link fnsi C)))
                (rec_closed (rec_mod (rec_syn_link fnss C))).
*)

(** ** Semantic linking *)
Definition lam_link_filter (fns1 fns2 : gset string) : seq_product_case → list seq_product_case → lam_ev → seq_product_case → list seq_product_case → lam_ev → bool → Prop :=
  λ p cs e p' cs' e' ok,
    e' = e ∧
    ok = true ∧
    match e with
    | ELCall f vs h =>
          p' = (if bool_decide (f.1 ∈ fns1) then SPLeft else if bool_decide (f.1 ∈ fns2) then SPRight else SPNone) ∧
          (cs' = p::cs) ∧
          p ≠ p'
      
    | ELReturn v h =>
        cs = p'::cs' ∧
        p ≠ p'
    end.
Arguments lam_link_filter _ _ _ _ _ _ _ _ /.

Definition lam_link_trans (fns1 fns2 : gset string) (m1 m2 : mod_trans lam_event) : mod_trans lam_event :=
  link_trans (lam_link_filter fns1 fns2) m1 m2.

Definition lam_link (fns1 fns2 : gset string) (m1 m2 : module lam_event) : module lam_event :=
  Mod (lam_link_trans fns1 fns2 m1.(m_trans) m2.(m_trans)) (MLFNone, [], m1.(m_init), m2.(m_init)).

Lemma lam_link_trefines m1 m1' m2 m2' fns1 fns2 `{!VisNoAng m1.(m_trans)} `{!VisNoAng m2.(m_trans)}:
  trefines m1 m1' →
  trefines m2 m2' →
  trefines (lam_link fns1 fns2 m1 m2) (lam_link fns1 fns2 m1' m2').
Proof. move => ??.  by apply link_mod_trefines. Qed.



(* ** Need to change this!*)
(** ** Relating semantic and syntactic linking *)
Inductive lam_link_combine_ectx_stack (f1 f2:gset string):
  nat → link_case lam_ev → list seq_product_case → 
  list expr_ectx → list expr_ectx → list expr_ectx →
  list string→list string→list string →Prop := 
  | LLCENil : 
    lam_link_combine_ectx_stack f1 f2 0 MLFNone [] [] [] [] [] [] []
  | LLCENoneToLeft n cs K Kl Kr f s sl sr: 
    lam_link_combine_ectx_stack f1 f2 n MLFNone cs K Kl Kr s sl sr→
    f∈f1 →
    lam_link_combine_ectx_stack f1 f2 (S n) MLFLeft (SPNone :: cs) (ReturnIntCtx::ReturnExtCtx::K) 
    (ReturnIntCtx::ReturnExtCtx::Kl) Kr (f::s) (f::sl) sr
  | LLCENoneToRight n cs K Kl Kr f s sl sr: 
    lam_link_combine_ectx_stack f1 f2 n MLFNone cs K Kl Kr s sl sr →
    f∈f2→
    lam_link_combine_ectx_stack f1 f2 (S n) MLFRight (SPNone :: cs) (ReturnIntCtx::ReturnExtCtx::K) 
    Kl (ReturnIntCtx::ReturnExtCtx::Kr) (f::s) sl (f::sr) 
  | LLCELeftToRight n cs K Kl Kl' Kr f s sl sr: 
    lam_link_combine_ectx_stack f1 f2 n MLFLeft cs K Kl Kr s sl sr →
    f∈f2 →
    is_static_expr true (expr_fill Kl' (Var "")) →
    lam_link_combine_ectx_stack f1 f2 (S n) MLFRight (SPLeft::cs) 
    (ReturnIntCtx::Kl'++K) (Kl'++Kl) (ReturnIntCtx::ReturnExtCtx::Kr) (f::s) sl (f::sr) 
  | LLCELeftToNone n cs K Kl Kl' Kr s sl sr : 
    lam_link_combine_ectx_stack f1 f2 n MLFLeft cs K Kl Kr s sl sr→
    is_static_expr true (expr_fill Kl' (Var ""))→
    lam_link_combine_ectx_stack f1 f2 (S n) MLFNone (SPLeft::cs) (Kl'++K) (Kl'++Kl) Kr s sl sr  
  | LLCERighttoLeft n cs K Kl Kr Kr' f s sl sr : 
    lam_link_combine_ectx_stack f1 f2 n MLFRight cs K Kl Kr s sl sr→
    f ∈f1 →
    is_static_expr true (expr_fill Kr' (Var "")) →
    lam_link_combine_ectx_stack f1 f2 (S n) MLFLeft (SPRight::cs) 
    (ReturnIntCtx::Kr'++K) (ReturnIntCtx::ReturnExtCtx::Kl) (Kr'++Kr) (f::s) (f::sl) sr  
  | LLCERightToNone n cs K Kl Kr Kr' s sl sr : 
    lam_link_combine_ectx_stack f1 f2 n MLFRight cs K Kl Kr s sl sr →
    is_static_expr true (expr_fill Kr' (Var ""))→
    lam_link_combine_ectx_stack f1 f2 (S n) MLFNone (SPRight::cs) (Kr'++K) Kl (Kr'++Kr) s sl sr   
  | LLCELeftToLeft n cs K Kl Kl' Kr f s sl sr: 
    lam_link_combine_ectx_stack f1 f2 n MLFLeft cs K Kl Kr s sl sr →
    f∈ f1 →
    is_static_expr true (expr_fill Kl' (Var ""))→
    lam_link_combine_ectx_stack f1 f2 (S n) MLFLeft cs (ReturnIntCtx::Kl'++K) (ReturnIntCtx::Kl'++Kl) Kr 
    (f::s) (f::sl) sr 
  | LLCERightToRight n cs K Kl Kr Kr' f s sl sr : 
    lam_link_combine_ectx_stack f1 f2 n MLFRight cs K Kl Kr s sl sr →
    f ∈ f2 →
    is_static_expr true (expr_fill Kr' (Var ""))→
    lam_link_combine_ectx_stack f1 f2 (S n) MLFRight cs (ReturnIntCtx::Kr'++K) Kl (ReturnIntCtx::Kr'++Kr)
    (f::s) sl (f::sr) 
.



Definition fns_inv fns1 fns2 fns fnsl fnsr:= 
  fns = fnsl ∪ fnsr ∧
  get_string_set_from_fid_set fnsl ## get_string_set_from_fid_set fnsr ∧
  get_string_set_from_fid_set fnsl = get_string_set_from_fid_set fns1 ∧
  get_string_set_from_fid_set fnsr = get_string_set_from_fid_set fns2 .


Definition lam_link_inv (bv : bool) (fns1 fns2 : gmap fid fndef) (σ1 : lam_trans.(m_state)) (σ2 : link_case lam_ev * list seq_product_case * lam_state * lam_state) : Prop :=
  let 'Lam e1 s1 h1 fns1' := σ1 in
  let '(σf, cs, Lam el sl hl fnsl, Lam er sr hr fnsr) := σ2 in
  ∃ n K Kl Kr e1' el' er' ,
  fns_inv fns1 fns2  fns1' fnsl fnsr ∧
  lam_link_combine_ectx_stack (get_string_set_from_fid_set fns1) (get_string_set_from_fid_set fns2) 
  n  σf cs K Kl Kr s1 sl sr∧
  (*stack_inv (get_string_set_from_fid_set fns1) (get_string_set_from_fid_set fns2) σf s1 sl sr ∧*)
  (*returnext_prop K e1'∧*)
  e1 = expr_fill K e1' ∧
  el = expr_fill Kl el' ∧
  er = expr_fill Kr er' ∧
  match σf with
  | MLFLeft => e1' = el' ∧ is_static_expr true el' ∧ er' = Waiting ∧ h1 = hl
              ∧ (if bv then to_val el' = None else True)
  | MLFRight => e1' = er' ∧ is_static_expr true er' ∧ el' = Waiting ∧ h1 = hr
               ∧ (if bv then to_val er' = None else True)
  | MLFNone => e1' = Waiting  ∧ el' = Waiting ∧ er' = Waiting
  | _ => False
  end.




  
  

Lemma lam_syn_link_refines_link fns1 fns2:
  (get_string_set_from_fid_set fns1) ## (get_string_set_from_fid_set fns2) →
  trefines (lam_mod (lam_syn_link fns1 fns2)) 
  (lam_link  (get_string_set_from_fid_set fns1)  (get_string_set_from_fid_set fns2) (lam_mod fns1) (lam_mod fns2)).
Proof.
  move => Hdisj.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { exact: (λ _, lam_link_inv true fns1 fns2). }
  { split!. econs.  1,2,3: done. } { done. }
  move => /= {}n _ Hloop  [e1 s1 h1 fns1'] [[[ipfs cs] [el sl hl fnsl]] [er sr hr fnsr]] [m [K [Kl [Kr [e1'[el'[er' ?]]]]]]].
  have {}Hloop : ∀ σi σs,
            lam_link_inv false fns1 fns2 σi σs
            → σi ⪯{lam_trans, lam_link_trans (get_string_set_from_fid_set fns1) (get_string_set_from_fid_set fns2) lam_trans lam_trans, n, true} σs. {
    clear -Hloop.  
    move => [e1 s1 h1  fns1'] [[[ipfs cs] [el sl hl  fnsl]] [er sr hr fnsr]].
    move => [m [K [Kl [Kr [e1' [el' [er'  [?[HK[?[?[? Hm]]]]]]]]]]]]; simplify_eq.
    elim/lt_wf_ind: m ipfs h1 hl hr cs K Kl Kr e1' el' er' s1 sl sr HK Hm => m IHm.
    move => ipfs h1 hl hr cs K Kl Kr e1' el' er' s1 sl sr HK Hmatch.
    case_match; destruct!/=.
    - destruct (to_val el') eqn:?; [ |apply: Hloop;naive_solver].
      destruct el'; simplify_eq/=.
      inversion HK; clear HK; simplify_eq/=.
      * tstep_i. tstep_s. tstep_i. tstep_s.   split!; [done..|] => /=. 
        apply: Hloop; [done|]. split!; naive_solver. 
      * inversion H; subst.
        -- tstep_s. tstep_s. split!.
        tstep_s. right. split!. tstep_i.
        rewrite !expr_fill_app.  eapply IHm. 2: exact H. lia. split!. by apply is_static_expr_expr_fill.
        -- tstep_s. tstep_s. split!.
        tstep_s. right. split!. tstep_i.
        rewrite expr_fill_app . rewrite (expr_fill_app _ Kr').  eapply IHm.
        2: apply LLCELeftToRight; auto; exact H3.  lia. split!. by apply is_static_expr_expr_fill.
        -- tstep_s. tstep_s. split!.
        tstep_s. right. split!. tstep_i.
        rewrite expr_fill_app . rewrite (expr_fill_app _ Kr').  eapply IHm.
        2: apply LLCERightToRight; auto; exact H3.  lia. split!. by apply is_static_expr_expr_fill.
      * tstep_s. tstep_i. rewrite !expr_fill_app. eapply IHm. 2: exact H. lia.
        split!. by apply is_static_expr_expr_fill.
    - destruct (to_val er') eqn:?; [ |apply: Hloop;naive_solver].
      destruct er'; simplify_eq/=.
      inversion HK; clear HK; simplify_eq/=.
      * tstep_i. tstep_s. tstep_i. tstep_s.   split!; [done..|] => /=. 
        apply: Hloop; [done|]. split!; naive_solver. 
      * inversion H; subst.
        -- tstep_s. tstep_s. split!.
        tstep_s. right. split!. tstep_i.
        rewrite !expr_fill_app.  eapply IHm. 2: exact H. lia. split!. by apply is_static_expr_expr_fill.
        -- tstep_s. tstep_s. split!.
        tstep_s. right. split!. tstep_i.
        rewrite expr_fill_app . rewrite (expr_fill_app _ Kl').  eapply IHm.
        2: apply LLCERighttoLeft; auto; exact H3.  lia. split!. by apply is_static_expr_expr_fill.
        -- tstep_s. tstep_s. split!.
        tstep_s. right. split!. tstep_i.
        rewrite expr_fill_app . rewrite (expr_fill_app _ Kl').  eapply IHm.
        2: apply LLCELeftToLeft; auto; exact H3.  lia. split!. by apply is_static_expr_expr_fill.
      * tstep_s. tstep_i. rewrite !expr_fill_app. eapply IHm. 2: exact H. lia.
        split!. by apply is_static_expr_expr_fill.
    - apply: Hloop; naive_solver.
  }
  destruct!/=. case_match; destruct!.
  - (*left case*) tstep_both. apply: steps_impl_step_end => ?? /prim_step_inv[//|?[?[?[?[??]]]]].
    simplify_eq. revert select (Is_true (is_static_expr _ _)) => /is_static_expr_expr_fill/=[??]//.
    rewrite -expr_fill_app.
    inv_all head_step => //.
    + (* binop*) admit.
    + (* newref*) admit.
    + (* load*) admit.
    + (* store*) admit.
    + (* if*) admit.
    + (* lete*) admit.
    + (* fixe*) admit.
    + (* var*) admit.
    + (* internal app*) admit.
    + (* external app*) admit.
  - (* right case*)admit. (*same case as before*) 
  - tstep_i. split.
    + (*call?*) intros. unfold fns_inv in H. destruct!. tstep_s. split!.
      rewrite elem_get_string_set_union in H0. case_bool_decide. auto. case_bool_decide. auto.
      destruct H0;exfalso. rewrite H3 in H0. by apply H2 in H0. rewrite H5 in H0. by apply H4 in H0.
      repeat case_bool_decide.
      -- (* goto left*)
      tstep_s. left. split!. rewrite H3. auto. tstep_s. left. split!.
      rewrite H3; auto. intros.
      tstep_i. split!. intros. split!. apply lookup_union_Some_l. exact H4.  auto.
      assert (∀K e, expr_fill K (ReturnInt e) = expr_fill (ReturnIntCtx::K) e) as H10 by auto.
      assert (∀K e, expr_fill K (ReturnExt e) = expr_fill (ReturnExtCtx::K) e) as H11 by auto.
      apply Hloop. split!.
      2,3:rewrite H11 H10. 2,3,4:done. apply LLCENoneToLeft. exact H1. auto.
      apply is_static_expr_subst_l. apply fn.(fd_static).
      -- (* goto right*)
      tstep_s. left. split!. rewrite H5. auto. tstep_s. left. split!.
      rewrite H5; auto. intros.
      tstep_i. split!. intros. split!. apply lookup_union_Some_r. 
      apply get_string_sets_disjoint_implies_sets_disjoint; auto. (*helpful lemma*) 
      exact H6.  auto.
      assert (∀K e, expr_fill K (ReturnInt e) = expr_fill (ReturnIntCtx::K) e) as H10 by auto.
      assert (∀K e, expr_fill K (ReturnExt e) = expr_fill (ReturnExtCtx::K) e) as H11 by auto.
      apply Hloop. split!.
      2,4:rewrite H11 H10. 2,3,4:done. apply LLCENoneToRight. exact H1. auto.
      apply is_static_expr_subst_l. apply fn.(fd_static).
      -- (* contradiction*) rewrite elem_get_string_set_union in H0. destruct H0.
        rewrite H3 in H0. contradiction. rewrite H5 in H0. contradiction. 
    + (*ret?*) intros. destruct!.
      tstep_s. inversion H1; subst; split!.
      -- (* ret to left*)
      assert (∀K e, expr_fill K (ReturnInt e) = expr_fill (ReturnIntCtx::K) e) as H10 by auto.
      assert (∀K e, expr_fill K (ReturnExt e) = expr_fill (ReturnExtCtx::K) e) as H11 by auto.
      tstep_s. right. inversion H0;subst; split!; rewrite !expr_fill_app; apply Hloop; split!.
      all:try rewrite H11 H10; try done; try by rewrite expr_fill_app.
      all: apply is_static_expr_expr_fill; split! ;repeat case_match; auto.
      -- (* ret to right*)
      assert (∀K e, expr_fill K (ReturnInt e) = expr_fill (ReturnIntCtx::K) e) as H10 by auto.
      assert (∀K e, expr_fill K (ReturnExt e) = expr_fill (ReturnExtCtx::K) e) as H11 by auto.
      tstep_s. right. inversion H0;subst; split!; rewrite !expr_fill_app; apply Hloop; split!.
      all:try rewrite H11 H10; try done; try by rewrite expr_fill_app.
      all: apply is_static_expr_expr_fill; split! ;repeat case_match; auto.
Admitted.
  
  
(*
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
      revert select (lam_link_combine_ectx _ _ _ _ _ _ _ _) => HK.
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
*)




(* ** TODO test out the current invariant *)

Lemma rec_link_refines_syn_link fns1 fns2:
  (get_string_set_from_fid_set fns1) ## (get_string_set_from_fid_set fns2) →
  trefines (lam_link  (get_string_set_from_fid_set fns1)  (get_string_set_from_fid_set fns2) (lam_mod fns1) (lam_mod fns2))
           (lam_mod (lam_syn_link fns1 fns2)).
Proof.
  move => Hdisj.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. {exact: (λ _, flip (lam_link_inv false fns1 fns2)). }

  { split!. 1,2: by econs.  all:done. } { done. }
  move => /= {}n _ Hloop [[[ipfs cs] [el sl hl fnsl]] [er sr hr fnsr]] [e1 s1 h1 fns1'] [m [K [Kl [Kr ?]]]].
  destruct!/=. case_match; destruct!.
  - (* ** MLFLeft case*)
    destruct (to_val el') eqn:?.
    + (* ** is a value*) 
      destruct el'; simplify_eq/=.

      revert select (lam_link_combine_ectx_stack _ _ _ _ _ _ _ _ _ _ _ ) => HK.
      inversion HK; clear HK; simplify_eq/=.
      * (* **returnext to None*) tstep_i => *; destruct!. tstep_i => *. tstep_s. destruct!. tstep_s. split!.
        apply: Hloop; [done|]. split!; auto. done.
      *(* **returnext to right*)  tstep_i => *; destruct!. tstep_i => *. destruct!. tstep_i.
        split!=>*. destruct!. tstep_s. rewrite !expr_fill_app. apply Hloop;try done. split!;auto. exact H0.
        apply is_static_expr_expr_fill. split!.
      * (* ** returnint*) tstep_i=>*. tstep_s=>*. rewrite !expr_fill_app. apply Hloop; try done. split!; auto. exact H0.
      apply is_static_expr_expr_fill. split!.
    + tstep_both. apply: steps_impl_step_end => ?? /prim_step_inv[//|?[?[?[?[??]]]]] *.
      simplify_eq. revert select (Is_true (is_static_expr _ _)) => /is_static_expr_expr_fill/= [??] //.
      rewrite -expr_fill_app.

      inv_all/= head_step => //; destruct!. clear H0 H2. (* ** TODO*)
      * (*binop*) tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!;   [done..| ].
        apply is_static_expr_expr_fill; split!; apply is_static_expr_val.
      * (*newref*) tstep_s => *. exists l, h'. intros.  split!. symmetry in H3. auto.
        intros. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply is_static_expr_expr_fill.
      * (*load*) tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply is_static_expr_expr_fill; split!; apply is_static_expr_val.
      * (* store*) tstep_s => *. subst. tend. split!. apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply is_static_expr_expr_fill. split!. 
      * (* if*) tstep_s =>b *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply is_static_expr_expr_fill. split!. destruct b; auto. 
      * (* let*) tstep_s => *. tend. split!. apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply is_static_expr_expr_fill. split!. by apply is_static_expr_subst.   
      * (* fix e*) (*need to assert that s1 i nonempty*)
        inversion H1; subst.
        -- (*case 1 where it returns to None*) 
          tstep_s. exists n0. split!.
          unfold fns_inv in H. destruct!. rewrite lookup_union_l; auto. eapply lookup_disjoint_none_right. exact H.
          rewrite H2. auto.  
          intros. unfold fns_inv in *. destruct!. 
          tend. split!. apply: Hloop; [done|]. rewrite !expr_fill_app. 
          split!; try done.
          unfold fns_inv. split!.
          ** unfold fns_add. rewrite insert_union_l. reflexivity.
          ** rewrite insert_get_string_set_unchanged; auto. rewrite H3. auto.
          ** rewrite insert_get_string_set_unchanged; auto. rewrite H3. auto.
          ** apply is_static_expr_expr_fill. split!.
        -- (*case 2 where it returns to right*) 
          tstep_s. exists n0. split!.
          unfold fns_inv in H. destruct!. rewrite lookup_union_l; auto. eapply lookup_disjoint_none_right. exact H.
          rewrite H2. auto.  
          intros. unfold fns_inv in *. destruct!. 
          tend. split!. apply: Hloop; [done|]. rewrite !expr_fill_app.  split!; try done.
          unfold fns_inv. split!.
          ** unfold fns_add. rewrite insert_union_l. reflexivity.
          ** rewrite insert_get_string_set_unchanged; auto. rewrite H4. auto.
          ** rewrite insert_get_string_set_unchanged; auto. rewrite H4. auto. 
          ** rewrite !expr_fill_app. auto.
          **  apply is_static_expr_expr_fill. split!.
        -- (* case 3 where it returns to itself*)
          tstep_s. exists n0. split!.
          unfold fns_inv in H. destruct!. rewrite lookup_union_l; auto. eapply lookup_disjoint_none_right. exact H.
          rewrite H2. auto.  
          intros. unfold fns_inv in *. destruct!. 
          tend. split!. apply: Hloop; [done|]. rewrite !expr_fill_app.  split!; try done.
          unfold fns_inv;split!.
          ** unfold fns_add. rewrite insert_union_l. reflexivity.
          ** rewrite insert_get_string_set_unchanged; auto. rewrite H4. auto.
          ** rewrite insert_get_string_set_unchanged; auto. rewrite H4. auto. 
          ** apply is_static_expr_expr_fill. split!.
      * (* var*) by tstep_s.
      * (* app internal in fnsl*) tstep_s => *.  left. exists (s,o). split!. unfold fns_inv in *.
        destruct!. simpl in H7. rewrite elem_get_string_set_union. left. auto. (* simple by apply lookup_union_Some_l.*)
        intros. tend. unfold fns_inv in *. destruct!. split!.
        rewrite lookup_get_string_disjoint_union_left in H3; auto. exact H3. 
        auto.
        apply: Hloop; [done|].
        assert (∀K e, expr_fill K (ReturnInt e) = expr_fill (ReturnIntCtx::K) e) by auto.
        rewrite !H5. unfold fns_inv in *. destruct!. split!. eapply LLCELeftToLeft. exact H1.
        rewrite -H6. auto. 2,3:simpl;reflexivity. all:auto. apply is_static_expr_subst_l. apply fn.(fd_static). 
      *  move => *. destruct!/=. repeat case_bool_decide => //.
        -- (* app internal in fnsr*) tend. split!. tstep_i. split => ??? R *; simplify_eq.
        tstep_s.  destruct H; subst. split!. 
        rewrite elem_get_string_set_union. right. auto.
        destruct!.
        intros. tstep_i. split!. intros. split!.
        rewrite lookup_get_string_disjoint_union_right in H6; auto. exact H6.
        auto.
        apply: Hloop; [done|]. 
        assert (∀K e, expr_fill K (ReturnInt e) = expr_fill (ReturnIntCtx::K) e) by auto.
        assert (∀K e, expr_fill K (ReturnExt e) = expr_fill (ReturnExtCtx::K) e) by auto.
        split!.
        4: rewrite !H13. 2, 4:rewrite !H12. 2,3,4:done. apply LLCELeftToRight. exact H1.
        destruct!; simpl; auto. auto. apply is_static_expr_subst_l. apply fn.(fd_static). 
        -- (* app external*) tstep_s. right. eexists (s,o), _. split!. done.
            destruct H. destruct!. intro. rewrite elem_get_string_set_union in H. destruct!. rewrite H10 in H.  contradiction. 
            tend. split!. apply Hloop; try done. split!; try done. econs. exact H1. done.
  - (* ** MLRight case*)
    destruct (to_val er') eqn:?.
    + (* ** is a value*) 
      destruct er'; simplify_eq/=.

      revert select (lam_link_combine_ectx_stack _ _ _ _ _ _ _ _ _ _ _ ) => HK.
      inversion HK; clear HK; simplify_eq/=.
      * (* **returnext to None*) tstep_i => *; destruct!. tstep_i => *. tstep_s. destruct!. tstep_s. split!.
        apply: Hloop; [done|]. split!; auto. done.
      *(* **returnext to right*)  tstep_i => *; destruct!. tstep_i => *. destruct!. tstep_i.
        split!=>*. destruct!. tstep_s. rewrite !expr_fill_app. apply Hloop;try done. split!;auto. exact H0.
        apply is_static_expr_expr_fill. split!.
      * (* ** returnint*) tstep_i=>*. tstep_s=>*. rewrite !expr_fill_app. apply Hloop; try done. split!; auto. exact H0.
      apply is_static_expr_expr_fill. split!.
    + tstep_both. apply: steps_impl_step_end => ?? /prim_step_inv[//|?[?[?[?[??]]]]] *.
      simplify_eq. revert select (Is_true (is_static_expr _ _)) => /is_static_expr_expr_fill/= [??] //.
      rewrite -expr_fill_app.

      inv_all/= head_step => //; destruct!. clear H0 H2. (* ** TODO*)
      * (*binop*) tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!;   [done..| ].
        apply is_static_expr_expr_fill; split!; apply is_static_expr_val.
      * (*newref*) tstep_s => *. exists l, h'. intros.  split!. symmetry in H3. auto.
        intros. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply is_static_expr_expr_fill.
      * (*load*) tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply is_static_expr_expr_fill; split!; apply is_static_expr_val.
      * (* store*) tstep_s => *. subst. tend. split!. apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply is_static_expr_expr_fill. split!. 
      * (* if*) tstep_s =>b *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply is_static_expr_expr_fill. split!. destruct b; auto. 
      * (* let*) tstep_s => *. tend. split!. apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply is_static_expr_expr_fill. split!. by apply is_static_expr_subst.   
      * (* fix e*) (*need to assert that s1 i nonempty*)
        inversion H1; subst.
        -- (*case 1 where it returns to None*) 
          tstep_s. exists n0. split!.
          unfold fns_inv in H. destruct!. rewrite lookup_union_r; auto. eapply lookup_disjoint_none_left. exact H.
          rewrite H5. auto.  
          intros. unfold fns_inv in *. destruct!. 
          tend. split!. apply: Hloop; [done|]. rewrite !expr_fill_app. 
          split!; try done.
          unfold fns_inv. split!.
          ** unfold fns_add. rewrite insert_union_r. reflexivity. 
          eapply lookup_disjoint_none_left. exact H. rewrite H6. auto. (* ** fn lemma*)
          ** rewrite insert_get_string_set_unchanged; auto. rewrite H6. auto.
          ** rewrite insert_get_string_set_unchanged; auto. rewrite H6. auto.
          ** apply is_static_expr_expr_fill. split!.
        -- (*case 2 where it returns to right*) 
          tstep_s. exists n0. split!.
          unfold fns_inv in H. destruct!. rewrite lookup_union_r; auto. eapply lookup_disjoint_none_left. exact H.
          rewrite H6. auto.  
          intros. unfold fns_inv in *. destruct!. 
          tend. split!. apply: Hloop; [done|]. rewrite !expr_fill_app.  split!; try done.
          unfold fns_inv. split!.
          ** unfold fns_add. rewrite insert_union_r. reflexivity. 
          eapply lookup_disjoint_none_left. exact H. rewrite H8. auto.
          ** rewrite insert_get_string_set_unchanged; auto. rewrite H8. auto.
          ** rewrite insert_get_string_set_unchanged; auto. rewrite H8. auto. 
          ** rewrite !expr_fill_app. auto.
          **  apply is_static_expr_expr_fill. split!.
        -- (* case 3 where it returns to itself*)
          tstep_s. exists n0. split!.
          unfold fns_inv in H. destruct!. rewrite lookup_union_r; auto. eapply lookup_disjoint_none_left. exact H.
          rewrite H6. auto.  
          intros. unfold fns_inv in *. destruct!. 
          tend. split!. apply: Hloop; [done|]. rewrite !expr_fill_app.  split!; try done.
          unfold fns_inv;split!.
          ** unfold fns_add. rewrite insert_union_r. reflexivity. 
          eapply lookup_disjoint_none_left. exact H. rewrite H8. auto.
          ** rewrite insert_get_string_set_unchanged; auto. rewrite H8. auto.
          ** rewrite insert_get_string_set_unchanged; auto. rewrite H8. auto. 
          ** apply is_static_expr_expr_fill. split!.
      * (* var*) by tstep_s.
      * (* app internal in fnsl*) tstep_s => *.  left. exists (s,o). split!. unfold fns_inv in *.
        destruct!. simpl in H7. rewrite elem_get_string_set_union. right. auto. (* simple by apply lookup_union_Some_l.*)
        intros. tend. unfold fns_inv in *. destruct!. split!.
        rewrite lookup_get_string_disjoint_union_right in H3; auto. exact H3. 
        auto.
        apply: Hloop; [done|].
        assert (∀K e, expr_fill K (ReturnInt e) = expr_fill (ReturnIntCtx::K) e) by auto.
        rewrite !H5. unfold fns_inv in *. destruct!. split!. eapply LLCERightToRight. exact H1.
        rewrite -H9. auto. 2,3:simpl;reflexivity. all:auto. apply is_static_expr_subst_l. apply fn.(fd_static). 
      *  move => *. destruct!/=. repeat case_bool_decide => //.
        -- (* app internal in fnsr*) tend. split!. tstep_i. split => ??? R *; simplify_eq.
        tstep_s.  destruct H; subst. split!. 
        rewrite elem_get_string_set_union. left. auto.
        destruct!.
        intros. tstep_i. split!. intros. split!.
        rewrite lookup_get_string_disjoint_union_left in H5; auto. exact H5.
        auto.
        apply: Hloop; [done|]. 
        assert (∀K e, expr_fill K (ReturnInt e) = expr_fill (ReturnIntCtx::K) e) by auto.
        assert (∀K e, expr_fill K (ReturnExt e) = expr_fill (ReturnExtCtx::K) e) by auto.
        split!.
        3: rewrite !H12. 2, 3:rewrite !H11. 2,3,4:done. apply LLCERighttoLeft. exact H1.
        destruct!; simpl; auto. auto. apply is_static_expr_subst_l. apply fn.(fd_static). 
        -- (* app external*) tstep_s. right. eexists (s,o), _. split!. done.
            destruct H. destruct!. intro. rewrite elem_get_string_set_union in H. destruct!. rewrite H5 in H.  contradiction. 
            tend. split!. apply Hloop; try done. split!; try done. econs. exact H1. done.
  - tstep_i => *.
    repeat match goal with | x : lam_ev |- _ => destruct x end; simplify_eq/=; destruct!/=.
    +repeat case_bool_decide => //.  unfold fns_inv in H. destruct!.  
     * (*left call case*) tstep_s. left;split!.
     rewrite elem_get_string_set_union. left. rewrite H3. auto. 
     tstep_s. split!. 
     rewrite elem_get_string_set_union. left. rewrite H3. auto. 
     intros. tstep_i. split!. intros. tstep_i. split!. intros. exists fn.
     split!. inversion H8; subst. destruct id0. 
     rewrite lookup_get_string_disjoint_union_left in H2; auto.
     inversion H8; subst. auto.
     apply Hloop; auto.
     inversion H8; subst.
     assert (∀K e, expr_fill K (ReturnInt e) = expr_fill (ReturnIntCtx::K) e) as H10 by auto.
     assert (∀K e, expr_fill K (ReturnExt e) = expr_fill (ReturnExtCtx::K) e) as H11 by auto.
     split!.
     2,3 :rewrite H11 H10. 2,3,4:done. apply LLCENoneToLeft. exact H1. auto.
     apply is_static_expr_subst_l. apply fn.(fd_static). 
     * (*right call case*) unfold fns_inv in H. destruct!.  tstep_s. left;split!. 
     rewrite elem_get_string_set_union. right. rewrite H7. auto. 
     tstep_s. split!. 
     rewrite elem_get_string_set_union. right. rewrite H7. auto. 
     intros. tstep_i. split!. intros. tstep_i. split!. intros. exists fn.
     inversion H9; subst. 
     split!. inversion H8; subst. destruct id0. 
     rewrite lookup_get_string_disjoint_union_right in H3; auto.
     auto.
     apply Hloop; auto.
     inversion H9; subst.
     assert (∀K e, expr_fill K (ReturnInt e) = expr_fill (ReturnIntCtx::K) e) as H11 by auto.
     assert (∀K e, expr_fill K (ReturnExt e) = expr_fill (ReturnExtCtx::K) e) as H12 by auto.
     split!.
     2,4 :rewrite H12 H11. 2,3,4:done. apply LLCENoneToRight. exact H1. auto.
     apply is_static_expr_subst_l. apply fn.(fd_static). 
     
    + tstep_s. right.
      revert select (lam_link_combine_ectx_stack _ _ _ _ _ _ _ _ _ _ _) => HK.
      inversion HK; clear HK; simplify_eq; rewrite ?orb_true_r.
      * (* left case *) inversion H3; subst;split!.
        
        -- tstep_i. split => *; destruct!/=.
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done|done..|].
        apply is_static_expr_expr_fill. split!. destruct ret0; try destruct id, o;auto.
        -- tstep_i.
        assert (∀K e, expr_fill K (ReturnInt e) = expr_fill (ReturnIntCtx::K) e) as H6 by auto.
        assert (∀K e, expr_fill K (ReturnExt e) = expr_fill (ReturnExtCtx::K) e) as H7 by auto. 
        split => *; destruct!.
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!. 
        3:rewrite !H7. 2,3:rewrite H6. 2,3: reflexivity. 2:rewrite -expr_fill_app. 2:done.
        apply LLCERighttoLeft; auto. exact H0.
        apply is_static_expr_expr_fill. split!. destruct ret0; try destruct id, o;auto.
        -- tstep_i.
        assert (∀K e, expr_fill K (ReturnInt e) = expr_fill (ReturnIntCtx::K) e) as H6 by auto.
        split => *; destruct!.
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!. 
        2,3:rewrite H6. 2,3: reflexivity. 2:done.
        apply LLCELeftToLeft; auto. exact H0.
        apply is_static_expr_expr_fill. split!. destruct ret0; try destruct id, o;auto.

      * (* same case as before*)inversion H3; subst;split!.
        
        -- tstep_i. split => *; destruct!/=.
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done|done..|].
        apply is_static_expr_expr_fill. split!. destruct ret0; try destruct id, o;auto.
        -- tstep_i.
        assert (∀K e, expr_fill K (ReturnInt e) = expr_fill (ReturnIntCtx::K) e) as H6 by auto.
        assert (∀K e, expr_fill K (ReturnExt e) = expr_fill (ReturnExtCtx::K) e) as H7 by auto. 
        split => *; destruct!.
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!. 
        4:rewrite !H7. 2,4:rewrite H6. 2,3: reflexivity. 2:rewrite -expr_fill_app. 2:done.
        apply LLCELeftToRight; auto. exact H0.
        apply is_static_expr_expr_fill. split!. destruct ret0; try destruct id, o;auto.
        -- tstep_i.
        assert (∀K e, expr_fill K (ReturnInt e) = expr_fill (ReturnIntCtx::K) e) as H6 by auto.
        split => *; destruct!.
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!. 
        2,4:rewrite H6. 2,3: reflexivity. 2:done.
        apply LLCERightToRight; auto. exact H0.
        apply is_static_expr_expr_fill. split!. destruct ret0; try destruct id, o;auto.
  
Qed.



(*
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


