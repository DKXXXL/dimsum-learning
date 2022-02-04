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

Inductive binop : Set :=
| AddOp | ShiftOp | EqOp.

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

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

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
Record heap_state := Heap {
  h_heap : gmap loc val;
  h_provs : gset prov;
  heap_wf l : is_Some (h_heap !! l) → l.1 ∈ h_provs;
}.
Add Printing Constructor heap_state.

Program Definition initial_heap_state : heap_state :=
  Heap ∅ ∅ _.
Next Obligation. move => ?. rewrite lookup_empty => -[??]. done. Qed.

Definition heap_alive (h : heap_state) (l : loc) : Prop :=
  is_Some (h.(h_heap) !! l).

Definition heap_is_fresh (h : heap_state) (l : loc) : Prop :=
  l.1 ∉ h.(h_provs) ∧ l.2 = 0.

Definition heap_fresh (ps : gset prov) (h : heap_state) : loc :=
  (fresh (ps ∪ h.(h_provs)), 0).

Program Definition heap_update (h : heap_state) (l : loc) (v : val) : heap_state :=
  Heap (alter (λ _, v) l h.(h_heap)) h.(h_provs) _.
Next Obligation. move => ????. rewrite lookup_alter_is_Some. apply heap_wf. Qed.

Program Definition heap_alloc (h : heap_state) (l : loc) (n : Z) : heap_state :=
  Heap (list_to_map ((λ z, (l +ₗ z, ValNum 0)) <$> seqZ 0 n) ∪ h.(h_heap)) ({[l.1]} ∪ h.(h_provs)) _.
Next Obligation.
  move => ???? [? /lookup_union_Some_raw[Hl|[? Hh]]]; apply elem_of_union; [left|right; by apply heap_wf].
  move: Hl => /(elem_of_list_to_map_2 _ _ _)/elem_of_list_fmap. set_solver.
Qed.

Program Definition heap_free (h : heap_state) (l : loc) : heap_state :=
  Heap (filter (λ '(l', v), l'.1 ≠ l.1) h.(h_heap)) h.(h_provs) _.
Next Obligation. move => ???. rewrite map_filter_lookup => -[?/bind_Some[?[??]]]. by apply heap_wf. Qed.

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

(** ** step *)
Definition eval_binop (op : binop) (v1 v2 : val) : option val :=
  match op with
  | AddOp => z1 ← val_to_Z v1; z2 ← val_to_Z v2; Some (ValNum (z1 + z2))
  | ShiftOp => l ← val_to_loc v1; z ← val_to_Z v2; Some (ValLoc (l +ₗ z))
  | EqOp => z1 ← val_to_Z v1; z2 ← val_to_Z v2; Some (ValBool (bool_decide (z1 = z2)))
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
  have ->:= Hsub _ _ ltac:(done). { by apply: val_head_stuck. }
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

(** * syntactic linking *)
Definition imp_link (fns1 fns2 : gmap string fndef) : gmap string fndef :=
  fns1 ∪ fns2.

Definition imp_ctx_refines (fnsi fnss : gmap string fndef) :=
  ∀ C, trefines (MS imp_module (initial_imp_state (imp_link fnsi C)))
                (MS imp_module (initial_imp_state (imp_link fnss C))).

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
        apply: Hloop. by split!.
      * tstep_s. split!.
        tstep_s. split!.
        rewrite !expr_fill_app. apply: IHm; [|done|]; [lia|]. split!. by apply static_expr_expr_fill.
    - destruct (to_val er') eqn:?; [ |apply: Hloop; naive_solver].
      destruct er'; simplify_eq/=.
      inversion HK; clear HK; simplify_eq/=.
      * tstep_i. tstep_s. split!. apply: Hloop. by split!.
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
        apply Hloop. by split!.
      * tstep_i => *; destruct_all?; simplify_eq/=.
        tstep_i; split => *; simplify_eq.
        apply Hloop. rewrite !expr_fill_app. split!; [done..|].
        by apply static_expr_expr_fill.
    + tstep_both. apply: steps_impl_step_end => ?? /prim_step_inv[//|?[?[?[?[??]]]]] *.
      simplify_eq. revert select (Is_true (static_expr _ _)) => /static_expr_expr_fill/=[??]//.
      rewrite -expr_fill_app.
      invert_all head_step => //; destruct_all?; simplify_eq.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
        by apply static_expr_expr_fill.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
        by apply static_expr_expr_fill.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
        by apply static_expr_expr_fill.
      * tstep_s => *. split!; [done..|] => *. tend. split!; [done..|].
        apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
        by apply static_expr_expr_fill.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
        by apply static_expr_expr_fill.
      * tstep_s => b ?. subst. tend. split!. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
        apply static_expr_expr_fill. split!. destruct b; naive_solver.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
        apply static_expr_expr_fill. split!. by apply static_expr_subst.
      * by tstep_s.
      * tstep_s. left. split!; [apply lookup_union_Some; naive_solver|] => ?. tend. split!; [done..|].
        apply: Hloop. rewrite !expr_fill_app. split!; [done..|].
        apply static_expr_expr_fill. split!. apply static_expr_subst_l; [|done].
        apply static_expr_mono. apply fd_static.
      * move => *. destruct_all?; simplify_eq/=. repeat case_bool_decide => //.
        -- have [??] : is_Some (fns2 !! f) by apply elem_of_dom.
           tstep_s. left. split!; [apply lookup_union_Some; naive_solver|] => ?. tend. split!.
           tstep_i. split => *; simplify_eq. case_bool_decide => //.
           apply: Hloop. split!; [by econs|done..|].
           apply static_expr_subst_l; [|done]. apply static_expr_mono. apply fd_static.
        -- tstep_s. right. split!; [apply lookup_union_None;split!;by apply not_elem_of_dom| done|].
           tend. split!. apply: Hloop. split!; [by econs|done..].
  - destruct (to_val er') eqn:?.
    + destruct er'; simplify_eq/=.
      revert select (imp_link_prod_combine_ectx _ _ _ _ _ _ _ _) => HK.
      inversion HK; clear HK; simplify_eq/=.
      * tstep_i => *; destruct_all?; simplify_eq. tstep_s. split!.
        apply Hloop. by split!.
      * tstep_i => *; destruct_all?; simplify_eq/=.
        tstep_i; split => *; simplify_eq.
        apply Hloop. rewrite !expr_fill_app. split!; [done..|].
        by apply static_expr_expr_fill.
    + tstep_both. apply: steps_impl_step_end => ?? /prim_step_inv[//|?[?[?[?[??]]]]] *.
      simplify_eq. revert select (Is_true (static_expr _ _)) => /static_expr_expr_fill/=[??]//.
      rewrite -expr_fill_app.
      invert_all head_step => //; destruct_all?; simplify_eq.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
        by apply static_expr_expr_fill.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
        by apply static_expr_expr_fill.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
        by apply static_expr_expr_fill.
      * tstep_s => *. split!;[done..|] => *. tend. split!; [done..|].
        apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
        by apply static_expr_expr_fill.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
        by apply static_expr_expr_fill.
      * tstep_s => b ?. subst. tend. split!. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
        apply static_expr_expr_fill. split!. destruct b; naive_solver.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
        apply static_expr_expr_fill. split!. by apply static_expr_subst.
      * by tstep_s.
      * tstep_s. left. split!; [apply lookup_union_Some; naive_solver|] => ?. tend. split!; [done..|].
        apply: Hloop. rewrite !expr_fill_app. split!; [done..|].
        apply static_expr_expr_fill. split!. apply static_expr_subst_l; [|done].
        apply static_expr_mono. apply fd_static.
      * move => *. destruct_all?; simplify_eq/=. repeat case_bool_decide => //.
        -- have [??] : is_Some (fns1 !! f) by apply elem_of_dom.
           tstep_s. left. split!; [apply lookup_union_Some; naive_solver|] => ?.
           tend. split!.
           tstep_i. split => *; invert_all imp_prod_filter. case_bool_decide => //.
           apply: Hloop. split!; [by econs|done..|].
           apply static_expr_subst_l; [|done]. apply static_expr_mono. apply fd_static.
        -- tstep_s. right. split!; [apply lookup_union_None;split!;by apply not_elem_of_dom|done|].
           tend. split!. apply: Hloop. split!; [by econs|rewrite ?orb_true_r; done..].
  - tstep_i => *.
    repeat match goal with | x : imp_ev |- _ => destruct x end; simplify_eq/=; destruct_all?; simplify_eq/=.
    + tstep_s. left. repeat case_bool_decide => //.
      all: revert select (_ ∈ dom _ _) => /elem_of_dom[??]; split!;
               [rewrite lookup_union_Some //; naive_solver |].
      * case_bool_decide. 2: { by tstep_s. }
        tstep_i. split => *; destruct_all?; simplify_eq/=. case_bool_decide => //.
        apply Hloop. split!; [by econs|done..|]. apply static_expr_subst_l; [|done].
        apply static_expr_mono. apply fd_static.
      * case_bool_decide. 2: { by tstep_s. }
        tstep_i. split => *; destruct_all?; simplify_eq/=. case_bool_decide => //.
        apply Hloop. split!; [by econs|done..|]. apply static_expr_subst_l; [|done].
        apply static_expr_mono. apply fd_static.
    + tstep_s. right.
      revert select (imp_link_prod_combine_ectx _ _ _ _ _ _ _ _) => HK.
      inversion HK; clear HK; simplify_eq; rewrite ?orb_true_r.
      * split!. tstep_i. split => *; destruct_all?; simplify_eq/=.
        apply Hloop. rewrite !expr_fill_app. split!; [done|done..|].
        by apply static_expr_expr_fill.
      * split!. tstep_i. split => *; destruct_all?; simplify_eq/=.
        apply Hloop. rewrite !expr_fill_app. split!; [done|done..|].
        by apply static_expr_expr_fill.
Qed.

Lemma imp_trefines_implies_ctx_refines fnsi fnss :
  dom (gset _) fnsi = dom (gset _) fnss →
  trefines (MS imp_module (initial_imp_state fnsi)) (MS imp_module (initial_imp_state fnss)) →
  imp_ctx_refines fnsi fnss.
Proof.
  move => Hdom Href C. rewrite /imp_link map_difference_union_r (map_difference_union_r fnss).
  etrans. { apply imp_link_refines_prod. apply map_disjoint_difference_r'. }
  etrans. 2: { apply imp_prod_refines_link. apply map_disjoint_difference_r'. }
  rewrite !dom_difference_L Hdom.
  apply imp_prod_trefines; [apply _..| |].
  - apply: Href.
  - erewrite map_difference_eq_dom_L => //. apply _.
Qed.


(** * imp_heap_bij *)
Record heap_bij := HeapBij {
  hb_bij : gset (prov * prov);
  hb_env : gset prov;
  hb_prog : gset prov;
  hb_disj_env : hb_env ## set_map snd hb_bij;
  hb_disj_prog : hb_prog ## set_map snd hb_bij;
  hb_disj_priv : hb_prog ## hb_env;
  hb_inj_left i x1 x2 : (i, x1) ∈ hb_bij → (i, x2) ∈ hb_bij → x1 = x2;
  hb_inj_right i x1 x2 : (x1, i) ∈ hb_bij → (x2, i) ∈ hb_bij → x1 = x2;
}.

Global Program Instance imp_heap_bij_empty : Empty heap_bij :=
  HeapBij ∅ ∅ ∅ _ _ _ _ _.
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
  HeapBij ({[ (p1, p2 )]} ∪ hb_bij bij) (hb_env bij) (hb_prog bij) _ _ _ _ _.
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
  move => ??? Hl Hr?????. set_unfold.
  destruct_all?; simplify_eq => //.
  - contradict Hl. eexists (_,_). naive_solver.
  - contradict Hl. eexists (_,_). naive_solver.
  - by apply: hb_inj_left.
Qed.
Next Obligation.
  move => ??? Hl Hr?????. set_unfold.
  destruct_all?; simplify_eq => //.
  - contradict Hr. left. left. eexists (_,_). naive_solver.
  - contradict Hr. left. left. eexists (_,_). naive_solver.
  - by apply: hb_inj_right.
Qed.

Lemma heap_bij_iff p1 p2 p1' p2' bij:
  (p1, p2) ∈ hb_bij bij →
  (p1', p2') ∈ hb_bij bij →
  p1 = p1' ↔ p2 = p2'.
Proof. move => ??. split => ?; subst; [by apply: hb_inj_left| by apply: hb_inj_right]. Qed.

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

Lemma heap_preserved_bij_env p1 p2 l v he hp bij:
  (p1, p2) ∈ hb_bij bij →
  l.1 = p2 →
  heap_preserved (hb_env bij) he hp →
  heap_preserved (hb_env bij) he (heap_update hp l v).
Proof.
  move => ?? Hp p o /=?. destruct (decide (l = (p, o))); subst; simplify_map_eq.
  - exfalso. have := hb_disj_env bij. apply; [done|]. apply elem_of_map. by eexists (_, _).
  - by apply Hp.
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

Lemma heap_preserved_bij_env_alloc l n he hp bij:
  l.1 ∉ bij →
  heap_preserved bij he hp →
  heap_preserved bij he (heap_alloc hp l n).
Proof.
  move => Hni Hp p o /= ?. rewrite lookup_union_r; [| by apply Hp].
  apply not_elem_of_list_to_map_1 => /elem_of_list_fmap[[[??]?] [?/elem_of_list_fmap[?[??]]]]; simplify_eq/=.
  done.
Qed.

Record imp_heap_bij_state := ImpHeapBij {
  ihb_bij : heap_bij;
  (* last seen heap *)
  ihb_heap : heap_state;
}.
Add Printing Constructor imp_heap_bij_state.

Definition imp_heap_bij_pre (e : imp_event) (s : imp_heap_bij_state) : prepost (imp_event * imp_heap_bij_state) :=
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

Definition imp_heap_bij_post (e : imp_event) (s : imp_heap_bij_state) : prepost (imp_event * imp_heap_bij_state) :=
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
  (@SMFilter imp_event, σ, (@PPOutside imp_event imp_event, ImpHeapBij ∅ initial_heap_state)).

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
      (λ ips '(ImpHeapBij bij1 hi1) '(ImpHeapBij bij2 hi2) '(ImpHeapBij bij hi) ics1 ics2,
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
  { split!. all: set_solver. }
  all: move => [bij1 hi1] [bij2 hi2] [bij hi] ics1 ics2.
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
    all: try abstract (by apply hb_inj_left).
    all: try abstract (by apply hb_inj_right).
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

Inductive imp_heap_bij_refl_ectx :
  nat → (* paramater of previous waiting *) bool → @pp_state imp_event imp_event → list expr_ectx → Prop :=
| IHBRE_Nil:
  imp_heap_bij_refl_ectx 0 false PPOutside []
| IHBRE_Return n b K:
  imp_heap_bij_refl_ectx n b PPOutside K →
  imp_heap_bij_refl_ectx (S n) true PPInside (ReturnExtCtx b :: K)
| IHBRE_Ctx b n K K':
  imp_heap_bij_refl_ectx n b PPInside K →
  static_expr true (expr_fill K' (Var "")) →
  imp_heap_bij_refl_ectx (S n) true PPOutside (K' ++ K)
.

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

(* Local Ltac split_tac ::= original_split_tac. *)

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
  move => p1' p2' o' /=?. have ?: p1 = p1' ↔ p2 = p2' by apply: heap_bij_iff.
  split.
  - rewrite !lookup_alter_is_Some. by apply Hbij.
  - move => ?? /lookup_alter_Some[[?[?[??]]]|[??]] /lookup_alter_Some[[?[?[??]]]|[??]]; simplify_eq.
    all: try by eapply Hbij. all: naive_solver.
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
    { apply eq_None_ne_Some => ??. apply Hi1. by apply: (heap_wf _ (_, _)). }
    { apply eq_None_ne_Some => ??. apply Hi2. by apply: (heap_wf _ (_, _)). }
    split.
    + rewrite !list_to_map_lookup_is_Some. f_equiv => ?. rewrite !elem_of_list_fmap. f_equiv => ?. naive_solver.
    + move => ?? /(elem_of_list_to_map_2 _ _ _)/elem_of_list_fmap[?[??]].
      move => /(elem_of_list_to_map_2 _ _ _)/elem_of_list_fmap[?[??]]. by simplify_eq/=.
  - have ? : p1 ≠ l1.1 by contradict H1; set_unfold; eexists (_, _); naive_solver.
    have ? : p2 ≠ l2.1 by contradict H2; set_unfold; left; left; eexists (_, _); naive_solver.
    have [Hbij1 Hbij2]:= Hbij p1 p2 o ltac:(set_solver).
    rewrite !lookup_union_r.
    1, 2: apply not_elem_of_list_to_map_1;
        move => /elem_of_list_fmap[[[??]?] [?/elem_of_list_fmap[?[??]]]]; simplify_eq/=.
    split; [done|] => *. apply: val_in_bij_mono; [naive_solver|]. set_solver.
Qed.


Lemma heap_in_bij_free hi hs l1 l2 bij:
  heap_in_bij (hb_bij bij) hi hs →
  (l1.1, l2.1) ∈ hb_bij bij →
  heap_in_bij (hb_bij bij) (heap_free hi l1) (heap_free hs l2).
Proof.
  move => Hbij Hin p1 p2 o /=?.
  have [Hbij1 Hbij2]:= Hbij p1 p2 o ltac:(done).
  have ?: p1 = l1.1 ↔ p2 = l2.1 by apply: heap_bij_iff.
  split.
  - rewrite !map_filter_lookup /=. destruct (h_heap hi !! (p1, o)), (h_heap hs !! (p2, o)) => //=.
    all: repeat case_option_guard => //; naive_solver.
  - move => ??. rewrite !map_filter_lookup => /bind_Some[?[??]] /bind_Some[?[??]].
    repeat case_option_guard => //; naive_solver.
Qed.

Lemma imp_heap_bij_imp_refl fns:
  trefines (MS imp_module (initial_imp_state fns))
           (MS (imp_heap_bij imp_module)
               (initial_imp_heap_bij_state imp_module (initial_imp_state fns))).
Proof.
  unshelve apply: inv_implies_trefines. { simpl. exact (λ '(Imp ei hi fnsi) '(ips, Imp es hs fnss, (pp, ImpHeapBij bij he)),
    ∃ bij' n Ki ei' b,
    fnsi = fns ∧ fnss = fns ∧
    imp_heap_bij_refl_ectx n b pp Ki ∧
    hb_env bij = hb_env bij' ∧
    hb_prog bij = ∅ ∧ hb_prog bij' = ∅ ∧
    heap_preserved (hb_env bij') he hs ∧
    ei = expr_fill Ki ei' ∧
    expr_in_bij (hb_bij bij') ei es ∧
    heap_in_bij (hb_bij bij') hi hs ∧
    set_map fst (hb_bij bij') ⊆ h_provs hi ∧
    match pp with
    | PPOutside =>
        ei' = Waiting b ∧ ips = SMFilter ∧ hb_bij bij = hb_bij bij'
    | PPInside =>
        hb_bij bij ⊆ hb_bij bij' ∧
        static_expr true ei' ∧ ips = SMProg
    | _ => False
    end
 ). }
  { eexists ∅. split!. econs. done. }
  move => /= [ei hi fnsi] [[ips [es hs fnss]] [pp [bij he]]] ??? Hprim. destruct_all?; simplify_eq.
  revert select (expr_in_bij _ (expr_fill _ _) _) => /expr_in_bij_fill_l[?[?[?[??]]]].
  case_match; destruct_all?; simplify_eq.
  - move: Hprim => /prim_step_inv_head[|//|??]. { solve_sub_redexes_are_values. } destruct_all?; simplify_eq.
    invert_all @head_step; destruct_all?; simplify_eq.
    + case_match => //; simplify_eq. tstep_s. split!; [done|]. tstep_s. move => *. tstep_s. split!.
      case_bool_decide. 2: { by tstep_s. }
      tend. case_bool_decide => //. 2: solve_length.
      unfold heap_bij_extend in *.
      split!. 1: by econs. 1: done. all: split!.
      1, 2: set_solver.
      1: { apply: ectx_in_bij_mono; [done|set_solver]. }
      1: { apply expr_in_bij_subst_l; [|done|solve_length]. apply expr_in_bij_static. apply fd_static. }
      apply static_expr_subst_l => //. apply static_expr_mono. apply fd_static.
    + case_match => //; simplify_eq. tstep_s. split!; [done|]. tstep_s. move => *. tstep_s. split!. tend.
      revert select (imp_heap_bij_refl_ectx _ _ _ _) => HK.
      inversion HK; clear HK; simplify_eq/=.
      unfold heap_bij_extend in *.
      split!. 1: done. 1: done. all: split!. 1, 2: set_solver.
      1: { apply: ectx_in_bij_mono; [done|set_solver]. }
      by decompose_Forall_hyps.
  - destruct (to_val ei') eqn:?.
    + destruct ei'; simplify_eq/=.
      revert select (imp_heap_bij_refl_ectx _ _ _ _) => HK.
      inversion HK; clear HK; simplify_eq/=.
      move: Hprim => /prim_step_inv_head[|//|??]. { solve_sub_redexes_are_values. } destruct_all?; simplify_eq.
      case_match => //; simplify_eq/=.
      revert select (ectx_in_bij _ (_ :: _) _) => /ectx_in_bij_cons_inv_l[Ki'[?[?[??]]]]; simplify_eq.
      destruct Ki' => //; simplify_eq/=.
      invert_all @head_step; destruct_all?; simplify_eq.
      tstep_s. tstep_s.
      eexists bij'. split!. 1: split; split!; set_solver. 1: done. 1: econs; [done|econs]. 1: done. 1: done. tend.
      split!. 1: done. 1: reflexivity. all: split!.
    + move: Hprim => /prim_step_inv[//|??]. destruct_all?; simplify_eq.
      revert select (expr_in_bij _ (expr_fill _ _) _) => /expr_in_bij_fill_l[?[?[?[??]]]].
      revert select (Is_true (static_expr _ _)) => /static_expr_expr_fill/=[??]//.
      invert_all @head_step; destruct_all?; simplify_eq.
      all: repeat (case_match; destruct_all? => //); simplify_eq.
      * tstep_s => ? /eval_binop_bij Hbin. have [?[??]]:= Hbin _ _ _ ltac:(done) ltac:(done).
        tend. split!. 1: done. 1: done. all: split!.
      * tstep_s => *; simplify_eq/=. destruct v1 => //; simplify_eq/=; destruct_all?; simplify_eq/=. tend.
        have [//|?[??]]:= heap_in_bij_lookup _ _ _ _ _ _ ltac:(done) ltac:(done) ltac:(done).
        split!. 1: done. 1: done. 1: done. all: split!.
      * tstep_s => *; simplify_eq/=. destruct v1 => //; simplify_eq/=; destruct_all?; simplify_eq/=. tend.
        split!. 1: by apply: heap_in_bij_alive. 1: done. 1: done. all: split!.
        1: by apply: heap_preserved_bij_env.
        1: by apply heap_in_bij_update.
      * tstep_s => *; simplify_eq/=.
        set (l' := (heap_fresh (hb_provs_right bij') hs)).
        eexists l'. split; [apply heap_fresh_is_fresh|] => *; simplify_eq/=. tend.
        destruct v => //; simplify_eq/=; destruct_all?; simplify_eq/=.
        split!. 1: done.
        unshelve instantiate (1:=(heap_bij_add_loc l.1 l'.1 bij' _ _)).
        { abstract (apply: not_elem_of_weaken; [|done]; unfold heap_is_fresh in *; naive_solver). }
        { apply: heap_fresh_not_in. }
        all: split!.
        1: { apply heap_preserved_bij_env_alloc; [|done] => ?.
             apply: (heap_fresh_not_in (hb_provs_right bij') hs). set_solver. }
        1: { apply: ectx_in_bij_mono; [by apply ectx_in_bij_app|set_solver]. }
        1: set_solver.
        1: unfold heap_is_fresh in *; naive_solver.
        1: { apply: (heap_in_bij_alloc l l').
             { abstract (apply: not_elem_of_weaken; [|done]; unfold heap_is_fresh in *; naive_solver). }
             { apply: heap_fresh_not_in. }
          done. done. apply heap_fresh_is_fresh. }
        1: set_solver.
        1: set_solver.
      * tstep_s => *; simplify_eq/=. tend.
        destruct v => //; simplify_eq/=; destruct_all?; simplify_eq/=.
        split!. 1: by apply: heap_in_bij_alive. 1: done. 1: done. all: split!.
        1: by apply: heap_preserved_bij_env_free.
        1: by apply heap_in_bij_free.
      * tstep_s => *; simplify_eq/=. destruct v => //; simplify_eq/=. tend.
        split!. 1: done. 1: done. all: split!. all: by case_match.
      * tstep_s. tend. split!. 1: done. 1: done. all: split!.
        1: by apply expr_in_bij_subst.
        1: by apply static_expr_subst.
      * tstep_s. done.
      * revert select (Forall id _) => /Forall_zip_with_1 Hall.
        move: (Hall ltac:(done)) => /Forall2_bij_val_inv_l[?[??]]; simplify_eq.
        tstep_s. left. split! => *. tend.
        split!. 1: solve_length. 1: done. 1: done. all: split!.
        1: { apply expr_in_bij_subst_l; [|done|solve_length]. apply expr_in_bij_static. apply fd_static. }
        apply static_expr_subst_l; [|solve_length]. apply static_expr_mono. apply fd_static.
      * revert select (Forall id _) => /Forall_zip_with_1 Hall.
        move: (Hall ltac:(done)) => /Forall2_bij_val_inv_l[?[??]]; simplify_eq.
        simplify_eq. tstep_s. right. split! => *. tstep_s.
        eexists bij'. split!. 1: split; split!; set_solver. 1,2,3,4: done. tend.
        split!. 1: by apply: IHBRE_Ctx. 1: reflexivity. all: split!.
Qed.
