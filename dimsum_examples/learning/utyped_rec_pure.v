(* Here we test about 
    1. linking between two utyped_rec and showing properties like rec-link-horizontal in the paper
    2. don't talk about memory at all .. we just talk about compilation now
    *)
(* Basically a reconstruction of the original proof, but much simpler *)

(* mostly copy and paste from rec.v *)


From dimsum.core Require Export proof_techniques seq_product link prepost.
From dimsum.core Require Import axioms.

(* Local Open Scope Z_scope. *)


(* OpSem for utyped Rec *)

Definition loc := nat.
Inductive val := | ValNum (z : nat) 
  | ValBool (b : bool) 
  | ValLoc (l : loc).

Inductive binop : Set :=
| AddOp 
(* | OffsetOp  *)
| EqOp | LeOp | LtOp.

Inductive expr : Set :=
| Var (v : string)
| Val (v : val)
| BinOp (e1 : expr) (o : binop) (e2 : expr)

| LetE (v : string) (e1 e2 : expr)
| Call (f : string) (args : list expr)

| ReturnExt (can_return_further : bool) (e : expr)
| Waiting (can_return : bool)
.

(** ** Substitution *)
Fixpoint subst (x : string) (v : val) (e : expr) : expr :=
  match e with
  | Var y => if bool_decide (x = y) then Val v else Var y
  | Val v => Val v
  | BinOp e1 o e2 => BinOp (subst x v e1) o (subst x v e2)

  | LetE y e1 e2 => LetE y (subst x v e1) (if bool_decide (x ≠ y) then subst x v e2 else e2)
  | Call f args => Call f (subst x v <$> args)

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

  | LetE y e1 e2 => LetE y (subst_map x e1) (subst_map (delete y x) e2)
  | Call f args => Call f (subst_map x <$> args)

  | ReturnExt b e => ReturnExt b (subst_map x e)
  | Waiting b => Waiting b
  end.

(* evluation context and fill in *)
Inductive expr_ectx :=
| BinOpLCtx (op : binop) (e2 : expr)
| BinOpRCtx (v1 : val) (op : binop)

| LetECtx (v : string) (e2 : expr)
| CallCtx (f : string) (vl : list val) (el : list expr)

| ReturnExtCtx (can_return_further : bool)
.

Definition expr_fill_item (Ki : expr_ectx) (e : expr) : expr :=
  match Ki with
  | BinOpLCtx op e2 => BinOp e op e2
  | BinOpRCtx v1 op => BinOp (Val v1) op e

  | LetECtx v e2 => LetE v e e2
  | CallCtx f vl el => Call f ((Val <$> vl) ++ e :: el)

  | ReturnExtCtx b => ReturnExt b e
  end.

Definition expr_fill (K : list expr_ectx) (e : expr) : expr :=
  foldl (flip expr_fill_item) e K.
(* our opsem is a bit special, 
  because we have to adhere to the style of DimSum
     *)

(* we need to define 
1. rec_state  -- record running state
2. rec_event  -- event for interaction between modules 
3. rec_step
4. function body and whole program definition  *)

Record fndef : Type := {
  fd_params : list string;
  fd_body : expr;
  (* fd_static : is_static_expr false fd_body; *)
}.


Record rec_state := Rec {
  st_expr : expr;
  st_fns : gmap string fndef;
}.

(** ** rec_event *)
(* we will pass state with the event as well *)
Inductive rec_ev : Type :=
| ERCall (fn : string) (args: list val) 
| ERReturn (ret: val) .


Definition rec_event := io_event rec_ev.

(* binop evaluation *)

Definition val_to_nat (v : val) : option nat :=
  match v with
  | ValNum z => Some z
  | _ => None
  end.
Definition val_to_bool (v : val) : option bool :=
  match v with
  | ValBool b => Some b
  | _ => None
  end.
Definition val_to_loc (v : val) : option nat :=
  match v with
  | ValLoc l => Some l
  | _ => None
  end.

Definition eval_binop (op : binop) (v1 v2 : val) : option val :=
  match op with
  | AddOp => z1 ← val_to_nat v1; z2 ← val_to_nat v2; Some (ValNum (z1 + z2))
  | EqOp =>
      match v1 with
      | ValNum z1 => z2 ← val_to_nat v2; Some (ValBool (bool_decide (z1 = z2)))
      | ValBool b1 => b2 ← val_to_bool v2; Some (ValBool (bool_decide (b1 = b2)))
      | _ => None
      end
  | LeOp => z1 ← val_to_nat v1; z2 ← val_to_nat v2; Some (ValBool (bool_decide (z1 ≤ z2)))
  | LtOp => z1 ← val_to_nat v1; z2 ← val_to_nat v2; Some (ValBool (bool_decide (z1 < z2)))
  end.

(* heap handling *)

Inductive head_step : rec_state → option rec_event → (rec_state → Prop) → Prop :=
| BinOpS v1 op v2 fns:
  head_step (Rec (BinOp (Val v1) op (Val v2)) fns) None (λ σ',
    ∃ v, eval_binop op v1 v2 = Some v ∧ σ' = Rec (Val v) fns)

| LetS x v e fns:
  head_step (Rec (LetE x (Val v) e) fns) None (λ σ, σ = Rec (subst x v e) fns)
| VarES fns v: (* unbound variable *)
  head_step (Rec (Var v) fns) None (λ σ, False)

| CallInternalS f fn fns vs:
  fns !! f = Some fn →
  head_step (Rec (Call f (Val <$> vs)) fns) None (λ σ,
   length vs = length fn.(fd_params) ∧
   σ = Rec  (subst_l fn.(fd_params) vs fn.(fd_body)) fns)
| CallExternalS f fns vs :
  fns !! f = None →
  head_step (Rec (Call f (Val <$> vs)) fns) (Some (Outgoing, ERCall f vs)) (λ σ, σ = Rec (Waiting true) fns)
| ReturnS fns v b:
  head_step (Rec (ReturnExt b (Val v)) fns) (Some (Outgoing, ERReturn v)) (λ σ, σ = (Rec (Waiting b) fns))
| RecvCallS fns f fn vs b :
  fns !! f = Some fn →
  head_step (Rec (Waiting b) fns) (Some (Incoming, ERCall f vs )) (λ σ,
    σ = (Rec (ReturnExt b (Call f (Val <$> vs)))  fns))
| RecvReturnS fns v:
  head_step (Rec (Waiting true) fns) (Some (Incoming, ERReturn v)) (λ σ, σ = (Rec (Val v)  fns))
.

Inductive prim_step : rec_state → option rec_event → (rec_state → Prop) → Prop :=
  Ectx_step K e e' fns κ Pσ:
    e = expr_fill K e' →
    head_step (Rec e' fns) κ Pσ →
    prim_step (Rec e fns) κ (λ σ, ∃ e2 fns2, Pσ (Rec e2 fns2) ∧ σ = Rec (expr_fill K e2) fns2).


Definition rec_trans := ModTrans prim_step.
Definition rec_init (fns : gmap string fndef) : rec_state :=
  Rec (Waiting false) fns.
Definition rec_mod (fns : gmap string fndef) := Mod rec_trans (rec_init fns).

(* above are the operational semantics for utyped_rec_pure *)
