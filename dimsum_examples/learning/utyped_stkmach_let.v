
(* Untyped version *)
Require Import Coq.Lists.List.
Import ListNotations.

Inductive lit : Set :=
  | litNum : nat -> lit.

Inductive val : Set :=
  | valLit : lit -> val.
  (* | valLabel : nat -> val. *)

Definition binop := lit -> lit -> option lit.

(* OpSem for utyped WASM, don't consider memory first *)
Inductive stkOp : Set :=
  (* | weaken : forall m n, stkOp m n -> stkOp (S m) (S n) *)
  | const  : val -> stkOp 
  | bin : binop -> stkOp
  (* | alloc  : stkOp 1 1
  | load   : stkOp 1 1 
  | store  : stkOp 2 0  *)
  | drop    : nat -> stkOp.

Definition stkOps := list stkOp.

Definition stk := list val.

Inductive step : stk -> stkOp -> stk -> Prop := 
  | st_const : forall v l,
      step l (const v) (v :: l)
  | st_bin : forall f a b c l,
      f a b = Some c ->
      step (valLit a :: valLit b :: l) (bin f) (valLit c :: l)
  | st_drop : forall l1 l2 n,
      List.length l1 = n ->
      step (l1 ++ l2) (drop n) l2.

Definition cfg : Set := stk * stkOps.

