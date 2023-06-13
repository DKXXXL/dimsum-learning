
(* Untyped version *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Inductive lit : Set :=
  | litNum : nat -> lit.

Inductive val : Set :=
  | valLit : lit -> val.
  (* | valLabel : nat -> val. *)
Definition binop := lit -> lit -> option lit.

Module STKM.






(* OpSem for utyped WASM, don't consider memory first *)
Inductive stkOp : Set :=
  (* | weaken : forall m n, stkOp m n -> stkOp (S m) (S n) *)
  | const  : val -> stkOp 
  | binstkop : binop -> stkOp
  | get : nat -> stkOp
  (* | alloc  : stkOp 1 1
  | load   : stkOp 1 1 
  | store  : stkOp 2 0  *)
  | drop    : nat -> stkOp.

Definition stkOps := list stkOp.

Definition stk := list val.




Inductive step : stk -> stkOp -> stk -> Prop := 
  | st_const : forall v l,
      step l (const v) (v :: l)
  | st_get : forall i v l,
      nth_error l i = Some v ->
      step l (get i) (v :: l) 
  | st_bin : forall f a b c l,
      f a b = Some c ->
      step (valLit a :: valLit b :: l) (binstkop f) (valLit c :: l)
  | st_drop : forall l1 l2 n,
      List.length l1 = n ->
      step (l1 ++ l2) (drop n) l2.

Definition cfg : Set := stk * stkOps.


End STKM.


Module LET.

Definition ID : Set := string.


Inductive EVal : Set :=
  | Var : ID -> EVal
  | Const : val -> EVal. 

Inductive EComp : Set := 
| Lets : ID -> EComp -> EComp -> EComp 
| BinOp : binop -> EVal -> EVal -> EComp
| res : EVal -> EComp.
(* | alloc : forall {G T}, expr G T -> expr G (tyref T)
| assign : forall {G T}, expr G (tyref T) -> expr G T -> expr G T 
| deref : forall {G T}, expr G (tyref T) -> expr G T *)

Definition env := list val.

Inductive ECont : Set :=
  | CLet : ID -> ECont -> EComp -> ECont.

Inductive step : env -> EComp -> ECont ->
                 env -> EComp -> ECont -> Prop :=
  | st_lets : forall E x binding body K,
    step E (Lets x binding body) K 
         E binding (CLet x K body)
  | st_lets_res : 
    step E ()
  | st_binop :
