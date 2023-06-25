
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
| rs : EVal -> EComp.

(* | alloc : forall {G T}, expr G T -> expr G (tyref T)
| assign : forall {G T}, expr G (tyref T) -> expr G T -> expr G T 
| deref : forall {G T}, expr G (tyref T) -> expr G T *)

(* Definition env := list val. *)
Axiom env : Set.
Axiom add : env -> ID -> val -> env.


Axiom val_of_EVal : env -> EVal -> option val.

Inductive ECont : Set :=
  | END : ECont
  (* continuation will store the original environment *)
  | CLet : ID -> ECont -> EComp -> ECont
  | CLetPop : env -> ECont -> ECont.

Inductive step : env -> EComp -> ECont ->
                 env -> EComp -> ECont -> Prop :=
  | st_lets : forall E x binding body K,
    step E (Lets x binding body) K 
         E binding (CLet x K body)
  | st_rsv_lets0 : forall v ev E x K body,
    val_of_EVal E ev = Some v ->
    step E           (rs ev) (CLet x K body)
         (add E x v) body    (CLetPop E K)
  | st_rsv_lets1 : forall v ev E1 E K,
    val_of_EVal E1 ev = Some v ->
    step E1 (rs ev) (CLetPop E K)
         E  (rs (Const v)) K.

End LET.


(* Now we start compilation *)

