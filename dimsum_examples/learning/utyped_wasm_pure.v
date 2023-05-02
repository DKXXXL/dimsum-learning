From dimsum.core Require Export proof_techniques seq_product link prepost.
From dimsum.core Require Import axioms.

(* OpSem for utyped WASM, don't consider memory first *)
Inductive stkOp : nat -> nat -> Set :=
  | weaken : forall m n, stkOp m n -> stkOp (S m) (S n)
  | const  : val -> stkOp 0 1
  | binary : binop -> stkOp 2 1
  (* | alloc  : stkOp 1 1
  | load   : stkOp 1 1 
  | store  : stkOp 2 0  *)
  | nop    : stkOp 0 0.

Inductive stkOps : nat -> nat -> Set :=
  | stknil   : forall n, stkOps n n 
  | stkcons  : forall a b c, stkOps a b -> stkOp b c -> stkOps a c.
  
