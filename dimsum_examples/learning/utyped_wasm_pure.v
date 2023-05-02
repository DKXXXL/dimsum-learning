From dimsum.core Require Export proof_techniques seq_product link prepost.
From dimsum.core Require Import axioms.

Inductive val := | ValNum (z : nat) 
  | ValBool (b : bool) 
  (* | ValLoc (l : loc) *)
  .

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
  
Record wasm_state := WASM {
    st_inss  : stkOps;
    st_defs  : gmap string stkOps;
  }.

Inductive wasm_ev : Type :=
| EWJump (fn : string).


Definition wasm_event := io_event wasm_ev.

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


Definition eval_binop (op : binop) (v1 v2 : val) : option val :=
  match op with
  | AddOp => z1 ← val_to_nat v1; z2 ← val_to_nat v2; Some (ValNum (z1 + z2))
  | EqOp =>
      match v1 with
      | ValNum z1 => z2 ← val_to_nat v2; Some (ValBool (bool_decide (z1 = z2)))
      | ValBool b1 => b2 ← val_to_bool v2; Some (ValBool (bool_decide (b1 = b2)))
      end
  | LeOp => z1 ← val_to_nat v1; z2 ← val_to_nat v2; Some (ValBool (bool_decide (z1 ≤ z2)))
  | LtOp => z1 ← val_to_nat v1; z2 ← val_to_nat v2; Some (ValBool (bool_decide (z1 < z2)))
  end.