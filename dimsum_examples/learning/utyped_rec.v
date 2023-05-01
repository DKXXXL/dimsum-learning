(* Here we test about 
    1. linking between two utyped_rec and showing properties like rec-link-horizontal in the paper
    2. memory non-interference might be provable at WASM level?
        if so we might directly prove 
        a. (well-typed ) generate well-typed WASM
        b. prove well-typed WASM has non-interference 
    3. it is also possible non provable at WASM level:
        because checked pointer is compiled to raw pointer (the original load instruction)
          
    *)
(* Basically a reconstruction of the original proof, but much simpler *)

(* mostly copy and paste from rec.v *)


From dimsum.core Require Export proof_techniques seq_product link prepost.
From dimsum.core Require Import axioms.

Local Open Scope Z_scope.


(* OpSem for utyped Rec *)

Definition loc := nat.
Inductive val := | ValNum (z : nat) | ValBool (b : bool) | ValLoc (l : loc).

Inductive binop : Set :=
| AddOp | OffsetOp | EqOp | LeOp | LtOp.

Inductive expr : Set :=
| Var (v : string)
| Val (v : val)
| BinOp (e1 : expr) (o : binop) (e2 : expr)
| Load (e : expr)
| Store (e1 e2 : expr)
| LetE (v : string) (e1 e2 : expr)
| Call (f : string) (args : list expr)
(* expressions only appearing at runtime: *)
| AllocA (ls : list (string * nat)) (e : expr)
(* | FreeA (ls : list (loc * Z)) (e : expr) *)
(* Returning to the context, insert automatically during execution. *)
| ReturnExt (can_return_further : bool) (e : expr)
| Waiting (can_return : bool)
.

(** ** Substitution *)
Fixpoint subst (x : string) (v : val) (e : expr) : expr :=
  match e with
  | Var y => if bool_decide (x = y) then Val v else Var y
  | Val v => Val v
  | BinOp e1 o e2 => BinOp (subst x v e1) o (subst x v e2)
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  (* | If e e1 e2 => If (subst x v e) (subst x v e1) (subst x v e2) *)
  | LetE y e1 e2 => LetE y (subst x v e1) (if bool_decide (x ≠ y) then subst x v e2 else e2)
  | Call f args => Call f (subst x v <$> args)
  | AllocA ls e => AllocA ls (subst x v e)
  (* | FreeA ls e => FreeA ls (subst x v e) *)
  | ReturnExt b e => ReturnExt b (subst x v e)
  | Waiting b => Waiting b
  end.

(* our opsem is a bit special, 
  because we have to adhere to the style of DimSum
     *)

(* we need to define 
1. rec_state  -- record running state
2. rec_event  -- event for interaction between modules 
3. rec_step
4. function body and whole program definition  *)
  
Record rec_state := Rec {
  st_expr : expr;
  st_heap : heap_state;
  st_fns : gmap string fndef;
}.