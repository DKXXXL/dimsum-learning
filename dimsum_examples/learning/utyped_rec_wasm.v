(* Here we test about 
    1. semantic wrapping, and the property compiler-correct and rec-wrapper-compat ... etc in the paper *)
(* Basically a reconstruction of the original proof, but much simpler *)




Inductive val := | ValNum (z : Z) | ValBool (b : bool) | ValLoc (l : loc).

Inductive binop : Set :=
| AddOp | OffsetOp | EqOp | LeOp | LtOp.

Inductive expr : Set :=
| Var (v : string)
| Val (v : val)
(* | BinOp (e1 : expr) (o : binop) (e2 : expr) *)
| Load (e : expr)
| Store (e1 e2 : expr)
| LetE (v : string) (e1 e2 : expr)
| Call (f : string) (args : list expr)
(* expressions only appearing at runtime: *)
| AllocA (ls : list (string * Z)) (e : expr)
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
  | If e e1 e2 => If (subst x v e) (subst x v e1) (subst x v e2)
  | LetE y e1 e2 => LetE y (subst x v e1) (if bool_decide (x ≠ y) then subst x v e2 else e2)
  | Call f args => Call f (subst x v <$> args)
  | AllocA ls e => AllocA ls (subst x v e)
  | FreeA ls e => FreeA ls (subst x v e)
  | ReturnExt b e => ReturnExt b (subst x v e)
  | Waiting b => Waiting b
  end.