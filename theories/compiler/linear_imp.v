Require Import refframe.imp.

Inductive var_val :=
| VVar (v : string)
| VVal (v : val).

Definition var_val_to_expr (v : var_val) : expr :=
  match v with
  | VVar v => Var v
  | VVal v => Val v
  end.

Inductive lexpr_op :=
| LVarVal (v : var_val)
| LBinOp (v1 : var_val) (o : binop) (v2 : var_val)
| LLoad (v : var_val)
| LStore (v1 v2 : var_val)
| LCall (f : string) (args : list var_val)
| LUbE.

Definition lexpr_op_to_expr (e : lexpr_op) : expr :=
  match e with
  | LVarVal v => var_val_to_expr v
  | LBinOp v1 o v2 => BinOp (var_val_to_expr v1) o (var_val_to_expr v2)
  | LLoad v => Load (var_val_to_expr v)
  | LStore v1 v2 => Store (var_val_to_expr v1) (var_val_to_expr v2)
  | LCall f args => Call f (var_val_to_expr <$> args)
  | LUbE => UbE
  end.

Inductive lexpr :=
| LLetE (v : string) (e1 : lexpr_op) (e2 : lexpr)
| LIf (e1 : lexpr_op) (e2 e3 : lexpr)
| LEnd (e : lexpr_op).

Fixpoint lexpr_to_expr (e : lexpr) : expr :=
  match e with
  | LLetE v e1 e2 => LetE v (lexpr_op_to_expr e1) (lexpr_to_expr e2)
  | LIf e1 e2 e3 => If (lexpr_op_to_expr e1) (lexpr_to_expr e2) (lexpr_to_expr e3)
  | LEnd e => (lexpr_op_to_expr e)
  end.
