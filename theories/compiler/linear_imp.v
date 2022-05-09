Require Import refframe.imp.

Inductive var_val :=
| VVar (v : string)
| VVal (v : static_val).

Definition var_val_to_expr (v : var_val) : expr :=
  match v with
  | VVar v => Var v
  | VVal v => Val (static_val_to_val v)
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

Lemma var_val_is_static v :
  is_static_expr false (var_val_to_expr v).
Proof. destruct v => //=. by destruct v. Qed.

Lemma lexpr_op_is_static e :
  is_static_expr false (lexpr_op_to_expr e).
Proof.
  destruct e => //=; rewrite ?andb_True; split!; try apply var_val_is_static.
  apply forallb_True. rewrite Forall_fmap. apply Forall_true => ?. apply var_val_is_static.
Qed.

Lemma lexpr_is_static e :
  is_static_expr false (lexpr_to_expr e).
Proof. elim: e => //= *; rewrite ?andb_True; split!; apply lexpr_op_is_static. Qed.

Record lfndef : Type := {
  lfd_args : list string;
  lfd_vars : list (string * Z);
  lfd_body : lexpr;
}.

Program Definition lfndef_to_fndef (fn : lfndef) : fndef := {|
   fd_args := fn.(lfd_args);
   fd_vars := fn.(lfd_vars);
   fd_body := lexpr_to_expr fn.(lfd_body);
|}.
Next Obligation. move => ?. apply lexpr_is_static. Qed.

Definition initial_imp_lstate (fns : gmap string lfndef) : imp_state :=
  initial_imp_state (lfndef_to_fndef <$> fns).