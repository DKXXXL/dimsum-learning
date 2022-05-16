Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.filter.
Require Import refframe.product.
Require Import refframe.seq_product.
Require Import refframe.link.
Require Import stdpp.strings.
Require Import stdpp.pretty.
Require Import refframe.prepost.
Require Import refframe.proof_techniques.
Require Import refframe.imp.
Require Export refframe.compiler.monad.
Require Export refframe.compiler.linear_imp.
Require Export refframe.compiler.linearize.


Module ci2a_mem2reg.

Inductive error := UsedAsLoc.

Definition M := compiler_monad unit (fn_compiler_monoid lexpr) error.


Definition is_var (e: var_val) (x: string) :=
  if e is (VVar y) then bool_decide (x = y) else false.


Definition lexpr_op_pass (x: string) (e: lexpr_op) : M lexpr_op :=
  match e with
  | LVarVal v =>
    if is_var v x then cerror UsedAsLoc else mret $ LVarVal v
  | LBinOp v1 o v2 =>
    if is_var v1 x then cerror UsedAsLoc else
    if is_var v2 x then cerror UsedAsLoc else
    mret $ LBinOp v1 o v2
  | LLoad v =>
    if is_var v x then mret $ LVarVal v else mret $ LLoad v
  | LStore v1 v2 =>
    if is_var v2 x then cerror UsedAsLoc else
    if is_var v1 x then
      cappend (λ e, LLetE x (LVarVal v2) e);;
      mret $ LVarVal v2
    else mret $ LStore v1 v2
  | LCall f args =>
    vs ← cmap args 0 (λ _ v, if is_var v x then cerror UsedAsLoc else mret $ v);
    mret $ (LCall f vs)
  | LUbE => mret $ LUbE
  end.

Fixpoint pass (x: string) (e : lexpr) : M lexpr :=
  match e with
  | LLetE v e1 e2 =>
    if bool_decide (v = x) then
      '(e1', _) ← cscope (lexpr_op_pass x e1);
      mret $ LLetE v e1' e2
    else
      '(e1', upd) ← cscope (lexpr_op_pass x e1);
      e2' ← pass x e2;
      mret $
        LLetE v e1' $
        upd $
        e2'
  | LIf e1 e2 e3 =>
    '(e1', upd) ← cscope (lexpr_op_pass x e1);
    e2' ← pass x e2;
    e3' ← pass x e3;
    mret $ LIf e1' (upd e2') (upd e3')
  | LEnd e =>
    e' ← lexpr_op_pass x e;
    mret $ LEnd e'
  end.


Definition pass_fn (f : lfndef) : lfndef :=
  let (e, vars) := foldr (λ '(x, n) '(r, vars),
    let res := crun () (pass x r) in
    match res.(c_result) with
    | CSuccess r' => (LLetE x (LVarVal (VVal (StaticValNum 0))) r', vars)
    | CError _ => (r, (x, n)::vars)
    end
  ) (f.(lfd_body), []) f.(lfd_vars) in
  {|
     lfd_args := f.(lfd_args);
     lfd_vars := vars;
     lfd_body := e;
  |}.



Definition test_opt_fn (f: fndef) :=
  let s := fndef_to_static_fndef f in
  let c := ci2a_linearize.pass_fn s in
  let d := pass_fn <$> c in
  d.



Definition test_fn_1 : fndef := {|
  fd_args := ["y"];
  fd_vars := [("x", 4%Z)];
  fd_body := (LetE "_" (Store (Var "x") (Val 1)) (Load (Var "x")));
  fd_static := I;
|}.

Compute test_opt_fn test_fn_1.


Definition test_fn_2 : fndef := {|
  fd_args := ["y"];
  fd_vars := [("x", 4%Z); ("z", 4%Z)];
  fd_body := (LetE "_" (Store (Var "x") (Val 1))
             (LetE "_" (Store (Var "z") (Val 1))
              (BinOp (Load (Var "x")) AddOp (Var "z"))));
  fd_static := I;
|}.

Compute test_opt_fn test_fn_2.


(* TODO: this is kind of a corner case, since the expression has UB, which results in *)
Definition test_fn_3 : fndef := {|
  fd_args := ["y"];
  fd_vars := [("x", 4%Z)];
  fd_body := (BinOp (BinOp (Var "y") ShiftOp (Val 2)) AddOp (Call "f" [Load (Var "x"); Val 1]));
  fd_static := I;
|}.

Compute test_opt_fn test_fn_3.


End ci2a_mem2reg.
