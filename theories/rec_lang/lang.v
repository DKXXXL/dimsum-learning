Require Import stdpp.strings.
Require Import stdpp.propset.
From iris.program_logic Require Export language ectx_language ectxi_language.
Require Export refframe.base.
Require Export refframe.module.

Definition fn_name := string.
Definition var_name := string.

Inductive binop : Set :=
| AddOp | EqOp.

Inductive val := | ValNum (z : Z).
Coercion ValNum : Z >-> val.
Global Instance val_eq_dec : EqDecision val.
Proof. solve_decision. Qed.

Inductive expr : Set :=
| Var (v : var_name)
| Val (v : val)
| BinOp (e1 : expr) (o : binop) (e2 : expr)
| If (e e1 e2 : expr)
| LetE (v : var_name) (e1 e2 : expr)
| Call (f : fn_name) (args : list expr)
| Waiting
.
Coercion Val : val >-> expr.

Fixpoint subst (x : var_name) (v : val) (e : expr) : expr :=
  match e with
  | Var y => if bool_decide (x = y) then Val v else Var y
  | Val v => Val v
  | BinOp e1 o e2 => BinOp (subst x v e1) o (subst x v e2)
  | If e e1 e2 => If (subst x v e) (subst x v e1) (subst x v e2)
  | LetE y e1 e2 => LetE y (subst x v e1) (if bool_decide (x ≠ y) then subst x v e2 else e2)
  | Call f args => Call f (subst x v <$> args)
  | Waiting => Waiting
  end.
Fixpoint subst_l (xs : list var_name) (vs : list val) (e : expr) : expr :=
  match xs, vs with
  | x::xs', v::vs' => subst_l xs' vs' (subst x v e)
  | _,_ => e
  end.

Inductive expr_ectx :=
| BinOpLCtx (op : binop) (e2 : expr)
| BinOpRCtx (v1 : val) (op : binop)
| IfCtx (e2 e3 : expr)
| LetECtx (v : var_name) (e2 : expr)
| CallCtx (f : fn_name) (vl : list val) (el : list expr)
.

Definition expr_fill_item (Ki : expr_ectx) (e : expr) : expr :=
  match Ki with
  | BinOpLCtx op e2 => BinOp e op e2
  | BinOpRCtx v1 op => BinOp v1 op e
  | IfCtx e2 e3 => If e e2 e3
  | LetECtx v e2 => LetE v e e2
  | CallCtx f vl el => Call f ((Val <$> vl) ++ e :: el)
  end.

Record fndef : Type := {
  fd_args : list var_name;
  fd_body : expr;
}.

Record rec_state := {
  st_fns : gmap fn_name fndef;
}.

Inductive rec_event : Type :=
| RecvCallEvt (fn : fn_name) (args: list val) | RecvRetEvt (ret: val)
| CallEvt (fn : fn_name) (args: list val) | DoneEvt (ret: val).

Inductive step : expr → rec_state → list rec_event → expr → rec_state → list expr → Prop :=
| BinOpStep n1 op n2 σ:
    step (BinOp (Val (ValNum n1)) op (Val (ValNum n2))) σ []
         (match op with | AddOp => n1 + n2 | EqOp => Z_of_bool $ bool_decide (n1 = n2) end%Z) σ []
| IfStep n e1 e2 σ:
    step (If (Val (ValNum n)) e1 e2) σ [] (if bool_decide (n ≠ 0) then e1 else e2) σ []
| LetStep x v e σ:
    step (LetE x (Val v) e) σ [] (subst x v e) σ []
| CallInternalStep f fn σ vs:
    σ.(st_fns) !! f = Some fn →
    length vs = length fn.(fd_args) →
    step (Call f (Val <$> vs)) σ [] (subst_l fn.(fd_args) vs fn.(fd_body)) σ []
| CallExternalStep f σ vs:
    σ.(st_fns) !! f = None →
    step (Call f (Val <$> vs)) σ [CallEvt f vs] Waiting σ []
| RecvReturnStep σ v:
    step Waiting σ [RecvRetEvt v] (Val v)  σ []
(* (* External Calls *) *)
(* | CallExternalStep f vas ρ cs fns nas: *)
(*     Forall2 (λ n v, ρ !! n = Some v) vas nas → *)
(*     fns !! f = None → *)
(*     step {| st_exp := Running (Call f vas); st_env := ρ; st_conts := cs; st_fns := fns |} *)
(*          (Some (CallEvt f nas)) *)
(*          {| st_exp := WaitingForReturn; st_env := ρ; st_conts := cs; st_fns := fns |} *)
(* | RecvReturnStep ρ cs fns n: *)
(*     step {| st_exp := WaitingForReturn; st_env := ρ; st_conts := cs; st_fns := fns |} *)
(*          (Some (RecvRetEvt n)) *)
(*          {| st_exp := Running (Const n); st_env := ρ; st_conts := cs; st_fns := fns |} *)
(* | RecvCallStep ρ cs fns nas σ fn f: *)
(*     fns !! f = Some fn → *)
(*     σ = (if bool_decide (length nas = length fn.(fd_args)) then Running fn.(fd_body) else Stuck) → *)
(*     step {| st_exp := WaitingForCall; st_env := ρ; st_conts := cs; st_fns := fns |} *)
(*          (Some (RecvCallEvt f nas)) *)
(*          {| st_exp := σ; st_env := list_to_map (zip fn.(fd_args) nas); st_conts := cs; st_fns := fns |} *)
(* (* Const steps *) *)
(* | ConstConsStep n c ρ fns cs: *)
(*     step {| st_exp := Running (Const n); st_env := ρ; st_conts := c::cs; st_fns := fns |} *)
(*          None *)
(*          {| st_exp := Running c.(c_expr); st_env := <[c.(c_var) := n]>c.(c_env); st_conts := cs; st_fns := fns |} *)
(* | ConstNilStep n ρ fns: *)
(*     step {| st_exp := Running (Const n); st_env := ρ; st_conts := []; st_fns := fns |} *)
(*          (Some (DoneEvt n)) *)
(*          {| st_exp := Finished; st_env := ρ; st_conts := []; st_fns := fns |} *)
(* . *).



Definition to_val (e : expr) : option val := if e is Val v then Some v else None.
Definition of_val (v : val) : expr := Val v.

Lemma list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2 :
  (Val <$> vl1) ++ e1 :: el1 = (Val <$> vl2) ++ e2 :: el2 →
  to_val e1 = None → to_val e2 = None →
  vl1 = vl2 ∧ e1 = e2 ∧ el1 = el2.
Proof.
  revert vl2; induction vl1; destruct vl2; inversion 1; intros He1 He2.
  - done.
  - subst. by inversion He1.
  - subst. by inversion He2.
  - destruct (IHvl1 vl2); auto. split; f_equal; auto.
Qed.
Lemma list_expr_val_eq_false vl1 vl2 e el :
  to_val e = None → Val <$> vl1 = (Val <$> vl2) ++ e :: el → False.
Proof.
  move => He. elim: vl2 vl1 => [[]//=*|v vl2 IH [|??]?]; csimpl in *; simplify_eq; eauto.
Qed.


Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. case: e => //. naive_solver. Qed.

Lemma val_stuck e1 σ1 κ e2 σ2 ef :
  step e1 σ1 κ e2 σ2 ef → to_val e1 = None.
Proof. destruct 1 => //. Qed.

Instance fill_item_inj Ki : Inj (=) (=) (expr_fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (expr_fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  expr_fill_item Ki1 e1 = expr_fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  move: Ki1 Ki2 => [ ^ Ki1] [ ^Ki2] He1 He2 HEQ //; simplify_eq => //.
  efeed pose proof list_expr_val_eq_inv => //. naive_solver.
Qed.

Lemma expr_ctx_step_val Ki e σ1 κ e2 σ2 ef :
  step (expr_fill_item Ki e) σ1 κ e2 σ2 ef → is_Some (to_val e).
Proof.
  destruct Ki; inversion 1; simplify_eq/=; eauto.
  all: apply not_eq_None_Some; intros ?; by eapply list_expr_val_eq_false.
Qed.

Lemma rec_lang_mixin : EctxiLanguageMixin of_val to_val expr_fill_item step.
Proof.
  split => //; eauto using of_to_val, val_stuck, fill_item_inj, fill_item_val, fill_item_no_val_inj, expr_ctx_step_val.
Qed.
Canonical Structure rec_ectxi_lang := EctxiLanguage rec_lang_mixin.
Canonical Structure rec_ectx_lang := EctxLanguageOfEctxi rec_ectxi_lang.
Canonical Structure rec_lang := LanguageOfEctx rec_ectx_lang.

Instance val_inhabited : Inhabited val := populate $ ValNum 1.
Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).
Instance fndef_inhabited : Inhabited fndef := populate {| fd_args := []; fd_body := inhabitant |}.
Instance state_inhabited : Inhabited rec_state := populate {| st_fns := inhabitant |}.

Canonical Structure fndefO := leibnizO fndef.
