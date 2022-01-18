Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.filter.
Require Import refframe.product.
Require Import refframe.seq_product.
Require Import refframe.proof_techniques.

Local Open Scope Z_scope.

(** * C-like language language *)
Inductive binop : Set :=
| AddOp | EqOp.

Inductive val := | ValNum (z : Z) | ValBool (b : bool).
Coercion ValNum : Z >-> val.
Global Instance val_eq_dec : EqDecision val.
Proof. solve_decision. Qed.

Definition val_to_Z (v : val) : option Z :=
  match v with
  | ValNum z => Some z
  | _ => None
  end.
Definition val_to_bool (v : val) : option bool :=
  match v with
  | ValBool b => Some b
  | _ => None
  end.

Section expr.
Local Unset Elimination Schemes.
Inductive expr : Set :=
| Var (v : string)
| Val (v : val)
| BinOp (e1 : expr) (o : binop) (e2 : expr)
| If (e e1 e2 : expr)
| LetE (v : string) (e1 e2 : expr)
| Call (f : string) (args : list expr)
| UbE
(* Returning to the context, insert automatically during execution. *)
| ReturnExt (can_return_further : bool) (e : expr)
| Waiting (can_return : bool)
.
End expr.
Lemma expr_ind (P : expr → Prop) :
  (∀ (x : string), P (Var x)) →
  (∀ (v : val), P (Val v)) →
  (∀ (e1 : expr) (op : binop) (e2 : expr), P e1 → P e2 → P (BinOp e1 op e2)) →
  (∀ (e1 e2 e3 : expr), P e1 → P e2 → P e3 → P (If e1 e2 e3)) →
  (∀ (v : string) (e1 e2 : expr), P e1 → P e2 → P (LetE v e1 e2)) →
  (∀ (f : string) (args : list expr), Forall P args → P (Call f args)) →
  (P UbE) →
  (∀ (can_return_further : bool) (e : expr), P e → P (ReturnExt can_return_further e)) →
  (∀ (can_return : bool), P (Waiting can_return)) →
  ∀ (e : expr), P e.
Proof.
  move => *. generalize dependent P => P. match goal with | e : expr |- _ => revert e end.
  fix FIX 1. move => [ ^e] => ????? Hcall ???.
  6: { apply Hcall. apply Forall_true => ?. by apply: FIX. }
  all: auto.
Qed.
Coercion Val : val >-> expr.

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

Fixpoint subst (x : string) (v : val) (e : expr) : expr :=
  match e with
  | Var y => if bool_decide (x = y) then Val v else Var y
  | Val v => Val v
  | BinOp e1 o e2 => BinOp (subst x v e1) o (subst x v e2)
  | If e e1 e2 => If (subst x v e) (subst x v e1) (subst x v e2)
  | LetE y e1 e2 => LetE y (subst x v e1) (if bool_decide (x ≠ y) then subst x v e2 else e2)
  | Call f args => Call f (subst x v <$> args)
  | UbE => UbE
  | ReturnExt b e => ReturnExt b (subst x v e)
  | Waiting b => Waiting b
  end.
Fixpoint subst_l (xs : list string) (vs : list val) (e : expr) : expr :=
  match xs, vs with
  | x::xs', v::vs' => subst_l xs' vs' (subst x v e)
  | _,_ => e
  end.

Inductive expr_ectx :=
| BinOpLCtx (op : binop) (e2 : expr)
| BinOpRCtx (v1 : val) (op : binop)
| IfCtx (e2 e3 : expr)
| LetECtx (v : string) (e2 : expr)
| CallCtx (f : string) (vl : list val) (el : list expr)
| ReturnExtCtx (can_return_further : bool)
.

Definition expr_fill_item (Ki : expr_ectx) (e : expr) : expr :=
  match Ki with
  | BinOpLCtx op e2 => BinOp e op e2
  | BinOpRCtx v1 op => BinOp v1 op e
  | IfCtx e2 e3 => If e e2 e3
  | LetECtx v e2 => LetE v e e2
  | CallCtx f vl el => Call f ((Val <$> vl) ++ e :: el)
  | ReturnExtCtx b => ReturnExt b e
  end.

Global Instance expr_fill_item_inj Ki : Inj (=) (=) (expr_fill_item Ki).
Proof. destruct Ki => ??? //=; by simplify_eq/=. Qed.

Lemma list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2 :
  to_val e1 = None → to_val e2 = None →
  (Val <$> vl1) ++ e1 :: el1 = (Val <$> vl2) ++ e2 :: el2 →
  vl1 = vl2 ∧ e1 = e2 ∧ el1 = el2.
Proof.
  revert vl2; induction vl1; destruct vl2; intros H1 H2; inversion 1.
  - done.
  - subst. by inversion H1.
  - subst. by inversion H2.
  - destruct (IHvl1 vl2); auto. split; f_equal; auto.
Qed.

Lemma list_expr_val_inv vl1 vl2 e2 el2 :
  (Val <$> vl1) = (Val <$> vl2) ++ e2 :: el2 →
  is_Some (to_val e2).
Proof. revert vl2; induction vl1; destruct vl2 => //?; simplify_eq/=; naive_solver. Qed.

Lemma fill_item_val Ki e : is_Some (to_val (expr_fill_item Ki e)) → is_Some (to_val e).
Proof. destruct Ki => //=; move => [??] //. Qed.

Lemma expr_fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  expr_fill_item Ki1 e1 = expr_fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1, Ki2 => //= *; simplify_eq => //.
  efeed pose proof list_expr_val_eq_inv; [| |done|]; naive_solver.
Qed.

Definition expr_fill (K : list expr_ectx) (e : expr) : expr :=
  foldl (flip expr_fill_item) e K.

Lemma expr_fill_app K1 K2 e:
  expr_fill (K2 ++ K1) e = expr_fill K1 (expr_fill K2 e).
Proof. apply foldl_app. Qed.

Lemma fill_val K e : is_Some (to_val (expr_fill K e)) → is_Some (to_val e).
Proof.
  elim/rev_ind: K e => //?? IH e. rewrite expr_fill_app /= => ?.
  apply IH. by apply: fill_item_val.
Qed.

Fixpoint static_expr (e : expr) : bool :=
  match e with
  | Var v => true
  | Val v => true
  | BinOp e1 o e2 => static_expr e1 && static_expr e2
  | If e e1 e2 => static_expr e && static_expr e1 && static_expr e2
  | LetE v e1 e2 => static_expr e1 && static_expr e2
  | Call f args => forallb static_expr args
  | UbE => true
  | ReturnExt can_return_further e => false
  | Waiting can_return => false
  end.

Lemma static_expr_subst x v e:
  static_expr e →
  static_expr (subst x v e).
Proof.
  elim: e => //= *; try naive_solver.
  - by case_bool_decide.
  - case_bool_decide; naive_solver.
  - apply forallb_True, Forall_forall => ? /elem_of_list_fmap[?[??]]. subst.
    revert select (Forall _ _) => /Forall_forall.
    revert select (Is_true (forallb _ _)) => /forallb_True/Forall_forall. naive_solver.
Qed.

Lemma static_expr_subst_l xs vs e:
  static_expr e →
  length xs = length vs →
  static_expr (subst_l xs vs e).
Proof.
  elim: xs vs e. { by case. }
  move => ?? IH [//|??] /=???. apply IH; [|lia].
  by apply static_expr_subst.
Qed.

Lemma static_expr_expr_fill K e:
  static_expr (expr_fill K e) ↔ static_expr (expr_fill K (Var "")) ∧ static_expr e.
Proof.
  elim/rev_ind: K e => /=. { naive_solver. }
  move => Ki K IH e. rewrite !expr_fill_app/=.
  destruct Ki => //=; rewrite ?forallb_app/=; naive_solver.
Qed.

Record fndef : Type := {
  fd_args : list string;
  fd_body : expr;
  fd_static : static_expr fd_body;
}.

Record imp_state := Imp {
  st_expr : expr;
  st_fns : gmap string fndef;
}.
Add Printing Constructor imp_state.

Definition initial_imp_state (fns : gmap string fndef) : imp_state :=
  Imp (Waiting false) fns.

Inductive imp_event : Type :=
| EICall (fn : string) (args: list val) | EIReturn (ret: val)
| EIRecvCall (fn : string) (args: list val) | EIRecvReturn  (ret: val).

Definition eval_binop (op : binop) (v1 v2 : val) : option val :=
  match op with
  | AddOp => z1 ← val_to_Z v1; z2 ← val_to_Z v2; Some (ValNum (z1 + z2))
  | EqOp => z1 ← val_to_Z v1; z2 ← val_to_Z v2; Some (ValBool (bool_decide (z1 = z2)))
  end.

(* TODO: alternative idea: Define semantics as state → itree moduleE state
   Then put an itree forever around it after adding the evaluation context
This way one can reuse infrastructure
*)
Inductive head_step : imp_state → option imp_event → (imp_state → Prop) → Prop :=
| BinOpS v1 op v2 fns:
  head_step (Imp (BinOp (Val v1) op (Val v2)) fns) None (λ σ',
    ∃ v, eval_binop op v1 v2 = Some v ∧ σ' = Imp v fns)
| IfS v fns e1 e2:
  head_step (Imp (If (Val v) e1 e2) fns) None (λ σ,
       ∃ b, val_to_bool v = Some b ∧ σ = Imp (if b then e1 else e2) fns)
| LetS x v e fns:
  head_step (Imp (LetE x (Val v) e) fns) None (λ σ, σ = Imp (subst x v e) fns)
| UbES fns:
  head_step (Imp UbE fns) None (λ σ, False)
| CallInternalS f fn fns vs:
  fns !! f = Some fn →
  head_step (Imp (Call f (Val <$> vs)) fns) None (λ σ,
   length vs = length fn.(fd_args) ∧
   σ = Imp (subst_l fn.(fd_args) vs fn.(fd_body)) fns)
| CallExternalS f fns vs:
  fns !! f = None →
  head_step (Imp (Call f (Val <$> vs)) fns) (Some (EICall f vs)) (λ σ, σ = Imp (Waiting true) fns)
| ReturnS fns v b:
  head_step (Imp (ReturnExt b (Val v)) fns) (Some (EIReturn v)) (λ σ, σ = (Imp (Waiting b) fns))
| RecvCallS fns f fn vs b:
  fns !! f = Some fn →
  head_step (Imp (Waiting b) fns) (Some (EIRecvCall f vs)) (λ σ,
    σ = (Imp (if bool_decide (length vs = length fn.(fd_args)) then
                ReturnExt b (subst_l fn.(fd_args) vs fn.(fd_body))
              else
                UbE) fns))
| RecvReturnS fns v:
  head_step (Imp (Waiting true) fns) (Some (EIRecvReturn v)) (λ σ, σ = (Imp (Val v) fns))
.

Definition sub_redexes_are_values (e : expr) :=
  ∀ K e', e = expr_fill K e' → to_val e' = None → K = [].

Lemma sub_redexes_are_values_item e :
  (∀ Ki e', e = expr_fill_item Ki e' → is_Some (to_val e')) →
  sub_redexes_are_values e.
Proof.
  move => Hitem. elim/rev_ind => //= ?? IH?.
  rewrite expr_fill_app /= => /Hitem/fill_val[??].
  naive_solver.
Qed.

Ltac solve_sub_redexes_are_values := apply sub_redexes_are_values_item; case; naive_solver.

Global Instance expr_fill_inj K : Inj (=) (=) (expr_fill K).
Proof. induction K as [|Ki K IH]; rewrite /Inj; naive_solver. Qed.

Lemma val_head_stuck e1 σ1 κ Pσ : head_step (Imp e1 σ1) κ Pσ → to_val e1 = None.
Proof. by inversion 1. Qed.

Lemma head_ctx_step_val Ki e σ1 κ Pσ :
  head_step (Imp (expr_fill_item Ki e) σ1) κ Pσ → is_Some (to_val e).
Proof. destruct Ki; inversion 1; simplify_eq => //; by apply: list_expr_val_inv. Qed.

Lemma head_fill_step_val K e σ1 κ Pσ :
  to_val e = None →
  head_step (Imp (expr_fill K e) σ1) κ Pσ →
  K = [].
Proof.
  elim/rev_ind: K => //=????. rewrite expr_fill_app /= => /head_ctx_step_val /fill_val[??].
  naive_solver.
Qed.

Lemma step_by_val K K' e1' e1_redex σ1 κ Pσ :
  expr_fill K e1' = expr_fill K' e1_redex →
  to_val e1' = None →
  head_step (Imp e1_redex σ1) κ Pσ →
  ∃ K'', K' = K'' ++ K.
Proof.
  assert (fill_val : ∀ K e, is_Some (to_val (expr_fill K e)) → is_Some (to_val e)).
  { intros K''. induction K'' as [|Ki K'' IH]=> e //=. by intros ?%IH%fill_item_val. }
  assert (fill_not_val : ∀ K e, to_val e = None → to_val (expr_fill K e) = None).
  { intros ? e. rewrite !eq_None_not_Some. eauto. }

  intros Hfill Hred Hstep; revert K' Hfill.
  induction K as [|Ki K IH] using rev_ind=> /= K' Hfill; eauto using app_nil_r.
  destruct K' as [|Ki' K' _] using @rev_ind; simplify_eq/=.
  { rewrite expr_fill_app in Hstep. apply head_ctx_step_val in Hstep.
    apply fill_val in Hstep. by apply not_eq_None_Some in Hstep. }
  rewrite !expr_fill_app /= in Hfill.
  assert (Ki = Ki') as ->.
  { eapply expr_fill_item_no_val_inj, Hfill; eauto using val_head_stuck. }
  simplify_eq. destruct (IH K') as [K'' ->]; auto.
  exists K''. by rewrite assoc.
Qed.

Inductive prim_step : imp_state → option imp_event → (imp_state → Prop) → Prop :=
  Ectx_step K e e' fns κ Pσ:
    e = expr_fill K e' →
    head_step (Imp e' fns) κ Pσ →
    prim_step (Imp e fns) κ (λ σ, ∃ e2 fns2, Pσ (Imp e2 fns2) ∧ σ = Imp (expr_fill K e2) fns2).

Lemma prim_step_inv K e fns κ Pσ:
  prim_step (Imp (expr_fill K e) fns) κ Pσ →
  to_val e = None →
  ∃ K' e' Pσ', e = expr_fill K' e' ∧ head_step (Imp e' fns) κ Pσ' ∧
      Pσ = (λ σ, ∃ e2 fns2, Pσ' (Imp e2 fns2) ∧ σ = Imp (expr_fill (K' ++ K) e2) fns2).
Proof.
  inversion 1; simplify_eq => ?.
  revert select (expr_fill _ _ = expr_fill _ _) => Heq. move: (Heq) => /step_by_val Hg.
  have [//|? ?]:= Hg _ _ _ _ ltac:(done). subst.
  rewrite expr_fill_app in Heq. naive_solver.
Qed.

Lemma prim_step_inv_head K e fns κ Pσ:
  prim_step (Imp (expr_fill K e) fns) κ Pσ →
  sub_redexes_are_values e →
  to_val e = None →
  ∃ Pσ', head_step (Imp e fns) κ Pσ' ∧
      Pσ = (λ σ, ∃ e2 fns2, Pσ' (Imp e2 fns2) ∧ σ = Imp (expr_fill K e2) fns2).
Proof.
  move => Hprim Hsub ?.
  move: Hprim => /prim_step_inv[|?[?[?[?[Hstep ?]]]]]. { done. } subst.
  have ->:= Hsub _ _ ltac:(done). { by apply: val_head_stuck. }
  naive_solver.
Qed.

Definition imp_module := Mod prim_step.
Global Hint Transparent imp_module : tstep.

Global Instance imp_vis_no_all: VisNoAll imp_module.
Proof. move => *. invert_all' @m_step; invert_all head_step; naive_solver. Qed.

(** * tstep *)
Lemma imp_step_UbE_s fns K:
  TStepS imp_module (Imp (expr_fill K UbE) fns) (λ G, G None (λ G', True)).
Proof.
  constructor => ? HG. eexists _, _. split; [done|] => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?. naive_solver.
Qed.
Global Hint Resolve imp_step_UbE_s : tstep.

Lemma imp_step_Waiting_i fns K b:
  TStepI imp_module (Imp (expr_fill K (Waiting b)) fns) (λ G,
    (∀ f fn vs, fns !! f = Some fn →
      G true (Some (EIRecvCall f vs)) (λ G',  G'
          (Imp (expr_fill K (
           if bool_decide (length vs = length (fd_args fn)) then
             ReturnExt b ((subst_l fn.(fd_args) vs fn.(fd_body)))
           else
             UbE)) fns))) ∧
    ∀ v, b → G true (Some (EIRecvReturn v)) (λ G', G' (Imp (expr_fill K v) fns))
   ).
Proof.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  invert_all head_step.
  - naive_solver.
  - naive_solver.
Qed.
Global Hint Resolve imp_step_Waiting_i : tstep.

Lemma imp_step_Waiting_s fns K b:
  TStepS imp_module (Imp (expr_fill K (Waiting b)) fns) (λ G,
    (∃ f fn vs, fns !! f = Some fn ∧
      G (Some (EIRecvCall f vs)) (λ G', G'
          (Imp (expr_fill K (if bool_decide (length vs = length (fd_args fn)) then
                               ReturnExt b ((subst_l fn.(fd_args) vs fn.(fd_body)))
                             else
                               UbE)) fns))) ∨
    ∃ v, b ∧ G (Some (EIRecvReturn v)) (λ G', G' (Imp (expr_fill K v) fns))
   ).
Proof.
  constructor => ? HG. destruct_all!; (split!; [done|]) => /= ??. 2: destruct b => //.
  all: apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?; destruct_all?; simplify_eq; done.
Qed.
Global Hint Resolve imp_step_Waiting_s : tstep.

Lemma imp_step_ReturnExt_i fns K b (v : val):
  TStepI imp_module (Imp (expr_fill K (ReturnExt b v)) fns) (λ G,
    (G true (Some (EIReturn v)) (λ G', G' (Imp (expr_fill K (Waiting b)) fns)))).
Proof.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  invert_all head_step.
  naive_solver.
Qed.
Global Hint Resolve imp_step_ReturnExt_i : tstep.

Lemma imp_step_ReturnExt_s fns K b (v : val):
  TStepS imp_module (Imp (expr_fill K (ReturnExt b v)) fns) (λ G,
    (G (Some (EIReturn v)) (λ G', G' (Imp (expr_fill K (Waiting b)) fns)))).
Proof.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct_all?; simplify_eq. done.
Qed.
Global Hint Resolve imp_step_ReturnExt_s : tstep.


(** * syntactic linking *)
Definition imp_link (fns1 fns2 : gmap string fndef) : gmap string fndef :=
  fns1 ∪ fns2.

Definition imp_ctx_refines (fnsi fnss : gmap string fndef) :=
  ∀ C, trefines (MS imp_module (initial_imp_state (imp_link fnsi C)))
                (MS imp_module (initial_imp_state (imp_link fnss C))).

(** * semantic linking *)
Inductive imp_prod_filter_enum :=
| IPFLeft | IPFRight | IPFNone
| IPFLeftRecvCall (f : string) (vs : list val)
| IPFRightRecvCall (f : string) (vs : list val)
| IPFLeftRecvReturn (v : val)
| IPFRightRecvReturn (v : val)
.
Record imp_prod_filter_state := IPFState {
  ipf_cur : imp_prod_filter_enum;
  (* list of returns *)
  ipf_stack : list imp_prod_filter_enum
}.
Add Printing Constructor imp_prod_filter_state.

Inductive imp_prod_filter (fns1 fns2 : gset string) :
  imp_prod_filter_state → (seq_product_event imp_event imp_event) →
  option imp_event → imp_prod_filter_state → Prop :=
(* call l -> r *)
| IPFCallLeftToRight f vs cs:
  f ∉ fns1 → f ∈ fns2 →
  imp_prod_filter fns1 fns2 (IPFState IPFLeft cs) (SPELeft (EICall f vs) SPRight)
                  None (IPFState (IPFRightRecvCall f vs) (IPFLeft :: cs))
(* call l -> r step 2 *)
| IPFCallLeftToRight2 f vs cs:
  imp_prod_filter fns1 fns2 (IPFState (IPFRightRecvCall f vs) cs) (SPERight (EIRecvCall f vs) SPRight)
                  None (IPFState IPFRight cs)
(* call r -> l *)
| IPFCallRightToLeft f vs cs:
  f ∈ fns1 → f ∉ fns2 →
  imp_prod_filter fns1 fns2 (IPFState IPFRight cs) (SPERight (EICall f vs) SPLeft)
                  None (IPFState (IPFLeftRecvCall f vs) (IPFRight :: cs))
(* call r -> l step 2*)
| IPFCallRightToLeft2 f vs cs:
  imp_prod_filter fns1 fns2 (IPFState (IPFLeftRecvCall f vs) cs) (SPELeft (EIRecvCall f vs) SPLeft)
                  None (IPFState IPFLeft cs)
(* call l -> ext *)
| IPFCallLeftToExt f vs cs:
  f ∉ fns1 → f ∉ fns2 →
  imp_prod_filter fns1 fns2 (IPFState IPFLeft cs) (SPELeft (EICall f vs) SPNone)
                  (Some (EICall f vs)) (IPFState IPFNone (IPFLeft :: cs))
(* call r -> ext *)
| IPFCallRightToExt f vs cs:
  f ∉ fns1 → f ∉ fns2 →
  imp_prod_filter fns1 fns2 (IPFState IPFRight cs) (SPERight (EICall f vs) SPNone)
                  (Some (EICall f vs)) (IPFState IPFNone (IPFRight :: cs))
(* call ext -> l *)
| IPFCallExtToLeft f vs cs:
  f ∈ fns1 → f ∉ fns2 →
  imp_prod_filter fns1 fns2 (IPFState IPFNone cs) (SPENone SPLeft)
                  (Some (EIRecvCall f vs)) (IPFState (IPFLeftRecvCall f vs) (IPFNone :: cs))
(* call ext -> r *)
| IPFCallExtToRight f vs cs:
  f ∉ fns1 → f ∈ fns2 →
  imp_prod_filter fns1 fns2 (IPFState IPFNone cs) (SPENone SPRight)
                  (Some (EIRecvCall f vs)) (IPFState (IPFRightRecvCall f vs) (IPFNone :: cs))
(* ret l -> r *)
| IPFReturnLeftToRight v cs:
  imp_prod_filter fns1 fns2 (IPFState IPFLeft (IPFRight :: cs)) (SPELeft (EIReturn v) SPRight)
                  None (IPFState (IPFRightRecvReturn v) cs)
(* ret l -> r step 2 *)
| IPFReturnLeftToRight2 v cs:
  imp_prod_filter fns1 fns2 (IPFState (IPFRightRecvReturn v) cs) (SPERight (EIRecvReturn v) SPRight)
                  None (IPFState IPFRight cs)
(* ret r -> l *)
| IPFReturnRightToLeft v cs:
  imp_prod_filter fns1 fns2 (IPFState IPFRight (IPFLeft :: cs)) (SPERight (EIReturn v) SPLeft)
                  None (IPFState (IPFLeftRecvReturn v) cs)
(* ret l -> r step 2 *)
| IPFReturnRightToLeft2 v cs:
  imp_prod_filter fns1 fns2 (IPFState (IPFLeftRecvReturn v) cs) (SPELeft (EIRecvReturn v) SPLeft)
                  None (IPFState IPFLeft cs)
(* ret l -> ext *)
| IPFReturnLeftToExt v cs:
  imp_prod_filter fns1 fns2 (IPFState IPFLeft (IPFNone :: cs)) (SPELeft (EIReturn v) SPNone)
                  (Some (EIReturn v)) (IPFState IPFNone cs)
(* ret r -> ext *)
| IPFReturnRightToExt v cs:
  imp_prod_filter fns1 fns2 (IPFState IPFRight (IPFNone :: cs)) (SPERight (EIReturn v) SPNone)
                  (Some (EIReturn v)) (IPFState IPFNone cs)
(* ret ext -> l *)
| IPFReturnExtToLeft v cs:
  imp_prod_filter fns1 fns2 (IPFState IPFNone (IPFLeft :: cs)) (SPENone SPLeft)
                  (Some (EIRecvReturn v)) (IPFState (IPFLeftRecvReturn v) cs)
(* ret ext -> r *)
| IPFReturnExtToRight v cs:
  imp_prod_filter fns1 fns2 (IPFState IPFNone (IPFRight :: cs)) (SPENone SPRight)
                  (Some (EIRecvReturn v)) (IPFState (IPFRightRecvReturn v) cs)
.

Definition imp_prod (fns1 fns2 : gset string) (m1 m2 : module imp_event) : module imp_event :=
  mod_map (mod_seq_product m1 m2) (imp_prod_filter fns1 fns2).
Global Hint Transparent imp_prod : tstep.

Inductive imp_link_prod_combine_ectx :
  nat → bool → bool → imp_prod_filter_state → list expr_ectx → list expr_ectx → list expr_ectx → Prop :=
| IPCENil:
  imp_link_prod_combine_ectx 0 false false (IPFState IPFNone []) [] [] []
| IPCENoneToLeft n cs K Kl Kr bl br:
  imp_link_prod_combine_ectx n bl br (IPFState IPFNone cs) K Kl Kr →
  imp_link_prod_combine_ectx (S n) bl br (IPFState IPFLeft (IPFNone :: cs))
                             (ReturnExtCtx (bl || br)::K) (ReturnExtCtx bl::Kl) Kr
| IPCENoneToRight n cs K Kl Kr bl br:
  imp_link_prod_combine_ectx n bl br (IPFState IPFNone cs) K Kl Kr →
  imp_link_prod_combine_ectx (S n) bl br (IPFState IPFRight (IPFNone :: cs))
                             (ReturnExtCtx (bl || br)::K) Kl (ReturnExtCtx br::Kr)
| IPCELeftToRight n cs K Kl Kl' Kr bl br:
  imp_link_prod_combine_ectx n bl br (IPFState IPFLeft cs) K Kl Kr →
  static_expr (expr_fill Kl' (Var "")) →
  imp_link_prod_combine_ectx (S n) true br (IPFState IPFRight (IPFLeft :: cs))
                             (Kl' ++ K) (Kl' ++ Kl) (ReturnExtCtx br::Kr)
| IPCELeftToNone n cs K Kl Kl' Kr bl br:
  imp_link_prod_combine_ectx n bl br (IPFState IPFLeft cs) K Kl Kr →
  static_expr (expr_fill Kl' (Var "")) →
  imp_link_prod_combine_ectx (S n) true br (IPFState IPFNone (IPFLeft :: cs))
                             (Kl' ++ K) (Kl' ++ Kl) Kr
| IPCERightToLeft n cs K Kl Kr' Kr bl br:
  imp_link_prod_combine_ectx n bl br (IPFState IPFRight cs) K Kl Kr →
  static_expr (expr_fill Kr' (Var "")) →
  imp_link_prod_combine_ectx (S n) bl true (IPFState IPFLeft (IPFRight :: cs))
                             (Kr' ++ K) (ReturnExtCtx bl::Kl) (Kr' ++ Kr)
| IPCERightToNone n cs K Kl Kr' Kr bl br:
  imp_link_prod_combine_ectx n bl br (IPFState IPFRight cs) K Kl Kr →
  static_expr (expr_fill Kr' (Var "")) →
  imp_link_prod_combine_ectx (S n) bl true (IPFState IPFNone (IPFRight :: cs))
                             (Kr' ++ K) Kl (Kr' ++ Kr)
.

Definition imp_link_prod_inv (bv : bool) (fns1 fns2 : gmap string fndef) (σ1 : imp_module.(m_state)) (σ2 : ((seq_product_state * imp_state * imp_state) * imp_prod_filter_state)) : Prop :=
  let 'Imp e1 fns1' := σ1 in
  let '((σsp, Imp el fnsl, Imp er fnsr), σf) := σ2 in
  ∃ n K Kl Kr e1' el' er' bl br,
  fns1' = fns1 ∪ fns2 ∧
  fnsl = fns1 ∧
  fnsr = fns2 ∧
  imp_link_prod_combine_ectx n bl br σf K Kl Kr ∧
  e1 = expr_fill K e1' ∧
  el = expr_fill Kl el' ∧
  er = expr_fill Kr er' ∧
  match σf.(ipf_cur) with
  | IPFLeft => σsp = SPLeft ∧ e1' = el' ∧ static_expr el' ∧ er' = Waiting br
              ∧ (if bv then to_val el' = None else True)
  | IPFRight => σsp = SPRight ∧ e1' = er' ∧ static_expr er' ∧ el' = Waiting bl
               ∧ (if bv then to_val er' = None else True)
  | IPFNone => σsp = SPNone ∧ e1' = Waiting (bl || br) ∧ el' = Waiting bl ∧ er' = Waiting br
  | _ => False
  end.

Lemma imp_link_refines_prod fns1 fns2:
  fns1 ##ₘ fns2 →
  trefines (MS imp_module (initial_imp_state (imp_link fns1 fns2)))
           (MS (imp_prod (dom _ fns1) (dom _ fns2) imp_module imp_module)
               (SPNone, initial_imp_state fns1, initial_imp_state fns2, (IPFState IPFNone []))).
Proof.
  move => Hdisj.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { exact: (λ _, imp_link_prod_inv true fns1 fns2). }
  { split!. 1: by econs. all: done. } { done. }
  move => /= {}n Hloop [e1 fns1'] [[[? [el fnsl]] [er fnsr] [ipfs cs]]] [K [Kl [Kr ?]]].
  have {}Hloop : ∀ σi σs,
            imp_link_prod_inv false fns1 fns2 σi σs
            → σi ⪯{imp_module, imp_prod (dom (gset string) fns1) (dom (gset string) fns2) imp_module imp_module, n, true} σs. {
    clear -Hloop. move => [e1 fns1'] [[[sp [el fnsl]] [er fnsr] [ipfs cs]]].
    move => [m [K [Kl [Kr [e1' [el' [er' [bl [br [?[?[?[HK[?[?[? Hm]]]]]]]]]]]]]]]]; simplify_eq.
    elim/lt_wf_ind: m sp ipfs cs K Kl Kr e1' el' er' bl br HK Hm => m IHm.
    move => ipfs cs sp K Kl Kr e1' el' er' bl br HK Hmatch.
    case_match; destruct_all?; simplify_eq/=.
    - destruct (to_val el') eqn:?; [ |apply: Hloop; naive_solver].
      destruct el'; simplify_eq/=.
      inversion HK; clear HK; simplify_eq/=.
      * tstep_i. tstep_s. split!; [econs|] => /=. split!.
        apply: Hloop. by split!.
      * tstep_s. split!; [econs|] => /=.
        tstep_s. right. split!; [econs|] => /=.
        rewrite !expr_fill_app. apply: IHm; [|done|]; [lia|]. split!. by apply static_expr_expr_fill.
    - destruct (to_val er') eqn:?; [ |apply: Hloop; naive_solver].
      destruct er'; simplify_eq/=.
      inversion HK; clear HK; simplify_eq/=.
      * tstep_i. tstep_s. split!; [econs|] => /=. split!. apply: Hloop. by split!.
      * tstep_s. split!; [econs|] => /=.
        tstep_s. right. split!; [econs|] => /=.
        rewrite !expr_fill_app. apply: IHm; [|done|]; [lia|]. split!. by apply static_expr_expr_fill.
    - apply: Hloop; naive_solver.
  }
  destruct_all?; simplify_eq/=. case_match; destruct_all?; simplify_eq.
  - tstep_both. apply: steps_impl_step_end => ?? /prim_step_inv[//|?[?[?[?[??]]]]].
    simplify_eq. revert select (Is_true (static_expr _)) => /static_expr_expr_fill/=[??]//.
    rewrite -expr_fill_app.
    invert_all head_step => //.
    + tstep_s. eexists None. split!; [done..|] => /=.
      apply: steps_spec_step_end; [econs; [done|by econs]|].
      move => /=*; destruct_all?; simplify_eq. tend. split!; [done..|].
      apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply static_expr_expr_fill.
    + tstep_s. eexists None. split!; [done..|] => /=.
      apply: steps_spec_step_end; [econs; [done|by econs]|].
      move => /=*; destruct_all?; simplify_eq. tend. split!; [done..|].
      apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by destruct b; apply static_expr_expr_fill.
    + tstep_s. eexists None. split!; [done..|] => /=.
      apply: steps_spec_step_end; [econs; [done|by econs]|].
      move => /=*; destruct_all?; simplify_eq. tend. split!; [done..|].
      apply: Hloop. rewrite !expr_fill_app. split!; [done..|].
      apply static_expr_expr_fill. split!. by apply static_expr_subst.
    + tstep_s. by split!.
    + revert select ((_ ∪ _) !! _ = Some _) => /lookup_union_Some_raw[?|[??]].
      * tstep_s. eexists None. split!; [done..|] => /=.
        apply: steps_spec_step_end; [econs; [done|by econs]|].
        move => /=??. destruct_all?; simplify_eq. tend. split!; [done..|].
        apply: Hloop. rewrite !expr_fill_app. split!; [done..|].
        apply static_expr_expr_fill. split!. apply static_expr_subst_l; [|done]. apply fd_static.
      * tstep_s. eexists (Some _). split!; [econs|].
        { by apply not_elem_of_dom. } { by apply elem_of_dom. } simpl.
        apply: steps_spec_step_end; [econs; [done|by econs]|].
        move => /=??. destruct_all?; simplify_eq.
        tstep_s. left. split!; [done|econs|] => /=. case_bool_decide.
        2: { tstep_s. naive_solver. }
        tend. split!; [done..|]. apply: Hloop. split!; [by econs|done..|].
        apply static_expr_subst_l; [|done]. apply fd_static.
    + revert select ((_ ∪ _) !! _ = None) => /lookup_union_None[??].
      tstep_s. eexists (Some _). split!; [apply IPFCallLeftToExt; by apply not_elem_of_dom|] => /=.
      split!; [done|]. apply: steps_spec_step_end; [econs; [done|by econs]|].
      move => /=??. destruct_all?; simplify_eq. tend. split!; [done..|].
      apply: Hloop. split!; [by econs|done..].
  - tstep_both. apply: steps_impl_step_end => ?? /prim_step_inv[//|?[?[?[?[??]]]]].
    simplify_eq. revert select (Is_true (static_expr _)) => /static_expr_expr_fill/=[??]//.
    rewrite -expr_fill_app.
    invert_all head_step => //.
    + tstep_s. eexists None. split!; [done..|] => /=.
      apply: steps_spec_step_end; [econs; [done|by econs]|].
      move => /=*; destruct_all?; simplify_eq. tend. split!; [done..|].
      apply: Hloop. rewrite !expr_fill_app. split!; [done..|].
      by apply static_expr_expr_fill.
    + tstep_s. eexists None. split!; [done..|] => /=.
      apply: steps_spec_step_end; [econs; [done|by econs]|].
      move => /=*; destruct_all?; simplify_eq. tend. split!; [done..|].
      apply: Hloop. rewrite !expr_fill_app. split!; [done..|].
      by destruct b; apply static_expr_expr_fill.
    + tstep_s. eexists None. split!; [done..|] => /=.
      apply: steps_spec_step_end; [econs; [done|by econs]|].
      move => /=*; destruct_all?; simplify_eq. tend. split!; [done..|].
      apply: Hloop. rewrite !expr_fill_app. split!; [done..|].
      apply static_expr_expr_fill. split!. by apply static_expr_subst.
    + tstep_s. by split!.
    + revert select ((_ ∪ _) !! _ = Some _) => /lookup_union_Some_raw[?|[??]].
      * have ? : fns2 !! f = None by apply: map_disjoint_Some_l.
        tstep_s. eexists (Some _). split!; [econs|].
        { by apply elem_of_dom. } { by apply not_elem_of_dom. } simpl.
        apply: steps_spec_step_end; [econs; [done|by econs]|].
        move => /=??. destruct_all?; simplify_eq.
        tstep_s. left. split!; [done|econs|] => /=. case_bool_decide.
        2: { tstep_s. naive_solver. }
        tend. split!; [done..|]. apply: Hloop. split!; [by econs|done..|].
        apply static_expr_subst_l; [|done]. apply fd_static.
      * tstep_s. eexists None. split!; [done..|] => /=.
        apply: steps_spec_step_end; [econs; [done|by econs]|].
        move => /=??. destruct_all?; simplify_eq. tend. split!; [done..|].
        apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
        apply static_expr_expr_fill. split!. apply static_expr_subst_l; [|done]. apply fd_static.
    + revert select ((_ ∪ _) !! _ = None) => /lookup_union_None[??].
      tstep_s. eexists (Some _). split!; [apply IPFCallRightToExt; by apply not_elem_of_dom|] => /=.
      split!; [done|]. apply: steps_spec_step_end; [econs; [done|by econs]|].
      move => /=??. destruct_all?; simplify_eq. tend. split!; [done..|].
      apply: Hloop. split!; [by econs|rewrite ?orb_true_r; done..].
  - tstep_i. split.
    + move => f fn vs /lookup_union_Some_raw[?|[??]].
      * have ?: fns2 !! f = None by apply: map_disjoint_Some_l.
        tstep_s. split!; [econs|]. { by apply elem_of_dom. } { by apply not_elem_of_dom. }
        simpl. split!; [done|].
        tstep_s. left. split!; [done|by econs|] => /=. case_bool_decide. 2: { tstep_s. naive_solver. }
        apply Hloop. split!; [by econs|done..| ].
        apply static_expr_subst_l; [|done]. apply fd_static.
      * tstep_s. split!; [apply IPFCallExtToRight|]. { by apply not_elem_of_dom. } { by apply elem_of_dom. }
        split!; [done|].
        tstep_s. left. split!; [done|econs|] => /=. case_bool_decide. 2: { tstep_s. naive_solver. }
        apply Hloop. split!; [by econs|done..| ].
        apply static_expr_subst_l; [|done]. apply fd_static.
    + move => v ?.
      revert select (imp_link_prod_combine_ectx _ _ _ _ _ _ _) => HK.
      inversion HK; clear HK; simplify_eq/= => //.
      * tstep_s. split!;[apply IPFReturnExtToLeft|] => /=. split!; [done|].
        tstep_s. right. split!; [econs|] => /=.
        apply Hloop. rewrite !expr_fill_app. split!; [done..|].
        by apply static_expr_expr_fill.
      * tstep_s. split!; [apply IPFReturnExtToRight|] => /=. split!; [done|].
        tstep_s. right. split!; [econs|] => /=.
        apply Hloop. rewrite !expr_fill_app. split!;[done..| ].
        by apply static_expr_expr_fill.
Qed.

Lemma imp_prod_refines_link fns1 fns2:
  fns1 ##ₘ fns2 →
  trefines (MS (imp_prod (dom _ fns1) (dom _ fns2) imp_module imp_module)
               (SPNone, initial_imp_state fns1, initial_imp_state fns2, (IPFState IPFNone [])))
           (MS imp_module (initial_imp_state (imp_link fns1 fns2))).
Proof.
  move => Hdisj.
  apply tsim_implies_trefines => /= n.
Admitted.

Lemma imp_trefines_implies_ctx_refines fnsi fnss :
  dom (gset _) fnsi = dom (gset _) fnss →
  trefines (MS imp_module (initial_imp_state fnsi)) (MS imp_module (initial_imp_state fnss)) →
  imp_ctx_refines fnsi fnss.
Proof.
  move => Hdom Href C. rewrite /imp_link map_difference_union_r (map_difference_union_r fnss).
  etrans. { apply imp_link_refines_prod. apply map_disjoint_difference_r'. }
  etrans. 2: { apply imp_prod_refines_link. apply map_disjoint_difference_r'. }
  rewrite !dom_difference_L Hdom.
  apply mod_map_trefines.
  apply: mod_seq_product_trefines.
  - apply: Href.
  - erewrite map_difference_eq_dom_L => //. apply _.
Qed.
