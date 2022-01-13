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

Inductive expr : Set :=
| Var (v : string)
| Val (v : val)
| BinOp (e1 : expr) (o : binop) (e2 : expr)
| If (e e1 e2 : expr)
| LetE (v : string) (e1 e2 : expr)
| Call (f : string) (args : list expr)
(* Returning to the context, insert automatically during execution. *)
| ReturnExt (e : expr)
| Waiting
.
Coercion Val : val >-> expr.

Fixpoint subst (x : string) (v : val) (e : expr) : expr :=
  match e with
  | Var y => if bool_decide (x = y) then Val v else Var y
  | Val v => Val v
  | BinOp e1 o e2 => BinOp (subst x v e1) o (subst x v e2)
  | If e e1 e2 => If (subst x v e) (subst x v e1) (subst x v e2)
  | LetE y e1 e2 => LetE y (subst x v e1) (if bool_decide (x ≠ y) then subst x v e2 else e2)
  | Call f args => Call f (subst x v <$> args)
  | ReturnExt e => ReturnExt (subst x v e)
  | Waiting => Waiting
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
.

Definition expr_fill_item (Ki : expr_ectx) (e : expr) : expr :=
  match Ki with
  | BinOpLCtx op e2 => BinOp e op e2
  | BinOpRCtx v1 op => BinOp v1 op e
  | IfCtx e2 e3 => If e e2 e3
  | LetECtx v e2 => LetE v e e2
  | CallCtx f vl el => Call f ((Val <$> vl) ++ e :: el)
  end.

Definition expr_fill (K : list expr_ectx) (e : expr) : expr :=
  foldl (flip expr_fill_item) e K.

Record fndef : Type := {
  fd_args : list string;
  fd_body : expr;
}.

Record imp_state := Imp {
  st_expr : expr;
  st_fns : gmap string fndef;
}.
Add Printing Constructor imp_state.

Definition initial_imp_state (fns : gmap string fndef) :=
  Imp Waiting fns.

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
| CallInternalS f fn fns vs:
  fns !! f = Some fn →
  head_step (Imp (Call f (Val <$> vs)) fns) None (λ σ,
   length vs = length fn.(fd_args) ∧
   σ = Imp (subst_l fn.(fd_args) vs fn.(fd_body)) fns)
| CallExternalS f fns vs:
  fns !! f = None →
  head_step (Imp (Call f (Val <$> vs)) fns) (Some (EICall f vs)) (λ σ, σ = Imp Waiting fns)
| ReturnS fns v:
  head_step (Imp (ReturnExt (Val v)) fns) (Some (EIReturn v)) (λ σ, σ = (Imp Waiting fns))
| RecvCallS fns f fn vs:
  fns !! f = Some fn →
  length vs = length fn.(fd_args) →
  head_step (Imp Waiting fns) (Some (EIRecvCall f vs)) (λ σ,
    σ = (Imp (ReturnExt (subst_l fn.(fd_args) vs fn.(fd_body))) fns))
| RecvReturnS fns v:
  head_step (Imp Waiting fns) (Some (EIRecvReturn v)) (λ σ, σ = (Imp (Val v) fns))
.

Inductive prim_step : imp_state → option imp_event → (imp_state → Prop) → Prop :=
  Ectx_step K e e' fns κ Pσ:
    e = expr_fill K e' →
    head_step (Imp e' fns) κ Pσ →
    prim_step (Imp e fns) κ (λ σ, ∃ e2 fns2, Pσ (Imp e2 fns2) ∧ σ = Imp (expr_fill K e2) fns2).

Definition imp_module := Mod prim_step.

Global Instance imp_vis_no_all: VisNoAll imp_module.
Proof. move => *. invert_all' @m_step; invert_all head_step; naive_solver. Qed.

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
                  (Some (EIReturn v)) (IPFState (IPFLeftRecvReturn v) cs)
(* ret ext -> r *)
| IPFReturnExtToRight v cs:
  imp_prod_filter fns1 fns2 (IPFState IPFNone (IPFRight :: cs)) (SPENone SPRight)
                  (Some (EIReturn v)) (IPFState (IPFRightRecvReturn v) cs)
.

Definition imp_prod (fns1 fns2 : gset string) (m1 m2 : module imp_event) : module imp_event :=
  mod_map (mod_seq_product m1 m2) (imp_prod_filter fns1 fns2).
Global Hint Transparent imp_prod : tstep.

Lemma imp_link_refines_prod fns1 fns2:
  fns1 ##ₘ fns2 →
  trefines (MS imp_module (initial_imp_state (imp_link fns1 fns2)))
           (MS (imp_prod (dom _ fns1) (dom _ fns2) imp_module imp_module)
               (SPNone, initial_imp_state fns1, initial_imp_state fns2, (IPFState IPFNone []))).
Proof.
  move => Hdisj.
  apply tsim_implies_trefines => /= n.
Admitted.

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
