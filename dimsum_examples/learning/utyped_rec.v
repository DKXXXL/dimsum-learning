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

(* Local Open Scope Z_scope. *)


(* OpSem for utyped Rec *)

Definition loc := nat.
Inductive val := | ValNum (z : nat) 
  | ValBool (b : bool) 
  | ValLoc (l : loc).

Inductive binop : Set :=
| AddOp 
(* | OffsetOp  *)
| EqOp | LeOp | LtOp.

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

Fixpoint subst_map (x : gmap string val) (e : expr) : expr :=
  match e with
  | Var y => if x !! y is Some v then Val v else Var y
  | Val v => Val v
  | BinOp e1 o e2 => BinOp (subst_map x e1) o (subst_map x e2)
  | Load e => Load (subst_map x e)
  | Store e1 e2 => Store (subst_map x e1) (subst_map x e2)
  (* | If e e1 e2 => If (subst_map x e) (subst_map x e1) (subst_map x e2) *)
  | LetE y e1 e2 => LetE y (subst_map x e1) (subst_map (delete y x) e2)
  | Call f args => Call f (subst_map x <$> args)
  | AllocA ls e => AllocA ls (subst_map x e)
  (* | FreeA ls e => FreeA ls (subst_map x e) *)
  | ReturnExt b e => ReturnExt b (subst_map x e)
  | Waiting b => Waiting b
  end.

(* evluation context and fill in *)
Inductive expr_ectx :=
| BinOpLCtx (op : binop) (e2 : expr)
| BinOpRCtx (v1 : val) (op : binop)
| LoadCtx
| StoreLCtx (e2 : expr)
| StoreRCtx (v1 : val)
(* | IfCtx (e2 e3 : expr) *)
| LetECtx (v : string) (e2 : expr)
| CallCtx (f : string) (vl : list val) (el : list expr)
(* why there is no AllocaA? Weird *)
(* | FreeACtx (ls : list (loc * Z)) *)
| ReturnExtCtx (can_return_further : bool)
.

Definition expr_fill_item (Ki : expr_ectx) (e : expr) : expr :=
  match Ki with
  | BinOpLCtx op e2 => BinOp e op e2
  | BinOpRCtx v1 op => BinOp (Val v1) op e
  | LoadCtx => Load e
  | StoreLCtx e2 => Store e e2
  | StoreRCtx v1 => Store (Val v1) e
  (* | IfCtx e2 e3 => If e e2 e3 *)
  | LetECtx v e2 => LetE v e e2
  | CallCtx f vl el => Call f ((Val <$> vl) ++ e :: el)
  (* why there is no AllocaA? Weird *)
  (* | FreeACtx ls => FreeA ls e *)
  | ReturnExtCtx b => ReturnExt b e
  end.


(* our opsem is a bit special, 
  because we have to adhere to the style of DimSum
     *)

(* we need to define 
1. rec_state  -- record running state
2. rec_event  -- event for interaction between modules 
3. rec_step
4. function body and whole program definition  *)

Record fndef : Type := {
  fd_params : list string;
  fd_body : expr;
  (* fd_static : is_static_expr false fd_body; *)
}.

Record heap_state : Set := Heap {
  h_heap : gmap loc val;
  (* h_provs : gset prov;
  heap_wf l : is_Some (h_heap !! l) → l.1 ∈ h_provs; *)
}.

Record rec_state := Rec {
  st_expr : expr;
  st_heap : heap_state;
  st_fns : gmap string fndef;
}.

(** ** rec_event *)
(* we will pass state with the event as well *)
Inductive rec_ev : Type :=
| EVCall (fn : string) (args: list val) (h : heap_state)
| EVReturn (ret: val) (h : heap_state).


Definition rec_event := io_event rec_ev.

(* binop evaluation *)

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
Definition val_to_loc (v : val) : option nat :=
  match v with
  | ValLoc l => Some l
  | _ => None
  end.

Definition eval_binop (op : binop) (v1 v2 : val) : option val :=
  match op with
  | AddOp => z1 ← val_to_nat v1; z2 ← val_to_nat v2; Some (ValNum (z1 + z2))
  (* | OffsetOp => l ← val_to_loc v1; z ← val_to_nat v2; Some (ValLoc (l + z)) *)
  | EqOp =>
      match v1 with
      | ValNum z1 => z2 ← val_to_nat v2; Some (ValBool (bool_decide (z1 = z2)))
      | ValBool b1 => b2 ← val_to_bool v2; Some (ValBool (bool_decide (b1 = b2)))
      | _ => None
      end
  | LeOp => z1 ← val_to_nat v1; z2 ← val_to_nat v2; Some (ValBool (bool_decide (z1 ≤ z2)))
  | LtOp => z1 ← val_to_nat v1; z2 ← val_to_nat v2; Some (ValBool (bool_decide (z1 < z2)))
  end.

(* heap handling *)

Inductive head_step : rec_state → option rec_event → (rec_state → Prop) → Prop :=
| BinOpS v1 op v2 h fns:
  head_step (Rec (BinOp (Val v1) op (Val v2)) h fns) None (λ σ',
    ∃ v, eval_binop op v1 v2 = Some v ∧ σ' = Rec (Val v) h fns)
| LoadS v1 h fns:
  head_step (Rec (Load (Val v1)) h fns) None (λ σ',
    ∃ l v, v1 = ValLoc l ∧ h.(h_heap) !! l = Some v ∧ σ' = Rec (Val v) h fns)
| StoreS v1 v h fns:
  head_step (Rec (Store (Val v1) (Val v)) h fns) None (λ σ',
    ∃ l, v1 = ValLoc l 
    (* ∧ heap_alive h l  *)
    ∧ σ' = Rec (Val v) (heap_update h l v) fns)
(* | IfS v fns e1 e2 h:
  head_step (Rec (If (Val v) e1 e2) h fns) None (λ σ,
       ∃ b, val_to_bool v = Some b ∧ σ = Rec (if b then e1 else e2) h fns) *)
| LetS x v e fns h:
  head_step (Rec (LetE x (Val v) e) h fns) None (λ σ, σ = Rec (subst x v e) h fns)
| VarES fns h v: (* unbound variable *)
  head_step (Rec (Var v) h fns) None (λ σ, False)
| AllocAS h h' fns ls xs e:
  heap_alloc_list xs.*2 ls h h' →
  head_step (Rec (AllocA xs e) h fns) None (λ σ',
    Forall (λ x, 0 < x) xs.*2 ∧ σ' = Rec (FreeA (zip ls xs.*2) (subst_l xs.*1 (ValLoc <$> ls) e)) h' fns)
(* | FreeAS h fns ls v:
  head_step (Rec (FreeA ls (Val v)) h fns) None (λ σ',
    ∃ h', heap_free_list ls h h' ∧ σ' = Rec (Val v) h' fns) *)
| CallInternalS f fn fns vs h:
  fns !! f = Some fn →
  head_step (Rec (Call f (Val <$> vs)) h fns) None (λ σ,
   length vs = length fn.(fd_args) ∧
   σ = Rec (AllocA fn.(fd_vars) (subst_l fn.(fd_args) vs fn.(fd_body))) h fns)
| CallExternalS f fns vs h:
  fns !! f = None →
  head_step (Rec (Call f (Val <$> vs)) h fns) (Some (Outgoing, ERCall f vs h)) (λ σ, σ = Rec (Waiting true) h fns)
| ReturnS fns v b h:
  head_step (Rec (ReturnExt b (Val v)) h fns) (Some (Outgoing, ERReturn v h)) (λ σ, σ = (Rec (Waiting b) h fns))
| RecvCallS fns f fn vs b h h':
  fns !! f = Some fn →
  head_step (Rec (Waiting b) h fns) (Some (Incoming, ERCall f vs h')) (λ σ,
    σ = (Rec (ReturnExt b (Call f (Val <$> vs))) h' fns))
| RecvReturnS fns v h h':
  head_step (Rec (Waiting true) h fns) (Some (Incoming, ERReturn v h')) (λ σ, σ = (Rec (Val v) h' fns))
.
