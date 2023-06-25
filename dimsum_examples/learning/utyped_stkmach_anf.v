
(* Untyped version *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Inductive lit : Set :=
  | litNum : nat -> lit.

Inductive val : Set :=
  | valLit : lit -> val.
  (* | valLabel : nat -> val. *)
Definition binop := lit -> lit -> option lit.

Module STKM.






(* OpSem for utyped WASM, don't consider memory first *)
Inductive stkOp : Set :=
  (* | weaken : forall m n, stkOp m n -> stkOp (S m) (S n) *)
  | const  : val -> stkOp 
  | binstkop : binop -> stkOp
  | get : nat -> stkOp
  (* | alloc  : stkOp 1 1
  | load   : stkOp 1 1 
  | store  : stkOp 2 0  *)
  | drop    : nat -> stkOp.

Definition stkOps := list stkOp.

Definition stk := list val.




Inductive step : stk -> stkOp -> stk -> Prop := 
  | st_const : forall v l,
      step l (const v) (v :: l)
  | st_get : forall i v l,
      nth_error l i = Some v ->
      step l (get i) (v :: l) 
  | st_bin : forall f a b c l,
      f a b = Some c ->
      step (valLit a :: valLit b :: l) (binstkop f) (valLit c :: l)
  | st_drop : forall l1 l2 n,
      List.length l1 = n ->
      step (l1 ++ l2) (drop n) l2.

Definition cfg : Set := stk * stkOps.

Inductive step' : stk -> stkOps -> stk -> stkOps -> Prop :=
  | st_ :
    forall x stk0 ops0 stk1 ops1,
      ops0 = x :: ops1 ->
      step stk0 x stk1 ->
      step' stk0 ops0 stk1 ops1.


End STKM.


Module LET.

Definition ID : Set := string.



Inductive EVal : Set :=
  | Var : ID -> EVal
  | Const : val -> EVal. 

Inductive EComp : Set := 
  | Lets : ID -> EComp -> EComp -> EComp 
  | BinOp : binop -> EVal -> EVal -> EComp
  | rs : EVal -> EComp.

(* | alloc : forall {G T}, expr G T -> expr G (tyref T)
| assign : forall {G T}, expr G (tyref T) -> expr G T -> expr G T 
| deref : forall {G T}, expr G (tyref T) -> expr G T *)

(* Definition env := list val. *)
Axiom env : Set.
Axiom add : env -> ID -> val -> env.


Axiom val_of_EVal : env -> EVal -> option val.

Inductive ECont : Set :=
  | END : ECont
  (* continuation will store the original environment *)
  | CLet : ID -> ECont -> EComp -> ECont
  | CLetPop : env -> ECont -> ECont.

Definition cfg : Set := env * EComp * ECont.

Inductive step : env -> EComp -> ECont ->
                 env -> EComp -> ECont -> Prop :=
  | st_lets : forall E x binding body K,
    step E (Lets x binding body) K 
         E binding (CLet x K body)
  | st_rsv_lets0 : forall v ev E x K body,
    val_of_EVal E ev = Some v ->
    step E           (rs ev) (CLet x K body)
         (add E x v) body    (CLetPop E K)
  | st_rsv_lets1 : forall v ev E1 E K,
    val_of_EVal E1 ev = Some v ->
    step E1 (rs ev) (CLetPop E K)
         E  (rs (Const v)) K.

End LET.


(* Now we start compilation, intensional way of proving compilation correctness *)

(* Proof relevant matching -- we have a function  *)
(* Definition match_env : LET.env -> STKM.stk -> Type := 
  {g : ID -> option nat |
    forall i, 

  
  }. *)

Axiom match_env : LET.env -> STKM.stk -> Set.


Section FixEnvStk.

Context {env0 : LET.env} .
Context {stk0 : STKM.stk}.
Variable matched_es : match_env env0 stk0.

Fixpoint compile' (e : LET.EVal) : STKM.stkOps.
Admitted.

(* given matched env0 and stk0 *)
Fixpoint compile (e : LET.EComp) : STKM.stkOps :=
  match e with 
  | LET.Lets x bind body => compile bind ++ compile body 
  | LET.BinOp f a b => []
  end.
Admitted.

(* Axiom compile_cont : LET.ECont -> STKM.stkOps.  *)

(* Intention 1 was *)
(* env0 ⊢ LET.ECont *)
(* stk0 ⊢ STKM.stkOps *)
Inductive match_cont : LET.ECont -> STKM.stkOps -> Prop :=
  | mc_end :  match_cont LET.END []
  | mc_CLet :
    forall kont code x body,
      match_cont kont code ->
      (* but here it breaks the intention, 
         because body should well typed in env0[x -> ...] *)
      match_cont (LET.CLet x kont body) ((compile body) ++ code)
  | mc_CLetPop :
    forall kont code,
      match_cont kont code ->
      match_cont (LET.CLetPop env0 kont) code.

End FixEnvStk.

(* Print compile. *)

Definition match_config  :
  LET.env -> LET.EComp -> LET.ECont ->  STKM.stk -> STKM.stkOps -> Prop :=
  fun ev comp kont stk code =>
    exists (g : (match_env ev stk)), 
    (exists compcode kontcode,
      match_cont g kont kontcode /\ 
      compile g comp = compcode /\ 
      code = compcode ++ kontcode).
      

Ltac destruct_ALL :=
  repeat 
    match goal with
    | [h : _ \/ _ |- _ ] => destruct h; subst; eauto    
    | [h : _ + _ |- _ ] => destruct h; subst; eauto
    | [h : _ * _ |- _ ] => destruct h; subst; eauto
    | [h : _ /\ _ |- _ ] => destruct h; subst; eauto
    | [h : exists _ , _ |- _ ] => destruct h; subst; eauto
    | [h : {_ & _} |- _ ] => destruct h; subst; eauto
    | [h : {_ & _ & _} |- _ ] => destruct h; subst; eauto
    | [h : Some _ = Some _ |- _] => inversion h; subst; eauto
    | [h : {_} + {_} |- _] => destruct h; subst; eauto
    end.

(* back simulation *)
Lemma match_config_inv :
  forall stk op stk' ,
    STKM.step stk op stk' ->
    forall ev comp kont code code',
    code = op :: code' ->
    match_config ev comp kont stk code ->
    exists ev' comp' kont',
    (LET.step ev  comp  kont 
             ev' comp' kont') /\ 
    (match_config ev' comp' kont' stk' code').
intros stk op stk' h.
induction h; intros; subst; eauto;
unfold match_config in *.

destruct_ALL; subst; eauto.

