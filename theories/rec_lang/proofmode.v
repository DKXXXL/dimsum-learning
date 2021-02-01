From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import atomic.
From refframe.rec_lang Require Export lifting.
From iris.prelude Require Import options.


(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_expr e tac :=
  (* Note that the current context is spread into a list of fully-constructed
     items [K] A fully-constructed item is inserted into [K] by calling
     [add_item]. *)
  let rec go K e :=
    match e with
    | _                               => tac K e
    | BinOp ?op ?e (Val ?v)           => add_item (BinOpLCtx op v) K e
    | BinOp ?op ?e1 ?e2               => add_item (BinOpRCtx op e1) K e2
    | If ?e0 ?e1 ?e2                  => add_item (IfCtx e1 e2) K e0
    | LetE ?v ?e1 ?e2                 => add_item (LetECtx v e2) K e1
    end
  with add_item Ki K e := go (Ki :: K) e
  in go (@nil expr_ectx) e.


Lemma tac_wp_bind `{!reclangG Σ} K Δ s E Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WP e @ s; E {{ v, WP f (Val v) @ s; E {{ Φ }} }})%I →
  envs_entails Δ (WP fill K e @ s; E {{ Φ }}).
Proof. rewrite envs_entails_eq=> -> ->. by apply: wp_bind. Qed.

Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_wp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K)
          | fail "wp_bind: cannot find" efoc "in" e ]
  | _ => fail "wp_bind: not a 'wp'"
  end.
