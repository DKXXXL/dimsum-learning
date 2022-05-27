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
Require Import refframe.imp_heap_bij_own.


Module ci2a_mem2reg.

Inductive error := UsedAsLoc.

Definition M := compiler_monad unit (fn_compiler_monoid lexpr) error.


Definition is_var (e: var_val) (x: string) :=
  if e is (VVar y) then bool_decide (x = y) else false.

Lemma is_var_dec v x: is_var v x = bool_decide (v = VVar x).
Proof.
  rewrite /is_var. destruct v;
    rewrite !bool_decide_decide; destruct decide.
  - subst. destruct decide; naive_solver.
  - destruct decide; naive_solver.
  - naive_solver.
  - naive_solver.
Qed.


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
    cassert UsedAsLoc (Forall (λ v, is_var v x = false) args);;
    (* vs ← cmap args 0 (λ _ v, if is_var v x then  else mret $ v); *)
    mret (LCall f args)
  | LUbE => mret $ LUbE
  end.

Fixpoint pass (x: string) (e : lexpr) : M lexpr :=
  match e with
  | LLetE v e1 e2 =>
    if bool_decide (v = x) then
      e1' ← lexpr_op_pass x e1;
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


Definition pass_single_var (x: string) (e: lexpr) (vars: list (string * Z)) :=
  let res := crun () (pass x e) in
  match list_find (λ '(y, n), bool_decide (y = x)) vars with
  | None => (e, vars)
  | Some (i, _) =>
    match res.(c_result) with
    | CSuccess e' => (LLetE x (LVarVal (VVal (StaticValNum 0))) e', delete i vars)
    | CError _ => (e, vars)
    end
  end.

Definition pass_body (e: lexpr) (vars: list (string * Z)) :=
  foldr (λ '(x, n) '(r, vars), pass_single_var x r vars) (e, vars) vars.


Definition pass_fn (f : lfndef) : lfndef :=
  let (e, vars) := pass_body f.(lfd_body) f.(lfd_vars) in
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

(*
Lemma pass_lookup_singleton (f g: string) fn fn':
  (lfndef_to_fndef <$> <[f:=fn]> ∅: gmap string fndef) !! g = Some fn' →
  fn' = lfndef_to_fndef fn ∧ f = g.
Proof.
  rewrite !lookup_fmap.
  intros [x [Hlook ->]]%fmap_Some_1.
  eapply lookup_insert_Some in Hlook as [[-> <-]|[? ?]]; last set_solver.
  done.
Qed. *)


Lemma subst_map_var_val_identical x v vss vsi:
  (∀ y, y ≠ x → vss !! y = vsi !! y) →
  v ≠ VVar x →
  subst_map vss (var_val_to_expr v) = subst_map vsi (var_val_to_expr v).
Proof.
  destruct v as [y|]; last done.
  intros Hlook Hneq.
  assert (y ≠ x) as Heq%Hlook by naive_solver.
  rewrite /= Heq //.
Qed.


Lemma pass_lexpr_op_correct ei' Ki ei Ks es es' x (l: loc) n hi hs fns1 fns2 vsi vss w rf upd
  `{Hfill1: !ImpExprFill es Ks (subst_map vss (lexpr_op_to_expr es'))}
  `{Hfill2: !ImpExprFill ei Ki (subst_map vsi (lexpr_op_to_expr ei'))}:
    imp_heap_bij_proof_call n fns1 fns2 →
    crun () (lexpr_op_pass x es') = CResult () upd (CSuccess ei') →
    (∀ y, y ≠ x → vsi !! y = vss !! y) →
    vss !! x = Some (ValLoc l) →
    vsi !! x = Some w →
    (* This should become local ownership eventually *)
    hs.(h_heap) !! l = Some w →
    Imp ei hi fns1
      ⪯{imp_module, imp_heap_bij imp_module, n, true}
    (SMProg, Imp es hs fns2, (PPInside, (), rf)).
Proof.
  intros Hbij Hrun Hlook Hxs Hxi Hl; destruct es' as [v|v1 op v2|v|v1 v2|y vs|]; simpl in Hrun.
  - rewrite is_var_dec bool_decide_decide in Hrun.
    destruct decide; first by eapply cerror_success in Hrun.
    eapply cret_success in Hrun as (_ & ? & ?); subst.
    simpl in Hfill1, Hfill2.
    admit.
  - rewrite is_var_dec bool_decide_decide in Hrun.
    destruct decide; first by eapply cerror_success in Hrun.
    rewrite is_var_dec bool_decide_decide in Hrun.
    destruct decide; first by eapply cerror_success in Hrun.
    eapply cret_success in Hrun as (_ & ? & ?); subst.
    simpl in Hfill1, Hfill2.
    admit.
  - rewrite is_var_dec bool_decide_decide in Hrun.
    destruct decide; eapply cret_success in Hrun as (_ & ? & ?); subst.
    + simpl in Hfill1, Hfill2.
      rewrite Hxs in Hfill1; rewrite Hxi in Hfill2.
      tstep_s. intros ??; injection 1 as <-; intros ?.
      simplify_eq.
      admit. (* there the continuation should apply *)
    + simpl in Hfill1, Hfill2.
      (* We should be able to proceed with the load here.
         Still need to fix the substitution stuff. *)
      tstep_both. admit.
  - rewrite !is_var_dec !bool_decide_decide in Hrun.
    destruct decide; first by eapply cerror_success in Hrun.
    destruct decide.
    + admit.
    + eapply cret_success in Hrun as (_ & ? & ?); subst.
      simpl in Hfill1, Hfill2.
      (* We should be able to proceed with the load here.
         Still need to fix the substitution stuff. *)
      tstep_both. admit.
  - eapply cbind_success in Hrun as ([] & g & vs' & ? & Hrun1 & Hrun2 & ->).
    eapply cret_success in Hrun2 as (_ & ? & ?); subst.
    eapply cassert_success in Hrun1 as (_ & ? & ? & ?); subst.
    simpl in Hfill1, Hfill2.
    eapply Hbij; eauto.
    (* we need the function call case here *)
    all: admit.
  - eapply cret_success in Hrun as (_ & ? & ?); subst.
    simpl in Hfill1, Hfill2.
    tstep_s. done.
  Admitted.

Lemma pass_correct ei' Ki ei Ks es es' x n h h' fns1 fns2 vsi vss rf r_p
  `{Hfill1: !ImpExprFill es Ks (subst_map vss (lexpr_to_expr es'))}
  `{Hfill2: !ImpExprFill ei Ki (subst_map vsi (lexpr_to_expr ei'))}:
    imp_heap_bij_proof_call n fns1 fns2 →
    crun () (pass x es') = CResult () r_p (CSuccess ei') →
    Imp ei h fns1
      ⪯{imp_module, imp_heap_bij imp_module, n, true}
    (SMProg, Imp es h' fns2, (PPInside, (), rf)).
Proof.
  revert ei' Ki ei Ks es x n h h' fns1 fns2 vsi vss rf r_p Hfill1 Hfill2.
  induction es' as [y op es' IH| op es1' IH1 es2' IH2 | op];
    intros ei' Ki ei Ks es x n h h' fns1 fns2 vsi vss rf r_p Hfill1 Hfill2;
    intros Hcall Hrun; simpl in Hrun.
  - rewrite bool_decide_decide in Hrun.
    destruct decide.
    + subst. eapply cbind_success in Hrun as ([] & a2 & r2 & a3' & Hrun1 & Hrun2 & ->).
      eapply cret_success in Hrun2 as (_ & -> & ->).
      simpl in Hfill1, Hfill2.
      admit.
    + eapply cbind_success in Hrun as ([] & a2 & [e1' upd] & a3' & Hrun1 & Hrun2 & ->).
      eapply cbind_success in Hrun2 as ([] & a2' & r2 & ? & Hrun2 & Hrun3 & ->).
      eapply cret_success in Hrun3 as (_ & -> & ->).
      admit.
  - admit.
  - admit.
Admitted.

(*
Lemma pass_body_correct ei' Ki ei Ks es es' n h h' fns1 fns2 vin vout vsi vss  rf
      `{Hfill1: !ImpExprFill es Ks (subst_map vss (lexpr_to_expr es'))}
      `{Hfill2: !ImpExprFill ei Ki (subst_map vsi (lexpr_to_expr ei'))}:
  imp_heap_bij_proof_call n fns1 fns2 →
  (pass_body es' vin) = (ei', vout) →
  (* (∀ h' v' vsi',
    (s ≤ s')%N →
    lookup_var_val vsi' v = Some v' →
    vsi ⊆ vsi' →
    (∀ v, is_Some (vsi' !! v) → is_Some (vsi !! v) ∨
                                v ∈ assigned_vars (static_expr_to_expr es') ∨
                                ∃ n, v = tmp_var n ∧ (n < s')%N) →
    Imp (expr_fill Ki $ subst_map vsi' (lexpr_to_expr ei')) h' fns1
       ⪯{imp_module, imp_module, n, false}
    Imp (expr_fill Ks (Val v')) h' fns2) → *)
  Imp ei h fns1
      ⪯{imp_module, imp_heap_bij imp_module, n, true}
  (SMProg, Imp es h' fns2, (PPInside, (), rf)).
Proof. Admitted. *)
  (* revert ei' Ki ei Ks es es' n h h' fns1 fns2 vout vsi vss vs1 vs2 r rf Hfill1 Hfill2.
  induction vin as [|[s k] vin IH]; simpl;
    intros ei' Ki ei Ks es es' n h h' fns1 fns2 vout vsi vss vs1 vs2 r rf Hfill1 Hfill2;
    intros Hcall Hpass Hsat.
  - injection Hpass as ? <-.
    subst ei'. admit.
    (* FIXME: we need some kind of reflexivity here, with *)
  - destruct (pass_body es' vin) as [es'' vars''] eqn: Hbody.
    destruct (crun () (pass s es'')) as [r_s r_p [res|err]] eqn: Hpass_var;
      simpl in Hpass.
    + injection Hpass as ? ?. subst vout ei'. admit.
      (* FIXME: to proceed here, I think we need transitivity.
        We need to compose the refinement of the recursively
        optimized function with the one optimization pass we add now. *)

    + injection Hpass as ??. subst ei' vout.
      eapply IH; eauto.
Admitted. *)


Lemma pass_single_var_correct f x args exprs varss expri varsi :
  pass_single_var x exprs varss = (expri, varsi) →
  trefines
  (MS (imp_heap_bij imp_module)
     (initial_imp_heap_bij_state imp_module
        (initial_imp_state
           (lfndef_to_fndef <$>
            <[f:={| lfd_args := args; lfd_vars := varsi; lfd_body := expri |}]> ∅))))
  (MS (imp_heap_bij imp_module)
     (initial_imp_heap_bij_state imp_module
        (initial_imp_state
           (lfndef_to_fndef <$>
            <[f:={| lfd_args := args; lfd_vars := varss; lfd_body := exprs |}]> ∅)))).
Proof.
  rewrite /pass_single_var.
  destruct list_find as [[i [y n]]|] eqn: Hfind;
    first destruct (crun () (pass x exprs)) as [[] ? [res|]]; simpl;
    last first.
  - injection 1 as ??; subst. reflexivity.
  - injection 1 as ??; subst. reflexivity.
  - injection 1 as ??; subst.
Admitted.


Lemma pass_body_correct f args varss exprs expri varsi:
  pass_body exprs varss = (expri, varsi) →
  trefines
    (MS (imp_heap_bij imp_module)
       (initial_imp_heap_bij_state imp_module
          (initial_imp_state
             (lfndef_to_fndef <$>
              <[f:={| lfd_args := args; lfd_vars := varsi; lfd_body := expri |}]> ∅))))
    (MS (imp_heap_bij imp_module)
       (initial_imp_heap_bij_state imp_module
          (initial_imp_lstate
             (<[f:={| lfd_args := args; lfd_vars := varss; lfd_body := exprs |}]> ∅)))).
Proof.
  rewrite /pass_body. generalize varss at 2 as L.
  induction L as [|[x n] L IHL] in varss, varsi, exprs, expri |-*; simpl.
  - injection 1 as ??. subst; reflexivity.
  - destruct foldr as [expri' varsi'] eqn: Hbody.
    intros Hsingle.
    eapply IHL in Hbody as IH.
    etrans; last eapply IH. eapply pass_single_var_correct, Hsingle.
Qed.

Lemma pass_fn_correct f fn :
  trefines (MS imp_module (initial_imp_lstate (<[f := pass_fn fn]> ∅)))
           (MS (imp_heap_bij imp_module) (initial_imp_heap_bij_state imp_module
                                            (initial_imp_lstate (<[f := fn]> ∅)))).
Proof.
  etrans; first eapply imp_heap_bij_imp_refl.
  rewrite /pass_fn. destruct pass_body as [expri varsi] eqn: Hpass.
  revert Hpass. destruct fn as [args varss exprs]; simpl.
  by eapply pass_body_correct.
Qed.

(*
Lemma pass_fn_correct f fn :
  trefines (MS imp_module (initial_imp_lstate (<[f := pass_fn fn]> ∅)))
           (MS (imp_heap_bij imp_module) (initial_imp_heap_bij_state imp_module
                                            (initial_imp_lstate (<[f := fn]> ∅)))).
Proof.
  apply: imp_heap_bij_proof. { set_solver. }
  - move => ??. intros [-> ->]%pass_lookup_singleton.
    eexists. split; simpl.
    { rewrite lookup_fmap. eapply fmap_Some_2, lookup_insert.  }
    { destruct fn; unfold pass_fn, pass_body; simpl. by destruct foldr. }
  - intros n K1 K2 g fn1 fn2 vs1 vs2 h1 h2 r rf.
    intros [-> ->]%pass_lookup_singleton.
    intros [-> _]%pass_lookup_singleton.
    intros Hlen1 Hlen2 Hsat Hcalls Hcont.
    destruct fn; simpl. unfold pass_fn; simpl.
    destruct (pass_body) as [e' vars'] eqn: Hpass; simpl.
    tstep_both. intros ls h' Halloc. tstep_s.
    edestruct (heap_alloc_list_fresh lfd_vars.*2 ∅ h2) as [h Heap].
    eexists _, _. split; first done.
    intros Hall. tend. split.
    { eapply List.Forall_forall.
      intros x [s [-> Hel]]%elem_of_list_In%elem_of_list_fmap_2.
      eapply pass_body_vars in Hel; last done.
      eapply List.Forall_forall; first done.
      eapply elem_of_list_In, elem_of_list_fmap_1, Hel. }
    rewrite !fmap_insert fmap_empty.
    rewrite !subst_l_subst_map; first last.
    { eapply heap_alloc_list_length in Halloc.
      revert Halloc. rewrite !fmap_length //.  }
    { revert Hlen1. rewrite /pass_fn //=.
      rewrite Hpass //. }
    { rewrite !fmap_length. clear. unfold fmap.
      generalize (∅: (gset prov)). generalize h2.
      induction lfd_vars as [|[]? IH]; simpl; first done.
      intros ??. by erewrite IH. }
    { revert Hlen1. rewrite /pass_fn //=. }
    rewrite -!subst_map_subst_map.
    rewrite -!list_to_map_app.
    eapply pass_body_correct.
    + eapply imp_expr_fill_expr_fill, imp_expr_fill_FreeA, imp_expr_fill_end.
    + eapply imp_expr_fill_expr_fill, imp_expr_fill_FreeA, imp_expr_fill_end.
    + revert Hcalls. rewrite !fmap_insert fmap_empty /pass_fn //=.
      rewrite Hpass //.
    + done.
    + done.
  Qed. *)

End ci2a_mem2reg.
