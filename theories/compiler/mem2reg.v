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

Inductive error := UsedAsLoc | NotSupported.

Definition M := compiler_monad unit (fn_compiler_monoid (option var_val)) error.


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
    cassert UsedAsLoc (v ≠ VVar x);;
    mret $ LVarVal v
  | LBinOp v1 o v2 =>
    cassert UsedAsLoc (v1 ≠ VVar x);;
    cassert UsedAsLoc (v2 ≠ VVar x);;
    mret $ LBinOp v1 o v2
  | LLoad v =>
    if is_var v x then
      mret $ LVarVal v
    else
      mret $ LLoad v
  | LStore v1 v2 =>
    cassert UsedAsLoc (v2 ≠ VVar x);;
    if is_var v1 x then
      cappend (λ _, Some v2);;
      mret $ LVarVal v2
    else mret $ LStore v1 v2
  | LCall f args =>
    cassert UsedAsLoc (Forall (λ v, v ≠ VVar x) args);;
    mret (LCall f args)
  | LUbE => mret $ LUbE
  end.


Definition LLetM (x: string) (v: option var_val) (e: lexpr) :=
  match v with
  | None => e
  | Some w => LLetE x (LVarVal w) e
  end.

Fixpoint pass (x: string) (e : lexpr) : M lexpr :=
  match e with
  | LLetE v e1 e2 =>
    if bool_decide (v = x) then
      e1' ← lexpr_op_pass x e1;
      mret $ LLetE v e1' e2
    else
      '(e1', f) ← cscope (lexpr_op_pass x e1);
      e2' ← pass x e2;
      (* FIXME: discuss this constraint *)
      (* f None is the var_val that is assigned to x in e1'.
         if that var_val is v, then the meaning changes when
         we move the assignment to x underneath the
         assignment of v.*)
      cassert NotSupported (f None ≠ Some (VVar v));;
      mret $
        LLetE v e1' $
        LLetM x (f None) $
        e2'
  | LIf e1 e2 e3 =>
    '(e1', f) ← cscope (lexpr_op_pass x e1);
    e2' ← pass x e2;
    e3' ← pass x e3;
    mret $
      LIf e1' (LLetM x (f None) e2') (LLetM x (f None) e3')
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



Definition empty_block (l: loc) (n: Z) : gmap Z val :=
  gmap_curry (list_to_map ((λ z : Z, (l +ₗ z, ValNum 0%Z)) <$> seqZ 0 n)) !!! l.1.


Definition imp_heap_bij_cont n fns1 fns2 Ks Ki r :=
  (∀ n' v1 v2 h1' h2' rf' b,
      n' ⊆ n →
      satisfiable (heap_bij_inv h1' h2' ∗ val_in_bij v1 v2 ∗ r ∗ rf') →
      Imp (expr_fill Ki (Val v1)) h1' fns1
        ⪯{imp_module, imp_heap_bij imp_module, n', b}
      (SMProg, Imp (expr_fill Ks (Val v2)) h2' fns2, (PPInside, (), rf'))).


(* FIXME: place these definitions somewhere shared *)
Definition lookup_var_val (vs : gmap string val) (v : var_val) : option val :=
  match v with
  | VVal v => Some (static_val_to_val v)
  | VVar v => vs !! v
  end.

Lemma lookup_var_val_to_expr vs v v' :
  lookup_var_val vs v = Some v' →
  subst_map vs (var_val_to_expr v) = Val v'.
Proof. by destruct v => //= ?; simplify_option_eq. Qed.

Lemma lookup_var_val_to_expr_fmap vs v v' :
  Forall2 (λ v v', lookup_var_val vs v = Some v') v v' →
  subst_map vs <$> (var_val_to_expr <$> v) = Val <$> v'.
Proof. elim => //; csimpl => ???? /lookup_var_val_to_expr -> ? ->. done. Qed.

Lemma lookup_var_val_mono vs vs' v v':
  lookup_var_val vs v = Some v' →
  vs ⊆ vs' →
  lookup_var_val vs' v = Some v'.
Proof. destruct v => //. simplify_eq/=. apply lookup_weaken. Qed.




Lemma lexpr_tsim_var_val  v es ei Ks Ki vss vsi x n hi hs fns1 fns2 rf r
  `{Hfill1: !ImpExprFill es Ks (subst_map vss (var_val_to_expr v))}
  `{Hfill2: !ImpExprFill ei Ki (subst_map vsi (var_val_to_expr v))}:
    dom (gset string) vss ⊆ dom (gset string) vsi →
    v ≠ VVar x →
    satisfiable (([∗ map] vi;vs ∈ (delete x vsi); (delete x vss), val_in_bij vi vs) ∗ r) →
    (∀ v' w',
      subst_map vsi (var_val_to_expr v) = Val v' →
      subst_map vss (var_val_to_expr v) = Val w' →
      satisfiable (([∗ map] vi;vs ∈ (delete x vsi); (delete x vss), val_in_bij vi vs) ∗ val_in_bij v' w' ∗ r) →
      Imp (expr_fill Ki (Val v')) hi fns1
        ⪯{imp_module, imp_heap_bij imp_module, n, true}
      (SMProg, Imp (expr_fill Ks (Val w')) hs fns2, (PPInside, (), rf))
    ) →
    Imp ei hi fns1
      ⪯{imp_module, imp_heap_bij imp_module, n, true}
    (SMProg, Imp es hs fns2, (PPInside, (), rf)).
Proof.
 intros Hdom Hne Hsat Hcont; destruct Hfill1 as [->], Hfill2 as [->].
 destruct v as [y|w]; simpl.
 - destruct (vss !! y) eqn: Hlook; last first.
   { tstep_s. done. }
   eapply elem_of_dom_2 in Hlook as Hel.
   eapply elem_of_weaken in Hel; last done.
   eapply elem_of_dom in Hel as [w Hlook'].
   rewrite Hlook'. eapply Hcont; simpl.
   { rewrite Hlook' //. }
   { rewrite Hlook //. }
   iSatMono. iIntros "[#Hv $]". iFrame "Hv".
   iApply (big_sepM2_lookup with "Hv");
    rewrite !lookup_delete_ne //; naive_solver.
  - eapply Hcont; [done..|].
    iSatMono. iIntros "[#Hv $]". iFrame "Hv".
    destruct w; done.
Qed.


Lemma lexpr_tsim_var_val_call vs' ws' ys es ei Ks Ki vss vsi x n hi hs fns1 fns2 rf f r
  `{Hfill2: !ImpExprFill ei Ki (Call f ((Val <$> vs') ++ (subst_map vsi <$> (var_val_to_expr <$> ys))))}
  `{Hfill1: !ImpExprFill es Ks (Call f ((Val <$> ws') ++ (subst_map vss <$> (var_val_to_expr <$> ys))))}:
    dom (gset string) vss ⊆ dom (gset string) vsi →
    Forall (λ v, v ≠ VVar x) ys →
    satisfiable (([∗ map] vi;vs ∈ (delete x vsi); (delete x vss), val_in_bij vi vs) ∗ ([∗ list] v; w ∈ vs'; ws', val_in_bij v w) ∗ r) →
    (∀ vs ws,
      satisfiable (([∗ map] vi;vs ∈ (delete x vsi); (delete x vss), val_in_bij vi vs) ∗ ([∗ list] v; w ∈ vs' ++ vs; ws' ++ ws, val_in_bij v w) ∗ r) →
      Imp (expr_fill Ki (Call f (Val <$> (vs' ++ vs)))) hi fns1
        ⪯{imp_module, imp_heap_bij imp_module, n, true}
      (SMProg, Imp (expr_fill Ks (Call f (Val <$> (ws' ++ ws)))) hs fns2, (PPInside, (), rf))
    ) →
    Imp ei hi fns1
      ⪯{imp_module, imp_heap_bij imp_module, n, true}
    (SMProg, Imp es hs fns2, (PPInside, (), rf)).
Proof.
 intros Hdom Hall Hsat Hcont;destruct Hfill1 as [->], Hfill2 as [->].
 induction ys as [|y ys IH] in vs', ws', Hsat, Hall, Hcont |-*; simpl.
 - specialize (Hcont [] []). rewrite !app_nil_r in Hcont.
   rewrite !app_nil_r. eapply Hcont, Hsat.
 - eapply Forall_cons_1 in Hall as [Hne Hall]. eapply lexpr_tsim_var_val; eauto.
   { eapply imp_expr_fill_expr_fill, (imp_expr_fill_expr_fill _ [CallCtx _ _ _]), imp_expr_fill_end. }
   { eapply imp_expr_fill_expr_fill, (imp_expr_fill_expr_fill _ [CallCtx _ _ _]), imp_expr_fill_end. }
   clear Hsat; intros v w _ _ Hsat; simpl.
   rewrite !cons_middle !app_assoc. change ([Val v]) with (Val <$> [v]).
   change ([Val w]) with (Val <$> [w]). rewrite -!fmap_app.
   eapply IH.
   + done.
   + iSatMono. by iIntros "($ & $ & $ & $)".
   + clear Hsat. intros vs ws Hsat.
      rewrite -!app_assoc. eapply Hcont.
      rewrite !app_assoc //.
Qed.


Local Existing Instance imp_expr_fill_end.
Local Existing Instance imp_expr_fill_expr_fill.
Local Existing Instance imp_expr_fill_BinOpL.
Local Existing Instance imp_expr_fill_BinOpR.
Local Existing Instance imp_expr_fill_Load.
Local Existing Instance imp_expr_fill_StoreR.
Local Existing Instance imp_expr_fill_StoreL.
Local Existing Instance imp_expr_fill_LetE.
Local Existing Instance imp_expr_fill_If.



Lemma gmap_curry_total_lookup {K1 K2 : Type} `{Countable K1} `{Countable K2} {A : Type} (m : gmap (K1 * K2) A) (i : K1) (j : K2):
  ((gmap_curry m !!! i): gmap K2 A) !! j = m !! (i, j).
Proof.
  rewrite -lookup_gmap_curry lookup_total_alt.
  destruct (gmap_curry m !! i); simpl; first done.
  by eapply lookup_empty.
Qed.

Lemma block_heap_alloc h l n:
  heap_is_fresh h l →
  (h_block (heap_alloc h l n) l.1) = empty_block l n.
Proof.
  intros Hfresh.
  rewrite /h_block /heap_alloc /empty_block /=.
  eapply map_leibniz, map_equiv_iff; intros i.
  rewrite !gmap_curry_total_lookup.
  assert (h_heap h !! (l.1, i) = None) as Hlook.
  { rewrite /heap_is_fresh in Hfresh.
    destruct lookup eqn: Hlook; last done.
    destruct l; simpl in *.
    exfalso. eapply Hfresh, (heap_wf _ (p, i)); eauto.
  }
  rewrite lookup_union; rewrite Hlook; clear Hlook.
  destruct lookup; done.
Qed.

Lemma heap_update_block hs l w1 w2 k:
  l.2 = 0%Z →
  (∀ z, h_heap hs !! (l.1, z) = (<[0%Z:=w1]> (empty_block l k) !! z)) →
  (h_block (heap_update hs l w2) l.1) = (<[0%Z:=w2]> (empty_block l k)).
Proof.
  intros Hz Hs. rewrite /h_block /heap_alloc /=.
  eapply map_leibniz, map_equiv_iff; intros i.
  rewrite !gmap_curry_total_lookup.
  destruct l as [p z]; simpl in *; subst.
  destruct (decide (i = 0%Z)); subst.
  - rewrite lookup_insert.
    rewrite lookup_alter.
    rewrite Hs lookup_insert //.
  - rewrite lookup_insert_ne //.
    rewrite lookup_alter_ne; last by naive_solver.
    rewrite Hs. rewrite lookup_insert_ne //.
Qed.


Lemma imp_heap_bij_proof_call_downclosed n n' fns1 fns2:
  imp_heap_bij_proof_call n fns1 fns2 →
  n' ⊆ n →
  imp_heap_bij_proof_call n' fns1 fns2.
Proof.
  intros Hprf ???????????????????????.
  eapply Hprf; eauto. by etrans.
Qed.

Lemma pass_lexpr_op_correct ei' Ki ei Ks es es' x k (l: loc) n hi hs fns1 fns2 vsi vss wi ws r rf (f: option var_val → option var_val)
  `{Hfill1: !ImpExprFill es Ks (subst_map vss (lexpr_op_to_expr es'))}
  `{Hfill2: !ImpExprFill ei Ki (subst_map vsi (lexpr_op_to_expr ei'))}:
    imp_heap_bij_proof_call n fns1 fns2 →
    (∀ (w1 w2: val),
       default (Val wi) (subst_map vsi <$> (var_val_to_expr <$> (f None))) = Val w1 →
      imp_heap_bij_cont n fns1 fns2 Ks Ki (r ∗ heap_bij_const_s l.1 (<[0%Z := w2]> (empty_block l k)) ∗ val_in_bij w1 w2)) →
    satisfiable (([∗ map] v1;v2 ∈ (delete x vsi);(delete x vss), val_in_bij v1 v2) ∗ heap_bij_inv hi hs ∗ val_in_bij wi ws ∗ heap_bij_const_s l.1 (<[0%Z := ws]> (empty_block l k)) ∗ r ∗ rf) →
    vss !! x = Some (ValLoc l) →
    vsi !! x = Some wi →
    dom (gset string) vss ⊆ dom (gset string) vsi →
    l.2 = 0 →
    crun () (lexpr_op_pass x es') = CResult () f (CSuccess ei') →
    Imp ei hi fns1
      ⪯{imp_module, imp_heap_bij imp_module, n, true}
    (SMProg, Imp es hs fns2, (PPInside, (), rf)).
Proof.
  intros Hcalls Hcont Hsat Hxs Hxi Hsub Hl Hrun.
  destruct Hfill1 as [->], Hfill2 as [->].
  destruct es' as [v|v1 op v2|v|v1 v2|y vs|]; simpl in Hrun.
  - simplify_crun_eq.
    apply: lexpr_tsim_var_val; eauto; clear Hsat.
    intros v1 v2 _ _ Hsat; simpl.
    eapply Hcont; [done..|].
    iSatMono. iIntros "(_ & $ & $ & $ & $ & $ & $)".
  - simplify_crun_eq.
    apply: lexpr_tsim_var_val; eauto; clear Hsat.
    intros v1' w1' _ _ Hsat; simpl.
    apply: lexpr_tsim_var_val; eauto; clear Hsat.
    intros v2' w2' _ _ Hsat; simpl.
    tstep_s. intros w' Heval.
    iSatStart. iIntros "(Hvals & H1 & H2 & Hbij & Hval & Hl & r & rf)".
    iDestruct (eval_binop_bij with "H2 H1") as "[%v' [%Heval2 Hw]]"; first done.
    iSatStop. tstep_i. split!.
    eapply Hcont; [done..|].
    iSatMono. iFrame.
  - simplify_crun_eq.
     rewrite is_var_dec bool_decide_decide in Hrun.
      destruct decide; simplify_crun_eq.
    + simpl. rewrite Hxs Hxi.
      tstep_s. intros ??; injection 1 as <-; intros Heq.
      eapply Hcont; [done..|].
      iSatMono.
      iIntros "(Hvals & Hbij & #Hval & Hl & $ & $)".
      iDestruct (heap_bij_inv_lookup_s with "Hbij Hl") as "%Heq'".
      rewrite Heq in Heq'. rewrite Hl in Heq'.
      rewrite lookup_insert in Heq'. simplify_eq. iFrame.
      iFrame "Hval".
    + apply: lexpr_tsim_var_val; eauto; clear Hsat.
      intros v1 v2 _ _ Hsat; simpl.
      tstep_s. intros l' v' -> Hlook'.
      iSatStart. iIntros "(Hvals & Hbij & Hinv & Hval & Hl & r & rf)".
      destruct v1 as [| |l'']; simpl; try done.
      iDestruct (heap_bij_inv_lookup with "Hinv Hbij") as "[%w [%Heq' #Hval']]"; first done.
      iSatStop. tstep_i. split!. eapply Hcont; [done..|].
      iSatMono. iFrame. done.
  - rewrite !is_var_dec !bool_decide_decide in Hrun.
    destruct decide; simplify_crun_eq.
    + rewrite Hxs. apply: (lexpr_tsim_var_val); eauto; clear Hsat.
      intros w1 w2 ? ? Hsat; simpl.
      tstep_s. intros l' Heq Halive; injection Heq as <-.
      eapply Hcont; [done..|].
      iSatMonoBupd. iIntros "(Hvals & #Hbij & Hinv & #Hval & Hl & r & rf)".
      iMod (heap_bij_inv_update_s with "Hinv Hl") as "[Hinv Hl]".
      iFrame. erewrite heap_update_block; last first.
      { intros z. destruct l as [p z']; simpl in Hl. subst.
        iSatStart. iIntros "(? & ? & Hinv & ? & Hl & ?)"; simpl.
        iDestruct (heap_bij_inv_lookup_s (p, z) with "Hinv Hl") as "%".
        iSatStop. iSatClear. done. }
      { done. }
      { iFrame. by iFrame "Hbij". }
    + apply: (lexpr_tsim_var_val); eauto; clear Hsat.
      intros w1 w2 _ _ Hsat; simpl.
      apply: (lexpr_tsim_var_val); eauto; clear Hsat.
      intros u1 u2 _ _ Hsat; simpl.
      tstep_s. intros l' Heq Halive; subst w2.
      iSatStart. iIntros "(Hvals & #Hu & Hw & Hinv & Hval & Hl & r & rf)".
      destruct w1 as [| |l'']; simpl; try done.
      iDestruct (heap_bij_inv_alive with "Hinv Hw") as "%"; first done.
      iDestruct (heap_bij_inv_update with "Hinv Hw Hu") as "Hheap".
      iSatStop. tstep_i. split!. eapply Hcont; [done..|].
      iSatMono. iFrame. done.
  - simplify_crun_eq. apply: (lexpr_tsim_var_val_call nil nil); eauto.
    { iSatMono. iIntros "[$ H]". simpl. iSplit; first done. iExact "H". }
    simpl. clear Hsat. intros vs' ws' Hsat.
    apply: Hcalls; eauto.
    { by eapply Forall2_fmap_l, Forall_Forall2_diag, Forall_forall. }
    { by eapply Forall2_fmap_l, Forall_Forall2_diag, Forall_forall. }
    { iSatMono. iIntros "(H1 & $ & $ & H2 & H3 & H4 & $)".
      iCombine "H1 H2 H3 H4" as "H". iExact "H". }
    clear Hsat; intros v1'' v2'' h1'' h2'' rf'' Hsat; simpl.
    eapply Hcont; [done..|].
    iSatMono. iIntros "($ & $ & (_ & $ & $ & $) & $)".
  - simplify_crun_eq. tstep_s. done.
Qed.




Lemma LLetM_sim Ki Ks vsi vss x o ei es n hi hs fns1 fns2 rf vi wi:
  vsi !! x = Some vi →
  default (Val vi) (subst_map vsi <$> (var_val_to_expr <$> o)) = Val wi →
  Imp (expr_fill Ki (subst_map (<[x := wi]> vsi) (lexpr_to_expr ei))) hi fns1
    ⪯{imp_module, imp_heap_bij imp_module, n, true}
  (SMProg, Imp (expr_fill Ks (subst_map vss (lexpr_to_expr es))) hs fns2, (PPInside, (), rf)) →
  Imp (expr_fill Ki (subst_map vsi (lexpr_to_expr (LLetM x o ei)))) hi fns1
    ⪯{imp_module, imp_heap_bij imp_module, n, true}
  (SMProg, Imp (expr_fill Ks (subst_map vss (lexpr_to_expr es))) hs fns2, (PPInside, (), rf)).
Proof.
  destruct o; simpl.
  - intros Hlook Heq Hsim; rewrite Heq.
    tstep_i. rewrite -subst_subst_map_delete.
    eapply Hsim.
  - intros Hlook. injection 1 as ->.
    rewrite insert_id //.
Qed.

Lemma pass_correct  r rf ei' Ki ei Ks es es' x (l: loc) n k h h' fns1 fns2 vsi vss vi vs r_p
  `{Hfill1: !ImpExprFill es Ks (subst_map vss (lexpr_to_expr es'))}
  `{Hfill2: !ImpExprFill ei Ki (subst_map vsi (lexpr_to_expr ei'))}:
    l.2 = 0 →
    imp_heap_bij_proof_call n fns1 fns2 →
    (∀ w, imp_heap_bij_cont n fns1 fns2 Ks Ki (r ∗ heap_bij_const_s l.1 (<[0%Z := w]> (empty_block l k)))) →
    vss !! x = Some (ValLoc l) →
    vsi !! x = Some vi →
    dom (gset string) vss ⊆ dom (gset string) vsi →
    (* FIXME: val rel for v *)
    satisfiable (heap_bij_inv h h' ∗ heap_bij_const_s l.1 (<[0%Z := vs]> (empty_block l k)) ∗
                val_in_bij vi vs ∗ ([∗ map] v1;v2 ∈ (delete x vsi);(delete x vss), val_in_bij v1 v2) ∗ r ∗ rf) →
    crun () (pass x es') = CResult () r_p (CSuccess ei') →
    Imp ei h fns1
      ⪯{imp_module, imp_heap_bij imp_module, n, true}
    (SMProg, Imp es h' fns2, (PPInside, (), rf)).
Proof.
  intros Hl; destruct Hfill1 as [->]. destruct Hfill2 as [->].
  revert r rf ei' Ki Ks x n k h h' fns1 fns2 vsi vss vi vs r_p.
  induction es' as [y op es' IH| op es1' IH1 es2' IH2 | op];
    intros r rf ei' Ki Ks x n k h h' fns1 fns2 vsi vss vi vs r_p;
    intros Hcall Hcont Hvss Hvsi Hdom Hsat Hrun; simpl in Hrun.
  - rewrite bool_decide_decide in Hrun.
    destruct decide; simplify_crun_eq.
    + apply: pass_lexpr_op_correct; eauto; last first.
      { iSatMono. iIntros "($ & $ & $ & $ & r & $)". iExact "r". }
      simpl. clear Hsat. intros w1 w2 Hdef. intros n' v1 v2 h1' h2' rf' b Hsub Hsat.
      simpl. tstep_s. tstep_i.
      rewrite -!subst_subst_map_delete orb_true_r.
      (* we need some kind of reflexivity theorem here,
         where all values that are inserted are in the bijection *)
      admit.
    + (* FIXME: the next step should be automatic *)
      destruct x0, x2.
      simplify_crun_eq.

      apply: pass_lexpr_op_correct; eauto; last first.
      { iSatMono. iIntros "($ & $ & $ & #H & r & $)". iFrame "H". iCombine "H r" as "r". iExact "r". }
      simpl. clear Hsat. intros w1 w2 Hdef. intros n' v1 v2 h1' h2' rf' b Hsub Hsat.
      simpl. tstep_s. tstep_i.
      rewrite -!subst_subst_map_delete orb_true_r.
      eapply LLetM_sim.
      { rewrite lookup_insert_ne //. }
      { destruct o; last done.
        rewrite -Hdef /=. simpl in Hdef.
        destruct v as [z|]; last done; simpl.
        destruct (decide (z = y)); subst; first naive_solver.
        rewrite lookup_insert_ne //. }
      eapply IH; eauto using imp_heap_bij_proof_call_downclosed; first last.
      { iSatMono. iIntros "($ & Hv & ([Hall r] & $ & $) & $)".
        rewrite delete_insert_delete. rewrite !delete_insert_ne //.
        iSplitR "r"; last iExact "r".
        iApply (big_sepM2_insert_2 with "[Hv] Hall"); simpl.
        iFrame. }
      { set_solver. }
      { rewrite lookup_insert //. }
      { rewrite lookup_insert_ne //. }
      clear Hsat. intros w n'' v3 v4 h1'' h2'' rf'' b' Hn'' Hsat.
      eapply Hcont; eauto. by etrans.
  - simplify_crun_eq.
    (* FIXME: the next step should be automatic *)
    destruct x0, x2.
    simplify_crun_eq.
    destruct x0.

    apply: pass_lexpr_op_correct; eauto; last first.
    { iSatMono. iIntros "($ & $ & $ & #H & r & $)". iFrame "H". iCombine "H r" as "r". iExact "r". }
    simpl. clear Hsat. intros w1 w2 Hdef. intros n' v1 v2 h1' h2' rf' b Hsub Hsat.
    simpl. tstep_s. intros bb ->.
    assert (v1 = ValBool bb) as ->.
    { iSatStart. iIntros "(? & Hval & ? & ?)". destruct v1; eauto.
      iDestruct "Hval" as "%". subst. iSatStop. done. }
    tstep_i. rewrite orb_true_r.
    destruct bb; eapply LLetM_sim; eauto.
    + eapply IH1; eauto using imp_heap_bij_proof_call_downclosed; first last.
      { iSatMono. iIntros "($ & Hv & ([Hall r] & $ & $) & $)".
        rewrite delete_insert_delete. iFrame. iExact "r". }
      { set_solver. }
      { rewrite lookup_insert //. }
      clear Hsat. intros w n'' v3 v4 h1'' h2'' rf'' b' Hn'' Hsat.
      eapply Hcont; eauto. by etrans.
    + eapply IH2; eauto using imp_heap_bij_proof_call_downclosed; first last.
      { iSatMono. iIntros "($ & Hv & ([Hall r] & $ & $) & $)".
        rewrite delete_insert_delete. iFrame. iExact "r". }
      { set_solver. }
      { rewrite lookup_insert //. }
      clear Hsat. intros w n'' v3 v4 h1'' h2'' rf'' b' Hn'' Hsat.
      eapply Hcont; eauto. by etrans.
  - simplify_crun_eq.
    apply: pass_lexpr_op_correct; eauto; last first.
    { iSatMono. iIntros "($ & $ & $ & $ & r & $)". iExact "r". }
    simpl. clear Hsat. intros w1 w2 Hdef. intros n' v1 v2 h1' h2' rf' b Hsub Hsat.
    simpl. eapply Hcont; eauto.
    iSatMono. iIntros "($ & $ & ($ & $ & ?) & $)".
Admitted.

Lemma pass_lookup_singleton (f g: string) fn fn':
  (lfndef_to_fndef <$> <[f:=fn]> ∅: gmap string fndef) !! g = Some fn' →
  fn' = lfndef_to_fndef fn ∧ f = g.
Proof.
  rewrite !lookup_fmap.
  intros [x [Hlook ->]]%fmap_Some_1.
  eapply lookup_insert_Some in Hlook as [[-> <-]|[? ?]]; last set_solver.
  done.
Qed.


Lemma heap_alloc_list_app vs1 vs2 ls h1 h2:
  heap_alloc_list (vs1 ++ vs2) ls h1 h2 →
  ∃ h ls1 ls2,
    ls = ls1 ++ ls2 ∧
    length ls1 = length vs1 ∧
    heap_alloc_list vs1 ls1 h1 h ∧
    heap_alloc_list vs2 ls2 h h2.
Proof.
  induction vs1 as [|v vs1 IH] in ls, h1, h2 |-*; simpl.
  - intros ?. eexists _, nil, _. split; done.
  - simpl; intros (l' & ls' & Heq & Hfresh & Halloc). subst.
    eapply IH in Halloc as (h & ls1 & ls2 & -> & Hlen & Halloc1 & Halloc2).
    eexists _, (_ :: _), _. split_and!; eauto.
    simpl; by rewrite Hlen.
Qed.


Lemma heap_bij_alloc_elim vs l ls li i h1 h2 n h h':
  ls !! i = Some l →
  vs !! i = Some n →
  heap_alloc_list (delete i vs) li h1 h' →
  heap_alloc_list vs ls h2 h →
  heap_bij_inv h1 h2 ⊢ |==>
    heap_bij_inv h' h ∗
    heap_bij_const_s l.1 (empty_block l n) ∗
    [∗ list] li; ls ∈ li; (delete i ls), loc_in_bij li ls.
Proof.
  intros Hlook1 Hlook2.
  rewrite delete_take_drop.
  eapply take_drop_middle in Hlook2 as Hsplit2; symmetry in Hsplit2.
  rewrite {3}Hsplit2.
  intros (h1' & li1 & li2 & -> & Hlen1 & H1i & H2i)%heap_alloc_list_app.
  intros (h2' & ls1 & ls2 & -> & Hlen2 & H1s & H2s)%heap_alloc_list_app.
  destruct H2s as (l' & ls2' & -> & Hfresh & H2s).
  assert (i = length ls1) as Hi.
  { rewrite Hlen2. symmetry. eapply take_length_le. eapply lookup_lt_Some in Hlook2. lia. }
  rewrite list_lookup_middle // in Hlook1.
  injection Hlook1 as ?; subst.
  rewrite delete_middle.

  iIntros "Hbij".
  iMod (heap_bij_inv_alloc_list with "Hbij") as "[Hbij Hbl]"; [done..|].
  iMod (heap_bij_inv_alloc_s with "Hbij") as "[Hbij Hconst]"; first done.
  iMod (heap_bij_inv_alloc_list with "Hbij") as "[Hbij Hbl']"; [done..|].
  rewrite block_heap_alloc //. iFrame "Hconst Hbij".
  iApply (big_sepL2_app with "Hbl Hbl'").
Qed.


Lemma list_delete_fmap {X Y: Type} i (f: X → Y) (L: list X):
  f <$> (delete i L) = delete i (f <$> L).
Proof.
  induction L in i |-*; destruct i; simpl; eauto.
  by erewrite IHL.
Qed.

Lemma empty_block_insert_zero l (k: Z):
  (k > 0)%Z → l.2 = 0%Z → <[0%Z:=ValNum 0%Z]> (empty_block l k) = empty_block l k.
Proof.
  intros Hk Hl; rewrite /empty_block.
  eapply map_leibniz, map_equiv_iff; intros i.
  destruct (decide (i = 0)).
  - subst. rewrite lookup_insert gmap_curry_total_lookup.
    symmetry. eapply leibniz_equiv_iff.
    eapply elem_of_list_to_map_1; last first.
    { eapply elem_of_list_fmap. exists 0%Z. rewrite elem_of_seqZ.
      split; last lia. rewrite shift_loc_0. f_equal.
      destruct l; simpl in *. by subst. }
    eapply NoDup_fmap_fst; last first.
    { eapply NoDup_fmap_2, NoDup_seqZ.
      intros z1 z2; injection 1. lia. }
    intros x y1 y2 [? []]%elem_of_list_fmap_2 [? []]%elem_of_list_fmap_2.
    by simplify_eq.
  - rewrite lookup_insert_ne //.
Qed.

Lemma heap_alloc_list_offset_zero vs ls h1 h2 i l:
  heap_alloc_list vs ls h1 h2 →
  ls !! i = Some l →
  l.2 = 0%Z.
Proof.
  induction vs as [|v vs IHvs] in i, ls, h1, h2 |-*; destruct ls; simpl; try naive_solver.
  intros (? & ? & ? & Hf & ?) Hlook. simplify_eq.
  destruct i; last by eauto.
  injection Hlook as ->. by destruct Hf.
Qed.


Lemma heap_bij_free_elim lis lss hi hs hs' w l k i:
  heap_free_list lss hs hs' →
  lss !! i = Some (l, k) →
  lis.*2 = (delete i lss.*2) →
    heap_bij_inv hi hs -∗
    heap_bij_const_s l.1 (<[0%Z:=w]> (empty_block l k)) -∗
    ([∗ list] li;ls ∈ lis.*1;(delete i lss.*1), loc_in_bij li ls) ==∗
      ∃ hi' : heap_state, ⌜heap_free_list lis hi hi'⌝ ∗
        heap_bij_inv hi' hs'.
Proof.
  induction lss as [|[l' k'] lss IH] in i, lis, hi, hs, hs' |-*; first by naive_solver.
  destruct i; simpl.
  - intros [Hr Hfree] ? Heq. simplify_eq. simpl in *.
    iIntros "Hbij Hl Hlocs".
    iMod (heap_bij_inv_free_s with "Hbij Hl") as "Hbij".
    iDestruct (heap_bij_inv_free_list with "Hbij Hlocs") as "?"; eauto.
  - intros [Hr Hfree] ? Heq. destruct lis as [|[l'' k''] lis]; first naive_solver.
    simpl in Heq. simplify_eq. simpl.
    iIntros "Hbij Hl [Hl' Hlocs]".
    iDestruct (heap_bij_inv_range with "Hbij Hl'") as "%"; first done.
    iDestruct (heap_bij_inv_free with "Hbij Hl'") as "Hbij".
    iMod (IH with "Hbij Hl Hlocs") as "[%hi' [% Hbij]]"; eauto.
Qed.


Lemma zip_lookup {X Y} (l1: list X) (l2: list Y) i j k :
  l1 !! i = Some k → l2 !! i = Some j → zip l1 l2 !! i = Some (k, j).
Proof.
  induction i in l1, l2 |-*; destruct l1, l2; naive_solver.
Qed.

Lemma pass_correct_refines f x args vars exprs i k cont expri:
  vars !! i = Some (x, k) →
  crun () (pass x exprs) = CResult () cont (CSuccess expri) →
  trefines
    (MS imp_module
      (initial_imp_state
            (lfndef_to_fndef <$>
              <[f:={|
                    lfd_args := args;
                    lfd_vars := delete i vars;
                    lfd_body := LLetE x (LVarVal (VVal (StaticValNum 0))) expri
                  |}]> ∅)))
    (MS (imp_heap_bij imp_module)
      (initial_imp_heap_bij_state imp_module
          (initial_imp_state
            (lfndef_to_fndef <$>
              <[f:={| lfd_args := args; lfd_vars := vars; lfd_body := exprs |}]> ∅)))).
Proof.
  intros Heq Hrun. apply: imp_heap_bij_proof.
  - set_solver.
  - move => ??. intros [-> ->]%pass_lookup_singleton.
    eexists. split; simpl.
    { rewrite lookup_fmap. eapply fmap_Some_2, lookup_insert.  }
    { done. }
  - intros n K1 K2 g fn1 fn2 vs1 vs2 h1 h2 r rf.
    intros [-> ->]%pass_lookup_singleton.
    intros [-> _]%pass_lookup_singleton.
    rewrite /= !fmap_insert !fmap_empty /=.
    intros Hlen1 Hlen2 Hsat Hcalls Hcont.

    (* we allocate the stack variables *)
    tstep_both. intros li h' Halloc. tstep_s.
    edestruct (heap_alloc_list_fresh vars.*2 ∅ h2) as [h Heap].
    eexists _, _. split; first done. intros Hall. tend. split.
    { by eapply Forall_fmap, Forall_delete, Forall_fmap. }

    (* side condition we need later *)
    pose (ls := (heap_fresh_list vars.*2 ∅ h2)).
    assert (length vars.*2 = length ls) as Hlen.
    { subst ls. clear. unfold fmap. generalize (∅: (gset prov)). generalize h2.
      induction vars as [|[]? IH]; simpl; first done.
      intros ??. by erewrite IH. }

    (* we clean up the substitutions *)
    rewrite !subst_l_subst_map; first last.
    { eapply heap_alloc_list_length in Halloc.
      revert Halloc. rewrite !fmap_length //.  }
    { done. }
    { rewrite !fmap_length -Hlen !fmap_length //. }
    { done. }
    rewrite -!subst_map_subst_map.
    rewrite -!list_to_map_app /=.

    (* we bind the pruned location in the target *)
    tstep_i.
    (* we clean up the substitutions *)
    rewrite -subst_subst_map_delete.

    destruct (ls !! i) as [l|] eqn: Hl; last first.
    { eapply lookup_lt_Some in Heq.
      rewrite fmap_length in Hlen.
      rewrite Hlen in Heq.
      eapply lookup_lt_is_Some_2 in Heq as [].
      naive_solver. }


    eapply (pass_correct (r ∗ [∗ list] l1;l2 ∈ li;delete i ls, loc_in_bij l1 l2) _ _ _ _ _ _ _ _ l _ k); last done.
    + eapply imp_expr_fill_expr_fill, imp_expr_fill_FreeA, imp_expr_fill_end.
    + eapply imp_expr_fill_expr_fill, imp_expr_fill_FreeA, imp_expr_fill_end.
    + by eapply heap_alloc_list_offset_zero.
    + done.
    + iSatClear. simpl. intros w n' v1 v2 h1' h2' rf' b Hle Hsat. simpl.
      tstep_s. intros h2'' Hfree. tstep_i.
      eapply heap_alloc_list_length in Halloc as Hlen3.
      eapply heap_alloc_list_length in Heap as Hlen4.
      iSatStartBupd. iIntros "(Hbij & Hv & [[r Hlocs] Hloc] & Hl)".
      rewrite list_delete_fmap in Hlen3.
      iPoseProof ((heap_bij_free_elim (zip li (delete i vars.*2))) with "Hbij") as "Hw".
      { done. }
      { eapply zip_lookup; eauto.
        rewrite list_lookup_fmap Heq //. }
      { rewrite snd_zip ?Hlen3 //.
        f_equal. rewrite snd_zip //. rewrite Hlen4 //. }
      rewrite fst_zip ?Hlen3 //.
      rewrite fst_zip ?Hlen4 //.
      iSpecialize ("Hw" with "Hloc Hlocs").
      iMod "Hw" as "(%hi' & %Hfree' & Hbij)". iModIntro.
      iSatStop. eexists _; split.
      { rewrite list_delete_fmap //. }
      rewrite orb_true_r.
      eapply Hcont; first done.
      iSatMono. iFrame.
    + rewrite list_to_map_app lookup_union_r; last first.
      { admit. }
      eapply elem_of_list_to_map.
      { rewrite fst_zip; admit. }
      eapply (elem_of_list_lookup_2 _ i).
      admit.
    + rewrite lookup_insert //.
    + admit.
    + admit.
      (* rewrite (empty_block_insert_zero l k); last first.
      { admit. }
      { admit. }
      iSatMonoBupd. iIntros "(Hbij & Hvals & r & rf)".
      iFrame "rf r". iMod (heap_bij_alloc_elim with "Hbij") as "(Hbij & Hconst & #Hlocs)"; eauto.
      { rewrite list_lookup_fmap Heq //. }
      { rewrite -list_delete_fmap //. }
      iFrame "Hbij Hconst Hlocs".
      rewrite delete_insert_delete.
      (* we resolve the remaining open things with an induction *)
      iStopProof.
      clear Hcalls Hcont h' Halloc h Heap Hsat Hall.
      revert vs1 vs2 Hlen1 Hlen2.
      induction args as [|a args IH].
      * intros [|v1 vs1] [|v2 vs2]; try discriminate.
        intros _ _. simpl.
        revert i li Hlen Hl Heq. fold ls.
        generalize ls. clear ls. admit.
        (* induction vars as [|[y p] vars IH].
        -- discriminate.
        -- intros [|l' ls] i li Hlen Hl Heq; try discriminate.
           injection Hlen as Hlen. rewrite !fmap_cons.
           destruct i as [|i].
           ++ simpl in *. injection Hl as ?. injection Heq as ??. subst.
              rewrite delete_insert_delete.
              iIntros "Hctx". iMod (IH with "[Hctx]"). *) *)
Admitted.



Lemma pass_single_var_correct f x args exprs varss expri varsi :
  pass_single_var x exprs varss = (expri, varsi) →
  trefines
  (MS imp_module (initial_imp_state
    (lfndef_to_fndef <$>
    <[f:={| lfd_args := args; lfd_vars := varsi; lfd_body := expri |}]> ∅)))
  (MS (imp_heap_bij imp_module)
     (initial_imp_heap_bij_state imp_module
        (initial_imp_state
           (lfndef_to_fndef <$>
            <[f:={| lfd_args := args; lfd_vars := varss; lfd_body := exprs |}]> ∅)))).
Proof.
  rewrite /pass_single_var.
  destruct list_find as [[i [y n]]|] eqn: Hfind;
    first destruct (crun () (pass x exprs)) as [[] ? [res|]] eqn: Hrun; simpl;
    last first.
  - injection 1 as ??; subst. eapply imp_heap_bij_imp_refl.
  - injection 1 as ??; subst. eapply imp_heap_bij_imp_refl.
  - injection 1 as ??; subst.
    eapply list_find_Some in Hfind as (Hlook & Hdec & _).
    eapply bool_decide_unpack in Hdec. subst.
    by eapply pass_correct_refines.
Qed.



Definition imp_heap_bij_N n (M: module imp_event) : module imp_event :=
  Nat.iter n imp_heap_bij M.

Fixpoint initial_imp_heap_bij_state_N n (M: module imp_event) (s: M.(m_state)) : (imp_heap_bij_N n M).(m_state) :=
  match n with
  | 0 => s
  | S n => initial_imp_heap_bij_state (imp_heap_bij_N n M) (initial_imp_heap_bij_state_N n M s)
  end.


Lemma pass_body_correct f args varss exprs expri varsi:
  pass_body exprs varss = (expri, varsi) →
  trefines
    (MS imp_module (initial_imp_state
      (lfndef_to_fndef <$>
      <[f:={| lfd_args := args; lfd_vars := varsi; lfd_body := expri |}]> ∅)))
    (MS (imp_heap_bij_N (length varss) imp_module)
       (initial_imp_heap_bij_state_N _ imp_module
          (initial_imp_lstate
             (<[f:={| lfd_args := args; lfd_vars := varss; lfd_body := exprs |}]> ∅)))).
Proof.
  rewrite /pass_body. remember varss as L. rewrite {1 5}HeqL. clear HeqL.
  induction L as [|[x n] L IHL] in varss, varsi, exprs, expri |-*; simpl.
  - injection 1 as ??. subst; reflexivity.
  - destruct foldr as [expri' varsi'] eqn: Hbody.
    intros Hsingle.
    eapply IHL in Hbody as IH. etrans; last first.
Admitted.


Lemma pass_fn_correct f fn :
  trefines (MS imp_module (initial_imp_lstate (<[f := pass_fn fn]> ∅)))
           (MS (imp_heap_bij_N (length fn.(lfd_vars)) imp_module) (initial_imp_heap_bij_state_N _ imp_module
                                            (initial_imp_lstate (<[f := fn]> ∅)))).
Proof.
  rewrite /pass_fn. destruct pass_body as [expri varsi] eqn: Hpass.
  revert Hpass. destruct fn as [args varss exprs]; simpl.
  by eapply pass_body_correct.
Qed.

End ci2a_mem2reg.
