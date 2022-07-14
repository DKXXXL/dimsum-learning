From stdpp Require Import pretty strings.
From dimsum.core Require Export proof_techniques.
From dimsum.examples Require Import imp.
From dimsum.examples.compiler Require Import monad linear_imp.

Local Open Scope Z_scope.
Set Default Proof Using "Type".

Definition tmp_var (n : N) : string :=
  "$" ++ pretty n ++ "$".

Global Instance tmp_var_inj : Inj (=) (=) tmp_var.
Proof.
  move => x y. unfold tmp_var => Heq. simplify_eq.
  move: Heq => /string_app_inj_r?. by simplify_eq.
Qed.

Module ci2a_linearize.

Inductive error :=.

Definition M := compiler_monad N (fn_compiler_monoid lexpr) error.

Definition fresh_var : M string :=
  n ← cget;
  cput (n + 1)%N;;
  mret (tmp_var n).

Fixpoint pass (e : static_expr) : M var_val :=
  match e with
  | SVar v => mret $ VVar v
  | SVal v => mret $ VVal v
  | SBinOp e1 o e2 =>
      v1 ← pass e1;
      v2 ← pass e2;
      v ← fresh_var;
      cappend (λ x, LLetE v (LBinOp v1 o v2) x);;
      mret $ VVar v
  | SLoad e1 =>
      v1 ← pass e1;
      v ← fresh_var;
      cappend (λ x, LLetE v (LLoad v1) x);;
      mret $ VVar v
  | SStore e1 e2 =>
      v1 ← pass e1;
      v2 ← pass e2;
      v ← fresh_var;
      cappend (λ x, LLetE v (LStore v1 v2) x);;
      mret $ VVar v
  | SCall f args =>
      vs ← cmap (pass <$> args) 0 (λ _ a, a);
      v ← fresh_var;
      cappend (λ x, LLetE v (LCall f vs) x);;
      mret $ VVar v
  | SLetE v e1 e2 =>
      v1 ← pass e1;
      cappend (λ x, LLetE v (LVarVal v1) x);;
      pass e2
  | SIf e1 e2 e3 =>
      v1 ← pass e1;
      s ← cget;
      '(v2, p2) ← cscope (pass e2);
      '(v3, p3) ← cscope (pass e3);
      v ← fresh_var;
      cappend (λ x, LIf (LVarVal v1)
                        (p2 (LLetE v (LVarVal v2) x))
                        (p3 (LLetE v (LVarVal v3) x)));;
      mret $ (VVar v)
  end.

Definition test_fn_1 : fndef := {|
  fd_args := ["x"];
  fd_vars := [];
  fd_body := (BinOp (BinOp (Var "x") ShiftOp (Val 2)) AddOp (Call "f" [Load (Var "x"); Val 1]));
  fd_static := I;
|}.

Compute crun 0%N (pass (expr_to_static_expr $ test_fn_1.(fd_body))).
Compute crun 0%N (pass (expr_to_static_expr $ LetE "v" (BinOp (Val 1) AddOp (Val 1)) $ Var "v")).
Compute crun 0%N (pass
                    (expr_to_static_expr $  BinOp
                       (If (Val 1)
                           (BinOp (Val 1) AddOp (Val 2))
                           (Val 3))
                       AddOp (Var "x"))).
Compute crun 0%N (pass
                    (expr_to_static_expr $ BinOp
                       (If (Val 1)
                           (BinOp (Val 1) AddOp (Val 2))
                           (If (Val 1) (Val 2) (Val 3)))
                       AddOp (Var "x"))).

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

Lemma pass_state_mono s es s' ei v :
  crun s (pass es) = CResult s' ei (CSuccess v) →
  (s ≤ s')%N.
Proof.
  move: s s' ei v. induction es => s s' ei ? /= ?; unfold fresh_var in *; simplify_crun_eq => //.
  all: repeat (case_match; simplify_crun_eq).
  all: try pose proof (IHes1 _ _ _ _ ltac:(done)).
  all: try pose proof (IHes2 _ _ _ _ ltac:(done)).
  all: try pose proof (IHes3 _ _ _ _ ltac:(done)).
  all: try pose proof (IHes _ _ _ _ ltac:(done)).
  all: try lia.
  move: 0%nat H0 => m.
  elim: H s x x0 x1 m. { move => *; simplify_crun_eq; lia. }
  move => ?? IH1 ? IH2 *. simplify_crun_eq. move: H => /IH1. move: H0 => /IH2. lia.
Qed.


Local Ltac learn_state :=
  repeat match goal with
         | H : crun _ (pass _) = CResult _ _ (CSuccess _) |- _ =>
             learn_hyp (pass_state_mono _ _ _ _ _ H)
         end.

Local Ltac prepare_goal :=
  simplify_eq/=;
  repeat match goal with
  | H : ImpExprFill _ _ _ |- _ => destruct H; subst
  | H : NoDup (_ ++ _) |- _ => apply NoDup_app in H; destruct H as (?&?&?)
  | H : NoDup (_ :: _) |- _ => apply NoDup_cons in H; destruct H as (?&?)
  end;
  unfold fresh_var in *;
  simplify_crun_eq;
  repeat (destruct!; unfold fresh_var in *; simplify_crun_eq);
  learn_state.

Lemma pass_correct ei' Ki ei Ks es es' n h fns1 fns2 v s s' vsi vss
      `{!ImpExprFill es Ks (subst_map vss (static_expr_to_expr es'))}:
  imp_proof_call n fns1 fns2 →
  crun s (pass es') = CResult s' ei (CSuccess v) →
  vss ⊆ vsi →
  NoDup (assigned_vars (static_expr_to_expr es')) →
  (∀ n, tmp_var n ∉ assigned_vars (static_expr_to_expr es')) →
  (∀ v, is_Some (vsi !! v) → v ∉ assigned_vars (static_expr_to_expr es')) →
  (∀ n, is_Some (vsi !! tmp_var n) → (n < s)%N) →
  (* TODO: assigned_vars not in vsi and tmp_var greater than n *)
  (∀ h' v' vsi',
    (s ≤ s')%N →
    lookup_var_val vsi' v = Some v' →
    vsi ⊆ vsi' →
    (∀ v, is_Some (vsi' !! v) → is_Some (vsi !! v) ∨
                                v ∈ assigned_vars (static_expr_to_expr es') ∨
                                ∃ n, v = tmp_var n ∧ (n < s')%N) →
    Imp (expr_fill Ki $ subst_map vsi' (lexpr_to_expr ei')) h' fns1
       ⪯{imp_module, imp_module, n, false}
    Imp (expr_fill Ks (Val v')) h' fns2) →
  Imp (expr_fill Ki $ subst_map vsi (lexpr_to_expr (ei ei'))) h fns1
      ⪯{imp_module, imp_module, n, false}
  Imp es h fns2.
Proof.
  move => Hcall.
  elim: es' es s s' ei ei' v vsi vss h Ks ImpExprFill0; try by move => *; simplify_crun_eq.
  - move => ?????????????????? Hcont. prepare_goal. case_match. 2: by tstep_s.
    apply Hcont; [done|by eapply lookup_weaken|done|naive_solver].
  - move => ?????????????????? Hcont. prepare_goal. apply Hcont; [done|done|done|naive_solver].
  - move => /= ??? IH1 IH2 ????????????????? Hcont. prepare_goal.
    eapply IH1; [eauto_tstep|done|done|done|set_solver|set_solver|done|].
    move => ?????? Hvsi'/=.
    eapply IH2; [eauto_tstep|done|by etrans|done|set_solver|set_unfold; naive_solver lia|set_unfold; naive_solver lia|].
    move => ?????? Hvsi'' /=.
    erewrite lookup_var_val_to_expr; [|by apply: lookup_var_val_mono].
    erewrite lookup_var_val_to_expr; [|done].
    tstep_s => ??.
    tstep_i. split!.
    tstep_i. rewrite -subst_subst_map_delete.
    apply: tsim_mono_b. apply: Hcont.
    + lia.
    + by simplify_map_eq.
    + etrans; [done|]. etrans; [done|]. apply insert_subseteq.
      apply eq_None_not_Some => /Hvsi''. set_unfold; naive_solver lia.
    + move => ? /lookup_insert_is_Some'[|]; [naive_solver lia|].
      move => /Hvsi'' [|[?|?]]; [ |set_unfold; naive_solver lia..].
      move => /Hvsi'; set_unfold; naive_solver lia.
  - move => /= ? IH ????????????????? Hcont. prepare_goal.
    eapply IH; [eauto_tstep|done|done|done|set_solver|set_solver|done|].
    move => ?????? Hvsi'/=.
    erewrite lookup_var_val_to_expr; [|done].
    tstep_s => ????. subst.
    tstep_i. split!.
    tstep_i. rewrite -subst_subst_map_delete.
    apply: tsim_mono_b. apply: Hcont.
    + lia.
    + by simplify_map_eq.
    + etrans; [done|]. apply insert_subseteq.
      apply eq_None_not_Some => /Hvsi'. set_unfold; naive_solver lia.
    + move => ? /lookup_insert_is_Some'[|]; [naive_solver lia|].
      move => /Hvsi'; set_unfold; naive_solver lia.
  - move => /= ?? IH1 IH2 ????????????????? Hcont. prepare_goal.
    eapply IH1; [eauto_tstep|done|done|done|set_solver|set_solver|done|].
    move => ?????? Hvsi'/=.
    eapply IH2; [eauto_tstep|done|by etrans|done|set_solver|set_unfold; naive_solver lia|set_unfold; naive_solver lia|].
    move => ?????? Hvsi'' /=.
    erewrite lookup_var_val_to_expr; [|by apply: lookup_var_val_mono].
    erewrite lookup_var_val_to_expr; [|done].
    tstep_s => ???. subst.
    tstep_i. split!.
    tstep_i. rewrite -subst_subst_map_delete.
    apply: tsim_mono_b. apply: Hcont.
    + lia.
    + by simplify_map_eq.
    + etrans; [done|]. etrans; [done|]. apply insert_subseteq.
      apply eq_None_not_Some => /Hvsi''. set_unfold; naive_solver lia.
    + move => ? /lookup_insert_is_Some'[|]; [naive_solver lia|].
      move => /Hvsi'' [|[?|?]]; [ |set_unfold; naive_solver lia..].
      move => /Hvsi'; set_unfold; naive_solver lia.
  - move => ??? IH1 IH2 IH3 > ?????? Hcont. prepare_goal.
    eapply IH1; [eauto_tstep|done|done|done|set_solver|set_solver|done|].
    move => ?????? Hvsi'/=.
    erewrite lookup_var_val_to_expr; [|done].
    tstep_s => ??. subst.
    tstep_i. apply tsim_mono_b_false. case_match.
    + eapply IH2; [eauto_tstep|done|by etrans|done|set_solver|set_unfold; naive_solver lia|set_unfold; naive_solver lia|].
    move => ?????? Hvsi''/=.
    erewrite lookup_var_val_to_expr; [|by apply: lookup_var_val_mono].
    tstep_i. rewrite -subst_subst_map_delete.
    apply: tsim_mono_b. apply: Hcont.
    * lia.
    * by simplify_map_eq.
    * etrans; [done|]. etrans; [done|]. apply insert_subseteq.
      apply eq_None_not_Some => /Hvsi''. set_unfold; naive_solver lia.
    * move => ? /lookup_insert_is_Some'[|]; [naive_solver lia|].
      move => /Hvsi'' [|[?|?]]; [ |set_unfold; naive_solver lia..].
      move => /Hvsi'; set_unfold; naive_solver lia.
    + eapply IH3; [eauto_tstep|done|by etrans|done|set_solver|set_unfold; naive_solver lia|set_unfold; naive_solver lia|].
      move => ?????? Hvsi''/=.
      erewrite lookup_var_val_to_expr; [|by apply: lookup_var_val_mono].
      tstep_i. rewrite -subst_subst_map_delete.
      apply: tsim_mono_b. apply: Hcont.
      * lia.
      * by simplify_map_eq.
      * etrans; [done|]. etrans; [done|]. apply insert_subseteq.
        apply eq_None_not_Some => /Hvsi''. set_unfold; naive_solver lia.
      * move => ? /lookup_insert_is_Some'[|]; [naive_solver lia|].
        move => /Hvsi'' [|[?|?]]; [ |set_unfold; naive_solver lia..].
        move => /Hvsi'; set_unfold; naive_solver lia.
  - move => ??? IH1 IH2 ????????????????? Hcont. prepare_goal.
    eapply IH1; [eauto_tstep|done|done|done|set_solver|set_solver|done|].
    move => ?????? Hvsi'/=. erewrite lookup_var_val_to_expr; [|done].
    tstep_s. tstep_i. rewrite -!subst_subst_map_delete. apply tsim_mono_b_false.
    eapply IH2; [eauto_tstep|done| |done|set_solver| | |].
    { by apply insert_mono; etrans. }
    { move => ?/lookup_insert_is_Some'. set_solver. }
    { move => ?/lookup_insert_is_Some'. set_unfold; naive_solver lia. }
    move => ?????? Hvsi''/=.
    eapply Hcont; [lia|done| |].
    * etrans; [done|]. etrans; [|done]. apply insert_subseteq.
      apply eq_None_not_Some => /Hvsi'. set_unfold; naive_solver lia.
    * move => ? /Hvsi'' [|[?|?]]; [ |set_unfold; naive_solver lia..].
      move => /lookup_insert_is_Some'[|]; [set_solver|].
      move => /Hvsi'; set_unfold; naive_solver lia.
  - move => f args IH es s s' ei ei' v vsi vss h Ks [?] Hrun Hsub Hnodup Htmp Hvsi1 Hvsi2 Hcont. subst.
    simplify_eq/=. move: Hrun => /cbind_success[s''[p''[v''[?[Hrun ?]]]]]. prepare_goal.
    move: 0%nat Hrun => m Hrun.
    change (v'') with ([] ++ v''). move Heqvr'': ([]) => vr''.
    change (subst_map vss <$> (static_expr_to_expr <$> args)) with ((Val <$> []) ++ (subst_map vss <$> (static_expr_to_expr <$> args))). move Heqva'': ([]) => va''.
    have Hall : Forall2 (λ vr va, lookup_var_val vsi vr = Some va) vr'' va'' by subst; constructor.
    clear Heqvr'' Heqva''.
    elim: IH m p'' v'' s s'' vsi vr'' va'' h Hrun Hsub Hvsi1 Hvsi2 Hnodup Htmp Hall Hcont.
    + move => /= ??????????????? /lookup_var_val_to_expr_fmap Hall Hcont. simplify_crun_eq. rewrite !app_nil_r.
      rewrite Hall.
      apply: Hcall; [eauto_tstep|eauto_tstep|done| | |done|done|..].
      { apply Forall2_fmap_l. apply Forall_Forall2_diag. by apply Forall_true. }
      { apply Forall2_fmap_l. apply Forall_Forall2_diag. by apply Forall_true. }
      move => ?? /=.
      tstep_i. rewrite -!subst_subst_map_delete. apply tsim_mono_b_false.
      apply Hcont.
      * lia.
      * by simplify_map_eq.
      * apply insert_subseteq. apply eq_None_not_Some; naive_solver lia.
      * move => ? /lookup_insert_is_Some'[|]; naive_solver lia.
    + csimpl. move => ?? IHe _ IH ???????????????? Hcont. prepare_goal.
      eapply IHe; [ |done|done|done|set_solver|set_solver|done|].
      { constructor. by instantiate (1:=(CallCtx _ _ _) ::_). }
      move => ?????? Hvsi /=. rewrite !cons_middle !app_assoc -fmap_snoc.
      eapply IH.
      * done.
      * by etrans.
      * set_solver.
      * set_unfold; naive_solver lia.
      * done.
      * set_unfold; naive_solver lia.
      * apply Forall2_app; [|by econs].
        apply: Forall2_impl; [done|] => ?? /=?. apply: lookup_var_val_mono; [done|]. by etrans.
      * move => ?????? Hvsi'. apply Hcont; [lia|done|by etrans|].
        move => ? /Hvsi'[|]; [| set_unfold; naive_solver lia].
        move => /Hvsi. set_unfold; naive_solver lia.
Qed.

Definition pass_fn (f : static_fndef) : compiler_success error lfndef :=
  let x := crun 0%N (pass f.(sfd_body)) in
  (λ v, {|
     lfd_args := f.(sfd_args);
     lfd_vars := f.(sfd_vars);
     lfd_body := x.(c_prog) (LEnd $ LVarVal v);
  |} ) <$> x.(c_result).

Compute pass_fn (fndef_to_static_fndef test_fn_1).

Lemma pass_fn_args fn fn' :
  pass_fn fn = CSuccess fn' →
  lfd_args fn' = sfd_args fn.
Proof. rewrite /pass_fn => /(compiler_success_fmap_success _ _ _ _ _ _). naive_solver. Qed.

Lemma pass_fn_vars fn fn' :
  pass_fn fn = CSuccess fn' →
  lfd_vars fn' = sfd_vars fn.
Proof. rewrite /pass_fn => /(compiler_success_fmap_success _ _ _ _ _ _). naive_solver. Qed.

Lemma pass_fn_correct f fn fn' :
  pass_fn fn = CSuccess fn' →
  NoDup (sfd_args fn ++ (sfd_vars fn).*1 ++ assigned_vars (static_expr_to_expr (sfd_body fn))) →
  (∀ n, tmp_var n ∉ sfd_args fn ++ (sfd_vars fn).*1 ++ assigned_vars (static_expr_to_expr (sfd_body fn))) →
  trefines (MS imp_module (initial_imp_lstate (<[f := fn']> ∅)))
           (MS imp_module (initial_imp_sstate (<[f := fn]> ∅))).
Proof.
  destruct (crun 0%N (pass (sfd_body fn))) as [?? res] eqn: Hsucc.
  unfold pass_fn. rewrite Hsucc => /= /(compiler_success_fmap_success _ _ _ _ _ _)[?[??]]. subst.
  move => // /NoDup_app[?[?/NoDup_app[?[??]]]]?.
  apply imp_proof. { move => ?. rewrite !lookup_fmap !fmap_None !lookup_insert_None. naive_solver. }
  move => ???????. rewrite !fmap_insert !fmap_empty /=.
  move => /lookup_insert_Some[[??]|[??]]; simplify_map_eq. split!.
  move => ?? Hret.
  rewrite !subst_l_subst_map; [|lia..].
  tstep_both => ???.
  tstep_s. split!; [done|] => ?. tend. split!.
  efeed pose proof heap_alloc_list_length as Hl; [done|]. rewrite fmap_length in Hl.
  rewrite !subst_l_subst_map; [|rewrite ?fmap_length; lia..]. rewrite -!subst_map_subst_map.
  apply tsim_mono_b_false.
  have ->: ∀ K ls e, expr_fill K (FreeA ls e) = expr_fill (FreeACtx ls :: K) e by [].
  apply: pass_correct; [eauto_tstep|done|done|done|done|set_solver|..].
  { move => ?. rewrite lookup_union_is_Some !list_to_map_lookup_is_Some.
    move => [|] [? /(elem_of_zip_l _ _ _)]; set_solver. }
  { move => ?. rewrite lookup_union_is_Some !list_to_map_lookup_is_Some.
    move => [|] [? /(elem_of_zip_l _ _ _)]; set_solver. }
  move => /= ???????. erewrite lookup_var_val_to_expr; [|done].
  tstep_s => ??. tstep_i. split!; [done|]. by apply Hret.
Qed.

End ci2a_linearize.
