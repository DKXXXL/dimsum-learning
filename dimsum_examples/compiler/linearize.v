From stdpp Require Import pretty strings.
From dimsum.core Require Export proof_techniques.
From dimsum.examples Require Import rec.
From dimsum.examples.compiler Require Import monad linear_rec.

Local Open Scope Z_scope.
Set Default Proof Using "Type".

(** * Linearize pass : Rec -> LinearRec *)
(** This pass turns an Rec program into a LinearRec program. It
assumes that all variable names are unique (as established by the SSA
pass). *)

Definition tmp_var (n : N) : string :=
  "$" ++ pretty n ++ "$".

Global Instance tmp_var_inj : Inj (=) (=) tmp_var.
Proof.
  move => x y. unfold tmp_var => Heq. simplify_eq.
  move: Heq => /string_app_inj_r?. by simplify_eq.
Qed.

Module cr2a_linearize.

(** * pass *)
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
  | SMalloc e1 =>
      v1 ← pass e1;
      v ← fresh_var;
      cappend (λ x, LLetE v (LMalloc v1) x);;
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
  fd_body := (BinOp (BinOp (Var "x") OffsetOp (Val 2)) AddOp (Call "f" [Load (Var "x"); Val 1]));
  fd_static := I;
|}.


Lemma test_1 :
  crun 0%N (pass (expr_to_static_expr $ test_fn_1.(fd_body))) =
  CResult 4%N (λ x,
       LLetE "$0$" (LBinOp (VVar "x") OffsetOp (VVal (StaticValNum 2)))
         (LLetE "$1$" (LLoad (VVar "x"))
            (LLetE "$2$" (LCall "f" [VVar "$1$"; VVal (StaticValNum 1)])
               (LLetE "$3$" (LBinOp (VVar "$0$") AddOp (VVar "$2$")) x)))) (CSuccess (VVar "$3$")).
Proof. vm_compute. match goal with |- ?x = ?x => exact: eq_refl end. Abort.

Lemma test_2 :
  crun 0%N (pass (expr_to_static_expr $ LetE "v" (BinOp (Val 1) AddOp (Val 1)) $ Var "v")) =
  CResult 1%N (λ x,
       LLetE "$0$" (LBinOp (VVal (StaticValNum 1)) AddOp (VVal (StaticValNum 1)))
         (LLetE "v" (LVarVal (VVar "$0$")) x)) (CSuccess (VVar "v")).
Proof. vm_compute. match goal with |- ?x = ?x => exact: eq_refl end. Abort.

Lemma test_3 :
  crun 0%N (pass (expr_to_static_expr $  BinOp
                    (If (Val 1)
                       (BinOp (Val 1) AddOp (Val 2))
                       (Val 3))
                    AddOp (Var "x"))) =
  CResult 3%N (λ x,
       LIf (LVarVal (VVal (StaticValNum 1)))
         (LLetE "$0$" (LBinOp (VVal (StaticValNum 1)) AddOp (VVal (StaticValNum 2)))
            (LLetE "$1$" (LVarVal (VVar "$0$")) (LLetE "$2$" (LBinOp (VVar "$1$") AddOp (VVar "x")) x)))
         (LLetE "$1$" (LVarVal (VVal (StaticValNum 3))) (LLetE "$2$" (LBinOp (VVar "$1$") AddOp (VVar "x")) x)))
    (CSuccess (VVar "$2$")).
Proof. vm_compute. match goal with |- ?x = ?x => exact: eq_refl end. Abort.

Lemma test_4 :
  crun 0%N (pass (expr_to_static_expr $ BinOp
                    (If (Val 1)
                       (BinOp (Val 1) AddOp (Val 2))
                       (If (Val 1) (Val 2) (Val 3)))
                    AddOp (Var "x"))) =
  CResult 4%N (λ x,
       LIf (LVarVal (VVal (StaticValNum 1)))
         (LLetE "$0$" (LBinOp (VVal (StaticValNum 1)) AddOp (VVal (StaticValNum 2)))
            (LLetE "$2$" (LVarVal (VVar "$0$")) (LLetE "$3$" (LBinOp (VVar "$2$") AddOp (VVar "x")) x)))
         (LIf (LVarVal (VVal (StaticValNum 1)))
            (LLetE "$1$" (LVarVal (VVal (StaticValNum 2)))
               (LLetE "$2$" (LVarVal (VVar "$1$")) (LLetE "$3$" (LBinOp (VVar "$2$") AddOp (VVar "x")) x)))
            (LLetE "$1$" (LVarVal (VVal (StaticValNum 3)))
               (LLetE "$2$" (LVarVal (VVar "$1$")) (LLetE "$3$" (LBinOp (VVar "$2$") AddOp (VVar "x")) x)))))
    (CSuccess (VVar "$3$")).
Proof. vm_compute. match goal with |- ?x = ?x => exact: eq_refl end. Abort.

(** * Verification of pass *)
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
  | H : RecExprFill _ _ _ |- _ => destruct H; subst
  | H : NoDup (_ ++ _) |- _ => apply NoDup_app in H; destruct H as (?&?&?)
  | H : NoDup (_ :: _) |- _ => apply NoDup_cons in H; destruct H as (?&?)
  end;
  unfold fresh_var in *;
  simplify_crun_eq;
  repeat (destruct!; unfold fresh_var in *; simplify_crun_eq);
  learn_state.

Lemma pass_correct ei' Ki ei Ks es es' n h fns1 fns2 v s s' vsi vss
      `{!RecExprFill es Ks (subst_map vss (static_expr_to_expr es'))}:
  rec_proof_call n fns1 fns2 →
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
    Rec (expr_fill Ki $ subst_map vsi' (lexpr_to_expr ei')) h' fns1
       ⪯{rec_trans, rec_trans, n, false}
    Rec (expr_fill Ks (Val v')) h' fns2) →
  Rec (expr_fill Ki $ subst_map vsi (lexpr_to_expr (ei ei'))) h fns1
      ⪯{rec_trans, rec_trans, n, false}
  Rec es h fns2.
Proof.
  move => Hcall.
  elim: es' es s s' ei ei' v vsi vss h Ks RecExprFill0; try by move => *; simplify_crun_eq.
  - move => ?????????????????? Hcont. prepare_goal. case_match. 2: by tstep_s.
    apply Hcont; [done|by eapply lookup_weaken|done|naive_solver].
  - move => ?????????????????? Hcont. prepare_goal. apply Hcont; [done|done|done|naive_solver].
  - move => /= ??? IH1 IH2 ????????????????? Hcont. prepare_goal.
    apply: IH1; [done|done|done|set_solver|set_solver|done|].
    move => ?????? Hvsi'/=.
    apply: IH2; [done|by etrans|done|set_solver|set_unfold; naive_solver lia|set_unfold; naive_solver lia|].
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
    apply :IH; [done|done|done|set_solver|set_solver|done|].
    intros ???????Hvsi' =>/=. erewrite lookup_var_val_to_expr; [|done].
    destruct v' eqn:?.
    2,3: tstep_s; split!; intros; done.
    destruct (decide (z>0)) eqn:?.
    2:{ tstep_s. split!; intros. inversion H4.
        split; last first. intros; subst; done.
        split!. apply heap_fresh_is_fresh.
        Unshelve. all: try auto. exact (0,0). exact ∅. }
    tstep_i. intros. split; try done.
    tstep_i. tstep_s. split!. intros. split!; [naive_solver|naive_solver|].
    intros. rewrite -subst_subst_map_delete.
    apply :tsim_mono_b. destruct!. apply: Hcont.
    + lia.
    + by simplify_map_eq.
    + etrans; [done|]. apply insert_subseteq.
      apply eq_None_not_Some => /Hvsi'. set_unfold; naive_solver lia.
    + move => ? /lookup_insert_is_Some'[|]; [naive_solver lia|].
      move => /Hvsi'; set_unfold; naive_solver lia.
  - move => /= ? IH ????????????????? Hcont. prepare_goal.
    apply: IH; [done|done|done|set_solver|set_solver|done|].
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
    apply: IH1; [done|done|done|set_solver|set_solver|done|].
    move => ?????? Hvsi'/=.
    apply: IH2; [done|by etrans|done|set_solver|set_unfold; naive_solver lia|set_unfold; naive_solver lia|].
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
    apply: IH1; [done|done|done|set_solver|set_solver|done|].
    move => ?????? Hvsi'/=.
    erewrite lookup_var_val_to_expr; [|done].
    tstep_s => ??. subst.
    tstep_i. apply tsim_mono_b_false. case_match.
    + apply: IH2; [done|by etrans|done|set_solver|set_unfold; naive_solver lia|set_unfold; naive_solver lia|].
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
    + apply: IH3; [done|by etrans|done|set_solver|set_unfold; naive_solver lia|set_unfold; naive_solver lia|].
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
    apply: IH1; [done|done|done|set_solver|set_solver|done|].
    move => ?????? Hvsi'/=. erewrite lookup_var_val_to_expr; [|done].
    tstep_s. tstep_i. rewrite -!subst_subst_map_delete. apply tsim_mono_b_false.
    apply: IH2; [done| |done|set_solver| | |].
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
      apply: Hcall; [done| | |done|done|..].
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

(** * pass_fn *)
Definition pass_fn (f : static_fndef) : compiler_success error lfndef :=
  let x := crun 0%N (pass f.(sfd_body)) in
  (λ v, {|
     lfd_args := f.(sfd_args);
     lfd_vars := f.(sfd_vars);
     lfd_body := x.(c_prog) (LEnd $ LVarVal v);
  |} ) <$> x.(c_result).

Lemma test_1 :
  pass_fn (fndef_to_static_fndef test_fn_1) =
  CSuccess {|
    lfd_args := ["x"];
    lfd_vars := [];
    lfd_body :=
      LLetE "$0$" (LBinOp (VVar "x") OffsetOp (VVal (StaticValNum 2)))
        (LLetE "$1$" (LLoad (VVar "x"))
           (LLetE "$2$" (LCall "f" [VVar "$1$"; VVal (StaticValNum 1)])
              (LLetE "$3$" (LBinOp (VVar "$0$") AddOp (VVar "$2$")) (LEnd (LVarVal (VVar "$3$"))))))
  |}.
Proof. vm_compute. match goal with |- ?x = ?x => exact: eq_refl end. Abort.

(** * Verification of pass_fn *)
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
  trefines (linear_rec_mod (<[f := fn']> ∅)) (rec_static_mod (<[f := fn]> ∅)).
Proof.
  destruct (crun 0%N (pass (sfd_body fn))) as [?? res] eqn: Hsucc.
  unfold pass_fn. rewrite Hsucc => /= /(compiler_success_fmap_success _ _ _ _ _ _)[?[??]]. subst.
  move => // /NoDup_app[?[?/NoDup_app[?[??]]]]?.
  apply rec_proof. { move => ?. rewrite !lookup_fmap !fmap_None !lookup_insert_None. naive_solver. }
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
  apply: pass_correct; [done|done|done|done|set_solver|..].
  { move => ?. rewrite lookup_union_is_Some !list_to_map_lookup_is_Some.
    move => [|] [? /(elem_of_zip_l _ _ _)]; set_solver. }
  { move => ?. rewrite lookup_union_is_Some !list_to_map_lookup_is_Some.
    move => [|] [? /(elem_of_zip_l _ _ _)]; set_solver. }
  move => /= ???????. erewrite lookup_var_val_to_expr; [|done].
  tstep_s => ??. tstep_i. split!; [done|]. by apply Hret.
Qed.

End cr2a_linearize.
