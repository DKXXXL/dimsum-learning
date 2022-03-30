Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.filter.
Require Import refframe.product.
Require Import refframe.seq_product.
Require Import refframe.link.
Require Import stdpp.pretty.
Require Import refframe.prepost.
Require Import refframe.proof_techniques.
Require Import refframe.imp.


Local Open Scope Z_scope.
Set Default Proof Using "Type".

Definition ssa_var (s : string) (n : N) : string :=
  s ++ "$" ++ pretty n.

Global Instance ssa_var_inj : Inj2 (=) (=) (=) ssa_var.
Proof.
  move => ????. unfold ssa_var.
  move => /string_list_eq.
  rewrite !string_to_list_app => /= /(app_inj_middle _ _ _ _  _)[| |??]. 3: naive_solver.
  all: move => /pretty_N_digits; compute_done.
Qed.

Module ci2a_ssa.

Fixpoint state_bind {S A} (l : list (S → (S * A))) (s : S) : (S * list A) :=
  match l with
  | [] => (s, [])
  | f::l' =>
      let r1 := f s in
      let r2 := state_bind l' r1.1 in
      (r2.1, r1.2::r2.2)
  end.

Fixpoint pass (ren : gmap string string) (e : static_expr) (s : N) : (N * static_expr) :=
  match e with
  | SVar v => (s, SVar (default v (ren !! v)))
  | SVal v => (s, SVal v)
  | SBinOp e1 o e2 =>
      let p1 := pass ren e1 s in
      let p2 := pass ren e2 p1.1 in
      (p2.1, SBinOp p1.2 o p2.2)
  | SAlloc e1 =>
      let p1 := pass ren e1 s in
      (p1.1, SAlloc p1.2)
  | SFree e1 =>
      let p1 := pass ren e1 s in
      (p1.1, SFree p1.2)
  | SLoad e1 =>
      let p1 := pass ren e1 s in
      (p1.1, SLoad p1.2)
  | SStore e1 e2 =>
      let p1 := pass ren e1 s in
      let p2 := pass ren e2 p1.1 in
      (p2.1, SStore p1.2 p2.2)
  | SCall f args =>
      let p1 := state_bind (pass ren <$> args) s in
      (p1.1, SCall f p1.2)
  | SUbE => (s, SUbE)
  | SLetE v e1 e2 =>
      let p1 := pass ren e1 (s + 1) in
      let p2 := pass (<[v := ssa_var v s]> ren) e2 p1.1 in
      (p2.1, SLetE (ssa_var v s) p1.2 p2.2)
  | SIf e1 e2 e3 =>
      let p1 := pass ren e1 s in
      let p2 := pass ren e2 p1.1 in
      let p3 := pass ren e3 p2.1 in
      (p3.1, SIf p1.2 p2.2 p3.2)
  end.

Definition test_fn_1 : fndef := {|
  fd_args := ["x"];
  fd_body := (LetE "x" (LetE "x" (Var "x") $ Var "x") $
              LetE "y" (Var "x") $
              LetE "x" (Var "x") $
              Var "x");
  fd_static := I;
|}.
Compute (pass ∅ (expr_to_static_expr $ test_fn_1.(fd_body)) 0).

Lemma pass_state ren s e :
  (pass ren e s).1 = (s + N.of_nat (length (assigned_vars (static_expr_to_expr e))))%N.
Proof.
  revert ren s. induction e => //= ren s; try lia.
  all: rewrite ?IHe1 ?IHe2 ?IHe3 ?app_length; try lia.
  move: ren s.
  revert select (Forall _ _). elim; csimpl; [lia|].
  move => ?? IH1 _ IH2 ??. rewrite IH1 IH2 app_length. lia.
Qed.

Lemma pass_vars ren s e :
  assigned_vars (static_expr_to_expr (pass ren e s).2) =
  imap (λ n v, ssa_var v (s + N.of_nat n)) (assigned_vars (static_expr_to_expr e)).
Proof.
  revert ren s. induction e => //= ren s.
  all: rewrite ?IHe1 ?IHe2 ?IHe3 ?pass_state ?imap_app.
  all: repeat match goal with
              | |- _ :: _ = _ :: _ => f_equal
              | |- _ ++ _ = _ ++ _ => f_equal
              | |- imap _ _ = imap _ _ => apply imap_ext => * /=
              | |- ssa_var _ _ = ssa_var _ _ => f_equal
              end; try lia.
  revert s. revert select (Forall _ _).
  elim => //; csimpl => ?? IH1 _ IH2 s.
  rewrite imap_app IH2 pass_state. f_equal; [done|].
  apply imap_ext => * /=. f_equal. lia.
Qed.

Lemma pass_correct Ki Ks ei es es' n h fns1 fns2 s vsi vss ren
      `{!ImpExprFill es Ks (subst_map vss (static_expr_to_expr es'))}
      `{!ImpExprFill ei Ki (subst_map vsi (static_expr_to_expr (pass ren es' s).2))}:
  imp_proof_call n fns1 fns2 →
  (∀ i v, vss !! i = Some v → ∃ i', ren !! i = Some i' ∧ vsi !! i' = Some v) →
  (∀ x s', (s ≤ s')%N → vsi !! ssa_var x s' = None) →
  (∀ h' v',
    Imp (expr_fill Ki $ (Val v')) h' fns1
       ⪯{imp_module, imp_module, n, false}
    Imp (expr_fill Ks (Val v')) h' fns2) →
  Imp ei h fns1
      ⪯{imp_module, imp_module, n, false}
  Imp es h fns2.
Proof.
  move => Hcall.
  revert es ei ren s vsi vss h Ks Ki ImpExprFill0 ImpExprFill1.
  induction es' => //= es ei ren s vsi vss h Ks Ki [?] [?] Hvs Hvars Hcont; simplify_eq.
  - destruct (vss !! x) eqn: Hx. 2: by tstep_s.
    move: Hx => /Hvs[?[-> ->]]. done.
  - done.
  - apply: IHes'1; [eauto_tstep|eauto_tstep|done|done|] => /= ??.
    apply: IHes'2; [eauto_tstep|eauto_tstep|done|rewrite pass_state;naive_solver lia|] => /= ??.
    tstep_s => ??. tstep_i. split!. by apply tsim_mono_b_false.
  - apply: IHes'; [eauto_tstep|eauto_tstep|done|done|] => /= ??.
    tstep_s => *. subst. tstep_i. split!. by apply tsim_mono_b_false.
  - apply: IHes'1; [eauto_tstep|eauto_tstep|done|done|] => /= ??.
    apply: IHes'2; [eauto_tstep|eauto_tstep|done|rewrite pass_state;naive_solver lia|] => /= ??.
    tstep_s => *. subst. tstep_i. split!. by apply tsim_mono_b_false.
  - apply: IHes'; [eauto_tstep|eauto_tstep|done|done|] => /= ??.
    admit.
  - apply: IHes'; [eauto_tstep|eauto_tstep|done|done|] => /= ??.
    tstep_s => *. subst. tstep_i. split!. by apply tsim_mono_b_false.
  - apply: IHes'1; [eauto_tstep|eauto_tstep|done|done|] => /= ??.
    tstep_s => *. subst. tstep_i. apply tsim_mono_b_false. case_match.
    + apply: IHes'2; [eauto_tstep|eauto_tstep|done|rewrite pass_state;naive_solver lia|] => /= ??. done.
    + apply: IHes'3; [eauto_tstep|eauto_tstep|done|rewrite !pass_state;naive_solver lia|] => /= ??. done.
  - apply: IHes'1; [eauto_tstep|eauto_tstep|done|naive_solver lia|] => /= ??.
    tstep_i. tstep_s. rewrite -!subst_subst_map_delete. apply tsim_mono_b_false.
    apply: IHes'2; [eauto_tstep|eauto_tstep| | |done].
    + move => ?? /lookup_insert_Some[[??]|[?/Hvs[?[? Hvsi]]]]; simplify_eq.
      { eexists _. by simplify_map_eq. }
      eexists _. rewrite lookup_insert_ne //. split; [done|].
      apply lookup_insert_Some. right. split!. move => ?. subst. move: Hvsi.
      apply: eq_None_ne_Some_1. naive_solver lia.
    + move => ? s'. rewrite !pass_state => ?. apply lookup_insert_None. naive_solver lia.
  - rewrite -(app_nil_l (subst_map vsi <$> _)) -(app_nil_l (subst_map vss <$> _)).
    change ([]) with (Val <$> []). move: [] => vs. move: s vs h Hvars.
    revert select (Forall _ _). elim.
    + move => ???? /=. rewrite app_nil_r.
      apply: Hcall; [eauto_tstep|eauto_tstep|done| | |done|done|done].
      { apply Forall2_fmap_l. apply Forall_Forall2_diag. by apply Forall_true. }
      { apply Forall2_fmap_l. apply Forall_Forall2_diag. by apply Forall_true. }
    + move => ?? IH _ IH2 s vs h Hvars. csimpl.
      eapply IH; [| |done|done|] => /=.
      { constructor. by instantiate (1:=(CallCtx _ _ _) ::_). }
      { constructor. by instantiate (1:=(CallCtx _ _ _) ::_). }
      move => ?? /=. rewrite !cons_middle !app_assoc -fmap_snoc. apply IH2.
      rewrite pass_state. naive_solver lia.
  - by tstep_s.
Admitted.

Definition pass_fn (f : static_fndef) : static_fndef :=
  let args := imap (λ n v, ssa_var v (N.of_nat n)) f.(sfd_args) in
  {|
     sfd_args := args;
     sfd_body := (pass (list_to_map (zip f.(sfd_args) args)) f.(sfd_body) (N.of_nat (length f.(sfd_args)))).2;
  |}.

Compute pass_fn (fndef_to_static_fndef test_fn_1).

Lemma pass_fn_args_NoDup fn:
  NoDup (sfd_args (pass_fn fn)).
Proof. apply NoDup_alt => /= ??? /list_lookup_imap_Some? /list_lookup_imap_Some?. naive_solver. Qed.

Lemma pass_fn_vars f :
  sfd_args (pass_fn f) ++ assigned_vars (static_expr_to_expr (sfd_body (pass_fn f))) =
  imap (λ n v, ssa_var v (N.of_nat n)) (sfd_args f ++ assigned_vars (static_expr_to_expr (sfd_body f))).
Proof.
  rewrite imap_app. f_equal => /=. rewrite pass_vars.
  apply imap_ext. move => *. f_equal. lia.
Qed.

Lemma pass_fn_correct f fn :
  trefines (MS imp_module (initial_imp_sstate (<[f := pass_fn fn]> ∅)))
           (MS imp_module (initial_imp_sstate (<[f := fn]> ∅))).
Proof.
  apply imp_proof. { move => ?. rewrite !lookup_fmap !fmap_None !lookup_insert_None. naive_solver. }
  move => ???????. rewrite !fmap_insert !fmap_empty /=.
  move => /lookup_insert_Some[[??]|[??]]; simplify_map_eq. split!. { by rewrite imap_length. }
  rewrite imap_length. move => ?? Hret.
  rewrite !subst_l_subst_map; [|rewrite ?imap_length; lia..].
  apply: pass_correct; [eauto_tstep|eauto_tstep|done|..].
  - move => i v /list_to_map_lookup_Some [? [/lookup_zip_with_Some [? [? [?[??]]]] Hl]]. simplify_eq.
    eexists _. split.
    + apply list_to_map_lookup_Some. eexists _. split.
      * apply lookup_zip_with_Some. split!; [done|]. apply list_lookup_imap_Some. split!.
      * move => ??. rewrite fst_zip ?imap_length // => ?. apply Hl.
        rewrite fst_zip //. lia.
    + apply list_to_map_lookup_Some. eexists _. split.
      * apply lookup_zip_with_Some. split!; [|done]. apply list_lookup_imap_Some. split!.
      * move => ??. rewrite fst_zip ?imap_length //; [|lia] => /list_lookup_imap_Some[?[??]] ??.
        simplify_eq. lia.
  - move => ???. apply not_elem_of_list_to_map_1.
    move => /elem_of_list_fmap[[??][?]] /(elem_of_zip_with _ _ _ _)[?[?[?[/elem_of_lookup_imap]]]].
    move => [?[?[? /(lookup_lt_Some _ _ _) ?]]]. naive_solver lia.
  - move => ?? /=. by apply Hret.
Qed.

End ci2a_ssa.
