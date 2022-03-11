Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.filter.
Require Import refframe.product.
Require Import refframe.seq_product.
Require Import refframe.link.
Require Import refframe.proof_techniques.
Require Import refframe.prepost.
Require Import refframe.imp.
Require Import refframe.asm.
Require Import refframe.itree.
Require Import refframe.imp_to_asm.

Local Open Scope Z_scope.

Definition int_to_ptr_asm : gmap Z asm_instr :=
  (* cast_int_to_ptr *)
  <[ 400 := [
        (* ret *)
        WriteReg "PC" (λ rs, rs !!! "R30")
    ] ]> $
  (* cast_ptr_to_int *)
  <[ 404 := [
        (* ret *)
        WriteReg "PC" (λ rs, rs !!! "R30")
    ] ]> $ ∅.

Definition int_to_ptr_itree : itree (moduleE imp_event (gmap prov Z)) unit :=
  ITree.forever (
      f ← TExist string;;;
      vs ← TExist (list val);;;
      h ← TExist (heap_state);;;
      TVis (Incoming, EICall f vs h);;;;
      if bool_decide (f = "cast_int_to_ptr") then
        z ← TAll Z;;;
        TAssume (vs = [ValNum z]);;;;
        l ← TAll loc;;;
        ps ← TGet;;;
        TAssume (ps !! l.1 = Some (z - l.2));;;;
        TVis (Outgoing, EIReturn (ValLoc l) h)
      else if bool_decide (f = "cast_ptr_to_int") then
        l ← TAll loc;;;
        TAssume (vs = [ValLoc l]);;;;
        z ← TExist Z;;;
        ps ← TGet;;;
        let ps' := <[l.1 := (default z (ps !! l.1))]> ps in
        TPut ps';;;;
        TVis (Outgoing, EIReturn (ValNum (ps' !!! l.1 + l.2)) h)
      else
        TNb).

Local Ltac go :=
  clear_itree.
Local Ltac go_s :=
  tstep_s; go.
Local Ltac go_i :=
  tstep_i; go.

Lemma int_to_ptr_asm_refines_itree :
  trefines (MS asm_module (initial_asm_state int_to_ptr_asm))
           (MS (imp_to_asm (dom _ int_to_ptr_asm) ({[ "cast_int_to_ptr"; "cast_ptr_to_int" ]})
                           (<["cast_int_to_ptr" := 400]> $ <["cast_ptr_to_int" := 404]> $ ∅)
                           (mod_itree imp_event (gmap prov Z)))
               (initial_imp_to_asm_state (mod_itree _ _) (int_to_ptr_itree, ∅))).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember. { simpl. exact (λ _ σa '(σf, (t, ps), (pp, σi2a, P)),
    t ≈ int_to_ptr_itree ∧
    σa.(asm_cur_instr) = None ∧
    σa.(asm_instrs) = int_to_ptr_asm ∧
    σi2a.(i2a_calls) = [] ∧
    σf = SMFilter ∧
    pp = PPOutside ∧
    (P ⊢ [∗ map] p↦z∈ps, i2a_heap_shared p z)). }
  { split!. by rewrite big_sepM_empty. } { done. }
  move => n _ Hloop [????] [[?[? ps]][[??]?]] ?. destruct_all?; simplify_eq/=.
  tstep_i => ????? Hi. tstep_s. split!. tstep_s => *. case_match => /= *. 2: congruence.
  tstep_s. rewrite -/int_to_ptr_itree. go. go_s. eexists _. go. go_s. eexists _. go. go_s. eexists _. go.
  go_s. split!. go.
  revert select (_ ⊢ _) => HP.
  revert select (imp_to_asm_args _ _ _) => -[?[?[??]]].
  revert select (_ ∉ dom _ _) => /not_elem_of_dom?.
  unfold int_to_ptr_asm in Hi. (repeat case_bool_decide); simplify_map_eq.
  - tstep_i. split; [by simplify_map_eq'|].
    go_s => ?. go.
    go_s => ?. go.
    go_s => ?. go.
    go_s. go_s => ?. go.
    iSatStart. iIntros!.
    iDestruct (big_sepL2_cons_inv_l with "[$]") as (???) "[% ?]".
    iDestruct (big_sepL2_nil_inv_l with "[$]") as %?. simplify_eq/=.
    decompose_Forall_hyps.
    iDestruct (HP with "[$]") as "HP".
    iDestruct (big_sepM_lookup with "HP") as "#?"; [done|].
    iSatStop.
    tstep_i => ??. simplify_map_eq'.
    go_s. go_s. split!. { by simplify_map_eq'. }
    1: { unfold imp_to_asm_ret; split!; simplify_map_eq'; split!.
         - by apply map_list_included_insert.
         - apply map_preserved_insert_r_not_in; [|done]. compute_done.
    }
    { apply map_scramble_insert_r_in; [compute_done|done]. }
    { iSatMono. simplify_map_eq'. iIntros!. iFrame. iSplitL; [iAccu|]. iSplit!; [|done]. lia. }
    apply Hloop; [done|].
    split!.
  - tstep_i. split; [by simplify_map_eq'|].
    go_s => l. go.
    go_s => ?. go.
    iSatStart. iIntros!.
    iDestruct (big_sepL2_cons_inv_l with "[$]") as (???) "[#[%z ?] ?]".
    iDestruct (big_sepL2_nil_inv_l with "[$]") as %?. simplify_eq/=.
    iDestruct!.
    iDestruct (HP with "[$]") as "HP".
    iDestruct (i2a_heap_shared_lookup with "[$] [$]") as %?. setoid_subst.
    decompose_Forall_hyps.
    iAssert ⌜z = default z (ps !! l.1)⌝%I as %Hz.
    { destruct (ps !! l.1) as [z'|] eqn:Hp => //=.
      iDestruct (big_sepM_lookup with "HP") as "?"; [done|].
      iAssert ⌜z = z'⌝%I as %?; [|done].
      by iApply i2a_heap_shared_ag. }
    iSatStop.
    go_s. eexists z. go.
    go_s. go_s. go_s.
    tstep_i => ??. simplify_map_eq'.
    go_s. split!. { by simplify_map_eq'. }
    1: { unfold imp_to_asm_ret; split!; simplify_map_eq'; split!.
         - by apply map_list_included_insert.
         - apply map_preserved_insert_r_not_in; [|done]. compute_done.
    }
    { apply map_scramble_insert_r_in; [compute_done|done]. }
    { iSatMono. simplify_map_eq'. iFrame. iSplitL; [by iStopProof|].
      rewrite -Hz. done.
    }
    apply Hloop; [done|].
    split!.
    iIntros "[#? #?]". rewrite -Hz.
    by iApply big_sepM_insert_2.
Qed.

Definition main_imp : fndef := {|
  fd_args := [];
  fd_body := LetE "l" (Alloc (Val 1)) $
             LetE "_" (Store (Var "l") (Val 1)) $
             LetE "z" (imp.Call "cast_ptr_to_int" [(Var "l")]) $
             LetE "z'" (BinOp (BinOp (Var "z") AddOp (Val (-1))) AddOp (Val 1)) $
             LetE "l'" (imp.Call "cast_int_to_ptr" [(Var "z")]) $
             LetE "r" (Load (Var "l'")) $
             LetE "_" (Free (Var "l")) $
             imp.Call "exit" [(Var "r")];
  fd_static := I
|}.

Definition main_imp_prog : gmap string fndef :=
  <[ "main" := main_imp ]> ∅.

Definition main_itree : itree (moduleE imp_event unit) unit :=
  f ← TExist string;;;
  vs ← TExist (list val);;;
  h ← TExist (heap_state);;;
  TVis (Incoming, EICall f vs h);;;;
  TAssume (f = "main");;;;
  TAssume (vs = []);;;;
  h' ← TExist (heap_state);;;
  TVis (Outgoing, EICall "exit" [ValNum 1] h');;;;
  TUb.

Lemma main_int_to_ptr_refines_itree :
  trefines (MS (imp_prod (dom _ main_imp_prog) ({[ "cast_int_to_ptr"; "cast_ptr_to_int" ]})
                         imp_module (mod_itree _ _))
               (MLFNone, [], initial_imp_state main_imp_prog, (int_to_ptr_itree, ∅)))
           (MS (mod_itree _ _) (main_itree, tt)).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  tstep_i => *. case_match; destruct_all?; simplify_eq.
  go_s. eexists _. go. go_s. eexists _. go. go_s. eexists _. go.
  go_s. split!. go.
  go_s => ?. go. go_s => ?. go. simplify_eq. rewrite bool_decide_true; [|compute_done].
  tstep_i. split! => ???? Hf ?. unfold main_imp_prog in Hf. simplify_map_eq.
  tstep_i => l ?. split!.
  tstep_i.
  tstep_i. split. { apply heap_alive_alloc; [done|lia]. }
  tstep_i. change ([Val (ValLoc l)]) with (Val <$> [ValLoc l]).
  tstep_i. split. { move => *; simplify_map_eq. }
  move => ????. rewrite bool_decide_false; [|compute_done]. rewrite bool_decide_true; [|compute_done].
  move => *. destruct_all?. simplify_eq/=.
  tstep_i. rewrite -/int_to_ptr_itree. go.
  go_i => ?. go.
  go_i => ?. go.
  go_i => ?. go.
  go_i => ?. go. simplify_eq/=.
  go_i. eexists _. go.
  go_i. split!. go.
  go_i => z. go.
  go_i. go_i. simplify_map_eq'.
  go_i => *. go. destruct_all?; simplify_eq.
  go_i. split!. move => *. simplify_eq.
  go_i.
  go_i.
  go_i.
  go_i. change ([Val (z + l.2)]) with (Val <$> [ValNum (z + l.2)]).
  tstep_i. split. { move => *; simplify_map_eq. }
  move => ????. rewrite bool_decide_false; [|compute_done]. rewrite bool_decide_true; [|compute_done].
  move => *. destruct_all?. simplify_eq/=.
  tstep_i. rewrite -/int_to_ptr_itree. go.
  go_i => ?. go.
  go_i => ?. go.
  go_i => ?. go.
  go_i => ?. go. simplify_eq/=.
  go_i. eexists _. go.
  go_i. split!. go.
  go_i. eexists l. go.
  go_i.
  go_i. simplify_map_eq. split; [f_equal; lia|]. go.
  go_i => *. go. destruct_all?; simplify_eq.
  go_i. split!. move => *. simplify_eq.
  go_i.
  go_i. eexists _. split. { rewrite shift_loc_0. by simplify_map_eq. }
  go_i.
  go_i. split. { apply heap_alive_update. apply heap_alive_alloc; [done|lia]. }
  go_i. change ([Val 1]) with (Val <$> [ValNum 1]).
  go_i. split. { move => *; simplify_map_eq. }
  move => ????. rewrite bool_decide_false; [|compute_done].
  move => *. destruct_all?. simplify_eq/=.
  go_s. eexists _. go.
  go_s. split!. go.
  go_s. done.
Qed.

Definition __NR_EXIT : Z := 93.

Definition exit_asm : gmap Z asm_instr :=
  (* exit *)
  <[ 100 := [
        WriteReg "R8" (λ rs, __NR_EXIT);
        WriteReg "PC" (λ rs, rs !!! "PC" + 4)
    ] ]> $
  <[ 104 := [
        Syscall false;
        WriteReg "PC" (λ rs, rs !!! "PC" + 4)
    ] ]> $
  <[ 108 := [
        (* loop *)
        WriteReg "PC" (λ rs, rs !!! "PC")
    ] ]> $ ∅.

Definition exit_itree : itree (moduleE asm_event unit) unit :=
  pc ← TExist _;;;
  rs ← TExist _;;;
  mem ← TExist _;;;
  TVis (Incoming, EAJump pc rs mem);;;;
  TAssume (pc = 100);;;;
  TAssume (map_list_included syscall_arg_regs rs);;;;
  args ← TExist _;;;
  TAssert (length args = length syscall_arg_regs);;;;
  TAssert (args !! 0%nat = Some (rs !!! "R0"));;;;
  TAssert (args !! 8%nat = Some __NR_EXIT);;;;
  TVis (Outgoing, EASyscallCall args);;;;
  ret ← TExist _;;;
  TVis (Incoming, EASyscallRet ret);;;;
  TNb.

Lemma exit_asm_refines_itree :
  trefines (MS asm_module (initial_asm_state exit_asm))
           (MS (mod_itree _ _) (exit_itree, tt)).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  go_i => ????? Hi.
  go_s. eexists _. go.
  go_s. eexists _. go.
  go_s. eexists _. go.
  go_s. split!. go.
  go_s => ?. go.
  go_s => ?. go.
  unfold exit_asm in Hi. simplify_map_eq.
  go_i. split. { apply: map_list_included_is_Some; [done|]. compute_done. }
  go_i. split. { by simplify_map_eq. }
  go_i => ??. simplify_map_eq'.
  go_i.
  go_s. eexists _. go.
  go_s. split; [shelve|]. go.
  go_s. split; [shelve|]. go.
  go_s. split; [shelve|]. go.
  go_s. split!. go.
  go_i => ?.
  go_s. eexists _. go.
  go_s. split!. go.
  go_i. split. { by simplify_map_eq. }
  sort_map_insert. simplify_map_eq'.
  unshelve eapply tsim_remember. { exact (λ _ '(AsmState i rs _ ins) _,
      i = Some [] ∧ rs !! "PC" = Some 108 ∧ ins = exit_asm). }
  { split!. by simplify_map_eq. } { done. }
  move => ?? Hloop [????] ? ?. destruct_all?; simplify_eq.
  go_i => ??. simplify_map_eq.
  go_i. split. { by simplify_map_eq. }
  apply Hloop; [done|]. split!. by simplify_map_eq'.
  Unshelve.
  - done.
  - by simplify_map_eq'.
  - by simplify_map_eq'.
Qed.

Definition top_level_itree : itree (moduleE asm_event unit) unit :=
  pc ← TExist _;;;
  rs ← TExist _;;;
  mem ← TExist _;;;
  TVis (Incoming, EAJump pc rs mem);;;;
  TAssume (pc = 200);;;;
  TAssume (map_list_included tmp_registers rs);;;;
  TAssume (map_list_included saved_registers rs);;;;
  TAssume (rs !!! "R30" ∉ ({[200; 400; 404]} : gset _));;;;
  args ← TExist _;;;
  TAssert (length args = length syscall_arg_regs);;;;
  TAssert (args !! 0%nat = Some 1);;;;
  TAssert (args !! 8%nat = Some __NR_EXIT);;;;
  TVis (Outgoing, EASyscallCall args);;;;
  ret ← TExist _;;;
  TVis (Incoming, EASyscallRet ret);;;;
  TNb.

Lemma top_level_refines_itree :
  trefines (MS (asm_prod {[200; 400; 404]} {[ 100; 104; 108 ]}
                         (imp_to_asm {[200; 400; 404]} {[ "main" ; "cast_int_to_ptr"; "cast_ptr_to_int" ]}
                                     (<[ "main" := 200 ]> $
                                      <[ "cast_int_to_ptr" := 400 ]> $
                                      <[ "cast_ptr_to_int" := 404 ]> $
                                      <[ "exit" := 100 ]> $ ∅)
                                     (mod_itree _ _)) (mod_itree _ _))
               (MLFNone, None, initial_imp_to_asm_state (mod_itree _ _) (main_itree, tt), (exit_itree, tt)))
           (MS (mod_itree _ _) (top_level_itree, tt)).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  go_i => ?????. case_match; destruct_all?; simplify_eq.
  go_s. eexists _. go.
  go_s. eexists _. go.
  go_s. eexists _. go.
  go_s. split!. go.
  go_s => ?. go.
  go_s => ?. go.
  go_s => ?. go.
  go_s => ?. go. simplify_eq/=.
  rewrite bool_decide_true; [|compute_done].
  go_i => ??. simplify_eq.
  go_i. eexists true => /=. split; [done|]. eexists ∅, ∅, ∅.
  split. { admit. }
  eexists (regs !!! "R30"), "main", [], [].
  split!. { unfold imp_to_asm_args. split!. apply lookup_lookup_total.
            apply: (map_list_included_is_Some tmp_registers); [done|]. compute_done. }
  { admit. }
  go_i => ?. go.
  go_i => ?. go.
  go_i => ?. go.
  go_i => ?. go. simplify_eq.
  go_i. split!. go.
  go_i. split!. go.
  go_i => ?. go.
  go_i.
  go_i. move => *. destruct_all?; simplify_map_eq.
  rewrite bool_decide_false; [|compute_done]. rewrite bool_decide_true; [|compute_done].
  go_i => ?. go.
  go_i => ?. go.
  go_i => ?. go.
  go_i => ?. go. simplify_eq.
  go_i. split!. go.
  go_i. split!. { admit. } go.
  go_i => ?. go.
  go_i => ?. go.
  go_i => ?. go.
  go_i => ?. go.
  go_i => *. destruct_all?; simplify_eq. go.
  go_s. eexists _. go.
  go_s. split; [shelve|]. go.
  go_s. split; [shelve|]. go.
  go_s. split; [shelve|]. go.
  go_s. split!. go.
  go_i => *. case_match; destruct_all?; simplify_eq.
  go_s. eexists _. go.
  go_s. split!. go.
  go_i => *. go.
  go_i => *. go.
  go_i => *. done.
  Unshelve.
  - admit.
  - admit.
  - done.
  - iSatStart. iIntros!. iDestruct (big_sepL2_cons_inv_l with "[$]") as (????) "?". iSatStop. simplify_eq.
    revert select (imp_to_asm_args _ _ _) => -[?[??]]. decompose_Forall_hyps. simplify_map_eq'. by f_equal.
  - done.
Admitted.
