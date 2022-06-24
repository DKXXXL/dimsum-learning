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
Require Import refframe.compiler.compiler.

Local Open Scope Z_scope.

Definition int_to_ptr_asm : gmap Z asm_instr :=
  (* cast_int_to_ptr *)
  <[ 400 := [
        (* ret *)
        WriteReg "PC" (λ rs, rs !!! "R30")
    ] ]> $
  (* cast_ptr_to_int *)
  <[ 401 := [
        (* ret *)
        WriteReg "PC" (λ rs, rs !!! "R30")
    ] ]> $ ∅.

Definition int_to_ptr_fns : gset string :=
  {["cast_int_to_ptr"; "cast_ptr_to_int" ]}.

Definition int_to_ptr_f2i : gmap string Z :=
  <["cast_int_to_ptr" := 400]> $ <["cast_ptr_to_int" := 401]> $ ∅.

Definition int_to_ptr_itree : itree (moduleE imp_event (gmap prov Z)) unit :=
  ITree.forever (
      '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, EICall f vs h));;;
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

(*

 100 <- cast_ptr_to_int(l);
 200 <- cast_ptr_to_int(p);

  (* b = nondet(); // works *)
  x = cast_int_to_ptr(300); // l + 200 | p + 100

  (* b = nondet(); // does not work *)

  assert(x == l);
  assert(x == p); // UB here (and in in PNVI)

  if(b) {
    assert(x == l);
  } else {
    assert(x == p);
  }

 *)

Local Ltac go :=
  clear_itree.
Local Ltac go_s :=
  tstep_s; go.
Local Ltac go_i :=
  tstep_i; go.

(*
  asm_module(int_to_ptr_asm) {asm_event}
    <= {asm_event}
  imp_to_asm(itree_module(int_to_ptr_itree {imp_event}) {imp_event}) {asm_event}
*)

Lemma int_to_ptr_asm_refines_itree :
  trefines (MS asm_module (initial_asm_state int_to_ptr_asm))
           (MS (imp_to_asm (dom _ int_to_ptr_asm) int_to_ptr_fns int_to_ptr_f2i
                           (mod_itree imp_event (gmap prov Z)))
               (initial_imp_to_asm_state ∅ (mod_itree _ _) (int_to_ptr_itree, ∅))).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember. { simpl. exact (λ _ σa '(σf, (t, ps), (pp, σi2a, P)),
    t ≈ int_to_ptr_itree ∧
    σa.(asm_cur_instr) = AWaiting ∧
    σa.(asm_instrs) = int_to_ptr_asm ∧
    σi2a.(i2a_calls) = [] ∧
    σf = SMFilter ∧
    pp = PPOutside ∧
    (P ⊢ [∗ map] p↦z∈ps, i2a_heap_shared p z)). }
  { split!. iIntros!. by rewrite big_sepM_empty. } { done. }
  move => n _ Hloop [????] [[?[? ps]][[??]?]] ?. destruct_all?; simplify_eq/=.
  tstep_i => ????? Hi. tstep_s. split!.
  tstep_i => ??. simplify_map_eq.
  tstep_s => *. case_match => /= *. 2: congruence.
  tstep_s. rewrite -/int_to_ptr_itree. go. go_s. eexists (_, _, _). go.
  go_s. split!. go. go_s.
  revert select (_ ⊢ _) => HP. unfold i2a_regs_call in *.
  revert select (_ ∉ dom _ _) => /not_elem_of_dom?.
  unfold int_to_ptr_asm in Hi. unfold int_to_ptr_f2i in *. (repeat case_bool_decide); simplify_map_eq'.
  - tstep_i.
    go_s => ?. go.
    go_s => ?. go.
    go_s => ?. go.
    go_s. go_s => ?. go.
    iSatStart. iIntros!.
    iDestruct (i2a_args_intro with "[$]") as "?"; [done|].
    rewrite i2a_args_cons ?i2a_args_nil; [|done]. iDestruct!.
    iDestruct (HP with "[$]") as "HP".
    iDestruct (big_sepM_lookup with "HP") as "#?"; [done|].
    iSatStop.
    tstep_i => ??. simplify_map_eq'.
    go_s. go_s. split!.
    { by simplify_map_eq'. }
    { instantiate (1:=[_]). unfold i2a_regs_ret; split!; simplify_map_eq'; split!.
      - apply map_preserved_insert_r_not_in; [|done]. compute_done.
    }
    { apply map_scramble_insert_r_in; [compute_done|done]. }
    { iSatMono. simplify_map_eq'. iIntros!. iFrame. iSplitL; [iAccu|]. iSplit!; [|done]. lia. }
    apply Hloop; [done|].
    split!.
  - tstep_i.
    go_s => l. go.
    go_s => ?. go.
    iSatStart. iIntros!.
    iDestruct (i2a_args_intro with "[$]") as "?"; [done|].
    rewrite i2a_args_cons ?i2a_args_nil; [|done]. iDestruct!.
    iDestruct (HP with "[$]") as "HP".
    iAssert ⌜z = default z (ps !! l.1)⌝%I as %Hz.
    { destruct (ps !! l.1) as [z'|] eqn:Hp => //=.
      iDestruct (big_sepM_lookup with "HP") as "?"; [done|].
      iAssert ⌜z' = z⌝%I as %?; [|done].
      by iApply (i2a_heap_shared_ag with "[$]"). }
    iSatStop.
    go_s. eexists z. go.
    go_s. go_s. go_s.
    tstep_i => ??. simplify_map_eq'.
    go_s. split!.
    { by simplify_map_eq'. }
    { instantiate (1:=[_]). unfold i2a_regs_ret; split!; simplify_map_eq'; split!.
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

(*
void main () {
  size_t *l = alloc(1);
  *l = 1;
  size_t z = cast_ptr_to_int(l);
  size_t z' = z - 1 + 1;
  size_t *l' = cast_int_to_ptr(z');
  size_t r = *l';
  free(l);
  exit(r);
}

*)

Definition main_imp : fndef := {|
  fd_args := [];
  fd_vars := [("l", 1)];
  fd_body := LetE "_" (Store (Var "l") (Val 1)) $
             LetE "z" (imp.Call "cast_ptr_to_int" [(Var "l")]) $
             LetE "z'" (BinOp (BinOp (Var "z") AddOp (Val (-1))) AddOp (Val 1)) $
             LetE "l'" (imp.Call "cast_int_to_ptr" [(Var "z")]) $
             LetE "r" (Load (Var "l'")) $
             imp.Call "exit" [(Var "r")];
  fd_static := I
|}.

Definition main_imp_prog : gmap string fndef :=
  <[ "main" := main_imp ]> ∅.

Definition main_itree : itree (moduleE imp_event unit) unit :=
  '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, EICall f vs h));;;
  TAssume (f = "main");;;;
  TAssume (vs = []);;;;
  h' ← TExist (heap_state);;;
  TVis (Outgoing, EICall "exit" [ValNum 1] h');;;;
  TUb.

(*
  imp_module(main_imp) {imp_event} +imp itree_module(int_to_ptr_itree {imp_event}) {imp_event}
      <= {imp_event}
  itree_module(main_itree {imp_event}) {imp_event}
*)

Lemma main_int_to_ptr_refines_itree :
  trefines (MS (imp_prod (dom _ main_imp_prog) int_to_ptr_fns
                         imp_module (mod_itree _ _))
               (MLFNone, [], initial_imp_state main_imp_prog, (int_to_ptr_itree, ∅)))
           (MS (mod_itree _ _) (main_itree, tt)).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  tstep_i => *. case_match; destruct_all?; simplify_eq.
  go_s. eexists (_, _, _). go. go_s. split!. go.
  go_s => ?. go. go_s => ?. go. simplify_eq. rewrite bool_decide_true; [|compute_done].
  tstep_i. split! => ???? Hf ?. simplify_eq.
  change (@nil expr) with (Val <$> []).
  tstep_i. split!. move => ??. simplify_eq. unfold main_imp_prog in Hf. simplify_map_eq. split!.
  tstep_i => ???. destruct_all?; simplify_eq. split!. { repeat econs. }
  tstep_i. split. { apply heap_alive_alloc; [done|lia]. }
  tstep_i. change ([Val (ValLoc l)]) with (Val <$> [ValLoc l]).
  tstep_i. split. { move => *; simplify_map_eq. }
  move => ????. rewrite bool_decide_false; [|compute_done]. rewrite bool_decide_true; [|compute_done].
  move => *. destruct_all?. simplify_eq/=.
  tstep_i. rewrite -/int_to_ptr_itree. go.
  go_i => -[[??]?]. go.
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
  go_i => -[[??]?]. go.
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
  go_i. change ([Val 1]) with (Val <$> [ValNum 1]).
  go_i. split. { move => *; simplify_map_eq. }
  move => ????. rewrite bool_decide_false; [|compute_done].
  move => *. destruct_all?. simplify_eq/=.
  go_s. eexists _. go.
  go_s. split!. go.
  go_s. done.
Qed.

Definition main_f2i : gmap string Z := <["main" := 200]> $ <["exit" := 100]> int_to_ptr_f2i .

Definition main_asm : gmap Z asm_instr :=
  deep_to_asm_instrs 200 ltac:(i2a_compile main_f2i main_imp).

(* We need to lock this, otherwise simpl goes crazy. *)
Definition main_asm_dom : gset Z := locked (dom _) main_asm.

(*
  asm_module(main_asm) {asm_event}
    <= {asm_event}
  imp_to_asm(imp_module(main_imp) {imp_event}) {asm_event}
*)

Lemma main_asm_refines_imp :
  trefines (MS asm_module (initial_asm_state main_asm))
           (MS (imp_to_asm (dom _ main_asm) {["main"]} main_f2i imp_module)
               (initial_imp_to_asm_state ∅ imp_module (initial_imp_state main_imp_prog))).
Proof. apply: compile_correct; [|done|..]; compute_done. Qed.

(* https://thog.github.io/syscalls-table-aarch64/latest.html *)
Definition __NR_EXIT : Z := 93.

Definition exit_asm : gmap Z asm_instr :=
  (* exit *)
  <[ 100 := [
        WriteReg "R8" (λ rs, __NR_EXIT);
        WriteReg "PC" (λ rs, rs !!! "PC" + 1)
    ] ]> $
  <[ 101 := [
        Syscall;
        WriteReg "PC" (λ rs, rs !!! "PC" + 1)
    ] ]> $
  <[ 102 := [
        (* loop *)
        WriteReg "PC" (λ rs, rs !!! "PC")
    ] ]> $ ∅.

Definition exit_itree : itree (moduleE asm_event unit) unit :=
  '(rs, mem) ← TReceive (λ '(rs, mem), (Incoming, EAJump rs mem));;;
  TAssume (rs !!! "PC" = 100);;;;
  args ← TExist _;;;
  TAssert (length args = length syscall_arg_regs);;;;
  TAssert (args !! 0%nat = Some (rs !!! "R0"));;;;
  TAssert (args !! 8%nat = Some __NR_EXIT);;;;
  TVis (Outgoing, EASyscallCall args);;;;
  (* TUb. *)
  TReceive (λ ret, (Incoming, EASyscallRet ret));;;;
  TNb.

(*
  asm_module(exit_asm) {asm_event}
    <= {asm_event}
  itree_module(exit_itree {asm_event}) {asm_event}
*)

Lemma exit_asm_refines_itree :
  trefines (MS asm_module (initial_asm_state exit_asm))
           (MS (mod_itree _ _) (exit_itree, tt)).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  go_i => ????? Hi.
  go_s. eexists (_, _). go.
  go_s. split!. go.
  go_i => ??. simplify_map_eq.
  go_s => ?. go.
  unfold exit_asm in Hi. simplify_map_eq'.
  go_i.
  go_i.
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
  go_i.
  sort_map_insert. simplify_map_eq'.
  unshelve eapply tsim_remember. { exact (λ _ '(AsmState i rs _ ins) _,
      i = ARunning [] ∧ rs !!! "PC" = 102 ∧ ins = exit_asm). }
  { split!. by simplify_map_eq'. } { done. }
  move => ?? Hloop [????] ? ?. destruct_all?; simplify_eq.
  go_i => ??. simplify_map_eq'.
  go_i.
  apply Hloop; [done|]. split!. by simplify_map_eq'.
  Unshelve.
  - done.
  - by simplify_map_eq'.
  - by simplify_map_eq'.
Qed.

(* TODO: something even more high-level? Maybe stated as safety property on traces? *)

Definition top_level_itree : itree (moduleE asm_event unit) unit :=
  '(rs, mem) ← TReceive (λ '(rs, mem), (Incoming, EAJump rs mem));;;
  TAssume (rs !!! "PC" = 200);;;;
  TAssume (rs !!! "R30" ∉ main_asm_dom ∪ dom (gset Z) int_to_ptr_asm);;;;
  TAssume (∃ gp, gp + GUARD_PAGE_SIZE ≤ rs !!! "SP" ∧
            (∀ a, gp ≤ a < gp + GUARD_PAGE_SIZE → mem !! a = Some None) ∧
            (∀ a, gp + GUARD_PAGE_SIZE ≤ a < rs !!! "SP" → ∃ v, mem !! a = Some (Some v)));;;;
  args ← TExist _;;;
  TAssert (length args = length syscall_arg_regs);;;;
  TAssert (args !! 0%nat = Some 1);;;;
  TAssert (args !! 8%nat = Some __NR_EXIT);;;;
  TVis (Outgoing, EASyscallCall args);;;;
  TReceive (λ ret, (Incoming, EASyscallRet ret));;;;
  TNb.

(*
   imp_to_asm(itree_module(main_itree {imp_event}) {imp_event}) {asm_event}
    +asm
   itree_module(exit_itree {asm_event}) {asm_event}
      <= {asm_event}
   itree_module(toplevel_itree {asm_event}) {asm_event}
*)

Lemma top_level_refines_itree :
  trefines (MS (asm_prod (main_asm_dom ∪ dom _ int_to_ptr_asm) (dom _ exit_asm)
                         (imp_to_asm (main_asm_dom ∪ dom _ int_to_ptr_asm)
                                     (dom _ main_imp_prog ∪ int_to_ptr_fns)
                                     main_f2i
                                     (mod_itree _ _)) (mod_itree _ _))
               (MLFNone, None, initial_imp_to_asm_state ∅ (mod_itree _ _) (main_itree, tt), (exit_itree, tt)))
           (MS (mod_itree _ _) (top_level_itree, tt)).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  go_i => ??????. case_match; destruct_all?; simplify_eq.
  go_s. eexists (_, _). go.
  go_s. split!. go.
  go_s => ?. go.
  go_s => ?. go.
  go_s => ?. go. destruct_all?. simplify_map_eq'.
  rewrite bool_decide_true; [|unfold main_asm_dom;unlock; compute_done].
  go_i => ??. simplify_eq.
  go_i. eexists true => /=. split; [done|]. eexists initial_heap_state, _, [], [], (regs !!! "R30"), "main".
  split!.
  { by simplify_map_eq'. }
  { apply: satisfiable_mono; [by eapply i2a_res_init|].
    iIntros!.
    iDestruct (i2a_mem_inv_init with "[$] [$]") as "$"; [done..|].
    iFrame. rewrite /i2a_mem_map big_sepM_empty. iSplit; [done|]. iAccu. }
  go_i => -[[??]?]. go.
  go_i => ?. go. simplify_eq.
  go_i. split!. go.
  go_i. split!. go.
  go_i => ?. go.
  go_i.
  go_i. move => *. unfold main_f2i in *. destruct_all?; simplify_map_eq'.
  rewrite bool_decide_false; [|unfold main_asm_dom;unlock;compute_done].
  rewrite bool_decide_true; [|compute_done].
  go_i => -[??]. go.
  go_i => ?. go. simplify_eq.
  go_i. split!. go.
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
  - done.
  - iSatStart. iIntros!. iDestruct (i2a_args_intro with "[$]") as "?"; [done|].
    rewrite i2a_args_cons; [|done]. iDestruct!. iSatStop. by simplify_map_eq'.
  - done.
Qed.

(*
  asm_module(main_asm ∪ int_to_ptr_asm ∪ exit_asm) {asm_event}
    <= {asm_event}
  itree_module(toplevel_itree {asm_event}) {asm_event}
*)

Lemma complete_refinement :
  trefines (MS asm_module (initial_asm_state (main_asm ∪ int_to_ptr_asm ∪ exit_asm)))
           (MS (mod_itree _ _) (top_level_itree, tt)).
Proof.
  etrans. {
    apply asm_link_refines_prod. compute_done.
  }
  etrans. {
    apply: asm_prod_trefines.
    - etrans. {
        apply asm_link_refines_prod. compute_done.
      }
      etrans. {
        apply: asm_prod_trefines.
        - apply main_asm_refines_imp.
        - apply int_to_ptr_asm_refines_itree.
      }
      etrans. {
        apply: imp_to_asm_combine; compute_done.
      }
      etrans. {
        apply: imp_to_asm_trefines.
        apply main_int_to_ptr_refines_itree.
      }
      have -> : (main_f2i ∪ int_to_ptr_f2i) = main_f2i by compute_done.
      done.
    - apply exit_asm_refines_itree.
  }
  etrans. {
    etrans; [|apply: (top_level_refines_itree)].
    rewrite dom_union_L /main_asm_dom left_id_L. unlock. done.
  }
  done.
Qed.

(* Print Assumptions complete_refinement. *)

(* TODO: make asm_module a dem_module, have a dem_mod_itree (that
makes non-trivial angelic choice UB) and show that the trefines implies
dem_refines and then use this to prove trace properties about the
assembly code? This would remove trefines from the TCB *)
