Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.filter.
Require Import refframe.product.
Require Import refframe.seq_product.
Require Import refframe.proof_techniques.
Require Import refframe.imp.
Require Import refframe.asm.
Require Import refframe.itree.
Require Import refframe.imp_to_asm.

Local Open Scope Z_scope.

Definition asm_add : gmap Z asm_instr :=
  <[ 100 := [
        (* add R0, R0, R1 *)
        WriteReg "R0" (λ rs, rs !!! "R0" + rs !!! "R1");
        WriteReg "PC" (λ rs, rs !!! "PC" + 4)
    ] ]> $
  <[ 104 := [
        (* ret *)
        WriteReg "PC" (λ rs, rs !!! "R30")
    ] ]> $ ∅.

Definition imp_add : fndef := {|
  fd_args := ["a"; "b"];
  fd_body := (BinOp (Var "a") AddOp (Var "b"));
  fd_static := I
|}.

Definition imp_add_prog : gmap string fndef :=
  <[ "add" := imp_add ]> ∅.

Local Hint Constants Transparent : tstep.
Local Ltac go := clear_itree; destruct_all?; simplify_eq/=.
Local Ltac go_i := tstep_i; go.
Local Ltac go_s := tstep_s; go.

Lemma asm_add_refines_imp_add :
  trefines (MS asm_module (initial_asm_state asm_add))
           (MS (imp_to_asm imp_module) (initial_imp_to_asm_state imp_module (initial_imp_state imp_add_prog) {[ 100; 104 ]} {[ "add" ]} (<["add" := 100]> ∅))).
Proof.
  apply tsim_implies_trefines => /= n.

  rewrite /initial_asm_state/initial_imp_state/initial_imp_to_asm_state.

  tstep_i => ???? Hin. unfold asm_add in Hin.
  go_s. go_s. eexists _; go. go_s. eexists _; go. go_s. split; [done|]. go.
  go_s => b; go. destruct b. 2: { repeat (go_s; intros; go). }
  go_s => r; go. go_s => f; go. go_s => vs; go.
  go_s => ?; go. go_s => ?; go. go_s => ?; go. go_s => Hargs; go.
  go_s. go_s. go_s.
  have ?: f = "add" by set_solver. subst. simplify_map_eq.
  tstep_s. split!; [|done|]; simplify_map_eq; [done|]. case_bool_decide.
  2: { by tstep_s. }
  destruct vs as [|v1 [|v2 []]] => //=.
  move: Hargs => -[?[? /= Hregs]]. unfold saved_registers in *. decompose_Forall_hyps.
  tstep_i. split; [done|].
  tstep_i; simplify_map_eq'. split; [done|].
  tstep_i => ??. simplify_map_eq'.
  tstep_i; simplify_map_eq'. split!.
  tstep_i => ??; simplify_map_eq'.
  case_match. 1: { admit. }
  go_s => n1 n2 ??; subst.
  go_s. go_s. eexists _; go. go_s. eexists _; go. go_s. eexists false; go.
  go_s. eexists _; go. go_s. eexists _; go. go_s. eexists _; go.
  go_s. go_s. split; [done|]; go. go_s. go_s. split; [shelve|]; go. go_s. split; [done|]. go.
  go_s. split; [done|]. go.
  Unshelve.
  2: { unfold imp_to_asm_ret. unfold tmp_registers, saved_registers.
       split!; decompose_Forall; simplify_map_eq => //.
       all: try by apply lookup_lookup_total. }
Abort.
