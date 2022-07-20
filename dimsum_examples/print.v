From dimsum.core Require Export proof_techniques.
From dimsum.core Require Import itree.
From dimsum.examples Require Import asm.

Local Open Scope Z_scope.

(** * Library for calling the PRINT syscall *)

Definition __NR_PRINT : Z := 8.
Definition print_addr : Z := 500.

Definition print_args (z : Z) (args : list Z) : Prop :=
  length args = length syscall_arg_regs ∧
  args !! 0%nat = Some z ∧
  args !! 8%nat = Some __NR_PRINT.

Definition print_asm : gmap Z asm_instr :=
  deep_to_asm_instrs print_addr [
      Amov "R8" __NR_PRINT;
      ASyscall;
      Aret
    ].

Definition print_itree : itree (moduleE asm_event unit) unit :=
  ITree.forever (
    '(rs, mem) ← TReceive (λ '(rs, mem), (Incoming, EAJump rs mem));;;
    TAssume (rs !!! "PC" = print_addr);;;;
    TAssume (print_asm !! (rs !!! "R30") = None);;;;
    args ← TExist _;;;
    TAssert (print_args (rs !!! "R0") args);;;;
    TVis (Outgoing, EASyscallCall args mem);;;;
    '(ret, mem) ← TReceive (λ '(ret, mem), (Incoming, EASyscallRet ret mem));;;
    TVis (Outgoing, EAJump (<["PC" := rs !!! "R30"]> $
                            <["R0" := ret]> $
                            <["R8" := __NR_PRINT]> $
                            rs) mem)).

Local Ltac go :=
  clear_itree.
Local Ltac go_s :=
  tstep_s; go.
Local Ltac go_i :=
  tstep_i; go.

Lemma print_asm_refines_itree :
  trefines (MS asm_module (initial_asm_state print_asm))
           (MS (mod_itree _ _) (print_itree, tt)).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember. { simpl. exact (λ _ σa '(t, _),
    t ≈ print_itree ∧
    σa.(asm_cur_instr) = AWaiting ∧
    σa.(asm_instrs) = print_asm). }
  { split!. } { done. }
  move => n _ Hloop [????] [??] ?. destruct!/=.
  tstep_i => ????? Hi. tstep_s. rewrite -/print_itree. go.
  go_s. eexists (_, _). go.
  go_s. split!. go.
  go_s => ?. go.
  go_s => ?. go.
  tstep_i => ??. simplify_map_eq'.
  tstep_i.
  tstep_i.
  tstep_i => ??. simplify_map_eq'.
  tstep_i.
  go_s. eexists _. go.
  go_s. split; [shelve|]. go.
  go_s. split!. go.
  tstep_i => ? ?.
  go_s. eexists (_, _). go.
  go_s. split!. go.
  tstep_i.
  tstep_i => ??. simplify_map_eq'.
  tstep_i. simplify_map_eq'.
  tstep_i => ??. simplify_map_eq'.
  go_s. sort_map_insert. simplify_map_eq'. split!. go.
  by apply: Hloop.
  Unshelve.
  - split; [done|by simplify_map_eq'].
Qed.
