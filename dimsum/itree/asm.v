From dimsum.core.itree Require Export upstream events.
From dimsum.core Require Import universes module axioms itree_mod.
From dimsum.examples Require Import asm.

Local Open Scope Z_scope.

(** ** Operational semantics *)
Definition set_asm_run_state {E} `{!stateE asm_state -< E} (i : asm_run_state) : itree E unit :=
  (σ ← get_state; set_state (AsmState i σ.(asm_regs) σ.(asm_mem) σ.(asm_instrs)))%itree.
Definition set_asm_regs {E} `{!stateE asm_state -< E} (rs : gmap string Z) : itree E unit :=
  (σ ← get_state; set_state (AsmState σ.(asm_cur_instr) rs σ.(asm_mem) σ.(asm_instrs)))%itree.
Definition set_asm_mem {E} `{!stateE asm_state -< E} (mem : gmap Z (option Z)) : itree E unit :=
  (σ ← get_state; set_state (AsmState σ.(asm_cur_instr) σ.(asm_regs) mem σ.(asm_instrs)))%itree.

Definition asm_itree : itree (moduleE asm_event asm_state) void :=
  ITree.forever (
  s ← get_state;
  match s.(asm_cur_instr) with
  | ARunning (WriteReg r f :: es) =>
      set_asm_regs (<[r := f s.(asm_regs)]> s.(asm_regs));;
      set_asm_run_state (ARunning es)
  | ARunning (ReadMem r1 r2 f :: es) =>
      v ← (s.(asm_mem) !! f (s.(asm_regs) !!! r2))?;
      v' ← v!;
      set_asm_regs (<[r1 := v']> s.(asm_regs));;
      set_asm_run_state (ARunning es)
  | ARunning (WriteMem r1 r2 f :: es) =>
      mv ← (s.(asm_mem) !! f (s.(asm_regs) !!! r2))?;
      mv!;;
      set_asm_mem (<[f (s.(asm_regs) !!! r2) := Some (s.(asm_regs) !!! r1)]> s.(asm_mem));;
      set_asm_run_state (ARunning es)
  | ARunning (Syscall :: es) =>
      visible (Outgoing, EASyscallCall (extract_syscall_args s.(asm_regs)) s.(asm_mem));;
      ret ← demonic _; mem' ← demonic _;
      visible (Incoming, EASyscallRet ret mem');;
      set_asm_regs (<["R0" := ret]> s.(asm_regs));;
      set_asm_mem mem';;
      set_asm_run_state (ARunning es)
  | ARunning [] =>
      let pc := s.(asm_regs) !!! "PC" in
      if s.(asm_instrs) !! pc is Some es then
        set_asm_run_state (ARunning es)
      else
        visible (Outgoing, EAJump s.(asm_regs) s.(asm_mem));;
        set_asm_run_state AWaiting
  | AWaiting =>
      regs' ← demonic _;
      mem' ← demonic _;
      let pc := regs' !!! "PC" in
      (s.(asm_instrs) !! pc)!;;
      visible (Incoming, EAJump regs' mem');;
      set_asm_regs regs';; set_asm_mem mem';;
      set_asm_run_state (ARunning [])
  | AHalted => NB
  | _ => UB
  end)%itree.

Local Ltac go :=
  clear_itree; repeat itree_step.
Local Ltac go_s :=
  tstep_s; go.
Local Ltac go_i :=
  tstep_i; go.

Lemma asm_itree_refines_asm ins :
  trefines (itree_mod asm_itree (asm_init ins)) (asm_mod ins).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember. { simpl. exact (λ n '(t, AsmState i1 rs1 mem1 ins1) '(AsmState i2 rs2 mem2 ins2),
    t ⊒ ↓ᵢ asm_itree ∧ i1 = i2 ∧ rs1 = rs2 ∧ mem1 = mem2 ∧ ins1 = ins2 ∧ ins1 = ins ∧
    match i1 with | AWaitingSyscall _ => False | _ => True end). }
  { split!. } { done. }
  move => n /= ? Hloop [?[????]] [i ???] ?. destruct!/=.
  tstep_i. rewrite -/asm_itree. go. go_i.
  destruct i as [[|[] ?]| | |] => //.
  - case_match.
    + go_i. go_i. go_i. go_s. split!. simplify_option_eq. apply Hloop; [done|]. split!.
    + go_i. go_s. split!. simplify_option_eq. split!. go_i. go_i. go_i. apply Hloop; [done|]. split!.
  - go_i. go_i. go_i. go_i. go_i. go_s. apply Hloop; [done|]. split!.
  - go_s => ??. go_i. split!. go. go_i => ??. go. simplify_eq/=.
    go_i. go_i. go_i. go_i. go_i. apply Hloop; [done|]. split!.
  - go_s => ??. go_i. split!. go. go_i => ??. go. simplify_eq/=.
    go_i. go_i. go_i. go_i. go_i. apply Hloop; [done|]. split!.
  - go_i. go_s. split!. go_i => ?. go. go_i => ?. go. go_i. go_s. split!.
    go_i. go_i. go_i. go_i. go_i. go_i. go_i. apply Hloop; [done|]. split!.
  - go_i => ?. go. go_i => ?. go. go_i => ??. go. go_i.
    go_s. split!. go_i. go_i. go_i. go_i. go_i. go_i. go_i. apply Hloop; [done|]. split!.
  - by go_i.
Qed.

Lemma asm_refines_asm_itree ins :
  trefines (asm_mod ins) (itree_mod asm_itree (asm_init ins)).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember. { simpl. exact (λ n '(AsmState i2 rs2 mem2 ins2) '(t, AsmState i1 rs1 mem1 ins1),
    t ⊒ ↓ᵢ asm_itree ∧ i1 = i2 ∧ rs1 = rs2 ∧ mem1 = mem2 ∧ ins1 = ins2 ∧ ins1 = ins ∧
    match i1 with | AWaitingSyscall _ => False | _ => True end). }
  { split!. } { done. }
  move => n /= ? Hloop [i ???] [?[????]] ?. destruct!/=.
  tstep_s. rewrite -/asm_itree. go. go_s.
  destruct i as [[|[] ?]| | |] => //.
  - go_i => ??. simplify_eq. case_match.
    + go_s. go_s. go_s. apply Hloop; [done|]. split!.
    + go_s. split!. go. go_s. go_s. go_s. apply Hloop; [done|]. split!.
  - go_i. go_s. go_s. go_s. go_s. go_s. apply Hloop; [done|]. split!.
  - go_s => ??. go. go_i. split!. case_match; [|by go_i].
    go_s. split!. go. go_s. go_s. go_s. go_s. go_s. apply Hloop; [done|]. split!.
  - go_s => ??. go. go_i. split!. case_match; [|by go_i].
    go_s. split!. go. go_s. go_s. go_s. go_s. go_s. apply Hloop; [done|]. split!.
  - go_i. go_s. split!. go. go_i => ??. go_s. split!. go. go_s. split!. go.
    go_s. split!. go. go_s. go_s. go_s. go_s. go_s. go_s. go_s. apply Hloop; [done|]. split!.
  - go_i => *. simplify_eq. go_s. split!. go. go_s. split!. go. go_s. split!; [done|]. go.
    go_s. split!. go. go_s. go_s. go_s. go_s. go_s. go_s. go_s. apply Hloop; [done|]. split!.
  - by go_i.
Qed.
