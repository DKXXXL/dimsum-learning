Require Export dimsum.module.
Require Import dimsum.trefines.
Require Import dimsum.filter.
Require Import dimsum.product.
Require Import dimsum.seq_product.
Require Import dimsum.link.
Require Import dimsum.prepost.
Require Import dimsum.proof_techniques.

Local Open Scope Z_scope.

(** * Assembly language *)
(* see man 2 syscall (https://man7.org/linux/man-pages/man2/syscall.2.html),
  https://modexp.wordpress.com/2018/10/30/arm64-assembly/ or
  https://stackoverflow.com/questions/68711164/syscall-invoke-in-aarch64-assembly *)
Definition syscall_arg_regs : list string :=
  ["R0"; "R1"; "R2"; "R3"; "R4"; "R5"; "R6"; "R7"; "R8"].

Definition extract_syscall_args (rs : gmap string Z) : list Z :=
  (λ r, rs !!! r) <$> syscall_arg_regs.

Inductive asm_instr_elem :=
| WriteReg (r : string) (f : gmap string Z → Z)
(* ldr r1, [f r2] *)
| ReadMem (r1 r2 : string) (f : Z → Z)
(* str r1, [f r2] *)
| WriteMem (r1 r2 : string) (f : Z → Z)
| Syscall
.

Definition asm_instr := list asm_instr_elem.

Inductive asm_run_state : Set :=
| ARunning (i : asm_instr)
| AWaiting
| AWaitingSyscall (i : asm_instr)
(* TODO: Should we use the following? *)
| APagefaulting (a : Z)
| AHalted
.

Inductive asm_state := AsmState {
  asm_cur_instr : asm_run_state;
  asm_regs : gmap string Z;
  asm_mem : gmap Z (option Z);
  asm_instrs : gmap Z asm_instr;
}.
Add Printing Constructor asm_state.

Definition initial_asm_state (instrs : gmap Z asm_instr) := AsmState AWaiting ∅ ∅ instrs.

Inductive asm_ev :=
| EAJump (regs : gmap string Z) (mem : gmap Z (option Z))
| EASyscallCall (args : list Z) (mem : gmap Z (option Z))
| EASyscallRet (ret : Z) (mem : gmap Z (option Z))
| EAPagefault (a : Z)
.

Definition asm_event := io_event asm_ev.

Inductive asm_step : asm_state → option asm_event → (asm_state → Prop) → Prop :=
| SWriteReg regs instrs r f es mem:
  asm_step (AsmState (ARunning (WriteReg r f :: es)) regs mem instrs) None (λ σ',
         σ' = AsmState (ARunning es) (<[r := f regs]>regs) mem instrs)
| SReadMem regs instrs r1 r2 f es mem:
  asm_step (AsmState (ARunning (ReadMem r1 r2 f :: es)) regs mem instrs) None (λ σ', ∃ v,
         mem !! f (regs !!! r2) = Some v ∧
         σ' = if v is Some v' then
                AsmState (ARunning es) (<[r1 := v']>regs) mem instrs
              else
                (* TODO: Should this be (APagefaulting (f a)) ? *)
                AsmState AHalted regs mem instrs)
| SWriteMem regs instrs r1 r2 f es mem:
  asm_step (AsmState (ARunning (WriteMem r1 r2 f :: es)) regs mem instrs) None (λ σ', ∃ mv,
         mem !! f (regs !!! r2) = Some mv ∧
         (* TODO: Should we have the following constraint? *)
         (* is_Some (mem !! f a) ∧ *)
         σ' = if mv is Some mv' then
                AsmState (ARunning es) regs (<[f (regs !!! r2) := Some (regs !!! r1)]>mem) instrs
              else
                (* TODO: Should this be (APagefaulting (f a)) ? *)
                AsmState AHalted regs mem instrs)
| SSyscallCall regs instrs es mem:
  asm_step (AsmState (ARunning (Syscall :: es)) regs mem instrs)
           (Some (Outgoing, EASyscallCall (extract_syscall_args regs) mem))
           (λ σ', σ' = AsmState (AWaitingSyscall es) regs mem instrs)
| SSyscallRet regs instrs es mem mem' ret:
  asm_step (AsmState (AWaitingSyscall es) regs mem instrs)
           (Some (Incoming, EASyscallRet ret mem'))
           (λ σ', σ' = AsmState (ARunning es) (<["R0" := ret]>regs) mem' instrs)
| SJumpInternal regs instrs pc es mem:
  regs !!! "PC" = pc →
  instrs !! pc = Some es →
  asm_step (AsmState (ARunning []) regs mem instrs) None
           (λ σ', σ' = AsmState (ARunning es) regs mem instrs)
| SJumpExternal regs instrs pc mem:
  regs !!! "PC" = pc →
  instrs !! pc = None →
  asm_step (AsmState (ARunning []) regs mem instrs) (Some (Outgoing, EAJump regs mem))
           (λ σ', σ' = AsmState AWaiting regs mem instrs)
| SRecvJump regs regs' instrs pc es mem mem':
  regs' !!! "PC" = pc →
  instrs !! pc = Some es →
  asm_step (AsmState AWaiting regs mem instrs)
           (Some (Incoming, EAJump regs' mem'))
           (* We use [] here such that each instruction starts from [] *)
           (λ σ', σ' = AsmState (ARunning []) regs' mem' instrs)
| SPagefaulting regs instrs a mem:
  asm_step (AsmState (APagefaulting a) regs mem instrs)
           (Some (Outgoing, EAPagefault a))
           (λ σ', σ' = AsmState AHalted regs mem instrs)
.

Definition asm_module := Mod asm_step.

Global Instance asm_vis_no_all: VisNoAll asm_module.
Proof. move => *. inv_all @m_step; naive_solver. Qed.

(** * tstep *)
Lemma asm_step_WriteReg_i r f es rs ins mem:
  TStepI asm_module (AsmState (ARunning (WriteReg r f::es)) rs mem ins)
            (λ G, G true None (λ G', G' (AsmState (ARunning es) (<[r:=f rs]>rs) mem ins))).
Proof.
  constructor => ? ?. apply steps_impl_step_end => ???.
  inv_all @m_step. eexists _, _. split_and!; [done|done|].
  move => ? /=. naive_solver.
Qed.
Global Hint Resolve asm_step_WriteReg_i : tstep.

Lemma asm_step_WriteReg_s r f es rs ins mem:
  TStepS asm_module (AsmState (ARunning (WriteReg r f::es)) rs mem ins)
            (λ G, G None (λ G', G' (AsmState (ARunning es) (<[r:=f rs]>rs) mem ins))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= ?.
  apply: steps_spec_step_end. { econs. }
  move => ? /= ?. naive_solver.
Qed.
Global Hint Resolve asm_step_WriteReg_s : tstep.

Lemma asm_step_ReadMem_i r1 r2 f es rs ins mem:
  TStepI asm_module (AsmState (ARunning (ReadMem r1 r2 f::es)) rs mem ins)
            (λ G, G true None (λ G',
             ∃ mv, mem !! f (rs !!! r2) = Some mv ∧
                      G' (if mv is Some v then
                            AsmState (ARunning es) (<[r1:= v]>rs) mem ins
                          else
                            AsmState AHalted rs mem ins))).
Proof.
  constructor => ? ?.
  apply steps_impl_step_end => ???.
  inv_all @m_step. eexists _, _. split_and!; [done|done|].
  move => ? /=. naive_solver.
Qed.
Global Hint Resolve asm_step_ReadMem_i : tstep.

Lemma asm_step_ReadMem_s r1 r2 f es rs ins mem:
  TStepS asm_module (AsmState (ARunning (ReadMem r1 r2 f::es)) rs mem ins)
            (λ G, G None (λ G', ∀ mv, mem !! f (rs !!! r2) = Some mv →
      G' (if mv is Some v then
            AsmState (ARunning (es)) (<[r1:=v]>rs) mem ins
          else
            AsmState AHalted rs mem ins))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= ?.
  apply: steps_spec_step_end. { econs. }
  move => ? /= ?. naive_solver.
Qed.
Global Hint Resolve asm_step_ReadMem_s : tstep.

Lemma asm_step_WriteMem_i r1 r2 f es rs ins mem:
  TStepI asm_module (AsmState (ARunning (WriteMem r1 r2 f::es)) rs mem ins)
            (λ G, G true None (λ G',
             ∃ mv, mem !! f (rs !!! r2) = Some mv ∧
                      G' (if mv is Some mv' then
                            AsmState (ARunning es) rs (<[f (rs !!! r2):=Some (rs !!! r1)]>mem) ins
                          else
                            AsmState AHalted rs mem ins))).
Proof.
  constructor => ? ?. apply steps_impl_step_end => ???.
  inv_all @m_step. eexists _, _. split_and!; [done|done|].
  move => ? /=. naive_solver.
Qed.
Global Hint Resolve asm_step_WriteMem_i : tstep.

Lemma asm_step_WriteMem_s r1 r2 f es rs ins mem:
  TStepS asm_module (AsmState (ARunning (WriteMem r1 r2 f::es)) rs mem ins)
            (λ G, G None (λ G', ∀ mv, mem !! f (rs !!! r2) = Some mv →
                      G' (if mv is Some mv' then
                            AsmState (ARunning es) rs (<[f (rs !!! r2):=Some (rs !!! r1)]>mem) ins
                          else
                            AsmState AHalted rs mem ins))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= ?.
  apply: steps_spec_step_end. { econs. }
  move => ? /= ?. naive_solver.
Qed.
Global Hint Resolve asm_step_WriteMem_s : tstep.

Lemma asm_step_Syscall_call_i es rs ins mem:
  TStepI asm_module (AsmState (ARunning (Syscall::es)) rs mem ins)
            (λ G, G true (Some (Outgoing, EASyscallCall (extract_syscall_args rs) mem))
                    (λ G', G' (AsmState (AWaitingSyscall es) rs mem ins))).
Proof.
  constructor => ? ?. apply steps_impl_step_end => ???.
  inv_all @m_step. eexists _, _. split_and!; [done|done|].
  move => ? /=. naive_solver.
Qed.
Global Hint Resolve asm_step_Syscall_call_i : tstep.

Lemma asm_step_Syscall_call_s es rs ins mem:
  TStepS asm_module (AsmState (ARunning (Syscall :: es)) rs mem ins)
            (λ G, G (Some (Outgoing, EASyscallCall (extract_syscall_args rs) mem))
                    (λ G', G' (AsmState (AWaitingSyscall es) rs mem ins))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= ?.
  apply: steps_spec_step_end. { econs. } naive_solver.
Qed.
Global Hint Resolve asm_step_Syscall_call_s : tstep.

Lemma asm_step_Syscall_ret_i es rs ins mem:
  TStepI asm_module (AsmState (AWaitingSyscall es) rs mem ins)
            (λ G, ∀ ret mem', G true (Some (Incoming, EASyscallRet ret mem'))
                    (λ G', G' (AsmState (ARunning es) (<["R0" := ret]> rs) mem' ins))).
Proof.
  constructor => ? ?. apply steps_impl_step_end => ???.
  inv_all @m_step. eexists _, _. split_and!; [naive_solver|done|].
  move => ? /=. naive_solver.
Qed.
Global Hint Resolve asm_step_Syscall_ret_i : tstep.

Lemma asm_step_Syscall_ret_s es rs ins mem:
  TStepS asm_module (AsmState (AWaitingSyscall es) rs mem ins)
            (λ G, ∃ ret mem', G (Some (Incoming, EASyscallRet ret mem'))
                    (λ G', G' (AsmState (ARunning es) (<["R0":=ret]> rs) mem' ins))).
Proof.
  constructor => ? [?[??]]. eexists _, _. split; [done|] => ? /= ?.
  apply: steps_spec_step_end. { econs. } naive_solver.
Qed.
Global Hint Resolve asm_step_Syscall_ret_s : tstep.

Lemma asm_step_Jump_i rs ins mem:
  TStepI asm_module (AsmState (ARunning []) rs mem ins) (λ G,
    ∀ pc, rs !!! "PC" = pc →
          if ins !! pc is Some i then
            G true None (λ G', G' (AsmState (ARunning i) rs mem ins))
          else
            G true (Some (Outgoing, EAJump rs mem)) (λ G', G' (AsmState AWaiting rs mem ins))
   ).
Proof.
  constructor => ? HG. apply steps_impl_step_end => ???.
  inv_all/= @m_step; specialize_hyps; simplify_option_eq.
  all: eexists _, _; split_and!; [done..|]; naive_solver.
Qed.
Global Hint Resolve asm_step_Jump_i : tstep.

Lemma asm_step_Jump_s rs ins mem:
  TStepS asm_module (AsmState (ARunning []) rs mem ins) (λ G,
    ∃ pc, rs !!! "PC" = pc ∧
      if ins !! pc is Some i then
        G None (λ G', G' (AsmState (ARunning i) rs mem ins))
      else
        G (Some (Outgoing, EAJump rs mem)) (λ G', G' (AsmState AWaiting rs mem ins))).
Proof.
  constructor => ?[?[??]]. case_match.
  all: eexists _, _; split; [done|] => ? /= ?.
  all: apply: steps_spec_step_end; [ by econs |] => ? ->; done.
Qed.
Global Hint Resolve asm_step_Jump_s : tstep.

Lemma asm_step_AWaiting_i rs ins mem:
  TStepI asm_module (AsmState AWaiting rs mem ins) (λ G,
    ∀ pc i rs' mem',
      rs' !!! "PC" = pc →
      ins !! pc = Some i →
      G true (Some (Incoming, EAJump rs' mem')) (λ G', G' (AsmState (ARunning []) rs' mem' ins))
   ).
Proof.
  constructor => ? HG. apply steps_impl_step_end => ???.
  inv_all @m_step. eexists _, _. split_and!; [naive_solver..|]. naive_solver.
Qed.
Global Hint Resolve asm_step_AWaiting_i : tstep.

Lemma asm_step_AWaiting_s rs mem ins:
  TStepS asm_module (AsmState AWaiting rs mem ins) (λ G,
    ∃ pc i rs' mem', rs' !!! "PC" = pc ∧
      ins !! pc = Some i ∧
      G (Some (Incoming, EAJump rs' mem')) (λ G', G' (AsmState (ARunning []) rs' mem' ins))).
Proof.
  constructor => ??. destruct_all!. eexists _, _. split; [done|] => ? /= ?.
  apply: steps_spec_step_end. { by econs. } naive_solver.
Qed.
Global Hint Resolve asm_step_AWaiting_s : tstep.

Lemma asm_step_APagefaulting_i rs ins mem a:
  TStepI asm_module (AsmState (APagefaulting a) rs mem ins) (λ G,
      G true (Some (Outgoing, EAPagefault a)) (λ G', G' (AsmState AHalted rs mem ins))
   ).
Proof.
  constructor => ? HG. apply steps_impl_step_end => ???.
  inv_all @m_step. eexists _, _. split_and!; [naive_solver..|]. naive_solver.
Qed.
Global Hint Resolve asm_step_APagefaulting_i : tstep.

Lemma asm_step_APagefaulting_s rs mem ins a:
  TStepS asm_module (AsmState (APagefaulting a) rs mem ins) (λ G,
      G (Some (Outgoing, EAPagefault a)) (λ G', G' (AsmState AHalted rs mem ins))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= ?.
  apply: steps_spec_step_end. { by econs. } naive_solver.
Qed.
Global Hint Resolve asm_step_APagefaulting_s : tstep.

Lemma asm_step_AHalted_i rs ins mem:
  TStepI asm_module (AsmState AHalted rs mem ins) (λ G, True).
Proof.
  constructor => ? HG. apply steps_impl_step_end => ???. inv_all @m_step.
Qed.
Global Hint Resolve asm_step_AHalted_i : tstep.

(** * closing *)
Inductive asm_closed_event : Type :=
| EACStart (rs : gmap string Z) (mem : gmap Z (option Z))
| EACSyscallCall (args : list Z) (mem : gmap Z (option Z))
| EACSyscallRet (ret : Z) (mem : gmap Z (option Z))
| EACPagefault (a : Z)
.

(* s tells us if we already started the execution *)
Definition asm_closed_pre (e : asm_closed_event) (s : bool) :
 prepost (asm_event * bool) unitUR :=
  if s then
    match e with
    | EACSyscallRet ret mem => pp_end ((Incoming, EASyscallRet ret mem), true)
    | _ => pp_prop False (pp_quant $ λ e', pp_end e')
    end
  else
    match e with
    | EACStart rs mem =>
        pp_end ((Incoming, EAJump rs mem), true)
    | _ => pp_prop False (pp_quant $ λ e', pp_end e')
    end
.

Definition asm_closed_post (e : asm_event) (s : bool) :
  prepost (asm_closed_event * bool) unitUR :=
  match e with
  | (Outgoing, EASyscallCall args mem) => pp_end (EACSyscallCall args mem, s)
  | (Outgoing, EAPagefault a) => pp_end (EACPagefault a, s)
  | _ => pp_prop False (pp_quant $ λ e', pp_end e')
  end.

Definition asm_closed (m : module asm_event) : module asm_closed_event :=
  mod_prepost asm_closed_pre asm_closed_post m.

Definition initial_asm_closed_state (m : module asm_event) (σ : m.(m_state)) :=
  (@SMFilter asm_event, σ, (@PPOutside asm_event asm_closed_event, false, (True : uPred unitUR)%I)).


(** * syntactic linking *)
Definition asm_link (instrs1 instrs2 : gmap Z asm_instr) : gmap Z asm_instr :=
  instrs1 ∪ instrs2.

Definition asm_ctx_refines (instrsi instrss : gmap Z asm_instr) :=
  ∀ C, trefines (MS (asm_closed asm_module)
                    (initial_asm_closed_state asm_module (initial_asm_state (asm_link instrsi C))))
                (MS (asm_closed asm_module)
                    (initial_asm_closed_state asm_module (initial_asm_state (asm_link instrss C)))).

(** * semantic linking *)

(* State s says whether we are currently in the environment and
expecting a syscall return. Some SPNone means that the program
executed a page fault and is not waiting for any return. *)
Definition asm_prod_filter (ins1 ins2 : gset Z) : seq_product_state → option seq_product_state → asm_ev → seq_product_state → option seq_product_state → asm_ev → bool → Prop :=
  λ p s e p' s' e' ok,
    e' = e ∧
    ok = true ∧
    match e with
    | EAJump rs mem =>
        s = None ∧
        s' = None ∧
        p' = (if bool_decide (rs !!! "PC" ∈ ins1) then SPLeft else if bool_decide (rs !!! "PC" ∈ ins2) then SPRight else SPNone) ∧
        p ≠ p'
    | EASyscallCall _ _ =>
        s = None ∧
        s' = Some p ∧
        p' = SPNone ∧
        p ≠ SPNone
    | EASyscallRet _ _ =>
        s = Some p' ∧
        s' = None ∧
        p' ≠ SPNone ∧
        p  = SPNone
    | EAPagefault _ =>
        s = None ∧
        s' = Some SPNone ∧
        p' = SPNone ∧
        p ≠ SPNone
    end.
Arguments asm_prod_filter _ _ _ _ _ _ _ _ /.

Definition asm_prod (ins1 ins2 : gset Z) (m1 m2 : module asm_event) : module asm_event :=
  mod_link (asm_prod_filter ins1 ins2) m1 m2.

(* TODO: use this more *)
Definition initial_asm_prod_state (m1 m2 : module asm_event) (σ1 : m1.(m_state)) (σ2 : m2.(m_state)) :=
  (@MLFNone asm_ev, @None seq_product_state, σ1, σ2).

Lemma asm_prod_trefines m1 m1' m2 m2' σ1 σ1' σ2 σ2' σ ins1 ins2 `{!VisNoAll m1} `{!VisNoAll m2}:
  trefines (MS m1 σ1) (MS m1' σ1') →
  trefines (MS m2 σ2) (MS m2' σ2') →
  trefines (MS (asm_prod ins1 ins2 m1 m2) (σ, σ1, σ2))
           (MS (asm_prod ins1 ins2 m1' m2') (σ, σ1', σ2')).
Proof. move => ??. by apply mod_link_trefines. Qed.

Definition asm_link_prod_inv (ins1 ins2 : gmap Z asm_instr) (σ1 : asm_module.(m_state)) (σ2 : mod_link_state asm_ev * option seq_product_state * asm_state * asm_state) : Prop :=
  let 'AsmState i1 rs1 mem1 ins1' := σ1 in
  let '(σf, s, AsmState il rsl meml insl, AsmState ir rsr memr insr) := σ2 in
  ins1' = ins1 ∪ ins2 ∧
  insl = ins1 ∧
  insr = ins2 ∧
  s = None ∧
  match σf with
  | MLFLeft => ∃ i, i1 = ARunning i ∧ il = i1 ∧ rsl = rs1 ∧ meml = mem1 ∧ ir = AWaiting
  | MLFRight => ∃ i, i1 = ARunning i ∧ ir = i1 ∧ rsr = rs1 ∧ memr = mem1 ∧ il = AWaiting
  | MLFNone => i1 = AWaiting ∧ ir = AWaiting ∧ il = AWaiting
  | _ => False
  end.

Lemma asm_link_refines_prod ins1 ins2:
  ins1 ##ₘ ins2 →
  trefines (MS asm_module (initial_asm_state (asm_link ins1 ins2)))
           (MS (asm_prod (dom _ ins1) (dom _ ins2) asm_module asm_module)
               (initial_asm_prod_state asm_module asm_module (initial_asm_state ins1) (initial_asm_state ins2))).
Proof.
  move => Hdisj.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { exact: (λ _, asm_link_prod_inv ins1 ins2). }
  { naive_solver. } { done. }
  move => /= {}n _ Hloop [i1 rs1 mem1 ins1'] [[[σf s] [il rsl meml insl]] [ir rsr memr insr]] [? [? [? Hinv]]].
  case_match; destruct_all?; simplify_eq.
  - destruct i as [|[??|???|???|]?].
    + tstep_i => pc ?. case_match as Hunion. 1: move: Hunion => /lookup_union_Some_raw[Hl|[? Hl]].
      * tstep_s. split!. simplify_option_eq. apply: Hloop; [done|]. naive_solver.
      * tstep_s. split!. simplify_eq. simpl_map_decide. simplify_option_eq. split! => /=.
        tstep_s. split!. tstep_s. split!. simplify_map_eq. apply: Hloop; [done|]. naive_solver.
      * move: Hunion => /lookup_union_None[??]. tstep_s.
        split!. simplify_eq. simpl_map_decide. simplify_option_eq. split! => /=.
        apply: Hloop; [done|]. naive_solver.
    + tstep_both. tstep_s => *. tend. split!. apply: Hloop; [done|]. naive_solver.
    + tstep_both. tstep_s => *. tend. split!. case_match.
      * apply: Hloop; [done|]. naive_solver.
      * by tstep_i.
    + tstep_both. tstep_s => *. tend. split!. case_match.
      * apply: Hloop; [done|]. naive_solver.
      * by tstep_i.
    + tstep_both. tstep_s => *. split!; [done|]. tend.
      tstep_both => *. tstep_s => *. split!; [|done|]; [done|].
      tstep_s. split!. tend. apply: Hloop; [done|]. naive_solver.
  - destruct i as [|[??|???|???|]?].
    + tstep_i => pc ?. case_match as Hunion. 1: move: Hunion => /lookup_union_Some_raw[Hl|[? Hl]].
      * have ?: ins2 !! pc = None by apply: map_disjoint_Some_l.
        tstep_s. split!. simplify_eq. simpl_map_decide. simplify_option_eq. split! => /=.
        tstep_s. split!. tstep_s. split!. simplify_map_eq. apply: Hloop; [done|]. naive_solver.
      * tstep_s. split!. simplify_option_eq. apply: Hloop; [done|]. naive_solver.
      * move: Hunion => /lookup_union_None[??]. tstep_s.
        split!. simplify_eq. simpl_map_decide. simplify_option_eq. split!.
        apply: Hloop; [done|]. naive_solver.
    + tstep_both. tstep_s => *. tend. split!. apply: Hloop; [done|]. naive_solver.
    + tstep_both. tstep_s => *. tend. split!. case_match.
      * apply: Hloop; [done|]. naive_solver.
      * by tstep_i.
    + tstep_both. tstep_s => *. tend. split!. case_match.
      * apply: Hloop; [done|]. naive_solver.
      * by tstep_i.
    + tstep_both. tstep_s => *. split!; [done|]. tend.
      tstep_both => *. tstep_s => *. split!; [|done|]; [done|].
      tstep_s. split!. tend. apply: Hloop; [done|]. naive_solver.
  - tstep_i => pc???? Hin.
    tstep_s. eexists (EAJump _ _). split!.
    { move: Hin => /lookup_union_Some_raw[?|[??]]; simplify_eq; by simpl_map_decide. }
    move: Hin => /lookup_union_Some_raw[?|[??]]; simplify_eq; simpl_map_decide.
    all: tstep_s; split!; apply: Hloop; naive_solver.
Qed.

Lemma asm_prod_refines_link ins1 ins2:
  ins1 ##ₘ ins2 →
  trefines (MS (asm_prod (dom _ ins1) (dom _ ins2) asm_module asm_module)
               (initial_asm_prod_state asm_module asm_module (initial_asm_state ins1) (initial_asm_state ins2)))
           (MS asm_module (initial_asm_state (asm_link ins1 ins2))).
Proof.
  move => Hdisj.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { exact: (λ _, flip (asm_link_prod_inv ins1 ins2)). }
  { naive_solver. } { done. }
  move => /= {}n _ Hloop [[[σf ?] [il rsl meml insl]] [ir rsr memr insr]] [i1 rs1 mem1 ins1'] [? [? [? Hinv]]].
  case_match; destruct_all?; simplify_eq.
  - destruct i as [|[??|???|???|]?].
    + tstep_i => pc ?. case_match => *; destruct_all?; simplify_eq/=.
      * tstep_s. split!. erewrite lookup_union_Some_l by done.
        apply: Hloop; [done|]. naive_solver.
      * tstep_s. split!. rewrite lookup_union_r //.
        destruct (ins2 !! (rs1 !!! "PC")) eqn:? => /=; simpl_map_decide.
        -- tstep_i => *; simplify_eq. tstep_i => *. simplify_map_eq. apply: Hloop; [done|]. naive_solver.
        -- split!. apply: Hloop; [done|]. naive_solver.
    + tstep_both => *. tstep_s. tend. split!. apply: Hloop; [done|]. naive_solver.
    + tstep_both => *. tstep_s => ?. tend. split!. case_match.
      * apply: Hloop; [done|]. naive_solver.
      * by tstep_i.
    + tstep_both => *. tstep_s => ?. tend. split!. case_match.
      * apply: Hloop; [done|]. naive_solver.
      * by tstep_i.
    + tstep_both => *. destruct_all?; simplify_eq. tstep_s. split!; [done|]. tend.
      tstep_both => *. destruct_all?; case_match; destruct_all?; simplify_eq/=. tstep_s. split!; [done|]. tend.
      tstep_i => *. simplify_eq/=. apply: Hloop; [done|]. naive_solver.
  - destruct i as [|[??|???|???|]?].
    + tstep_i => pc ?. case_match => *; destruct_all?; simplify_eq/=.
      * tstep_s. split!. erewrite lookup_union_Some_r by done.
        apply: Hloop; [done|]. naive_solver.
      * tstep_s. split!. rewrite lookup_union_l' //.
        destruct (ins1 !! (rs1 !!! "PC")) eqn:? => /=; simpl_map_decide.
        -- tstep_i => *; simplify_eq. tstep_i => *. simplify_map_eq. apply: Hloop; [done|]. naive_solver.
        -- split!. apply: Hloop; [done|]. naive_solver.
    + tstep_both => *. tstep_s. tend. split!. apply: Hloop; [done|]. naive_solver.
    + tstep_both => *. tstep_s => ?. tend. split!. case_match.
      * apply: Hloop; [done|]. naive_solver.
      * by tstep_i.
    + tstep_both => *. tstep_s => ?. tend. split!. case_match.
      * apply: Hloop; [done|]. naive_solver.
      * by tstep_i.
    + tstep_both => *. destruct_all?; simplify_eq. tstep_s. split!; [done|]. tend.
      tstep_both => *. destruct_all?; case_match; destruct_all?; simplify_eq/=. tstep_s. split!; [done|]. tend.
      tstep_i => *. simplify_eq/=. apply: Hloop; [done|]. naive_solver.
  - tstep_i => -[] /= *; destruct_all?; simplify_eq/=.
    tstep_s.
    repeat case_bool_decide => //.
    all: revert select (_ ∈ dom _ _) => /elem_of_dom[? Hin];
           split!; [rewrite lookup_union_Some //;naive_solver|].
    all: tstep_i => *; simplify_eq; apply: Hloop; naive_solver.
Qed.

Lemma asm_trefines_implies_ctx_refines insi inss :
  dom (gset _) insi = dom (gset _) inss →
  trefines (MS asm_module (initial_asm_state insi)) (MS asm_module (initial_asm_state inss)) →
  asm_ctx_refines insi inss.
Proof.
  move => Hdom Href C. rewrite /asm_link map_difference_union_r (map_difference_union_r inss).
  apply mod_seq_map_trefines. { apply _. } { apply _. }
  etrans. {
    apply asm_link_refines_prod. apply map_disjoint_difference_r'.
  }
  etrans. 2: {
    apply asm_prod_refines_link. apply map_disjoint_difference_r'.
  }
  rewrite !dom_difference_L Hdom.
  apply asm_prod_trefines; [apply _..| |].
  - apply: Href.
  - erewrite map_difference_eq_dom_L => //. apply _.
Qed.

(** * Deeply embedded assembly language *)
Inductive asm_operand :=
| RegisterOp (r : string) | ImmediateOp (z : Z).

Definition op_lookup (rs : gmap string Z) (op : asm_operand) : Z :=
  match op with
  | RegisterOp r => rs !!! r
  | ImmediateOp z => z
  end.

Inductive deep_asm_instr :=
| Amov (rd : string) (o : asm_operand)
| Aadd (rd r1 : string) (o : asm_operand)
| Amul (rd r1 : string) (o : asm_operand)
| Aseq (rd r1 : string) (o : asm_operand) (* set rd to 1 if r1 == o else to 0 *)
| Asle (rd r1 : string) (o : asm_operand) (* set rd to 1 if r1 <= o else to 0 *)
| Aslt (rd r1 : string) (o : asm_operand) (* set rd to 1 if r1 <  o else to 0 *)
| Aload (r r1 : string) (o2 : Z) (* ldr r, [r1 + o2] *)
| Astore (r r1: string) (o2 : Z) (* str r, [r1 + o2] *)
| Abranch (abs : bool) (o : asm_operand) (* abs: absolute or relative address? *)
| Abranch_eq (abs : bool) (od : asm_operand) (r1 : string) (o : asm_operand)
| Abranch_link (abs : bool) (o : asm_operand)
| Aret
| ASyscall
.

Definition deep_to_asm_instr (di : deep_asm_instr) : asm_instr :=
  match di with
  | Amov rd o => [
      WriteReg rd (λ rs, op_lookup rs o);
      WriteReg "PC" (λ rs, rs !!! "PC" + 1)
    ]
  | Aadd rd r1 o => [
      WriteReg rd (λ rs, rs !!! r1 + op_lookup rs o);
      WriteReg "PC" (λ rs, rs !!! "PC" + 1)
    ]
  | Amul rd r1 o => [
      WriteReg rd (λ rs, rs !!! r1 * op_lookup rs o);
      WriteReg "PC" (λ rs, rs !!! "PC" + 1)
    ]
  | Aseq rd r1 o => [
      WriteReg rd (λ rs, bool_to_Z (bool_decide (rs !!! r1 = op_lookup rs o)));
      WriteReg "PC" (λ rs, rs !!! "PC" + 1)
    ]
  | Asle rd r1 o => [
      WriteReg rd (λ rs, bool_to_Z (bool_decide (rs !!! r1 ≤ op_lookup rs o)));
      WriteReg "PC" (λ rs, rs !!! "PC" + 1)
    ]
  | Aslt rd r1 o => [
      WriteReg rd (λ rs, bool_to_Z (bool_decide (rs !!! r1 < op_lookup rs o)));
      WriteReg "PC" (λ rs, rs !!! "PC" + 1)
    ]
  | Aload r r1 o2 => [
      ReadMem r r1 (λ v, v + o2);
      WriteReg "PC" (λ rs, rs !!! "PC" + 1)
    ]
  | Astore r r1 o2 => [
      WriteMem r r1 (λ v, v + o2);
      WriteReg "PC" (λ rs, rs !!! "PC" + 1)
    ]
  | Abranch abs o => [
      WriteReg "PC" (λ rs, if abs then op_lookup rs o else  rs !!! "PC" + op_lookup rs o)
    ]
  | Abranch_eq abs od r1 o => [
      WriteReg "PC" (λ rs,
        if bool_decide (rs !!! r1 = op_lookup rs o) then
          if abs then op_lookup rs od else  rs !!! "PC" + op_lookup rs od
        else
          rs !!! "PC" + 1)
    ]
  | Abranch_link abs o => [
      WriteReg "R30" (λ rs, rs !!! "PC" + 1);
      WriteReg "PC" (λ rs, if abs then op_lookup rs o else  rs !!! "PC" + op_lookup rs o)
    ]
  | Aret => [
      WriteReg "PC" (λ rs, rs !!! "R30")
    ]
  | Asyscall => [
      Syscall;
      WriteReg "PC" (λ rs, rs !!! "PC" + 1)
    ]
  end.

Definition deep_to_asm_instrs (s : Z) (di : list deep_asm_instr) : gmap Z asm_instr :=
  map_seqZ s (deep_to_asm_instr <$> di).

Lemma deep_to_asm_instrs_nil pc :
  deep_to_asm_instrs pc [] = ∅.
Proof. done. Qed.

Lemma deep_to_asm_instrs_cons pc di dins :
  deep_to_asm_instrs pc (di :: dins) = <[pc := deep_to_asm_instr di]> $ deep_to_asm_instrs (pc + 1) dins.
Proof. done. Qed.

Lemma deep_to_asm_instrs_app pc dins1 dins2 :
  deep_to_asm_instrs pc (dins1 ++ dins2) = deep_to_asm_instrs pc dins1 ∪ deep_to_asm_instrs (pc + length dins1) dins2.
Proof.
  elim: dins1 pc => /=. { move => ?. rewrite left_id_L. f_equal. lia. }
  move => ?? IH ?. rewrite !deep_to_asm_instrs_cons IH insert_union_l. f_equal. f_equal. lia.
Qed.

Lemma deep_to_asm_instrs_is_Some a dins pc:
  is_Some (deep_to_asm_instrs a dins !! pc) ↔ a ≤ pc < a + length dins.
Proof. by rewrite lookup_map_seqZ_is_Some fmap_length. Qed.

Lemma deep_to_asm_instrs_subseteq_range a1 di1 a2 di2:
  deep_to_asm_instrs a1 di1 ⊆ deep_to_asm_instrs a2 di2 →
  (a2 ≤ a1 ∧ a1 + length di1 ≤ a2 + length di2) ∨ length di1 = 0%nat.
Proof.
  destruct (decide (length di1 = 0%nat)); [naive_solver|].
  move => Hsub. left.
  have : is_Some (deep_to_asm_instrs a1 di1 !! a1). { apply deep_to_asm_instrs_is_Some. lia. }
  move => /(lookup_weaken_is_Some _ _ _)/(_ Hsub)/deep_to_asm_instrs_is_Some?.
  have : is_Some (deep_to_asm_instrs a1 di1 !! (a1 + length di1 - 1)). { apply deep_to_asm_instrs_is_Some. lia. }
  move => /(lookup_weaken_is_Some _ _ _)/(_ Hsub)/deep_to_asm_instrs_is_Some?. lia.
Qed.

Lemma deep_to_asm_instrs_cons_inv pc di dins ins :
  deep_to_asm_instrs pc (di :: dins) ⊆ ins →
  ins !! pc = Some (deep_to_asm_instr di) ∧ deep_to_asm_instrs (pc + 1) dins ⊆ ins.
Proof.
  rewrite deep_to_asm_instrs_cons => Hsub.
  split.
  - eapply lookup_weaken; [|done]. apply lookup_insert.
  - etrans; [|done]. apply insert_subseteq. apply lookup_map_seqZ_None. lia.
Qed.

Lemma deep_to_asm_instrs_lookup_nat n a pc dins:
  pc = a + Z.of_nat n →
  deep_to_asm_instrs a dins !! pc = deep_to_asm_instr <$> (dins !! n).
Proof.
  move => ->. rewrite /deep_to_asm_instrs. rewrite lookup_map_seqZ. case_option_guard; [|lia].
  have -> : Z.to_nat (a + n - a) = n by lia.
  by rewrite list_lookup_fmap.
Qed.

(** * itree examples *)
Require Import dimsum.itree.
Local Ltac go :=
  clear_itree.
Local Ltac go_s :=
  tstep_s; go.
Local Ltac go_i :=
  tstep_i; go.

(* TODO: Get rid of Some in recursive call (maybe by passing an itree to t instead of the +'? ) *)
(* TODO: prove merging of two asm loops (should just be all choice between the two implementations ) *)
Definition asm_loop (ins : list Z)
   (t : gmap string Z → gmap Z (option Z) → itree (callE
     (option (gmap string Z * gmap Z (option Z))) (gmap string Z * gmap Z (option Z)) +' moduleE asm_event unit) (gmap string Z * gmap Z (option Z)))
  : itree (moduleE asm_event unit) unit :=
  rec (λ a,
    '(rs, mem) ← (
       if a is Some (nrs, nmem) then
         if bool_decide (nrs !!! "PC" ∈ ins) then
           Ret (nrs, nmem)
         else
           translate (inr_) (TVis (Outgoing, EAJump nrs nmem));;;;
           rs ← translate (inr_) (TExist _);;;
           mem ← translate (inr_) (TExist _);;;
           translate (inr_) (TVis (Incoming, EAJump rs mem));;;;
           Ret (rs, mem)
        else
          rs ← translate (inr_) (TExist _);;;
          mem ← translate (inr_) (TExist _);;;
          translate (inr_) (TVis (Incoming, EAJump rs mem));;;;
          Ret (rs, mem)
     );;;
    translate (inr_) (TAssert (rs !!! "PC" ∈ ins));;;;
    (* The env can choose if this call should be treated as a call or a return. *)
    b ← translate (inr_) (TAll bool);;;
    if b then Ret (rs, mem) else
      r ← t rs mem;;;
      call (Some r)
    ) None;;;; TUb.

Lemma tsim_asm_loop n b rs mem ins t insaddrs:
  (∀ z, z ∈ insaddrs ↔ is_Some (ins !! z)) →
  (∀ n rc pc' rs' mem' i k,
      rs' !!! "PC" = pc' →
      ins !! pc' = Some i →
      (∀ pc'' rs1'' rs2'' mem1'' mem2'' h',
         rs1'' = rs2'' →
         mem1'' = mem2'' →
         rs1'' !!! "PC" = pc'' →
          (∀ pc''' rs''' mem''' i,
              rs''' !!! "PC" = pc''' →
              ins !! pc''' = Some i →
              AsmState (ARunning i) rs''' mem''' ins ⪯{asm_module, mod_itree asm_event (), n, b} (h' (rs''', mem'''), ())) →
          (AsmState (ARunning []) rs1'' mem1'' ins)
            ⪯{asm_module, mod_itree asm_event (), n, true}
          (y ← rec rc (Some (rs2'', mem2''));;; h' y, ())) →
      (∀ pc rs1 rs2 mem1 mem2,
          rs1 = rs2 →
          mem1 = mem2 →
          rs1 !!! "PC" = pc →
          tsim n true asm_module (mod_itree asm_event ()) (AsmState (ARunning []) rs1 mem1 ins) tnil (k (rs2, mem2), ())) →
    AsmState (ARunning i) rs' mem' ins ⪯{asm_module, mod_itree asm_event (), n, true}
       (r ← interp (recursive rc) (t rs' mem');;; k r, ())) →
  (** Then we can prove an asm_loop *)
  AsmState AWaiting rs mem ins ⪯{asm_module, mod_itree asm_event (), n, b} (asm_loop insaddrs t, ()).
Proof.
  rewrite /asm_loop => Hins Hl. set rc := (X in (rec X)).
  apply (tsim_remember_rec (mi:=asm_module)
   (λ a σi s,
     if a is Some (rs, mem) then
       σi = AsmState (ARunning []) rs mem ins
     else
       ∃ rs mem, σi = AsmState AWaiting rs mem ins
   )
   (λ σi '(rs, mem) s', ∃ i, σi = AsmState (ARunning i) rs mem ins ∧ ins !! (rs !!! "PC") = Some i)).
  { naive_solver. }
  { move => ????. go_s. done. }
  move => {}n _ Hloop σi [] CONT a Ha HCONT.
  destruct a as [[rs' mem']|]. 2: {
    move: Ha => [{}rs [{}mem ?]]. subst.
    tstep_i => pc i {}rs {}mem HPC Hi.
    rewrite {1}rec_as_interp {2}/rc.
    go_s. eexists _. go.
    go_s. eexists _. go.
    go_s. split; [done|]. go.
    go_s. split. { apply Hins. naive_solver. } go.
    tstep_i => ??. simplify_map_eq.
    go_s => -[]; go.
    { go_s. apply: tsim_mono_b. revert select (eqit eq _ _ _ _) => ->. apply HCONT. naive_solver. }
    revert select (eqit eq _ _ _ _) => ->. rewrite interp_bind bind_bind.
    apply: Hl; [done..| |].
    - move => ??????????. subst. apply Hloop; [done|].
      move => ? [rs' mem'] []. naive_solver.
    - move => ????????. rewrite interp_recursive_call.
      apply Hloop. { naive_solver. }
      move => ? [??] [] [?[??]]. apply: HCONT. naive_solver.
  }
  simplify_eq.
  tstep_i => pc HPC. simplify_eq.
  case_match.
  - rewrite {1}rec_as_interp {2}/rc. rewrite bool_decide_true. 2: { apply Hins. naive_solver. }
    go_s. split. { apply Hins. naive_solver. } go.
    go_s => -[]; go.
    { go_s. apply: tsim_mono_b. revert select (eqit eq _ _ _ _) => ->. apply HCONT. naive_solver. }
    revert select (eqit eq _ _ _ _) => ->. rewrite interp_bind bind_bind.
    apply: Hl; [done..| |].
    + move => ??????????. subst. apply Hloop; [done|].
      move => ? [? ?] []. naive_solver.
    + move => ????????. rewrite interp_recursive_call.
      apply Hloop. { naive_solver. }
      move => ? [??] [] [?[??]]. apply: HCONT. naive_solver.
  - rewrite {1}rec_as_interp {2}/rc. rewrite bool_decide_false. 2: { move => /Hins[??]. naive_solver. }
    go_s. split; [done|]. go.
    tstep_i => pc i {}rs {}mem HPC Hi.
    go_s. eexists _. go.
    go_s. eexists _. go.
    go_s. split; [done|]. go.
    go_s. split. { apply Hins. naive_solver. } go.
    tstep_i => ??. simplify_map_eq.
    go_s => -[]; go.
    { go_s. apply: tsim_mono_b. revert select (eqit eq _ _ _ _) => ->. apply HCONT. naive_solver. }
    revert select (eqit eq _ _ _ _) => ->. rewrite interp_bind bind_bind.
    apply: Hl; [done..| |].
    + move => ??????????. subst. apply Hloop; [done|].
      move => ? [? ?] []. naive_solver.
    + move => ????????. rewrite interp_recursive_call.
      apply Hloop. { naive_solver. }
      move => ? [??] [] [?[??]]. apply: HCONT. naive_solver.
Qed.

Module asm_examples.
  Local Open Scope Z_scope.
  Definition asm_mul : gmap Z asm_instr :=
    <[ 100 := [
          (* mul R1, R1, R2 *)
          WriteReg "R1" (λ rs, rs !!! "R1" * rs !!! "R2");
          WriteReg "PC" (λ rs, rs !!! "PC" + 1)
      ] ]> $
    <[ 101 := [
          (* ret *)
          WriteReg "PC" (λ rs, rs !!! "R30")
      ] ]> $ ∅.

  Definition itree_mul : itree (moduleE asm_event unit) unit :=
    asm_loop [100; 101] (λ rs mem,
       if bool_decide (rs !!! "PC" = 100) then
         Ret ((<["PC":=(rs !!! "R30")]> $ <["R1":=(rs !!! "R1") * (rs !!! "R2")]> $ rs), mem)
       else if bool_decide (rs !!! "PC" = 101) then
         translate (inr_) TUb
       else
         translate (inr_) TNb
    ).


  Lemma asm_mul_refines_itree :
    trefines (MS asm_module (initial_asm_state asm_mul)) (MS (mod_itree _ _) (itree_mul, tt)).
  Proof.
    apply tsim_implies_trefines => /= n. rewrite /initial_asm_state.
    rewrite {1}/itree_mul.
    apply tsim_asm_loop. {
      move => z. rewrite !elem_of_cons elem_of_nil.
      rewrite !lookup_insert_is_Some' lookup_empty -not_eq_None_Some.
      naive_solver.
    }
    move => {}n rc pc rs mem i CONT HPC Hi Hloop HCONT.
    move: Hi. rewrite !lookup_insert_Some !lookup_empty => Hi. destruct_all!; simplify_eq.
    all: repeat (rewrite bool_decide_false; [|done]); rewrite bool_decide_true //.
    all: try by go_s.

    go_s.
    tstep_i; simplify_map_eq'. split!.
    tstep_i; simplify_map_eq'.
    tstep_i => ??; simplify_map_eq'.
    tstep_i; simplify_map_eq'. split!.
    revert select (eqit eq _ _ _ _) => ->.
    apply: HCONT; simplify_map_eq' => //.
  Qed.

  Definition asm_mul_client : gmap Z asm_instr :=
    <[ 200 := [
          (* mov R1, 2; mov R2, 2; *)
          WriteReg "R1" (λ rs, 2);
          WriteReg "R2" (λ rs, 2);
          WriteReg "PC" (λ rs, rs !!! "PC" + 1)
      ] ]> $
    <[ 201 := [
          (* mov R29, R30; *)
          WriteReg "R29" (λ rs, rs !!! "R30");
          WriteReg "PC" (λ rs, rs !!! "PC" + 1)
      ] ]> $
    <[ 202 := [
          (* bl 100; *)
          WriteReg "R30" (λ rs, rs !!! "PC" + 1);
          WriteReg "PC" (λ rs, 100)
      ] ]> $
    <[ 203 := [
          (* mov R30, R29; *)
          WriteReg "R30" (λ rs, rs !!! "R29");
          WriteReg "PC" (λ rs, rs !!! "PC" + 1)
      ] ]> $
    <[ 204 := [
          (* ret; *)
          WriteReg "PC" (λ rs, rs !!! "R30")
      ] ]> $ ∅.

  Definition itree_mul_client : itree (moduleE asm_event unit) unit :=
    asm_loop [200; 201; 202; 203; 204] (λ rs mem,
       if bool_decide (rs !!! "PC" = 200) then
         r29' ← translate (inr_) (TExist Z);;;
         (* translate (inr_) (TVis (EAJump 100 (<["PC":=100]> $ <["R30":= 212]> $ <["R29":= r29']> $ <["R2":= 2]> $ <["R1":= 2]> $ rs)));;;; *)
         '(rs', mem') ← call (Some ((<["PC":=100]> $ <["R30":= 203]> $ <["R29":= r29']> $ <["R2":= 2]> $ <["R1":= 2]> $ rs), mem));;;
         translate (inr_) (TAssume (rs' !!! "PC" = 203));;;;
         translate (inr_) (TAssume (rs' !!! "R29" = r29'));;;;
         translate (inr_) (TAssume ((rs !!! "R30") ≠ 200 ∧ (rs !!! "R30") ≠ 201 ∧ (rs !!! "R30") ≠ 202 ∧ (rs !!! "R30") ≠ 203 ∧ (rs !!! "R30") ≠ 204));;;;
         r30' ← translate (inr_) (TExist Z);;;
         (* translate (inr_) (TVis (EAJump r30 (<["PC":= r30]> $ <["R30":= r30']> rs')));;;; *)
         Ret ((<["PC":= (rs !!! "R30")]> $ <["R30":= r30']> rs'), mem')
       else if bool_decide (rs !!! "PC" = 201) then translate (inr_) TUb
       else if bool_decide (rs !!! "PC" = 202) then translate (inr_) TUb
       else if bool_decide (rs !!! "PC" = 203) then translate (inr_) TUb
       else if bool_decide (rs !!! "PC" = 204) then translate (inr_) TUb
       else translate (inr_) TNb
    ).


  Lemma asm_mul_client_refines_itree :
    trefines (MS asm_module (initial_asm_state asm_mul_client)) (MS (mod_itree _ _) (itree_mul_client, tt)).
  Proof.
    apply tsim_implies_trefines => /= n. rewrite /initial_asm_state.
    rewrite {1}/itree_mul_client.
    apply tsim_asm_loop. {
      move => z. rewrite !elem_of_cons elem_of_nil.
      rewrite !lookup_insert_is_Some' lookup_empty -not_eq_None_Some.
      naive_solver.
    }
    move=> {}n rc pc rs mem i CONT HPC Hi Hloop HCONT.
    move: Hi. rewrite !lookup_insert_Some !lookup_empty => Hi. destruct_all!; simplify_eq.
    all: repeat (rewrite bool_decide_false; [|done]); rewrite bool_decide_true //.
    all: try by go_s.
    tstep_i; simplify_map_eq'.
    tstep_i; simplify_map_eq'.
    tstep_i; simplify_map_eq'.
    tstep_i => ??; simplify_map_eq'.
    tstep_i; simplify_map_eq'.
    tstep_i; simplify_map_eq'.
    tstep_i => ??; simplify_map_eq'.
    tstep_i; simplify_map_eq'.
    tstep_i; simplify_map_eq'.
    sort_map_insert; simplify_map_eq'.
    go_s. eexists (rs !!! "R30"); go.
    go_s.
    revert select (eqit eq _ _ _ _) => ->.
    apply: Hloop. { by sort_map_insert. } { done. } { by simplify_map_eq'. }
    move => pc' rs'' mem'' i HPC' Hi'.
    go_s => ?; go; subst. unfold asm_mul_client in Hi'. simplify_map_eq.
    go_s => ?; go.
    go_s => -[?[?[?[??]]]]; go. simplify_map_eq'.

    tstep_i; simplify_map_eq'. split!.
    tstep_i; simplify_map_eq'. split!.
    tstep_i => ??; simplify_map_eq'.
    tstep_i; simplify_map_eq'. split!.
    go_s. eexists _; go.
    go_s. revert select (eqit eq _ _ _ _) => ->.
    apply: HCONT; by simplify_map_eq'.
  Qed.
End asm_examples.
