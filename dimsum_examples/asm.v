From dimsum.core Require Export proof_techniques link prepost.

Local Open Scope Z_scope.

(** * Assembly language *)

(** * Language defnition using Islaris-like microinstructions *)

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
| AllocMem (r : string) (f : gmap string Z → Z)
.

Definition asm_instr := list asm_instr_elem.

Inductive asm_run_state : Set :=
| ARunning (i : asm_instr)
| AWaiting
| AWaitingSyscall (i : asm_instr)
| AHalted
.

Inductive asm_state := AsmState {
  asm_cur_instr : asm_run_state;
  (** [asm_regs] is a map from register names to values. It is always
  used with !!! instead of !!, i.e. it is a total map. *)
  asm_regs : gmap string Z;
  (** [asm_mem] is a map from addresses to values stored in memory.
  Accessing memory with [asm_mem !! a = None] leads to UB.
  Accessing memory with [asm_mem !! a = Some None] leads to NB. *)
  asm_mem : gmap Z (option Z);
  asm_instrs : gmap Z asm_instr;
}.
Add Printing Constructor asm_state.

Definition asm_init (ins : gmap Z asm_instr) := AsmState AWaiting ∅ ∅ ins.

Inductive asm_ev :=
| EAJump (regs : gmap string Z) (mem : gmap Z (option Z))
| EASyscallCall (args : list Z) (mem : gmap Z (option Z))
| EASyscallRet (ret : Z) (mem : gmap Z (option Z))
.

Definition asm_event := io_event asm_ev.

Definition mem_range_free (mem : gmap Z (option Z)) (a : Z) (n : Z) := 
  ∀ i, 0 ≤ i < n → mem !! (a + i) = None.

Definition mem_alloc (mem : gmap Z (option Z)) (a : Z) (n : Z) : gmap Z (option Z) :=
  (list_to_map ((λ z, (a + z, Some 0)) <$> seqZ 0 n) ∪ mem).

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
                AsmState AHalted regs mem instrs)
| SWriteMem regs instrs r1 r2 f es mem:
  asm_step (AsmState (ARunning (WriteMem r1 r2 f :: es)) regs mem instrs) None (λ σ', ∃ mv,
         mem !! f (regs !!! r2) = Some mv ∧
         σ' = if mv is Some mv' then
                AsmState (ARunning es) regs (<[f (regs !!! r2) := Some (regs !!! r1)]>mem) instrs
              else
                AsmState AHalted regs mem instrs)
| SSyscallCall regs instrs es mem:
  asm_step (AsmState (ARunning (Syscall :: es)) regs mem instrs)
           (Some (Outgoing, EASyscallCall (extract_syscall_args regs) mem))
           (λ σ', σ' = AsmState (AWaitingSyscall es) regs mem instrs)
| SSyscallRet regs instrs es mem mem' ret:
  asm_step (AsmState (AWaitingSyscall es) regs mem instrs)
           (Some (Incoming, EASyscallRet ret mem'))
           (λ σ', σ' = AsmState (ARunning es) (<["R0" := ret]>regs) mem' instrs)
| SAllocMem f a es r regs mem instrs:
  mem_range_free mem a (f regs) →
  asm_step (AsmState (ARunning (AllocMem r f :: es)) regs mem instrs) None (λ σ', 
    f regs > 0 ∧
    σ' = AsmState (ARunning es) (<[r := a]> regs) (mem_alloc mem a (f regs)) instrs)
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
.

Definition asm_trans := ModTrans asm_step.
Definition asm_mod (ins : gmap Z asm_instr) := Mod asm_trans (asm_init ins).

Global Instance asm_vis_no_all: VisNoAng asm_trans.
Proof. move => *. inv_all @m_step; naive_solver. Qed.

(** * tstep *)
Lemma asm_step_WriteReg_i r f es rs ins mem:
  TStepI asm_trans (AsmState (ARunning (WriteReg r f::es)) rs mem ins)
            (λ G, G true None (λ G', G' (AsmState (ARunning es) (<[r:=f rs]>rs) mem ins))).
Proof.
  constructor => ? ?. apply steps_impl_step_end => ???.
  inv_all @m_step. eexists _, _. split_and!; [done|done|].
  move => ? /=. naive_solver.
Qed.
Global Hint Resolve asm_step_WriteReg_i : typeclass_instances.

Lemma asm_step_WriteReg_s r f es rs ins mem:
  TStepS asm_trans (AsmState (ARunning (WriteReg r f::es)) rs mem ins)
            (λ G, G None (λ G', G' (AsmState (ARunning es) (<[r:=f rs]>rs) mem ins))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= ?.
  apply: steps_spec_step_end. { econs. }
  move => ? /= ?. naive_solver.
Qed.
Global Hint Resolve asm_step_WriteReg_s : typeclass_instances.

Lemma asm_step_ReadMem_i r1 r2 f es rs ins mem:
  TStepI asm_trans (AsmState (ARunning (ReadMem r1 r2 f::es)) rs mem ins)
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
Global Hint Resolve asm_step_ReadMem_i : typeclass_instances.

Lemma asm_step_ReadMem_s r1 r2 f es rs ins mem:
  TStepS asm_trans (AsmState (ARunning (ReadMem r1 r2 f::es)) rs mem ins)
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
Global Hint Resolve asm_step_ReadMem_s : typeclass_instances.

Lemma asm_step_WriteMem_i r1 r2 f es rs ins mem:
  TStepI asm_trans (AsmState (ARunning (WriteMem r1 r2 f::es)) rs mem ins)
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
Global Hint Resolve asm_step_WriteMem_i : typeclass_instances.

Lemma asm_step_WriteMem_s r1 r2 f es rs ins mem:
  TStepS asm_trans (AsmState (ARunning (WriteMem r1 r2 f::es)) rs mem ins)
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
Global Hint Resolve asm_step_WriteMem_s : typeclass_instances.

Lemma asm_step_Syscall_call_i es rs ins mem:
  TStepI asm_trans (AsmState (ARunning (Syscall::es)) rs mem ins)
            (λ G, G true (Some (Outgoing, EASyscallCall (extract_syscall_args rs) mem))
                    (λ G', G' (AsmState (AWaitingSyscall es) rs mem ins))).
Proof.
  constructor => ? ?. apply steps_impl_step_end => ???.
  inv_all @m_step. eexists _, _. split_and!; [done|done|].
  move => ? /=. naive_solver.
Qed.
Global Hint Resolve asm_step_Syscall_call_i : typeclass_instances.

Lemma asm_step_Syscall_call_s es rs ins mem:
  TStepS asm_trans (AsmState (ARunning (Syscall :: es)) rs mem ins)
            (λ G, G (Some (Outgoing, EASyscallCall (extract_syscall_args rs) mem))
                    (λ G', G' (AsmState (AWaitingSyscall es) rs mem ins))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= ?.
  apply: steps_spec_step_end. { econs. } naive_solver.
Qed.
Global Hint Resolve asm_step_Syscall_call_s : typeclass_instances.

Lemma asm_step_Syscall_ret_i es rs ins mem:
  TStepI asm_trans (AsmState (AWaitingSyscall es) rs mem ins)
            (λ G, ∀ ret mem', G true (Some (Incoming, EASyscallRet ret mem'))
                    (λ G', G' (AsmState (ARunning es) (<["R0" := ret]> rs) mem' ins))).
Proof.
  constructor => ? ?. apply steps_impl_step_end => ???.
  inv_all @m_step. eexists _, _. split_and!; [naive_solver|done|].
  move => ? /=. naive_solver.
Qed.
Global Hint Resolve asm_step_Syscall_ret_i : typeclass_instances.

Lemma asm_step_Syscall_ret_s es rs ins mem:
  TStepS asm_trans (AsmState (AWaitingSyscall es) rs mem ins)
            (λ G, ∃ ret mem', G (Some (Incoming, EASyscallRet ret mem'))
                    (λ G', G' (AsmState (ARunning es) (<["R0":=ret]> rs) mem' ins))).
Proof.
  constructor => ? [?[??]]. eexists _, _. split; [done|] => ? /= ?.
  apply: steps_spec_step_end. { econs. } naive_solver.
Qed.
Global Hint Resolve asm_step_Syscall_ret_s : typeclass_instances.

Lemma asm_step_AllocMem_i r f es rs mem ins: 
  TStepI asm_trans (AsmState (ARunning (AllocMem r f::es)) rs mem ins)
            (λ G, ∀ a, mem_range_free mem a (f rs) →
              G true None (λ G', f rs > 0 ∧ G' (AsmState (ARunning es) (<[r:=a]> rs) (mem_alloc mem a (f rs)) ins))).
Proof.
  constructor => ? ?. apply: steps_impl_step_end => ???. 
  inv_all @m_step. split!; naive_solver. 
Qed.
Global Hint Resolve asm_step_AllocMem_i : typeclass_instances.

Lemma asm_step_AllocMem_s r f es rs mem ins: 
  TStepS asm_trans (AsmState (ARunning (AllocMem r f :: es)) rs mem ins)
            (λ G, (G None (λ G', ∃ a, 
            mem_range_free mem a (f rs) ∧ 
            (f rs > 0 → G' (AsmState (ARunning es) (<[r:=a]> rs) (mem_alloc mem a (f rs)) ins))))).
Proof.
  constructor => ??. split!;[done| ]=> ? /= ?. destruct!.
  apply: steps_spec_step_end; [by econs|naive_solver]. 
Qed.
Global Hint Resolve asm_step_AllocMem_s : typeclass_instances.

Lemma asm_step_Jump_i rs ins mem:
  TStepI asm_trans (AsmState (ARunning []) rs mem ins) (λ G,
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
Global Hint Resolve asm_step_Jump_i : typeclass_instances.

Lemma asm_step_Jump_s rs ins mem:
  TStepS asm_trans (AsmState (ARunning []) rs mem ins) (λ G,
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
Global Hint Resolve asm_step_Jump_s : typeclass_instances.

Lemma asm_step_AWaiting_i rs ins mem:
  TStepI asm_trans (AsmState AWaiting rs mem ins) (λ G,
    ∀ pc i rs' mem',
      rs' !!! "PC" = pc →
      ins !! pc = Some i →
      G true (Some (Incoming, EAJump rs' mem')) (λ G', G' (AsmState (ARunning []) rs' mem' ins))
   ).
Proof.
  constructor => ? HG. apply steps_impl_step_end => ???.
  inv_all @m_step. eexists _, _. split_and!; [naive_solver..|]. naive_solver.
Qed.
Global Hint Resolve asm_step_AWaiting_i : typeclass_instances.

Lemma asm_step_AWaiting_s rs mem ins:
  TStepS asm_trans (AsmState AWaiting rs mem ins) (λ G,
    ∃ pc i rs' mem', rs' !!! "PC" = pc ∧
      ins !! pc = Some i ∧
      G (Some (Incoming, EAJump rs' mem')) (λ G', G' (AsmState (ARunning []) rs' mem' ins))).
Proof.
  constructor => ??. destruct!. eexists _, _. split; [done|] => ? /= ?.
  apply: steps_spec_step_end. { by econs. } naive_solver.
Qed.
Global Hint Resolve asm_step_AWaiting_s : typeclass_instances.

Lemma asm_step_AHalted_i rs ins mem:
  TStepI asm_trans (AsmState AHalted rs mem ins) (λ G, True).
Proof.
  constructor => ? HG. apply steps_impl_step_end => ???. inv_all @m_step.
Qed.
Global Hint Resolve asm_step_AHalted_i : typeclass_instances.

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
  | _ => pp_prop False (pp_quant $ λ e', pp_end e')
  end.

Definition asm_closed_mod (m : module asm_event) : module asm_closed_event :=
  prepost_mod asm_closed_pre asm_closed_post m false True%I.

(** * Linking *)
(** ** Syntactic linking *)
Definition asm_syn_link (instrs1 instrs2 : gmap Z asm_instr) : gmap Z asm_instr :=
  instrs1 ∪ instrs2.

Definition asm_ctx_refines (instrsi instrss : gmap Z asm_instr) :=
  ∀ C, trefines (asm_closed_mod (asm_mod (asm_syn_link instrsi C)))
                (asm_closed_mod (asm_mod (asm_syn_link instrss C))).

(** ** Semantic linking *)
(* State s says whether we are currently in the environment and
expecting a syscall return. Some SPNone means that the program
executed a page fault and is not waiting for any return. *)
Definition asm_link_filter (ins1 ins2 : gset Z) : seq_product_case → option seq_product_case → asm_ev → seq_product_case → option seq_product_case → asm_ev → bool → Prop :=
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
    end.
Arguments asm_link_filter _ _ _ _ _ _ _ _ /.

Definition asm_link_trans (ins1 ins2 : gset Z) (m1 m2 : mod_trans asm_event) : mod_trans asm_event :=
  link_trans (asm_link_filter ins1 ins2) m1 m2.

Definition asm_link (ins1 ins2 : gset Z) (m1 m2 : module asm_event) : module asm_event :=
  Mod (asm_link_trans ins1 ins2 m1.(m_trans) m2.(m_trans)) (MLFNone, None, m1.(m_init), m2.(m_init)).

Lemma asm_link_trefines m1 m1' m2 m2' ins1 ins2 `{!VisNoAng m1.(m_trans)} `{!VisNoAng m2.(m_trans)}:
  trefines m1 m1' →
  trefines m2 m2' →
  trefines (asm_link ins1 ins2 m1 m2) (asm_link ins1 ins2 m1' m2').
Proof. move => ??. by apply link_mod_trefines. Qed.

(** ** Relating semantic and syntactic linking *)
Definition asm_link_inv (ins1 ins2 : gmap Z asm_instr) (σ1 : asm_trans.(m_state)) (σ2 : link_case asm_ev * option seq_product_case * asm_state * asm_state) : Prop :=
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

Lemma asm_syn_link_refines_link ins1 ins2:
  ins1 ##ₘ ins2 →
  trefines (asm_mod (asm_syn_link ins1 ins2))
           (asm_link (dom ins1) (dom ins2) (asm_mod ins1) (asm_mod ins2)).
Proof.
  move => Hdisj.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { exact: (λ _, asm_link_inv ins1 ins2). }
  { naive_solver. } { done. }
  move => /= {}n _ Hloop [i1 rs1 mem1 ins1'] [[[σf s] [il rsl meml insl]] [ir rsr memr insr]] [? [? [? Hinv]]].
  case_match; destruct!.
  - destruct i as [|[??|???|???| |?]?].
    + tstep_i => pc ?. case_match eqn: Hunion. 1: move: Hunion => /lookup_union_Some_raw[Hl|[? Hl]].
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
    + tstep_both => *. tstep_s. split!; [done|]. move => *. tend.
      split!. apply: Hloop; [done|]. naive_solver.
  - destruct i as [|[??|???|???| |?]?].
    + tstep_i => pc ?. case_match eqn: Hunion. 1: move: Hunion => /lookup_union_Some_raw[Hl|[? Hl]].
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
    + tstep_both => *. tstep_s. split!; [done|]. move => *. tend.
      split!. apply: Hloop; [done|]. naive_solver.
  - tstep_i => pc???? Hin.
    tstep_s. eexists (EAJump _ _). split!.
    { move: Hin => /lookup_union_Some_raw[?|[??]]; simplify_eq; by simpl_map_decide. }
    move: Hin => /lookup_union_Some_raw[?|[??]]; simplify_eq; simpl_map_decide.
    all: tstep_s; split!; apply: Hloop; naive_solver.
Qed.

Lemma asm_link_refines_syn_link ins1 ins2:
  ins1 ##ₘ ins2 →
  trefines (asm_link (dom ins1) (dom ins2) (asm_mod ins1) (asm_mod ins2))
           (asm_mod (asm_syn_link ins1 ins2)).
Proof.
  move => Hdisj.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { exact: (λ _, flip (asm_link_inv ins1 ins2)). }
  { naive_solver. } { done. }
  move => /= {}n _ Hloop [[[σf ?] [il rsl meml insl]] [ir rsr memr insr]] [i1 rs1 mem1 ins1'] [? [? [? Hinv]]].
  case_match; destruct!.
  - destruct i as [|[??|???|???| |?]?].
    + tstep_i => pc ?. case_match => *; destruct!/=.
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
    + tstep_both => *. destruct!. tstep_s. split!; [done|]. tend.
      tstep_both => *. destruct!; case_match; destruct!/=. tstep_s. split!; [done|]. tend.
      tstep_i => *. simplify_eq/=. apply: Hloop; [done|]. naive_solver.
    + tstep_both => *. tstep_s. split!; [done|]. tend.
      split!. apply: Hloop; [done|]. naive_solver.
  - destruct i as [|[??|???|???| |?]?].
    + tstep_i => pc ?. case_match => *; destruct!/=.
      * tstep_s. split!. erewrite lookup_union_Some_r by done.
        apply: Hloop; [done|]. naive_solver.
      * tstep_s. split!. rewrite lookup_union_l //.
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
    + tstep_both => *. destruct!. tstep_s. split!; [done|]. tend.
      tstep_both => *. destruct!; case_match; destruct!/=. tstep_s. split!; [done|]. tend.
      tstep_i => *. simplify_eq/=. apply: Hloop; [done|]. naive_solver.
    + tstep_both => *. tstep_s. split!;[done|]. tend.
      split!. apply: Hloop; [done|]. naive_solver.
  - tstep_i => -[] /= *; destruct!/=.
    tstep_s.
    repeat case_bool_decide => //.
    all: revert select (_ ∈ dom _) => /elem_of_dom[? Hin];
           split!; [rewrite lookup_union_Some //;naive_solver|].
    all: tstep_i => *; simplify_eq; apply: Hloop; naive_solver.
Qed.

Lemma asm_trefines_implies_ctx_refines insi inss :
  dom insi = dom inss →
  trefines (asm_mod insi) (asm_mod inss) →
  asm_ctx_refines insi inss.
Proof.
  move => Hdom Href C. rewrite /asm_syn_link map_difference_union_r (map_difference_union_r inss).
  apply prepost_mod_trefines. { apply _. }
  etrans. {
    apply asm_syn_link_refines_link. apply map_disjoint_difference_r'.
  }
  etrans. 2: {
    apply asm_link_refines_syn_link. apply map_disjoint_difference_r'.
  }
  rewrite !dom_difference_L Hdom.
  apply asm_link_trefines; [apply _..| |].
  - apply: Href.
  - erewrite map_difference_eq_dom_L => //. apply _.
Qed.

(** * Deeply embedded assembly language *)
Inductive asm_operand :=
| RegisterOp (r : string) | ImmediateOp (z : Z).

Coercion ImmediateOp: Z >-> asm_operand.
Coercion RegisterOp: string >-> asm_operand.

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
| Aalloc (rd : string) (o : asm_operand)
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
  | Aalloc rd o => [
      AllocMem rd (λ rs, op_lookup rs o);
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
