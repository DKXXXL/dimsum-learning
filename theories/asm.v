Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.filter.
Require Import refframe.product.
Require Import refframe.seq_product.
Require Import refframe.link.
Require Import refframe.prepost.
Require Import refframe.proof_techniques.

Local Open Scope Z_scope.

(** * Assembly language *)
(* see https://modexp.wordpress.com/2018/10/30/arm64-assembly/ or
https://stackoverflow.com/questions/68711164/syscall-invoke-in-aarch64-assembly *)
Definition syscall_arg_regs : list string :=
  ["R0"; "R1"; "R2"; "R3"; "R4"; "R5"; "R6"; "R7"; "R8"].

Definition extract_syscall_args (rs : gmap string Z) : list Z :=
  (λ r, rs !!! r) <$> syscall_arg_regs.

Inductive asm_instr_event :=
| WriteReg (r : string) (f : gmap string Z → Z)
(* ldr r1, [f r2] *)
| ReadMem (r1 r2 : string) (f : Z → Z)
(* str r1, [f r2] *)
| WriteMem (r1 r2 : string) (f : Z → Z)
| Syscall (waiting : bool)
.

Definition asm_instr := list asm_instr_event.

Definition asm_instr_wf (i : asm_instr) : bool :=
  forallb (λ e, if e is Syscall true then false else true) i.

Definition asm_instrs_wf (ins : gmap Z asm_instr) : Prop :=
  map_Forall (λ _, asm_instr_wf) ins.

Inductive asm_state := AsmState {
  asm_cur_instr : option asm_instr;
  asm_regs : gmap string Z;
  asm_mem : gmap Z Z;
  asm_instrs : gmap Z asm_instr;
}.
Add Printing Constructor asm_state.

Definition initial_asm_state (instrs : gmap Z asm_instr) := AsmState None ∅ ∅ instrs.

Inductive asm_ev :=
| EAJump (pc : Z) (regs : gmap string Z) (mem : gmap Z Z)
| EASyscallCall (args : list Z)
| EASyscallRet (ret : Z)
.

Definition asm_event := io_event asm_ev.

Inductive asm_step : asm_state → option asm_event → (asm_state → Prop) → Prop :=
| SWriteReg regs instrs r f es mem:
  asm_step (AsmState (Some (WriteReg r f :: es)) regs mem instrs) None (λ σ',
         is_Some (regs !! r) ∧
         σ' = AsmState (Some es) (<[r := f regs]>regs) mem instrs)
| SReadMem regs instrs r1 r2 f es mem:
  asm_step (AsmState (Some (ReadMem r1 r2 f :: es)) regs mem instrs) None (λ σ', ∃ a,
         regs !! r2 = Some a ∧
         (* mem !! f a = Some v ∧ *)
         is_Some (regs !! r1) ∧
         σ' = AsmState (Some es) (<[r1 := mem !!! f a]>regs) mem instrs)
| SWriteMem regs instrs r1 r2 f es mem:
  asm_step (AsmState (Some (WriteMem r1 r2 f :: es)) regs mem instrs) None (λ σ', ∃ a v,
         regs !! r2 = Some a ∧
         regs !! r1 = Some v ∧
         (* TODO: Should we have the following constraint? *)
         (* is_Some (mem !! f a) ∧ *)
         σ' = AsmState (Some es) regs (<[f a := v]>mem) instrs)
| SSyscallCall regs instrs es mem:
  asm_step (AsmState (Some (Syscall false :: es)) regs mem instrs)
           (Some (Outgoing, EASyscallCall (extract_syscall_args regs)))
           (λ σ', σ' = AsmState (Some (Syscall true :: es)) regs mem instrs)
| SSyscallRet regs instrs es mem ret:
  asm_step (AsmState (Some (Syscall true :: es)) regs mem instrs)
           (Some (Incoming, EASyscallRet ret))
           (λ σ', σ' = AsmState (Some es) (<["R0" := ret]>regs) mem instrs)
| SJumpInternal regs instrs pc es mem:
  regs !! "PC" = Some pc →
  instrs !! pc = Some es →
  asm_step (AsmState (Some []) regs mem instrs) None
           (λ σ', σ' = AsmState (Some es) regs mem instrs)
| SJumpExternal regs instrs pc mem:
  regs !! "PC" = Some pc →
  instrs !! pc = None →
  asm_step (AsmState (Some []) regs mem instrs) (Some (Outgoing, EAJump pc regs mem))
           (λ σ', σ' = AsmState None regs mem instrs)
| SRecvJump regs regs' instrs pc es mem mem':
  regs' !! "PC" = Some pc →
  instrs !! pc = Some es →
  asm_step (AsmState None regs mem instrs) (Some (Incoming, EAJump pc regs' mem'))
           (λ σ', σ' = AsmState (Some es) regs' mem' instrs)
.

Definition asm_module := Mod asm_step.

Global Instance asm_vis_no_all: VisNoAll asm_module.
Proof. move => *. invert_all @m_step; naive_solver. Qed.

(** * tstep *)
Lemma asm_step_WriteReg_i r f es rs ins mem:
  TStepI asm_module (AsmState (Some (WriteReg r f::es)) rs mem ins)
            (λ G, G true None (λ G', is_Some (rs !! r) ∧ G' (AsmState (Some (es)) (<[r:=f rs]>rs) mem ins))).
Proof.
  constructor => ? ?. apply steps_impl_step_end => ???.
  invert_all @m_step. eexists _, _. split_and!; [done|done|].
  move => ? /=. naive_solver.
Qed.
Global Hint Resolve asm_step_WriteReg_i : tstep.

Lemma asm_step_WriteReg_s r f es rs ins mem:
  TStepS asm_module (AsmState (Some (WriteReg r f::es)) rs mem ins)
            (λ G, G None (λ G', is_Some (rs !! r) → G' (AsmState (Some (es)) (<[r:=f rs]>rs) mem ins))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= ?.
  apply: steps_spec_step_end. { econs. }
  move => ? /= [? ->]. naive_solver.
Qed.
Global Hint Resolve asm_step_WriteReg_s : tstep.

Lemma asm_step_ReadMem_i r1 r2 f es rs ins mem:
  TStepI asm_module (AsmState (Some (ReadMem r1 r2 f::es)) rs mem ins)
            (λ G, G true None (λ G',
             ∃ a, rs !! r2 = Some a ∧ is_Some (rs !! r1) ∧ G' (AsmState (Some es) (<[r1:=mem !!! f a]>rs) mem ins))).
Proof.
  constructor => ? ?. apply steps_impl_step_end => ???.
  invert_all @m_step. eexists _, _. split_and!; [done|done|].
  move => ? /=. naive_solver.
Qed.
Global Hint Resolve asm_step_ReadMem_i : tstep.

Lemma asm_step_ReadMem_s r1 r2 f es rs ins mem:
  TStepS asm_module (AsmState (Some (ReadMem r1 r2 f::es)) rs mem ins)
            (λ G, G None (λ G', ∀ a, rs !! r2 = Some a → is_Some (rs !! r1) → G' (AsmState (Some (es)) (<[r1:=mem !!! f a]>rs) mem ins))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= ?.
  apply: steps_spec_step_end. { econs. }
  move => ? /= [? [? [? ->]]]. naive_solver.
Qed.
Global Hint Resolve asm_step_ReadMem_s : tstep.

Lemma asm_step_WriteMem_i r1 r2 f es rs ins mem:
  TStepI asm_module (AsmState (Some (WriteMem r1 r2 f::es)) rs mem ins)
            (λ G, G true None (λ G',
             ∃ a v, rs !! r2 = Some a ∧ rs !! r1 = Some v ∧ G' (AsmState (Some es) rs (<[f a:=v]>mem) ins))).
Proof.
  constructor => ? ?. apply steps_impl_step_end => ???.
  invert_all @m_step. eexists _, _. split_and!; [done|done|].
  move => ? /=. naive_solver.
Qed.
Global Hint Resolve asm_step_WriteMem_i : tstep.

Lemma asm_step_WriteMem_s r1 r2 f es rs ins mem:
  TStepS asm_module (AsmState (Some (WriteMem r1 r2 f::es)) rs mem ins)
            (λ G, G None (λ G', ∀ a v, rs !! r2 = Some a → rs !! r1 = Some v → G' (AsmState (Some es) rs (<[f a:=v]>mem) ins))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= ?.
  apply: steps_spec_step_end. { econs. }
  move => ? /= [? [? [? [? ->]]]]. naive_solver.
Qed.
Global Hint Resolve asm_step_WriteMem_s : tstep.

Lemma asm_step_Syscall_call_i es rs ins mem:
  TStepI asm_module (AsmState (Some (Syscall false::es)) rs mem ins)
            (λ G, G true (Some (Outgoing, EASyscallCall (extract_syscall_args rs)))
                    (λ G', G' (AsmState (Some (Syscall true :: es)) rs mem ins))).
Proof.
  constructor => ? ?. apply steps_impl_step_end => ???.
  invert_all @m_step. eexists _, _. split_and!; [done|done|].
  move => ? /=. naive_solver.
Qed.
Global Hint Resolve asm_step_Syscall_call_i : tstep.

Lemma asm_step_Syscall_call_s es rs ins mem:
  TStepS asm_module (AsmState (Some (Syscall false::es)) rs mem ins)
            (λ G, G (Some (Outgoing, EASyscallCall (extract_syscall_args rs)))
                    (λ G', G' (AsmState (Some (Syscall true :: es)) rs mem ins))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= ?.
  apply: steps_spec_step_end. { econs. } naive_solver.
Qed.
Global Hint Resolve asm_step_Syscall_call_s : tstep.

Lemma asm_step_Syscall_ret_i es rs ins mem:
  TStepI asm_module (AsmState (Some (Syscall true::es)) rs mem ins)
            (λ G, ∀ ret, G true (Some (Incoming, EASyscallRet ret))
                    (λ G', G' (AsmState (Some es) (<["R0" := ret]> rs) mem ins))).
Proof.
  constructor => ? ?. apply steps_impl_step_end => ???.
  invert_all @m_step. eexists _, _. split_and!; [naive_solver|done|].
  move => ? /=. naive_solver.
Qed.
Global Hint Resolve asm_step_Syscall_ret_i : tstep.

Lemma asm_step_Syscall_ret_s es rs ins mem:
  TStepS asm_module (AsmState (Some (Syscall true::es)) rs mem ins)
            (λ G, ∃ ret, G (Some (Incoming, EASyscallRet ret))
                    (λ G', G' (AsmState (Some es) (<["R0":=ret]> rs) mem ins))).
Proof.
  constructor => ? [??]. eexists _, _. split; [done|] => ? /= ?.
  apply: steps_spec_step_end. { econs. } naive_solver.
Qed.
Global Hint Resolve asm_step_Syscall_ret_s : tstep.

Lemma asm_step_Jump_i rs ins mem:
  TStepI asm_module (AsmState (Some []) rs mem ins) (λ G,
    ∀ pc, rs !! "PC" = Some pc →
          if ins !! pc is Some i then
            G true None (λ G', G' (AsmState (Some i) rs mem ins))
          else
            G true (Some (Outgoing, EAJump pc rs mem)) (λ G', G' (AsmState None rs mem ins))
   ).
Proof.
  constructor => ? HG. apply steps_impl_step_end => ???.
  invert_all @m_step; specialize (HG _ ltac:(done)); simplify_option_eq.
  all: eexists _, _; split_and!; [done..|]; naive_solver.
Qed.
Global Hint Resolve asm_step_Jump_i : tstep.

Lemma asm_step_Jump_s rs ins mem:
  TStepS asm_module (AsmState (Some []) rs mem ins) (λ G,
    ∃ pc, rs !! "PC" = Some pc ∧
      if ins !! pc is Some i then
        G None (λ G', G' (AsmState (Some i) rs mem ins))
      else
        G (Some (Outgoing, EAJump pc rs mem)) (λ G', G' (AsmState None rs mem ins))).
Proof.
  constructor => ?[?[??]]. case_match.
  all: eexists _, _; split; [done|] => ? /= ?.
  all: apply: steps_spec_step_end; [ by econs |] => ? ->; done.
Qed.
Global Hint Resolve asm_step_Jump_s : tstep.

Lemma asm_step_None_i rs ins mem:
  TStepI asm_module (AsmState None rs mem ins) (λ G,
    ∀ pc i rs' mem',
      rs' !! "PC" = Some pc →
      ins !! pc = Some i →
      G true (Some (Incoming, EAJump pc rs' mem')) (λ G', G' (AsmState (Some i) rs' mem' ins))
   ).
Proof.
  constructor => ? HG. apply steps_impl_step_end => ???.
  invert_all @m_step. eexists _, _. split_and!; [naive_solver..|]. naive_solver.
Qed.
Global Hint Resolve asm_step_None_i : tstep.

Lemma asm_step_None_s rs mem ins:
  TStepS asm_module (AsmState None rs mem ins) (λ G,
    ∃ pc i rs' mem', rs' !! "PC" = Some pc ∧
      ins !! pc = Some i ∧
      G (Some (Incoming, EAJump pc rs' mem')) (λ G', G' (AsmState (Some i) rs' mem' ins))).
Proof.
  constructor => ??. destruct_all!. eexists _, _. split; [done|] => ? /= ?.
  apply: steps_spec_step_end. { by econs. } naive_solver.
Qed.
Global Hint Resolve asm_step_None_s : tstep.

(** * closing *)
Inductive asm_closed_event : Type :=
| EACStart (pc : Z) (rs : gmap string Z) (mem : gmap Z Z)
| EACSyscallCall (args : list Z)
| EACSyscallRet (ret : Z)
.

(* s tells us if we already started the execution *)
Definition asm_closed_pre (e : asm_closed_event) (s : bool) :
 prepost (asm_event * bool) unitUR :=
  if s then
    match e with
    | EACSyscallRet ret => pp_end ((Incoming, EASyscallRet ret), true)
    | _ => pp_prop False (pp_quant $ λ e', pp_end e')
    end
  else
    match e with
    | EACStart pc rs mem =>
        pp_prop (rs !! "PC" = Some pc) $
        pp_end ((Incoming, EAJump pc rs mem), true)
    | _ => pp_prop False (pp_quant $ λ e', pp_end e')
    end
.

Definition asm_closed_post (e : asm_event) (s : bool) :
  prepost (asm_closed_event * bool) unitUR :=
  match e with
  | (Outgoing, EASyscallCall args) => pp_end (EACSyscallCall args, s)
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
  ∀ C, asm_instrs_wf C →
       trefines (MS (asm_closed asm_module)
                    (initial_asm_closed_state asm_module (initial_asm_state (asm_link instrsi C))))
                (MS (asm_closed asm_module)
                    (initial_asm_closed_state asm_module (initial_asm_state (asm_link instrss C)))).

(** * semantic linking *)

(* State s says whether we are currently in the environment and expecting a syscall return *)
(* TODO: instead of bool have option that tracks which side was last *)
Definition asm_prod_filter (ins1 ins2 : gset Z) : seq_product_state → option seq_product_state → asm_ev → seq_product_state → option seq_product_state → asm_ev → Prop :=
  λ p s e p' s' e',
    e' = e ∧
    match e with
    | EAJump pc rs mem =>
        s = None ∧
        s' = None ∧
        p' = (if bool_decide (pc ∈ ins1) then SPLeft else if bool_decide (pc ∈ ins2) then SPRight else SPNone) ∧
        rs !! "PC" = Some pc ∧
        p ≠ p'
    | EASyscallCall _ =>
        s = None ∧
        s' = Some p ∧
        p' = SPNone ∧
        p ≠ SPNone
    | EASyscallRet _ =>
        s = Some p' ∧
        s' = None ∧
        p' ≠ SPNone ∧
        p  = SPNone
    end.
Arguments asm_prod_filter _ _ _ _ _ _ _ _ /.

Definition asm_prod (ins1 ins2 : gset Z) (m1 m2 : module asm_event) : module asm_event :=
  mod_link (asm_prod_filter ins1 ins2) m1 m2.

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
  | MLFLeft => ∃ i, i1 = Some i ∧ il = i1 ∧ rsl = rs1 ∧ meml = mem1 ∧ ir = None ∧ asm_instr_wf i
  | MLFRight => ∃ i, i1 = Some i ∧ ir = i1 ∧ rsr = rs1 ∧ memr = mem1 ∧ il = None ∧ asm_instr_wf i
  | MLFNone => i1 = None ∧ ir = None ∧ il = None
  | _ => False
  end.

Lemma asm_link_refines_prod ins1 ins2:
  ins1 ##ₘ ins2 →
  asm_instrs_wf ins1 →
  asm_instrs_wf ins2 →
  trefines (MS asm_module (initial_asm_state (asm_link ins1 ins2)))
           (MS (asm_prod (dom _ ins1) (dom _ ins2) asm_module asm_module) (MLFNone, None, initial_asm_state ins1, initial_asm_state ins2)).
Proof.
  move => Hdisj ??.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { exact: (λ _, asm_link_prod_inv ins1 ins2). }
  { naive_solver. } { done. }
  move => /= {}n _ Hloop [i1 rs1 mem1 ins1'] [[[σf s] [il rsl meml insl]] [ir rsr memr insr]] [? [? [? Hinv]]].
  case_match; destruct_all?; simplify_eq.
  - destruct i as [|[??|???|???|[]]?].
    + tstep_i => pc ?. case_match as Hunion. 1: move: Hunion => /lookup_union_Some_raw[Hl|[? Hl]].
      * tstep_s. split!. simplify_option_eq. apply: Hloop; [done|]. naive_solver.
      * tstep_s. split!. simpl_map_decide. simplify_option_eq. split! => /=.
        tstep_s. split!. apply: Hloop; [done|]. naive_solver.
      * move: Hunion => /lookup_union_None[??]. tstep_s.
        split!. simpl_map_decide. simplify_option_eq. split! => /=.
        apply: Hloop; [done|]. naive_solver.
    + tstep_both. tstep_s => *. tend. split!. apply: Hloop; [done|]. naive_solver.
    + tstep_both. tstep_s => *. tend. split!. apply: Hloop; [done|]. naive_solver.
    + tstep_both. tstep_s => *. tend. split!. apply: Hloop; [done|]. naive_solver.
    + naive_solver.
    + tstep_both. tstep_s => *. split!; [done|]. tend.
      tstep_both => *. tstep_s => *. split!; [|done|]; [done|].
      tstep_s. split!. tend. apply: Hloop; [done|]. naive_solver.
  - destruct i as [|[??|???|???|[]]?].
    + tstep_i => pc ?. case_match as Hunion. 1: move: Hunion => /lookup_union_Some_raw[Hl|[? Hl]].
      * have ?: ins2 !! pc = None by apply: map_disjoint_Some_l.
        tstep_s. split!. simpl_map_decide. simplify_option_eq. split! => /=.
        tstep_s. split!. apply: Hloop; [done|]. naive_solver.
      * tstep_s. split!. simplify_option_eq. apply: Hloop; [done|]. naive_solver.
      * move: Hunion => /lookup_union_None[??]. tstep_s.
        split!. simpl_map_decide. simplify_option_eq. split!.
        apply: Hloop; [done|]. naive_solver.
    + tstep_both. tstep_s => *. tend. split!. apply: Hloop; [done|]. naive_solver.
    + tstep_both. tstep_s => *. tend. split!. apply: Hloop; [done|]. naive_solver.
    + tstep_both. tstep_s => *. tend. split!. apply: Hloop; [done|]. naive_solver.
    + naive_solver.
    + tstep_both. tstep_s => *. split!; [done|]. tend.
      tstep_both => *. tstep_s => *. split!; [|done|]; [done|].
      tstep_s. split!. tend. apply: Hloop; [done|]. naive_solver.
  - tstep_i => pc???? Hin.
    tstep_s. eexists (EAJump _ _ _). split!.
    { move: Hin => /lookup_union_Some_raw[?|[??]]; by simpl_map_decide. }
    move: Hin => /lookup_union_Some_raw[?|[??]]; simpl_map_decide.
    all: tstep_s; split!; apply: Hloop; naive_solver.
Qed.

Lemma asm_prod_refines_link ins1 ins2:
  ins1 ##ₘ ins2 →
  asm_instrs_wf ins1 →
  asm_instrs_wf ins2 →
  trefines (MS (asm_prod (dom _ ins1) (dom _ ins2) asm_module asm_module) (MLFNone, None, initial_asm_state ins1, initial_asm_state ins2))
           (MS asm_module (initial_asm_state (asm_link ins1 ins2))).
Proof.
  move => Hdisj ??.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { exact: (λ _, flip (asm_link_prod_inv ins1 ins2)). }
  { naive_solver. } { done. }
  move => /= {}n _ Hloop [[[σf ?] [il rsl meml insl]] [ir rsr memr insr]] [i1 rs1 mem1 ins1'] [? [? [? Hinv]]].
  case_match; destruct_all?; simplify_eq.
  - destruct i as [|[??|???|???|[]]?].
    + tstep_i => pc ?. case_match => *; destruct_all?; simplify_eq/=.
      * tstep_s. split!. erewrite lookup_union_Some_l by done.
        apply: Hloop; [done|]. naive_solver.
      * tstep_s. split!. rewrite lookup_union_r //.
        destruct (ins2 !! pc) eqn:? => /=; simpl_map_decide.
        -- tstep_i => *; simplify_eq. apply: Hloop; [done|]. naive_solver.
        -- split!. apply: Hloop; [done|]. naive_solver.
    + tstep_both => *. tstep_s => ?. tend. split!. apply: Hloop; [done|]. naive_solver.
    + tstep_both => *. tstep_s => ?. tend. split!. apply: Hloop; [done|]. naive_solver.
    + tstep_both => *. tstep_s => ?. tend. split!. apply: Hloop; [done|]. naive_solver.
    + naive_solver.
    + tstep_both => *. destruct_all?; simplify_eq. tstep_s. split!; [done|]. tend.
      tstep_both => *. destruct_all?; case_match; destruct_all?; simplify_eq/=. tstep_s. split!; [done|]. tend.
      tstep_i => *. simplify_eq/=. apply: Hloop; [done|]. naive_solver.
  - destruct i as [|[??|???|???|[]]?].
    + tstep_i => pc ?. case_match => *; destruct_all?; simplify_eq/=.
      * tstep_s. split!. erewrite lookup_union_Some_r by done.
        apply: Hloop; [done|]. naive_solver.
      * tstep_s. split!. rewrite lookup_union_l' //.
        destruct (ins1 !! pc) eqn:? => /=; simpl_map_decide.
        -- tstep_i => *; simplify_eq. apply: Hloop; [done|]. naive_solver.
        -- split!. apply: Hloop; [done|]. naive_solver.
    + tstep_both => *. tstep_s => ?. tend. split!. apply: Hloop; [done|]. naive_solver.
    + tstep_both => *. tstep_s => ?. tend. split!. apply: Hloop; [done|]. naive_solver.
    + tstep_both => *. tstep_s => ?. tend. split!. apply: Hloop; [done|]. naive_solver.
    + naive_solver.
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
  asm_instrs_wf insi →
  asm_instrs_wf inss →
  trefines (MS asm_module (initial_asm_state insi)) (MS asm_module (initial_asm_state inss)) →
  asm_ctx_refines insi inss.
Proof.
  move => Hdom ?? Href C ?. rewrite /asm_link map_difference_union_r (map_difference_union_r inss).
  apply mod_seq_map_trefines. { apply _. } { apply _. }
  etrans. {
    apply asm_link_refines_prod; [apply map_disjoint_difference_r'|done|].
    move => ??/lookup_difference_Some. naive_solver. }
  etrans. 2: {
    apply asm_prod_refines_link; [apply map_disjoint_difference_r'|done|].
    move => ??/lookup_difference_Some. naive_solver. }
  rewrite !dom_difference_L Hdom.
  apply asm_prod_trefines; [apply _..| |].
  - apply: Href.
  - erewrite map_difference_eq_dom_L => //. apply _.
Qed.

Require Import refframe.itree.
Local Ltac go :=
  clear_itree.
Local Ltac go_s :=
  tstep_s; go.
Local Ltac go_i :=
  tstep_i; go.

(* TODO: Get rid of Some in recursive call (maybe by passing an itree to t instead of the +'? ) *)
(* TODO: prove merging of two asm loops (should just be all choice between the two implementations ) *)
Definition asm_loop (ins : list Z)
   (t : Z → gmap string Z → gmap Z Z → itree (callE
     (option (Z * gmap string Z * gmap Z Z)) (Z * gmap string Z * gmap Z Z) +' moduleE asm_event unit) (Z * gmap string Z * gmap Z Z))
  : itree (moduleE asm_event unit) unit :=
  rec (λ a,
    '(pc, rs, mem) ← (
       if a is Some (npc, nrs, nmem) then
         if bool_decide (npc ∈ ins) then
           Ret (npc, nrs, nmem)
         else
           translate (inr_) (TVis (Outgoing, EAJump npc nrs nmem));;;;
           pc ← translate (inr_) (TExist Z);;;
           rs ← translate (inr_) (TExist _);;;
           mem ← translate (inr_) (TExist _);;;
           translate (inr_) (TVis (Incoming, EAJump pc rs mem));;;;
           Ret (pc, rs, mem)
        else
          pc ← translate (inr_) (TExist Z);;;
          rs ← translate (inr_) (TExist _);;;
          mem ← translate (inr_) (TExist _);;;
          translate (inr_) (TVis (Incoming, EAJump pc rs mem));;;;
          Ret (pc, rs, mem)
     );;;
    translate (inr_) (TAssert (pc ∈ ins));;;;
    (* The env can choose if this call should be treated as a call or a return. *)
    b ← translate (inr_) (TAll bool);;;
    if b then Ret (pc, rs, mem) else
      r ← t pc rs mem;;;
      call (Some r)
    ) None;;;; TUb.

Lemma tsim_asm_loop n b rs mem ins t insaddrs:
  (∀ z, z ∈ insaddrs ↔ is_Some (ins !! z)) →
  (∀ n rc pc' rs' mem' i k,
      rs' !! "PC" = Some pc' →
      ins !! pc' = Some i →
      (∀ pc'' rs1'' rs2'' mem1'' mem2'' h',
         rs1'' = rs2'' →
         mem1'' = mem2'' →
         rs1'' !! "PC" = Some pc'' →
          (∀ pc''' rs''' mem''' i,
              rs''' !! "PC" = Some pc''' → ins !! pc''' = Some i →
              AsmState (Some i) rs''' mem''' ins ⪯{asm_module, mod_itree asm_event (), n, b} (h' (pc''', rs''', mem'''), ())) →
          (AsmState (Some []) rs1'' mem1'' ins)
            ⪯{asm_module, mod_itree asm_event (), n, true}
          (y ← rec rc (Some (pc'', rs2'', mem2''));;; h' y, ())) →
      (∀ pc rs1 rs2 mem1 mem2,
          rs1 = rs2 →
          mem1 = mem2 →
          rs1 !! "PC" = Some pc →
          tsim n true asm_module (mod_itree asm_event ()) (AsmState (Some []) rs1 mem1 ins) tnil (k (pc, rs2, mem2), ())) →
    AsmState (Some i) rs' mem' ins ⪯{asm_module, mod_itree asm_event (), n, true}
       (r ← interp (recursive rc) (t pc' rs' mem');;; k r, ())) →
  (** Then we can prove an asm_loop *)
  AsmState None rs mem ins ⪯{asm_module, mod_itree asm_event (), n, b} (asm_loop insaddrs t, ()).
Proof.
  rewrite /asm_loop => Hins Hl. set rc := (X in (rec X)).
  apply (tsim_remember_rec (mi:=asm_module)
   (λ a σi s,
     if a is Some (pc, rs, mem) then
       σi = AsmState (Some []) rs mem ins ∧ rs !! "PC" = Some pc
     else
       ∃ rs mem, σi = AsmState None rs mem ins
   )
   (λ σi '(pc, rs, mem) s', ∃ i, σi = AsmState (Some i) rs mem ins ∧ rs !! "PC" = Some pc ∧ ins !! pc = Some i)).
  { naive_solver. }
  { move => ????. go_s. done. }
  move => {}n _ Hloop σi [] CONT a Ha HCONT.
  destruct a as [[[pc' rs'] mem']|]. 2: {
    move: Ha => [{}rs [{}mem ?]]. subst.
    tstep_i => pc i {}rs {}mem HPC Hi.
    rewrite {1}rec_as_interp {2}/rc.
    go_s. eexists _. go.
    go_s. eexists _. go.
    go_s. eexists _. go.
    go_s. split; [done|]. go.
    go_s. split. { apply Hins. naive_solver. } go.
    go_s => -[]; go.
    { go_s. apply: tsim_mono_b. revert select (eqit eq _ _ _ _) => ->. apply HCONT. naive_solver. }
    revert select (eqit eq _ _ _ _) => ->. rewrite interp_bind bind_bind.
    apply: Hl; [done..| |].
    - move => ??????????. subst. apply Hloop; [done|].
      move => ? [[rs' pc'] mem'] []. naive_solver.
    - move => ????????. rewrite interp_recursive_call.
      apply Hloop. { naive_solver. }
      move => ? [[??]?] [] [?[??]]. apply: HCONT. naive_solver.
  }
  destruct Ha. simplify_eq.
  tstep_i => pc HPC. simplify_eq.
  case_match.
  - rewrite {1}rec_as_interp {2}/rc. rewrite bool_decide_true. 2: { apply Hins. naive_solver. }
    go_s. split. { apply Hins. naive_solver. } go.
    go_s => -[]; go.
    { go_s. apply: tsim_mono_b. revert select (eqit eq _ _ _ _) => ->. apply HCONT. naive_solver. }
    revert select (eqit eq _ _ _ _) => ->. rewrite interp_bind bind_bind.
    apply: Hl; [done..| |].
    + move => ??????????. subst. apply Hloop; [done|].
      move => ? [[??] ?] []. naive_solver.
    + move => ????????. rewrite interp_recursive_call.
      apply Hloop. { naive_solver. }
      move => ? [[??]?] [] [?[??]]. apply: HCONT. naive_solver.
  - rewrite {1}rec_as_interp {2}/rc. rewrite bool_decide_false. 2: { move => /Hins[??]. naive_solver. }
    go_s. split; [done|]. go.
    tstep_i => pc i {}rs {}mem HPC Hi.
    go_s. eexists _. go.
    go_s. eexists _. go.
    go_s. eexists _. go.
    go_s. split; [done|]. go.
    go_s. split. { apply Hins. naive_solver. } go.
    go_s => -[]; go.
    { go_s. apply: tsim_mono_b. revert select (eqit eq _ _ _ _) => ->. apply HCONT. naive_solver. }
    revert select (eqit eq _ _ _ _) => ->. rewrite interp_bind bind_bind.
    apply: Hl; [done..| |].
    + move => ??????????. subst. apply Hloop; [done|].
      move => ? [[??] ?] []. naive_solver.
    + move => ????????. rewrite interp_recursive_call.
      apply Hloop. { naive_solver. }
      move => ? [[??]?] [] [?[??]]. apply: HCONT. naive_solver.
Qed.

Module asm_examples.
  Local Open Scope Z_scope.
  Definition asm_mul : gmap Z asm_instr :=
    <[ 100 := [
          (* mul R1, R1, R2 *)
          WriteReg "R1" (λ rs, rs !!! "R1" * rs !!! "R2");
          WriteReg "PC" (λ rs, rs !!! "PC" + 4)
      ] ]> $
    <[ 104 := [
          (* ret *)
          WriteReg "PC" (λ rs, rs !!! "R30")
      ] ]> $ ∅.

  Definition itree_mul : itree (moduleE asm_event unit) unit :=
    asm_loop [100; 104] (λ pc rs mem,
       if bool_decide (pc = 100) then
         r1 ← translate (inr_) (TAssumeOpt (rs !! "R1"));;;
         r2 ← translate (inr_) (TAssumeOpt (rs !! "R2"));;;
         r30 ← translate (inr_) (TAssumeOpt (rs !! "R30"));;;
         Ret (r30, (<["PC":=r30]> $ <["R1":=r1 * r2]> $ rs), mem)
       else if bool_decide (pc = 104) then
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

    go_s => r1 HR1; go.
    go_s => r2 HR2; go.
    go_s => r30 HR30; go.
    go_s.
    tstep_i; simplify_map_eq'. split!.
    tstep_i; simplify_map_eq'. split!.
    tstep_i => ??; simplify_map_eq'.
    tstep_i; simplify_map_eq'. split!.
    revert select (eqit eq _ _ _ _) => ->.
    apply HCONT; simplify_map_eq => //.
  Qed.

  Definition asm_mul_client : gmap Z asm_instr :=
    <[ 200 := [
          (* mov R1, 2; mov R2, 2; *)
          WriteReg "R1" (λ rs, 2);
          WriteReg "R2" (λ rs, 2);
          WriteReg "PC" (λ rs, rs !!! "PC" + 4)
      ] ]> $
    <[ 204 := [
          (* mov R29, R30; *)
          WriteReg "R29" (λ rs, rs !!! "R30");
          WriteReg "PC" (λ rs, rs !!! "PC" + 4)
      ] ]> $
    <[ 208 := [
          (* bl 100; *)
          WriteReg "R30" (λ rs, rs !!! "PC" + 4);
          WriteReg "PC" (λ rs, 100)
      ] ]> $
    <[ 212 := [
          (* mov R30, R29; *)
          WriteReg "R30" (λ rs, rs !!! "R29");
          WriteReg "PC" (λ rs, rs !!! "PC" + 4)
      ] ]> $
    <[ 216 := [
          (* ret; *)
          WriteReg "PC" (λ rs, rs !!! "R30")
      ] ]> $ ∅.

  Definition itree_mul_client : itree (moduleE asm_event unit) unit :=
    asm_loop [200; 204; 208; 212; 216] (λ pc rs mem,
       if bool_decide (pc = 200) then
         translate (inr_) (TAssume (is_Some (rs !! "R1")));;;;
         translate (inr_) (TAssume (is_Some (rs !! "R2")));;;;
         translate (inr_) (TAssume (is_Some (rs !! "R29")));;;;
         r30 ← translate (inr_) (TAssumeOpt (rs !! "R30"));;;
         r29' ← translate (inr_) (TExist Z);;;
         (* translate (inr_) (TVis (EAJump 100 (<["PC":=100]> $ <["R30":= 212]> $ <["R29":= r29']> $ <["R2":= 2]> $ <["R1":= 2]> $ rs)));;;; *)
         '(pc', rs', mem') ← call (Some (100, (<["PC":=100]> $ <["R30":= 212]> $ <["R29":= r29']> $ <["R2":= 2]> $ <["R1":= 2]> $ rs), mem));;;
         translate (inr_) (TAssume (pc' = 212));;;;
         translate (inr_) (TAssume (is_Some (rs' !! "R30")));;;;
         translate (inr_) (TAssume (rs' !! "R29" = Some r29'));;;;
         translate (inr_) (TAssume (r30 ≠ 200 ∧ r30 ≠ 204 ∧ r30 ≠ 208 ∧ r30 ≠ 212 ∧ r30 ≠ 216));;;;
         r30' ← translate (inr_) (TExist Z);;;
         (* translate (inr_) (TVis (EAJump r30 (<["PC":= r30]> $ <["R30":= r30']> rs')));;;; *)
         Ret (r30, (<["PC":= r30]> $ <["R30":= r30']> rs'), mem')
       else if bool_decide (pc = 204) then translate (inr_) TUb
       else if bool_decide (pc = 208) then translate (inr_) TUb
       else if bool_decide (pc = 212) then translate (inr_) TUb
       else if bool_decide (pc = 216) then translate (inr_) TUb
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

    go_s => -[r1 HR1]; go.
    go_s => -[r2 HR2]; go.
    go_s => -[r29 HR29]; go.
    go_s => r30 HR30; go.

    tstep_i; simplify_map_eq'. split!.
    tstep_i; simplify_map_eq'. split!.
    tstep_i; simplify_map_eq'. split!.
    tstep_i => ??; simplify_map_eq'.
    tstep_i; simplify_map_eq'. split!.
    tstep_i; simplify_map_eq'. split!.
    tstep_i => ??; simplify_map_eq'.
    tstep_i; simplify_map_eq'. split!.
    tstep_i; simplify_map_eq'. split!.
    sort_map_insert; simplify_map_eq'.
    go_s. eexists r30; go.
    go_s.
    revert select (eqit eq _ _ _ _) => ->.
    apply Hloop. { by sort_map_insert. } { done. } { by simplify_map_eq. }
    move => pc' rs'' mem'' i HPC' Hi'.
    go_s => ?; go; subst. unfold asm_mul_client in Hi'. simplify_map_eq.
    go_s => -[r30'' HR30'']; go.
    go_s => ?; go.
    go_s => -[?[?[?[??]]]]; go.
    tstep_i; simplify_map_eq'. split!.
    tstep_i; simplify_map_eq'. split!.
    tstep_i => ??; simplify_map_eq'.
    tstep_i; simplify_map_eq'. split!.
    go_s. eexists _; go.
    go_s. revert select (eqit eq _ _ _ _) => ->.
    apply HCONT; [done..|]. by simplify_map_eq.
  Qed.
End asm_examples.
