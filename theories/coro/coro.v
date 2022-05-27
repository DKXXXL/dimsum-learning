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

Compute (length saved_registers).
(* Definition saved_registers : list string := *)
(*   ["R19"; "R20"; "R21"; "R22"; "R23"; "R24"; "R25"; "R26"; "R27"; "R28"; "R29"; "SP"]. *)
(* Notation "'gttbl[' n ']'" := (100 + (12 * n))%Z (at level 40). *)
Notation "'gttbl'"     := 100%Z (at level 40).
Notation "'gtcur'"     := 200%Z (at level 40).
(* Notation "'yield_val'" := 300%Z (at level 40). *)
Notation "'stack'"     := 400%Z (at level 40).
Notation "'stksize'"   := 1000000%Z (at level 40).

(***
void gtyield(void)
{
	struct gt *old, *new;

	old = &gttbl[gtcur];
        gtcur = (gtcur+1)%2; // rand()%2;
	new = &gttbl[gtcur];
	gtswtch(old, new);
}

gtswtch.s
        mov     %rsp, 0x00(%rdi)
        mov     %r15, 0x08(%rdi)
        mov     %r14, 0x10(%rdi)
        mov     %r13, 0x18(%rdi)
        mov     %r12, 0x20(%rdi)
        mov     %rbx, 0x28(%rdi)
        mov     %rbp, 0x30(%rdi)

        mov     0x00(%rsi), %rsp
        mov     0x08(%rsi), %r15
        mov     0x10(%rsi), %r14
        mov     0x18(%rsi), %r13
        mov     0x20(%rsi), %r12
        mov     0x28(%rsi), %rbx
        mov     0x30(%rsi), %rbp

        ret
***)
Coercion ImmediateOp: Z >-> asm_operand.
Coercion RegisterOp: string >-> asm_operand.

(* args_registers = ["R0"; "R1"; "R2"; "R3"; "R4"; "R5"; "R6"; "R7"; "R8"] *)
(* tmp_registers = ... + ["R9"; "R10"; "R11"; "R12"; "R13"; "R14"; "R15"; "R16"; "R17"; "R30"; "PC"] *)
(* saved_registers = ["R19"; "R20"; "R21"; "R22"; "R23"; "R24"; "R25"; "R26"; "R27"; "R28"; "R29"; "SP"] *)

Definition gtyield_deep: list deep_asm_instr :=
  [Amov "R9" 0;
   (*** basic setup ***)
   (* R17 := gtcur *)
   Aload "R17" "R9" (gtcur);
   (* R16 := gtnext *)
   Aslt "R16" "R17" 1;

   (* R15 := gttbl[gtcur] *)
   Amul "R9" "R17" 13;
   Aadd "R15" "R9" (gttbl);
   (* R14 := gttbl[gtnext] *)
   Amul "R9" "R16" 13;
   Aadd "R14" "R9" (gttbl);


   (*** store registers to gttbl[gtcur] ***)
   Astore "R19" "R15" 0;
   Astore "R20" "R15" 1;
   Astore "R21" "R15" 2;
   Astore "R22" "R15" 3;
   Astore "R23" "R15" 4;
   Astore "R24" "R15" 5;
   Astore "R25" "R15" 6;
   Astore "R26" "R15" 7;
   Astore "R27" "R15" 8;
   Astore "R28" "R15" 9;
   Astore "R29" "R15" 10;
   Astore "R30" "R15" 11;
   Astore "SP"  "R15" 12;

   (*** load gttbl[gtnext] to registers ***)
   Aload "R19" "R14" 0;
   Aload "R20" "R14" 1;
   Aload "R21" "R14" 2;
   Aload "R22" "R14" 3;
   Aload "R23" "R14" 4;
   Aload "R24" "R14" 5;
   Aload "R25" "R14" 6;
   Aload "R26" "R14" 7;
   Aload "R27" "R14" 8;
   Aload "R28" "R14" 9;
   Aload "R29" "R14" 10;
   Aload "R30" "R14" 11;
   Aload "SP"  "R14" 12;


   (*** argument passing ***)
   (*** already handled; argument 0 register == return register == R0 ***)
   (* Amov "R1" "R0"; *)
   (* Aload "R0" "R9" (yield_val); *)
   (* Astore "R1" "R9" (yield_val); *)

   Aret]
.

(***
int
gtgo(void *f)
{
	struct gt *p;

        p = &gttbl[1];

	/* *&stack[StackSize -  8] = (uint64_t)gtstop; */
	*&stack[StackSize - 16] = (uint64_t)f;
	p->rsp = (uint64_t)&stack[StackSize - 16];

	return 0;
}
***)

(*** simply set p->rsp to be stack, p->pc to be the function ***)

Definition gtgo_deep: list deep_asm_instr :=
  [
    Amov "R9" 0;
    (*** rsp ***)
    Amov "R10" (stack + stksize);
    Astore "R10" "R9" (gttbl + 13 + 12);

    (*** PC ***)
    Astore "R0" "R9" (gttbl + 13 + 11);
    Aret
  ]
.

(* compile *)
(* compile_correct *)
Print Instances Empty.
Goal forall tmp, ((asm_regs (initial_asm_state tmp)) !! "SP") = None.
  intros. cbn. reflexivity.
Qed.
(***
One possible way to give spec to the coroutine library would be by defining an event and its semantic linking. That is, we may able to say sth like:
`coro.asm +asm (imp_to_asm client.imp) <= imp_to_asm (link_yield_event (yield_call_to_yield_event (client.imp)))`
where `yield_call_to_yield_event: module imp_event -> module (imp_event + yield_event)` and
`link_yield_event: module (A + yield_event) -> module A`. Does this make sense to you?
***)


Section coro.
  Inductive coro_event: Type :=
  | ECYield (v: val)
  | ECSpawn (f: string)
  .

  Definition hijack_coro_event (md: module imp_event): module (coro_event + imp_event).
    admit.
  Admitted.

  Definition interp_coro_event {E} (md: module (coro_event + E)): module E.

End coro.
i2a_mem_constant is pointsto
