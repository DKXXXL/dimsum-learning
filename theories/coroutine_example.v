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
Require Import refframe.coroutine.
Require Import refframe.compiler.compiler.

(***
void stream_inner(int n) {
  gtyield_with_val(n);
  stream_inner(n+1);
}

void stream()
{
  stream_inner(0);
}

int main(void)
{
  gtgo(stream);
  for(int i=0; i<5; i++) {
    int v = gtyield_with_val(-1);
    printf("v is : %d\n", v);
  }
}
***)

Definition stream_addr: Z := 400.
Definition main_addr: Z := 500.
Definition print_addr: Z := 600.

Definition stream_imp: fndef := {|
  fd_args := [("n")];
  fd_vars := [];
  fd_body := LetE "_" (imp.Call "yield" [Var "n"]) $
             (imp.Call "stream" [(BinOp (Var "n") AddOp (Val $ ValNum 1))]);
  fd_static := I
|}.

Definition main_imp: fndef := {|
  fd_args := [];
  fd_vars := [];
  fd_body := LetE "x" (imp.Call "yield" [Val $ ValNum 0]) $
             LetE "_" (imp.Call "print" [(Var "x")]) $
             LetE "y" (imp.Call "yield" [Val $ ValNum 0]) $
             LetE "_" (imp.Call "print" [(Var "y")]) $
             (Val $ ValNum (-1));
  fd_static := I
|}.

Definition all_f2i : gmap string Z :=
  <["yield"  := yield_addr]> $
  <["stream" := stream_addr]> $
  <["main"   := main_addr]> $
  <["print"  := print_addr]> $
  ∅.

Definition stream_asm : gmap Z asm_instr :=
  deep_to_asm_instrs stream_addr ltac:(i2a_compile all_f2i stream_imp).

Definition main_asm : gmap Z asm_instr :=
  deep_to_asm_instrs main_addr ltac:(i2a_compile all_f2i main_imp).

Lemma stream_asm_refines_imp :
  trefines (MS asm_module (initial_asm_state stream_asm))
           (MS (imp_to_asm (dom _ stream_asm) {["stream"]} all_f2i imp_module)
               (initial_imp_to_asm_state ∅ imp_module (initial_imp_state (<["stream" := stream_imp]> ∅)))).
Proof.
  apply: compile_correct; [|done|..].
  - by vm_compute.
  - by vm_compute.
  - move => ??. rewrite /all_f2i !lookup_insert_Some !lookup_empty.
    move => ?. destruct_all?; simplify_eq; compute_done.
Qed.

Lemma main_asm_refines_imp :
  trefines (MS asm_module (initial_asm_state main_asm))
           (MS (imp_to_asm (dom _ main_asm) {["main"]} all_f2i imp_module)
               (initial_imp_to_asm_state ∅ imp_module (initial_imp_state (<["main" := main_imp]> ∅)))).
Proof.
  apply: compile_correct; [|done|..].
  - by vm_compute.
  - by vm_compute.
  - move => ??. rewrite /all_f2i !lookup_insert_Some !lookup_empty.
    move => ?. destruct_all?; simplify_eq; compute_done.
Qed.
