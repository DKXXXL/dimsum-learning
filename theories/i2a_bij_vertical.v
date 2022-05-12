Require Export iris.algebra.cmra.
Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.filter.
Require Import refframe.product.
Require Import refframe.seq_product.
Require Import refframe.link.
Require Import refframe.prepost.
Require Import refframe.proof_techniques.
Require Import refframe.imp.
Require Import refframe.asm.
Require Import refframe.imp_to_asm.
Require Import refframe.imp_heap_bij_own.

Local Open Scope Z_scope.

Lemma i2a_bij_vertical m σ `{!VisNoAll m} ins fns f2i gp:
  trefines (MS (imp_to_asm ins fns f2i gp (imp_heap_bij m))
               (initial_imp_to_asm_state (imp_heap_bij m) (initial_imp_heap_bij_state m σ)))
           (MS (imp_to_asm ins fns f2i gp m)
               (initial_imp_to_asm_state m σ))
.
Proof.
  unshelve apply: mod_prepost_combine. {
    exact (λ pl '(I2A csa lra) _ '(I2A cs lr) Pa Pb P,
      csa = cs ∧
      lra = lr ∧
    if pl is Env then
      True
    else
      True
). }
  { split!. }
  all: move => [csa lra] [] [cs lr] Pa Pb P [? e] ?/=; destruct_all?; simplify_eq.
  - move: e => []//= pc regs mem b ? h. move: b => [] /=.
    + move => i f args ???? P' HP'. eexists true => /=.
      (* split!. *)
      admit.
    + move => v av rs' cs' ?? P' HP'. eexists false => /=. simplify_eq.
      (* split!. *)
      admit.
  - move => vs hb' Pb' HPb' ? i rs' mem'.
    destruct e as [fn args h|v h]; simplify_eq/=.
    + move => ret ????? Pa' HPa'.
      (* split!. *)
      admit.
    + move => av lr' cs' ??? Pa' HPa'. simplify_eq/=.
      (* split!. *)
      admit.
Admitted.
