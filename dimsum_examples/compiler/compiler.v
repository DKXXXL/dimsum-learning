From dimsum.core Require Export proof_techniques.
From dimsum.examples Require Import imp asm imp_to_asm i2a_bij_vertical.
From dimsum.examples.compiler Require Import monad linear_imp ssa linearize mem2reg codegen.

Local Open Scope Z_scope.
Set Default Proof Using "Type".

Lemma tmp_var_ne_ssa_var n1 s n2 :
  tmp_var n1 ≠ ssa_var s n2.
Proof.
  suff : last (string_to_list (tmp_var n1)) ≠ last (string_to_list (ssa_var s n2)).
  { move => ? /string_list_eq?. congruence. }
  rewrite /tmp_var /ssa_var !string_to_list_app !last_app /=.
  rewrite pretty_N_last /pretty_N_char. by repeat case_match.
Qed.

Inductive compile_error :=
| LinearizeError (e : ci2a_linearize.error)
| CodegenError (e : ci2a_codegen.error)
.

Definition compile_ssa (fn : fndef) : static_fndef :=
  let static := fndef_to_static_fndef fn in
  ci2a_ssa.pass_fn static.

Definition compile_linear (fn : fndef) : compiler_success compile_error lfndef :=
  let ssa := compile_ssa fn in
  compiler_success_fmap_error LinearizeError (ci2a_linearize.pass_fn ssa).

Definition compile_mem2reg (fn : fndef) : compiler_success compile_error lfndef :=
  ci2a_mem2reg.pass_fn <$> (compile_linear fn).

Definition compile (f2i : gmap string Z) (fn : fndef) : compiler_success compile_error (list deep_asm_instr) :=
  opt ← compile_mem2reg fn;
  compiler_success_fmap_error CodegenError (ci2a_codegen.pass_fn f2i opt).

Lemma compile_correct f2i f fn dins ins a:
  compile f2i fn = CSuccess dins →
  ins = deep_to_asm_instrs a dins →
  f2i !! f = Some a →
  map_Forall (λ f' i', ins !! i' = None ↔ f' ≠ f) f2i →
  trefines (MS asm_module (initial_asm_state ins))
           (MS (imp_to_asm (dom _ ins) {[f]} f2i imp_module)
               (initial_imp_to_asm_state ∅ imp_module (initial_imp_state (<[f := fn]> ∅)))).
Proof.
  unfold compile.
  move => /compiler_success_bind_success[?[/compiler_success_fmap_success[?[/compiler_success_fmap_error_success ??]] /compiler_success_fmap_error_success?]]. simplify_eq.
  move => ??.
  etrans. {
    apply: ci2a_codegen.pass_fn_correct; [done..| |done].
    apply: ci2a_mem2reg.NoDup_pass_fn.
    erewrite ci2a_linearize.pass_fn_args; [|done].
    erewrite ci2a_linearize.pass_fn_vars; [|done]. apply ci2a_ssa.pass_fn_args_NoDup.
  }
  etrans. {
    apply: imp_to_asm_trefines.
    apply ci2a_mem2reg.pass_fn_correct.
    erewrite ci2a_linearize.pass_fn_args; [|done].
    erewrite ci2a_linearize.pass_fn_vars; [|done].
    apply ci2a_ssa.pass_fn_args_NoDup.
  }
  etrans. { apply: i2a_bij_vertical_N. }
  apply imp_to_asm_trefines; [apply _|].
  etrans. {
    apply: ci2a_linearize.pass_fn_correct; [done|..]; rewrite ci2a_ssa.pass_fn_vars.
    - apply NoDup_alt => ??? /list_lookup_imap_Some[?[??]] /list_lookup_imap_Some. naive_solver.
    - move => ? /elem_of_lookup_imap[?[?[??]]]. by apply: tmp_var_ne_ssa_var.
  }
  etrans. { apply: ci2a_ssa.pass_fn_correct. }
  rewrite /initial_imp_sstate fmap_insert fmap_empty static_fndef_to_fndef_to_static_fndef.
  done.
Qed.

Ltac i2a_compile f2i f :=
  (let e := eval vm_compute in
      match compile f2i f with
      | monad.CSuccess i => i | monad.CError _ => [] end
   in exact e).

Module ci2a_test.

Definition test_fn_1 : fndef := {|
  fd_args := ["x"];
  fd_vars := [("y", 1)];
  fd_body := (BinOp (BinOp (Var "x") ShiftOp (Val 2)) AddOp (Call "f" [Load (Var "x"); Load (Var "y"); Val 1]));
  fd_static := I;
|}.

Compute compile_ssa test_fn_1.
Compute compile_linear test_fn_1.
Compute compile_mem2reg test_fn_1.
Compute compile (<["f" := 100]> ∅) test_fn_1.

Definition test_sum : fndef := {|
  fd_args := ["n"];
  fd_vars := [];
  fd_body :=
    If (BinOp (Var "n") EqOp (Val 0)) (
         (Val 0)
    ) (
       LetE "rec" (Call "sum" [BinOp (Var "n") AddOp (Val (-1))]) $
       BinOp (Var "n") AddOp (Var "rec"));
  fd_static := I;
|}.

Compute compile_ssa test_sum.
Compute compile_linear test_sum.
Compute compile (<["sum" := 100]> ∅) test_sum.
End ci2a_test.
