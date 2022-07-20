From dimsum.core Require Export proof_techniques.
From dimsum.examples Require Import rec asm rec_to_asm r2a_bij_vertical.
From dimsum.examples.compiler Require Import monad linear_rec ssa linearize mem2reg codegen.

Local Open Scope Z_scope.
Set Default Proof Using "Type".

(** * Compiler from Rec to Asm  *)

(** * Helper lemmas  *)
Lemma tmp_var_ne_ssa_var n1 s n2 :
  tmp_var n1 ≠ ssa_var s n2.
Proof.
  suff : last (string_to_list (tmp_var n1)) ≠ last (string_to_list (ssa_var s n2)).
  { move => ? /string_list_eq?. congruence. }
  rewrite /tmp_var /ssa_var !string_to_list_app !last_app /=.
  rewrite pretty_N_last /pretty_N_char. by repeat case_match.
Qed.

(** * Definition of the compiler  *)
Inductive compile_error :=
| CodegenError (e : cr2a_codegen.error)
.

Definition compile_ssa (fn : fndef) : static_fndef :=
  let static := fndef_to_static_fndef fn in
  cr2a_ssa.pass_fn static.

Definition compile_linear (fn : fndef) : compiler_success compile_error lfndef :=
  let ssa := compile_ssa fn in
  compiler_success_fmap_error (λ x : cr2a_linearize.error, match x with end) (cr2a_linearize.pass_fn ssa).

Definition compile_mem2reg (fn : fndef) : compiler_success compile_error lfndef :=
  cr2a_mem2reg.pass_fn <$> (compile_linear fn).

Definition compile (f2i : gmap string Z) (fn : fndef) : compiler_success compile_error (list deep_asm_instr) :=
  opt ← compile_mem2reg fn;
  compiler_success_fmap_error CodegenError (cr2a_codegen.pass_fn f2i opt).

Ltac r2a_compile f2i f :=
  (let e := eval vm_compute in
      match compile f2i f with
      | monad.CSuccess i => i | monad.CError _ => [] end
   in exact e).

(** * Compiler correctness proof  *)
Theorem compile_correct f2i f fn dins ins a:
  compile f2i fn = CSuccess dins →
  ins = deep_to_asm_instrs a dins →
  f2i !! f = Some a →
  map_Forall (λ f' i', ins !! i' = None ↔ f' ≠ f) f2i →
  trefines (MS asm_module (initial_asm_state ins))
           (MS (rec_to_asm (dom ins) {[f]} f2i rec_module)
               (initial_rec_to_asm_state ∅ rec_module (initial_rec_state (<[f := fn]> ∅)))).
Proof.
  unfold compile.
  move => /compiler_success_bind_success[?[/compiler_success_fmap_success[?[/compiler_success_fmap_error_success ??]] /compiler_success_fmap_error_success?]]. simplify_eq.
  move => ??.
  etrans. {
    apply: cr2a_codegen.pass_fn_correct; [done..| |done].
    apply: cr2a_mem2reg.NoDup_pass_fn.
    erewrite cr2a_linearize.pass_fn_args; [|done].
    erewrite cr2a_linearize.pass_fn_vars; [|done]. apply cr2a_ssa.pass_fn_args_NoDup.
  }
  etrans. {
    apply: rec_to_asm_trefines.
    apply cr2a_mem2reg.pass_fn_correct.
    erewrite cr2a_linearize.pass_fn_args; [|done].
    erewrite cr2a_linearize.pass_fn_vars; [|done].
    apply cr2a_ssa.pass_fn_args_NoDup.
  }
  etrans. { apply: r2a_bij_vertical_N. }
  apply rec_to_asm_trefines; [apply _|].
  etrans. {
    apply: cr2a_linearize.pass_fn_correct; [done|..]; rewrite cr2a_ssa.pass_fn_vars.
    - apply NoDup_alt => ??? /list_lookup_imap_Some[?[??]] /list_lookup_imap_Some. naive_solver.
    - move => ? /elem_of_lookup_imap[?[?[??]]]. by apply: tmp_var_ne_ssa_var.
  }
  etrans. { apply: cr2a_ssa.pass_fn_correct. }
  rewrite /initial_rec_sstate fmap_insert fmap_empty static_fndef_to_fndef_to_static_fndef.
  done.
Qed.

(** * Tests *)
Module cr2a_test.

Definition test_fn_1 : fndef := {|
  fd_args := ["x"];
  fd_vars := [("y", 1)];
  fd_body := (BinOp (BinOp (Var "x") OffsetOp (Val 2)) AddOp (Call "f" [Load (Var "x"); Load (Var "y"); Val 1]));
  fd_static := I;
|}.

Lemma test :
 compile_ssa test_fn_1 =
 {|
    sfd_args := ["x$0"];
    sfd_vars := [("y$1", 1)];
    sfd_body :=
      SBinOp (SBinOp (SVar "x$0") OffsetOp (SVal (StaticValNum 2))) AddOp
        (SCall "f" [SLoad (SVar "x$0"); SLoad (SVar "y$1"); SVal (StaticValNum 1)])
 |}.
Proof. vm_compute. match goal with |- ?x = ?x => exact: eq_refl end. Abort.

Lemma test :
 compile_linear test_fn_1 =
  CSuccess {|
      lfd_args := ["x$0"];
      lfd_vars := [("y$1", 1)];
      lfd_body :=
        LLetE "$0$" (LBinOp (VVar "x$0") OffsetOp (VVal (StaticValNum 2)))
          (LLetE "$1$" (LLoad (VVar "x$0"))
             (LLetE "$2$" (LLoad (VVar "y$1"))
                (LLetE "$3$" (LCall "f" [VVar "$1$"; VVar "$2$"; VVal (StaticValNum 1)])
                   (LLetE "$4$" (LBinOp (VVar "$0$") AddOp (VVar "$3$")) (LEnd (LVarVal (VVar "$4$")))))))
  |}.
Proof. vm_compute. match goal with |- ?x = ?x => exact: eq_refl end. Abort.

Lemma test :
 compile_mem2reg test_fn_1 =
  CSuccess
    {|
      lfd_args := ["x$0"];
      lfd_vars := [];
      lfd_body :=
        LLetE "y$1" (LVarVal (VVal (StaticValNum 0)))
          (LLetE "$0$" (LBinOp (VVar "x$0") OffsetOp (VVal (StaticValNum 2)))
             (LLetE "$1$" (LLoad (VVar "x$0"))
                (LLetE "$2$" (LVarVal (VVar "y$1"))
                   (LLetE "$3$" (LCall "f" [VVar "$1$"; VVar "$2$"; VVal (StaticValNum 1)])
                      (LLetE "$4$" (LBinOp (VVar "$0$") AddOp (VVar "$3$")) (LEnd (LVarVal (VVar "$4$"))))))))
    |}.
Proof. vm_compute. match goal with |- ?x = ?x => exact: eq_refl end. Abort.

Lemma test :
 compile (<["f" := 100]> ∅) test_fn_1 =
  CSuccess
    [Aload "R17" "SP" (-1); Astore "R30" "SP" (-1); Aload "R17" "SP" (-2); Astore "R19" "SP" (-2);
    Aload "R17" "SP" (-3); Astore "R20" "SP" (-3); Aload "R17" "SP" (-4); Astore "R21" "SP" (-4);
    Aload "R17" "SP" (-5); Astore "R22" "SP" (-5); Aload "R17" "SP" (-6); Astore "R23" "SP" (-6);
    Aload "R17" "SP" (-7); Astore "R24" "SP" (-7); Aload "R17" "SP" (-8); Astore "R25" "SP" (-8);
    Amov "R19" "R0"; Aadd "SP" "SP" (-8); Amov "R0" 0; Amov "R20" "R0"; Amov "R1" "R19";
    Amov "R2" 2; Aadd "R0" "R1" "R2"; Amov "R21" "R0"; Amov "R1" "R19"; Aload "R0" "R1" 0;
    Amov "R22" "R0"; Amov "R0" "R20"; Amov "R23" "R0"; Amov "R0" "R22"; Amov "R1" "R23";
    Amov "R2" 1; Abranch_link true 100; Amov "R24" "R0"; Amov "R1" "R21"; Amov "R2" "R24";
    Aadd "R0" "R1" "R2"; Amov "R25" "R0"; Amov "R0" "R25"; Aadd "SP" "SP" 8; Aload "R25" "SP" (-8);
    Aload "R24" "SP" (-7); Aload "R23" "SP" (-6); Aload "R22" "SP" (-5); Aload "R21" "SP" (-4);
    Aload "R20" "SP" (-3); Aload "R19" "SP" (-2); Aload "R30" "SP" (-1); Aret].
Proof. vm_compute. match goal with |- ?x = ?x => exact: eq_refl end. Abort.

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

Lemma test :
 compile_ssa test_sum =
 {|
    sfd_args := ["n$0"];
    sfd_vars := [];
    sfd_body :=
      SIf (SBinOp (SVar "n$0") EqOp (SVal (StaticValNum 0))) (SVal (StaticValNum 0))
        (SLetE "rec$1" (SCall "sum" [SBinOp (SVar "n$0") AddOp (SVal (StaticValNum (-1)))])
           (SBinOp (SVar "n$0") AddOp (SVar "rec$1")))
  |}.
Proof. vm_compute. match goal with |- ?x = ?x => exact: eq_refl end. Abort.

Lemma test :
 compile_linear test_sum =
 CSuccess
    {|
      lfd_args := ["n$0"];
      lfd_vars := [];
      lfd_body :=
        LLetE "$0$" (LBinOp (VVar "n$0") EqOp (VVal (StaticValNum 0)))
          (LIf (LVarVal (VVar "$0$"))
             (LLetE "$4$" (LVarVal (VVal (StaticValNum 0))) (LEnd (LVarVal (VVar "$4$"))))
             (LLetE "$1$" (LBinOp (VVar "n$0") AddOp (VVal (StaticValNum (-1))))
                (LLetE "$2$" (LCall "sum" [VVar "$1$"])
                   (LLetE "rec$1" (LVarVal (VVar "$2$"))
                      (LLetE "$3$" (LBinOp (VVar "n$0") AddOp (VVar "rec$1"))
                         (LLetE "$4$" (LVarVal (VVar "$3$")) (LEnd (LVarVal (VVar "$4$")))))))))
    |}.
Proof. vm_compute. match goal with |- ?x = ?x => exact: eq_refl end. Abort.

Lemma test :
 compile (<["sum" := 100]> ∅) test_sum =
  CSuccess
    [Aload "R17" "SP" (-1); Astore "R30" "SP" (-1); Aload "R17" "SP" (-2); Astore "R19" "SP" (-2);
    Aload "R17" "SP" (-3); Astore "R20" "SP" (-3); Aload "R17" "SP" (-4); Astore "R21" "SP" (-4);
    Aload "R17" "SP" (-5); Astore "R22" "SP" (-5); Aload "R17" "SP" (-6); Astore "R23" "SP" (-6);
    Aload "R17" "SP" (-7); Astore "R24" "SP" (-7); Aload "R17" "SP" (-8); Astore "R25" "SP" (-8);
    Amov "R19" "R0"; Aadd "SP" "SP" (-8); Amov "R1" "R19"; Amov "R2" 0; Aseq "R0" "R1" "R2";
    Amov "R20" "R0"; Amov "R0" "R20"; Abranch_eq false 5 "R0" 0; Amov "R0" 0; Amov "R25" "R0";
    Amov "R0" "R25"; Abranch false 17; Amov "R1" "R19"; Amov "R2" (-1); Aadd "R0" "R1" "R2";
    Amov "R21" "R0"; Amov "R0" "R21"; Abranch_link true 100; Amov "R22" "R0"; Amov "R0" "R22";
    Amov "R23" "R0"; Amov "R1" "R19"; Amov "R2" "R23"; Aadd "R0" "R1" "R2"; Amov "R24" "R0";
    Amov "R0" "R24"; Amov "R25" "R0"; Amov "R0" "R25"; Aadd "SP" "SP" 8; Aload "R25" "SP" (-8);
    Aload "R24" "SP" (-7); Aload "R23" "SP" (-6); Aload "R22" "SP" (-5); Aload "R21" "SP" (-4);
    Aload "R20" "SP" (-3); Aload "R19" "SP" (-2); Aload "R30" "SP" (-1); Aret].
Proof. vm_compute. match goal with |- ?x = ?x => exact: eq_refl end. Abort.

End cr2a_test.
