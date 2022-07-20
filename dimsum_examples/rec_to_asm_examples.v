From dimsum.core Require Export proof_techniques.
From dimsum.examples Require Import rec asm rec_to_asm.

Local Open Scope Z_scope.

(** * Some examples for testing [rec_to_asm] *)

Definition asm_add : gmap Z asm_instr :=
  <[ 100 := [
        (* add R0, R0, R1 *)
        WriteReg "R0" (λ rs, rs !!! "R0" + rs !!! "R1");
        WriteReg "PC" (λ rs, rs !!! "PC" + 1)
    ] ]> $
  <[ 101 := [
        (* ret *)
        WriteReg "PC" (λ rs, rs !!! "R30")
    ] ]> $ ∅.

Definition rec_add : fndef := {|
  fd_args := ["a"; "b"];
  fd_vars := [];
  fd_body := (BinOp (Var "a") AddOp (Var "b"));
  fd_static := I
|}.

Definition rec_add_prog : gmap string fndef :=
  <[ "add" := rec_add ]> ∅.

Definition asm_add_client : gmap Z asm_instr :=
  <[ 200 := [
        (* mov R0, 1 *)
        WriteReg "R0" (λ rs, 1);
        WriteReg "PC" (λ rs, rs !!! "PC" + 1)
    ] ]> $
  <[ 201 := [
        (* mov R1, 1 *)
        WriteReg "R1" (λ rs, 1);
        WriteReg "PC" (λ rs, rs !!! "PC" + 1)
    ] ]> $
  <[ 202 := [
        (* push R30 *)
        WriteReg "SP" (λ rs, rs !!! "SP" - 1);
        WriteMem "R30" "SP" id;
        WriteReg "PC" (λ rs, rs !!! "PC" + 1)
    ] ]> $
  <[ 203 := [
        (* bl 100; *)
        WriteReg "R30" (λ rs, rs !!! "PC" + 1);
        WriteReg "PC" (λ rs, 100)
    ] ]> $
  <[ 204 := [
        (* pop R30 *)
        ReadMem "R30" "SP" id;
        WriteReg "SP" (λ rs, rs !!! "SP" + 1);
        WriteReg "PC" (λ rs, rs !!! "PC" + 1)
    ] ]> $
  <[ 205 := [
        (* ret *)
        WriteReg "PC" (λ rs, rs !!! "R30")
    ] ]> $ ∅.

Definition rec_add_client : fndef := {|
  fd_args := [];
  fd_vars := [("tmp", 1)];
  fd_body := (LetE "_" (Store (Var "tmp") (Val 1))
             (LetE "v" (Load (Var "tmp"))
             (rec.Call "add" [Val 1; Var "v"])));
  fd_static := I
|}.

Definition rec_add_client_prog : gmap string fndef :=
  <[ "add_client" := rec_add_client ]> ∅.

Definition full_asm_add : gmap Z asm_instr :=
  asm_add ∪ asm_add_client.

Definition full_rec_add_prog : gmap string fndef :=
  rec_add_prog ∪ rec_add_client_prog.

Local Ltac go := destruct!/=.
Local Ltac go_i := tstep_i; go.
Local Ltac go_s := tstep_s; go.


Lemma asm_add_refines_rec_add :
  trefines (MS asm_module (initial_asm_state asm_add))
           (MS (rec_to_asm (dom asm_add) (dom rec_add_prog) (<["add" := 100]> ∅) rec_module) (initial_rec_to_asm_state ∅ rec_module (initial_rec_state rec_add_prog))).
Proof.
  apply rec_to_asm_proof; [set_solver..|].
  move => n i rs mem K f fn vs h cs pc ssz rf rc lr Hpc Hi Hf Hf2i Hsat Hargs ? Hcall Hret.
  unfold rec_add_prog in Hf. unfold asm_add in Hi.
  move: Hf2i. rewrite !lookup_insert_Some => ?; destruct!; simplify_map_eq/=.
  destruct vs as [|v1 [|v2 []]] => //=.
  iSatStart. iIntros!. rewrite r2a_args_cons ?r2a_args_cons; [|done..].
  iDestruct!. iSatStop.
  tstep_i => ??. simplify_map_eq'.
  tstep_i.
  tstep_i; simplify_map_eq'.
  tstep_i => ??. simplify_map_eq'.
  tstep_i; simplify_map_eq'.
  go_s. split! => ?.
  go_s => n1 n2 ??; subst.
  go_s => ??; subst.
  iSatStart. simpl. iDestruct!. iSatStop.
  apply: Hret. 1: by simplify_map_eq'.
  1: { simplify_map_eq'. iSatMono. iFrame. done. }
  1: { unfold r2a_regs_ret; split!; simplify_map_eq' => //; by simplify_map_list. }
  1: by simplify_map_list.
Qed.

Lemma asm_add_client_refines_rec_add_client :
  trefines (MS asm_module (initial_asm_state asm_add_client))
           (MS (rec_to_asm (dom asm_add_client) (dom rec_add_client_prog)
                           (<["add_client" := 200]> $ <["add" := 100]> ∅) rec_module)
               (initial_rec_to_asm_state ∅ rec_module (initial_rec_state rec_add_client_prog) )).
Proof.
  apply rec_to_asm_proof; [set_solver..|].
  move => n i rs mem K f fn vs h cs pc ssz rf rc lr Hpc Hi Hf Hf2i Hsat Hargs ? Hcall Hret.
  unfold rec_add_client_prog in Hf. unfold asm_add_client in Hi.
  move: Hf2i. rewrite !lookup_insert_Some => ?; destruct!; simplify_map_eq/=.
  destruct vs as [|] => //=.
  iSatStart. iIntros!. iSatStop.
  tstep_i => ??. simplify_map_eq'.
  tstep_i.
  tstep_i; simplify_map_eq'.
  tstep_i => ??. simplify_map_eq'.
  tstep_i; simplify_map_eq'.
  tstep_i; simplify_map_eq'.
  tstep_i => ??. simplify_map_eq'.
  tstep_i; simplify_map_eq'.
  iSatStart.
  iDestruct (r2a_mem_exists 1 with "[$]") as %[??]; [done|].
  iSatStop.
  tstep_i; simplify_map_eq'. split!. case_match; [|by tstep_i].
  tstep_i; simplify_map_eq'.
  tstep_i => ??. simplify_map_eq'.
  tstep_i; simplify_map_eq'.
  tstep_i; simplify_map_eq'.
  sort_map_insert. simplify_map_eq'.
  tstep_s. split!; [apply (heap_fresh_is_fresh ∅)|]. move => *; simplify_eq.
  tstep_s => *; simplify_eq.
  tstep_s.
  tstep_s => ???. simplify_map_eq. rewrite heap_alloc_h_lookup; [|done|lia] => ?; simplify_map_eq.
  tstep_s.
  change (FreeA [(heap_fresh ∅ h, 1)] (rec.Call "add" [Val 1; Val 1])) with (expr_fill [FreeACtx [(heap_fresh ∅ h, 1)]] (rec.Call "add" [Val 1; Val 1])).
  apply: Hcall. { repeat econs. } { by simplify_map_eq. } { simplify_map_eq'. set_solver. } { by simplify_map_eq'. }
  { iSatMonoBupd.
    iMod (r2a_mem_alloc with "[$]") as (?) "[? Hp]"; [done|done|].
    iDestruct "Hp" as "[[% ?] _]" => /=. rewrite Z.add_0_l.
    iMod (r2a_mem_update with "[$] [$]") as "[? ?]". simplify_map_eq'.
    iMod (r2a_heap_alloc _ (heap_fresh ∅ h) 1 with "[$]") as "[??]". { apply heap_fresh_is_fresh. }
    iMod (r2a_heap_update with "[$] [$]") as "[? ?]".
    iModIntro. iFrame. iSplit; [|iAccu].
    rewrite !r2a_args_cons ?r2a_args_nil; [|done..].
    iSplit!; by simplify_map_eq'.
  }
  { split!; by simplify_map_eq'. }
  { by simplify_map_list. }
  iSatClear.
  move => rs'' ssz'' mem'' av v h'' rf'' lr'' Hpc'' Hsat'' Hr ?.
  move: Hr => [? Hm]; simplify_map_eq'.
  tstep_i => ??. simplify_map_eq'.
  iSatStart. iIntros!.
  iDestruct select (r2a_mem_constant _ _) as "Hret".
  iDestruct (r2a_mem_lookup with "[$] [$]") as %?.
  iSatStop.
  tstep_i; simplify_map_eq'. simplify_map_list. simplify_map_eq'. split!.
  tstep_i; simplify_map_eq'.
  tstep_i; simplify_map_eq'.
  tstep_i => ??. simplify_map_eq'.
  tstep_s => [?[??]]. simplify_eq.
  have ->: rs !!! "SP" - 1 + 1 = rs !!! "SP" by lia.
  tstep_i; simplify_map_eq'.
  apply: Hret.
  1: { by simplify_map_eq'. }
  1: { iSatMonoBupd.
       iMod (r2a_mem_delete 1 with "[$] [Hret]") as "?"; [done|..].
       { iSplitL; [|done]. iExists _. iFrame. }
       iMod (r2a_heap_free _ (heap_fresh ∅ h) with "[$] [$]") as "?".
       iModIntro. iFrame. simplify_map_eq'.
       by rewrite Z.sub_add.
  }
  1: { unfold r2a_regs_ret; split!; simplify_map_eq' => //; by simplify_map_list. }
  1: { by simplify_map_list. }
Qed.

Lemma full_add_stack :
  trefines (MS asm_module (initial_asm_state full_asm_add))
           (MS (rec_to_asm {[ 100; 101; 200; 201; 202; 203; 204; 205 ]} {[ "add"; "add_client" ]}
                           (<["add_client" := 200]> $ <["add" := 100]> ∅) rec_module)
               (initial_rec_to_asm_state ∅ rec_module (initial_rec_state full_rec_add_prog))).
Proof.
  etrans. {
    apply asm_syn_link_refines_link. { unfold asm_add, asm_add_client. eauto with map_disjoint. }
    all: compute_done. }
  etrans. {
    apply: asm_link_trefines.
    - apply asm_add_refines_rec_add.
    - apply asm_add_client_refines_rec_add_client.
  }
  etrans. {
    apply: rec_to_asm_combine; compute_done.
  }
  etrans. {
    apply: rec_to_asm_trefines.
    apply rec_link_refines_syn_link.
    unfold rec_add_prog, rec_add_client_prog. eauto with map_disjoint.
  }
  rewrite left_id.
  done.
Qed.

(* TODO: an interesting example would be to prove

main :

  mov SECRET, 0
  bl c_code
  bl ext

c_code :

  push R30
  bl set_secret
  pop R30
  ret

set_secret :
  mov SECRET, 1
  ret

The interesting property to prove here would be to prove that SECRET is 1 when calling ext
and showing that this can be proven even if one refines c_code to Call "set_secret".
This requires exploiting the fact that rec_to_asm guarantees that the C code only touches
certain registers.
*)
