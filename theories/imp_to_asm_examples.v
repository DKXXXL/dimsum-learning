Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.filter.
Require Import refframe.product.
Require Import refframe.seq_product.
Require Import refframe.proof_techniques.
Require Import refframe.prepost.
Require Import refframe.imp.
Require Import refframe.asm.
Require Import refframe.imp_to_asm.

Local Open Scope Z_scope.

Definition asm_add : gmap Z asm_instr :=
  <[ 100 := [
        (* add R0, R0, R1 *)
        WriteReg "R0" (λ rs, rs !!! "R0" + rs !!! "R1");
        WriteReg "PC" (λ rs, rs !!! "PC" + 4)
    ] ]> $
  <[ 104 := [
        (* ret *)
        WriteReg "PC" (λ rs, rs !!! "R30")
    ] ]> $ ∅.

Definition imp_add : fndef := {|
  fd_args := ["a"; "b"];
  fd_body := (BinOp (Var "a") AddOp (Var "b"));
  fd_static := I
|}.

Definition imp_add_prog : gmap string fndef :=
  <[ "add" := imp_add ]> ∅.

Definition asm_add_client : gmap Z asm_instr :=
  <[ 200 := [
        (* mov R0, 1 *)
        WriteReg "R0" (λ rs, 1);
        WriteReg "PC" (λ rs, rs !!! "PC" + 4)
    ] ]> $
  <[ 204 := [
        (* mov R1, 1 *)
        WriteReg "R1" (λ rs, 1);
        WriteReg "PC" (λ rs, rs !!! "PC" + 4)
    ] ]> $
  <[ 208 := [
        (* push R30 *)
        WriteReg "SP" (λ rs, rs !!! "SP" - 1);
        WriteMem "R30" "SP" id;
        WriteReg "PC" (λ rs, rs !!! "PC" + 4)
    ] ]> $
  <[ 212 := [
        (* bl 100; *)
        WriteReg "R30" (λ rs, rs !!! "PC" + 4);
        WriteReg "PC" (λ rs, 100)
    ] ]> $
  <[ 216 := [
        (* pop R30 *)
        ReadMem "R30" "SP" id;
        WriteReg "SP" (λ rs, rs !!! "SP" + 1);
        WriteReg "PC" (λ rs, rs !!! "PC" + 4)
    ] ]> $
  <[ 220 := [
        (* ret *)
        WriteReg "PC" (λ rs, rs !!! "R30")
    ] ]> $ ∅.

Definition imp_add_client : fndef := {|
  fd_args := [];
  fd_body := (LetE "tmp" (Alloc (Val 1))
             (LetE "_" (Store (Var "tmp") (Val 1))
             (LetE "v" (Load (Var "tmp"))
             (LetE "_" (Free (Var "tmp"))
             (imp.Call "add" [Val 1; Var "v"])))));
  fd_static := I
|}.

Definition imp_add_client_prog : gmap string fndef :=
  <[ "add_client" := imp_add_client ]> ∅.

Definition imp_add' : fndef := {|
  fd_args := ["a"; "b"];
  fd_body := UbE;
  fd_static := I
|}.

Definition imp_add_client' : fndef := {|
  fd_args := [];
  fd_body := (Val 2);
  fd_static := I
|}.

Definition full_asm_add : gmap Z asm_instr :=
  asm_add ∪ asm_add_client.

Definition full_imp_add_prog : gmap string fndef :=
  imp_add_prog ∪ imp_add_client_prog.

Definition full_imp_add_prog' : gmap string fndef :=
  <[ "add_client" := imp_add_client' ]> $ <[ "add" := imp_add' ]> ∅.

Local Ltac go := destruct_all?; simplify_eq/=.
Local Ltac go_i := tstep_i; go.
Local Ltac go_s := tstep_s; go.

Ltac simpl_map_ext tac ::=
  repeat match goal with
         | H : map_list_included ?ns ?m |- is_Some (?m !! ?r) =>
             is_closed_term ns;
             apply (map_list_included_is_Some _ _ _ H);
             compute_done
         | |- map_list_included ?ns (<[?i:=?x]> ?m) =>
             apply (map_list_included_insert ns m i x)
         | |- context [ map_scramble ?ns ?m (<[?i:=?x]> ?m') ] =>
             is_closed_term ns;
             rewrite ->(map_scramble_insert_r_in ns m m' i x) by compute_done
         | |- context [ map_preserved ?ns ?m (<[?i:=?x]> ?m') ] =>
             is_closed_term ns;
             rewrite ->(map_preserved_insert_r_not_in ns m m' i x) by compute_done
         | H : map_scramble ?ns (<[?i:=?x]> ?m) ?m' |- _ =>
             is_closed_term ns;
             rewrite ->(map_scramble_insert_l_in ns m m' i x) in H by compute_done
         | H : map_preserved ?ns (<[?i:=?x]> ?m) ?m' |- _ =>
             is_closed_term ns;
             rewrite ->(map_preserved_insert_l_not_in ns m m' i x) in H by compute_done
         | H : map_scramble ?ns (<[?i:=?x]> ?m) ?m' |- _ =>
             is_closed_term ns;
             apply map_scramble_insert_l_not_in in H; [|compute_done];
             let H' := fresh in
             destruct H as [H' H]
         | H : map_preserved ?ns (<[?i:=?x]> ?m) ?m' |- _ =>
             is_closed_term ns;
             apply map_preserved_insert_l_in in H; [|compute_done];
             let H' := fresh in
             destruct H as [H' H]
         | |- context [map_scramble ?ns ?m (<[?i:=?x]> ?m')] =>
             is_closed_term ns;
             rewrite ->(map_scramble_insert_r_not_in ns m m' i x) by compute_done
         | |- context [map_preserved ?ns ?m (<[?i:=?x]> ?m')] =>
             is_closed_term ns;
             rewrite ->(map_preserved_insert_r_in ns m m' i x) by compute_done
         | |- context [ map_scramble ?ns ?m ?m ] =>
             rewrite ->(map_scramble_eq' ns m)
         | |- context [ map_preserved ?ns ?m ?m ] =>
             rewrite ->(map_preserved_eq' ns m)
         end.


Lemma asm_add_refines_imp_add :
  trefines (MS asm_module (initial_asm_state asm_add))
           (MS (imp_to_asm (dom _ asm_add) (dom _ imp_add_prog) (<["add" := 100]> ∅) imp_module) (initial_imp_to_asm_state imp_module (initial_imp_state imp_add_prog))).
Proof.
  apply imp_to_asm_proof; [set_solver..|].
  move => n i rs mem K f fn vs h cs pc ret pb Hpc Hi Hf Hf2i Hargs Hvs Hcall Hret.
  unfold imp_add_prog in Hf. unfold asm_add in Hi.
  move: Hf2i. rewrite !lookup_insert_Some => ?; destruct_all?; simplify_map_eq/=.
  destruct vs as [|v1 [|v2 []]] => //=.
  move: Hargs => -[?[? /= [??]]]. decompose_Forall_hyps.
  tstep_i. split; [simplify_map_eq'|].
  tstep_i; simplify_map_eq'. split; [done|].
  tstep_i => ??. simplify_map_eq'.
  tstep_i; simplify_map_eq'. split!.
  go_s => n1 n2 ??; subst.
  apply: Hret; [by simplify_map_eq| |done|done|by simplify_map_eq'].
  unfold imp_to_asm_ret; split!; simplify_map_eq' => //.
Qed.

Lemma asm_add_client_refines_imp_add_client :
  trefines (MS asm_module (initial_asm_state asm_add_client))
           (MS (imp_to_asm (dom _ asm_add_client) (dom _ imp_add_client_prog)
                           (<["add_client" := 200]> $ <["add" := 100]> ∅) imp_module)
               (initial_imp_to_asm_state imp_module (initial_imp_state imp_add_client_prog) )).
Proof.
  apply imp_to_asm_proof; [set_solver..|].
  move => n i rs mem K f fn vs h cs pc ret pb Hpc Hi Hf Hf2i Hargs Hvs Hcall Hret.
  unfold imp_add_client_prog in Hf. unfold asm_add_client in Hi.
  move: Hf2i. rewrite !lookup_insert_Some => ?; destruct_all?; simplify_map_eq/=.
  destruct vs as [|] => //=.
  move: Hargs => -[?[? /= [? ?]]]. decompose_Forall_hyps.
  tstep_i. split; [simplify_map_eq'|].
  tstep_i; simplify_map_eq'. split; [done|].
  tstep_i => ??. simplify_map_eq'.
  tstep_i; simplify_map_eq'. split; [simplify_map_eq'|].
  tstep_i; simplify_map_eq'. split; [done|].
  tstep_i => ??. simplify_map_eq'.
  tstep_i; simplify_map_eq'. split; [simplify_map_eq'|].
  tstep_i; simplify_map_eq'. split!; [done..|].
  tstep_i; simplify_map_eq'. split!; [done..|].
  tstep_i => ??. simplify_map_eq'.
  tstep_i; simplify_map_eq'. split; [done|].
  tstep_i; simplify_map_eq'. split; [done|].
  sort_map_insert. simplify_map_eq'.
  tstep_s. split!; [apply (heap_fresh_is_fresh ∅)|]. move => *; simplify_eq.
  tstep_s.
  tstep_s => *; simplify_eq.
  tstep_s.
  tstep_s => *; simplify_map_eq.
  tstep_s.
  tstep_s => *; simplify_eq.
  tstep_s.
  change (imp.Call "add" [Val 1; Val 1]) with (expr_fill [] (imp.Call "add" [Val 1; Val 1])).
  apply: Hcall. { repeat econs. } { by simplify_map_eq. } { set_solver. } { set_solver. } { by simplify_map_eq. }
  { unfold imp_to_asm_args. split!; decompose_Forall; by simplify_map_eq'. }
  { by simplify_map_eq. } { done. } { by simplify_map_eq'. }
  move => rs'' mem'' v h'' pb'' Hpc'' Hv Hmem ?.
  move: Hv => [?[? Hm]]; simplify_map_eq'.
  tstep_i; simplify_map_eq'. split!; [by simplify_map_eq'..|].
  tstep_i; simplify_map_eq'. split!; [done..|].
  tstep_i; simplify_map_eq'. split!; [done..|].
  tstep_i => ??. simplify_map_eq'.
  have ->: rs !!! "SP" - 1 + 1 = rs !!! "SP" by lia.
  tstep_i; simplify_map_eq'. split; [done|].
  apply: Hret; [| | |done|by simplify_map_eq']. { simplify_map_eq'. f_equal. etrans; [eapply Hmem|]; by simplify_map_eq'. }
  2 : { move => ?. simplify_map_eq' => ?. etrans; [eapply Hmem; simplify_map_eq'; lia|].
        rewrite lookup_total_insert_ne //. lia. }
  unfold imp_to_asm_ret; split!; simplify_map_eq'; split!.
  apply lookup_lookup_total; simplify_map_eq'.
Qed.

(*
The following does not actually hold since the allocation adds a new provenance to h_heap provs

Lemma imp_add_refines_imp_add' :
  trefines (MS imp_module (initial_imp_state full_imp_add_prog))
           (MS (mod_prepost prepost_id prepost_id imp_module)
               (SMFilter, initial_imp_state full_imp_add_prog', (PPOutside, tt))).
Proof.
  pose (R := λ (b : bool) (r1 r2 : unit), True).
  apply: (imp_prepost_proof R); unfold R in *.
  { done. }
  unfold full_imp_add_prog. move => n K1 K2 f fn1 vs1 h0 r0 ?.
  rewrite lookup_union_Some_raw !lookup_insert_Some => ?; destruct_all?; simplify_map_eq/=.
  all: split! => ?; split! => Hcall Hret.
  - destruct vs1 as [|? [|??]] => //. by tstep_s.
  - destruct vs1 => //.
    tstep_i => *. split!.
    tstep_i.
    tstep_i. split!. { by apply heap_alive_alloc. }
    tstep_i.
    tstep_i. simplify_map_eq. eexists _.
    split. { rewrite shift_loc_0. by simplify_map_eq. }
    tstep_i.
    tstep_i. split!. { apply heap_alive_update. by apply heap_alive_alloc. }
    tstep_i.
    change (imp.Call "add" [Val 1; Val 1]) with (imp.Call "add" (Val <$> [ValNum 1; ValNum 1])).
    tstep_i. simplify_map_eq. split; [|naive_solver].
    move => ??. simplify_map_eq. split!.
    tstep_i.
    apply Hret; [done|]. split!.
    f_equal.
    f_equal.
    by rewrite heap_free_update // heap_free_alloc // heap_free_fresh.
Qed.
*)

Lemma full_add_stack :
  trefines (MS asm_module (initial_asm_state full_asm_add))
           (MS (imp_to_asm {[ 100; 104; 200; 204; 208; 212; 216; 220 ]} {[ "add"; "add_client" ]}
                           (<["add_client" := 200]> $ <["add" := 100]> ∅) imp_module)
               (initial_imp_to_asm_state imp_module (initial_imp_state full_imp_add_prog))).
Proof.
  etrans. { apply asm_link_refines_prod. unfold asm_add, asm_add_client. eauto with map_disjoint. }
  etrans. {
    apply: asm_prod_trefines.
    - apply asm_add_refines_imp_add.
    - apply asm_add_client_refines_imp_add_client.
  }
  etrans. {
    apply imp_to_asm_combine.
    - apply _.
    - apply _.
    - set_solver.
    - set_solver.
    - move => f ?. have ->: f = "add" by set_solver. eexists 100; simplify_map_eq. set_solver.
    - move => f ?. have ->: f = "add_client" by set_solver. eexists 200; simplify_map_eq. set_solver.
    - move => f ??. rewrite !lookup_insert_Some => ??. naive_solver.
    - move => f ?. rewrite !lookup_insert_Some => ?. naive_solver.
    - move => f ?. rewrite !lookup_insert_Some => ?. naive_solver.
  }
  etrans. {
    apply: imp_to_asm_trefines.
    apply imp_prod_refines_link.
    unfold imp_add_prog, imp_add_client_prog. eauto with map_disjoint.
  }
  done.
  (* etrans. { *)
  (*   apply: imp_to_asm_trefines. *)
  (*   apply: imp_add_refines_imp_add'. *)
  (* } *)
  (* etrans. { apply: prepost_id_l. } *)
  (* done. *)
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
This requires exploiting the fact that imp_to_asm guarantees that the C code only touches
certain registers.
*)
