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

Definition locle_addr : Z := 400.

Definition locle_asm : gmap Z asm_instr :=
  deep_to_asm_instrs locle_addr [
      Asle "R0" "R0" (RegisterOp "R1");
      Aret
    ].

Definition locle_fns : gset string :=
  {["locle" ]}.

Definition locle_f2i : gmap string Z :=
  <["locle" := locle_addr]> $ ∅.

Definition locle_itree_strong : itree (moduleE imp_event (gmap prov Z)) unit :=
  ITree.forever (
      '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, EICall f vs h));;;
      TAssume (f = "locle");;;;
      l1 ← TAll loc;;; l2 ← TAll loc;;;
      TAssume (vs = [ValLoc l1; ValLoc l2]);;;;
      ps ← TGet;;;
      z1 ← TExist Z;;;
      TAssert (z1 = default z1 (ps !! l1.1));;;;
      TPut (<[l1.1 := z1]> ps);;;;
      ps ← TGet;;;
      z2 ← TExist Z;;;
      TAssert (z2 = default z2 (ps !! l2.1));;;;
      TPut (<[l2.1 := z2]> ps);;;;
      TVis (Outgoing, EIReturn (ValBool (bool_decide (z1 + l1.2 ≤ z2 + l2.2))) h)
    ).

Local Ltac go :=
  clear_itree.
Local Ltac go_s :=
  tstep_s; go.
Local Ltac go_i :=
  tstep_i; go.

Lemma locle_asm_refines_itree_strong :
  trefines (MS asm_module (initial_asm_state locle_asm))
           (MS (imp_to_asm (dom _ locle_asm) locle_fns locle_f2i
                           (mod_itree imp_event (gmap prov Z)))
               (initial_imp_to_asm_state ∅ (mod_itree _ _) (locle_itree_strong, ∅))).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember. { simpl. exact (λ _ σa '(σf, (t, ps), (pp, σi2a, P)),
    t ≈ locle_itree_strong ∧
    σa.(asm_cur_instr) = AWaiting ∧
    σa.(asm_instrs) = locle_asm ∧
    σi2a.(i2a_calls) = [] ∧
    σf = SMFilter ∧
    pp = PPOutside ∧
    (P ⊢ [∗ map] p↦z∈ps, i2a_heap_shared p z)). }
  { split!. iIntros!. by rewrite big_sepM_empty. } { done. }
  move => n _ Hloop [????] [[?[? ps]][[??]?]] ?. destruct_all?; simplify_eq/=.
  tstep_i => ????? Hi. tstep_s. split!.
  tstep_i => ??. simplify_map_eq'.
  tstep_s => *. case_match => /= *. 2: congruence.
  tstep_s. rewrite -/locle_itree_strong. go. go_s. eexists (_, _, _). go.
  go_s. split!. go.
  go_s => ?. go.
  revert select (_ ⊢ _) => HP. unfold i2a_regs_call in *.
  revert select (_ ∉ dom _ _) => /not_elem_of_dom?.
  unfold locle_f2i in *. cbn in Hi. unfold Z.succ in Hi.
  simplify_map_eq'.
  tstep_i.
  tstep_i. simplify_map_eq'.
  tstep_i => ??. simplify_map_eq'.
  tstep_i. simplify_map_eq'.
  go_s => l1. go.
  go_s => l2. go.
  go_s => ?. go. simplify_eq.
  iSatStart. iIntros!.
  iDestruct (HP with "[$]") as "Hps".
  iDestruct (i2a_args_intro with "[$]") as "Hargs"; [done|]. rewrite !i2a_args_cons; [|done..].
  iDestruct "Hargs" as "([%z1 [% Hl1]] & [%z2 [% Hl2]] & ?)".
  iSatStop.
  go_s.
  go_s. eexists z1. go.
  go_s. split.
  { iSatStart. iDestruct (i2a_heap_shared_ag_big with "Hps Hl1") as %?. iSatStop. done. }
  go.
  go_s.
  iSatStart.
  iAssert ([∗ map] p↦z ∈ <[l1.1 := z1]>ps, i2a_heap_shared p z)%I as "#Hps'".
  { by iApply (big_sepM_insert_2 with "Hl1"). }
  iSatStop.
  go_s.
  go_s. eexists z2. go.
  go_s. split.
  { iSatStart. iDestruct (i2a_heap_shared_ag_big with "Hps' Hl2") as %?. iSatStop. done. }
  go.
  go_s.
  tstep_i => ??. simplify_map_eq'.
  go_s.
  go_s. split!.
  - by simplify_map_eq'.
  - instantiate (1 := [_]). unfold i2a_regs_ret; split!; simplify_map_eq'; split!.
    apply map_preserved_insert_r_not_in; [compute_done|].
    apply map_preserved_insert_r_not_in; [compute_done|].
    done.
  - apply map_scramble_insert_r_in; [compute_done|].
    apply map_scramble_insert_r_in; [compute_done|].
    done.
  - iSatMono. simplify_map_eq'. iFrame. iSplit!. iDestruct "Hps'" as "-#Hps'". iAccu.
  - apply: Hloop; [done|]. split!.
    iIntros!. by iApply (big_sepM_insert_2 with "[] [$]").
Qed.

Definition locle_itree : itree (moduleE imp_event unit) unit :=
  ITree.forever (
      '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, EICall f vs h));;;
      TAssume (f = "locle");;;;
      l1 ← TAll loc;;; l2 ← TAll loc;;;
      TAssume (vs = [ValLoc l1; ValLoc l2]);;;;
      b ← TExist _;;;
      TAssert (l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2));;;;
      TVis (Outgoing, EIReturn (ValBool b) h)).

Lemma locle_itree_strong_refines_itree :
  trefines (MS (mod_itree imp_event (gmap prov Z)) (locle_itree_strong, ∅))
           (MS (mod_itree imp_event unit) (locle_itree, tt)).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember. { simpl. exact (λ _ '(t1, ps) '(t2, _),
    eqit eq true false t1 locle_itree_strong ∧
    t2 ≈ locle_itree). }
  { split!. } { done. }
  move => n _ Hloop [??] [??] ?. destruct_all?. simplify_eq/=.
  go_i. go_s. fold locle_itree_strong in *. fold locle_itree in *.
  go_i => -[[??]?]. go.
  go_i.
  go_s. eexists (_, _, _). go.
  go_s. split!. go.
  go_s => ?. go.
  go_s => ?. go.
  go_s => ?. go.
  go_s => ?. go. simplify_eq.
  go_i. split!. go.
  go_i. split!. go.
  go_i. split!. go.
  go_i. split!. go.
  go_i.
  go_i => ?. go.
  go_i => ?. go.
  go_i.
  go_i.
  go_i => ?. go.
  go_i => Hz2. go.
  go_i.
  go_i.
  go_s. eexists _. go.
  go_s. split; [shelve|]. go.
  go_s. split!. go.
  by apply: Hloop.
  Unshelve.
  - move => Heq. rewrite Heq in Hz2. simplify_map_eq. repeat case_bool_decide; lia.
Qed.

Lemma locle_asm_refines_itree :
  trefines (MS asm_module (initial_asm_state locle_asm))
           (MS (imp_to_asm (dom _ locle_asm) locle_fns locle_f2i
                           (mod_itree imp_event unit))
               (initial_imp_to_asm_state ∅ (mod_itree _ _) (locle_itree, tt))).
Proof.
  etrans; [apply locle_asm_refines_itree_strong|].
  apply: imp_to_asm_trefines.
  apply: locle_itree_strong_refines_itree.
Qed.


Definition __NR_PRINT : Z := 42.
Definition print_addr : Z := 500.

Definition print_asm : gmap Z asm_instr :=
  deep_to_asm_instrs print_addr [
      Amov "R8" (ImmediateOp __NR_PRINT);
      ASyscall;
      Aret
    ].

Definition print_itree : itree (moduleE asm_event unit) unit :=
  ITree.forever (
    '(rs, mem) ← TReceive (λ '(rs, mem), (Incoming, EAJump rs mem));;;
    TAssume (rs !!! "PC" = print_addr);;;;
    TAssume (print_asm !! (rs !!! "R30") = None);;;;
    args ← TExist _;;;
    TAssert (length args = length syscall_arg_regs);;;;
    TAssert (args !! 0%nat = Some (rs !!! "R0"));;;;
    TAssert (args !! 8%nat = Some __NR_PRINT);;;;
    TVis (Outgoing, EASyscallCall args);;;;
    ret ← TReceive (λ ret, (Incoming, EASyscallRet ret));;;
    TVis (Outgoing, EAJump (<["PC" := rs !!! "R30"]> $
                            <["R0" := ret]> $
                            <["R8" := __NR_PRINT]> $
                            rs) mem)).

Lemma print_asm_refines_itree :
  trefines (MS asm_module (initial_asm_state print_asm))
           (MS (mod_itree _ _) (print_itree, tt)).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember. { simpl. exact (λ _ σa '(t, _),
    t ≈ print_itree ∧
    σa.(asm_cur_instr) = AWaiting ∧
    σa.(asm_instrs) = print_asm). }
  { split!. } { done. }
  move => n _ Hloop [????] [??] ?. destruct_all?; simplify_eq/=.
  tstep_i => ????? Hi. tstep_s. rewrite -/print_itree. go.
  go_s. eexists (_, _). go.
  go_s. split!. go.
  go_s => ?. go.
  go_s => ?. go.
  tstep_i => ??. simplify_map_eq'.
  tstep_i.
  tstep_i.
  tstep_i => ??. simplify_map_eq'.
  tstep_i.
  go_s. eexists _. go.
  go_s. split; [shelve|]. go.
  go_s. split; [shelve|]. go.
  go_s. split; [shelve|]. go.
  go_s. split!. go.
  tstep_i => ?.
  go_s. eexists _. go.
  go_s. split!. go.
  tstep_i.
  tstep_i => ??. simplify_map_eq'.
  tstep_i. simplify_map_eq'.
  tstep_i => ??. simplify_map_eq'.
  go_s. sort_map_insert. simplify_map_eq'. split!. go.
  by apply: Hloop.
  Unshelve.
  - done.
  - by simplify_map_eq'.
  - by simplify_map_eq'.
Qed.


Definition memmove_imp : fndef := {|
  fd_args := ["d"; "s"; "n"];
  fd_vars := [];
  fd_body := If (imp.Call "locle" [Var "d"; Var "s"])
                (imp.Call "memcpy" [Var "d"; Var "s"; Var "n"; Val $ ValNum 1])
                (LetE "d'" (BinOp (Var "d") ShiftOp (BinOp (Var "n") AddOp (Val $ ValNum (-1)))) $
                 LetE "s'" (BinOp (Var "s") ShiftOp (BinOp (Var "n") AddOp (Val $ ValNum (-1)))) $
                 imp.Call "memcpy" [Var "d'"; Var "s'"; Var "n"; Val $ ValNum (-1)]);
  fd_static := I
|}.
Definition memmove_prog : gmap string fndef :=
  <["memmove" := memmove_imp]> $ ∅.


Definition memcpy_imp : fndef := {|
  fd_args := ["d"; "s"; "n"; "o"];
  fd_vars := [];
  fd_body := If (BinOp (Val $ ValNum 0) LtOp (Var "n"))
               (LetE "_" (Store (Var "d") (Load (Var "s"))) $
                LetE "d'" (BinOp (Var "d") ShiftOp (Var "o")) $
                LetE "s'" (BinOp (Var "s") ShiftOp (Var "o")) $
                LetE "n'" (BinOp (Var "n") AddOp (Val $ ValNum (-1))) $
                imp.Call "memcpy" [Var "d'"; Var "s'"; Var "n'"; Var "o"])
               (Val 0);
  fd_static := I
|}.
Definition memcpy_prog : gmap string fndef :=
  <["memcpy" := memcpy_imp]> $ ∅.

Definition main_imp : fndef := {|
  fd_args := [];
  fd_vars := [("x", 3)];
  fd_body := LetE "_" (Store (BinOp (Var "x") ShiftOp (Val $ ValNum 0)) (Val $ ValNum 1)) $
             LetE "_" (Store (BinOp (Var "x") ShiftOp (Val $ ValNum 1)) (Val $ ValNum 2)) $
             LetE "_" (imp.Call "memmove" [BinOp (Var "x") ShiftOp (Val $ ValNum 0);
                                           BinOp (Var "x") ShiftOp (Val $ ValNum 1);
                                           (Val $ ValNum 2)]) $
             LetE "_" (imp.Call "print" [Load (BinOp (Var "x") ShiftOp (Val $ ValNum 1))]) $
             LetE "_" (imp.Call "print" [Load (BinOp (Var "x") ShiftOp (Val $ ValNum 2))]) $
             (Val $ ValNum 0);
  fd_static := I
|}.
Definition main_prog : gmap string fndef :=
  <["main" := main_imp]> $ ∅.

Definition main_f2i : gmap string Z :=
  <["main" := 50]> $
  <["memmove" := 200]> $
  <["memcpy"  := 300]> $
  <["print"  := print_addr]> $
  locle_f2i.

Definition main_asm : gmap Z asm_instr :=
  deep_to_asm_instrs 50 ltac:(i2a_compile main_f2i main_imp).

Definition memmove_asm : gmap Z asm_instr :=
  deep_to_asm_instrs 200 ltac:(i2a_compile main_f2i memmove_imp).

Definition memcpy_asm : gmap Z asm_instr :=
  deep_to_asm_instrs 300 ltac:(i2a_compile main_f2i memcpy_imp).

(* (* We need to lock this, otherwise simpl goes crazy. *) *)
(* Definition main_asm_dom : gset Z := locked (dom _) main_asm. *)

Lemma main_asm_refines_imp :
  trefines (MS asm_module (initial_asm_state main_asm))
           (MS (imp_to_asm (dom _ main_asm) {["main"]} main_f2i imp_module)
               (initial_imp_to_asm_state ∅ imp_module (initial_imp_state main_prog))).
Proof.
  apply: compile_correct; [|done|..].
  - by vm_compute.
  - by vm_compute.
  - move => ??. rewrite /main_f2i/locle_f2i !lookup_insert_Some !lookup_empty.
    move => ?. destruct_all?; simplify_eq; compute_done.
Qed.

Lemma memmove_asm_refines_imp :
  trefines (MS asm_module (initial_asm_state memmove_asm))
           (MS (imp_to_asm (dom _ memmove_asm) {["memmove"]} main_f2i imp_module)
               (initial_imp_to_asm_state ∅ imp_module (initial_imp_state memmove_prog))).
Proof.
  apply: compile_correct; [|done|..].
  - by vm_compute.
  - by vm_compute.
  - move => ??. rewrite /main_f2i/locle_f2i !lookup_insert_Some !lookup_empty.
    move => ?. destruct_all?; simplify_eq; compute_done.
Qed.

Lemma memcpy_asm_refines_imp :
  trefines (MS asm_module (initial_asm_state memcpy_asm))
           (MS (imp_to_asm (dom _ memcpy_asm) {["memcpy"]} main_f2i imp_module)
               (initial_imp_to_asm_state ∅ imp_module (initial_imp_state memcpy_prog))).
Proof.
  apply: compile_correct; [|done|..].
  - by vm_compute.
  - by vm_compute.
  - move => ??. rewrite /main_f2i/locle_f2i !lookup_insert_Some !lookup_empty.
    move => ?. destruct_all?; simplify_eq; compute_done.
Qed.

Lemma memcpy_spec n0 d s d' s' n o K e h m σ1 σ2 b cs hvs `{!ImpExprFill e K
      (imp.Call "memcpy" [Val (ValLoc d); Val (ValLoc s); Val (ValNum n); Val o])}:
  n = Z.of_nat (length hvs) →
  o = 1 ∨ o = -1 →
  d' = (if bool_decide (o = 1) then d else d +ₗ (- n + 1)) →
  s' = (if bool_decide (o = 1) then s else s +ₗ (- n + 1)) →
  (if bool_decide (o = 1) then d.1 = s.1 → d.2 ≤ s.2 else d.1 = s.1 → s.2 ≤ d.2) →
  (∀ i v, hvs !! i = Some v → h_heap h !! (s' +ₗ Z.of_nat i) = Some v) →
  (∀ i v, hvs !! i = Some v → heap_alive h (d' +ₗ Z.of_nat i)) →
  ((MLFLeft, cs, Imp (expr_fill K (Val (ValNum 0)))
                   (heap_update_big h (kmap (λ i, d' +ₗ i) (map_seqZ 0 hvs)))
                   (memmove_prog ∪ memcpy_prog), σ1)
    ⪯{imp_prod {["memmove"; "memcpy"]} {["locle"]} imp_module (mod_itree imp_event ()), m, n0, true}
  σ2) →
  (MLFLeft, cs, Imp e h (memmove_prog ∪ memcpy_prog), σ1)
    ⪯{imp_prod {["memmove"; "memcpy"]} {["locle"]} imp_module (mod_itree imp_event ()), m, n0, b}
  σ2.
Proof.
  elim/ti_lt_ind: n0 b d d' s s' n h hvs e K ImpExprFill0 => n1 IH b d d' s s' n h hvs e K [->] ? Ho ?? Hle Hhvs Halive Hcont. subst.
  tstep_i. split! => *. simplify_map_eq. split!. rewrite orb_true_r.
  tstep_i. move => ?? [??]. simplify_eq. split!.
  tstep_i. split!.
  tstep_i. case_bool_decide (_ < _). 2: {
    tstep_i. split!. destruct hvs; [|done]. simplify_eq/=.
    move: Hcont. rewrite kmap_empty heap_update_big_empty. done.
  }
  destruct Ho; simplify_eq/=; repeat case_bool_decide => //.
  - destruct hvs; [done|].
    have := Hhvs 0%nat _ ltac:(done). rewrite shift_loc_0 => ?.
    have := Halive 0%nat _ ltac:(done). rewrite shift_loc_0 => ?.
    tstep_i. split!.
    tstep_i. split!.
    tstep_i.
    tstep_i.
    tstep_i.
    tstep_i.
    tstep_i.
    tstep_i.
    tstep_i.
    have ->: (S (length hvs) + -1) = (length hvs) by lia.
    apply: tsim_mono_to_tiS => ??. apply: IH; [done|eauto_tstep|done|by left|done|done|..].
    { move => /=. lia. }
    { move => i v' ? /=. rewrite -shift_loc_S.
      rewrite lookup_alter_ne; [by apply: Hhvs|].
      destruct (decide (d.1 = s.1)); [|naive_solver].
      destruct d, s; rewrite /shift_loc => ?; simplify_eq/=. lia.
    } { move => ???. apply heap_alive_update. rewrite -shift_loc_S. by apply: Halive. }
    simpl. tstep_i. split!.
    move: Hcont.
    rewrite /= kmap_insert shift_loc_0 heap_update_big_update.
    rewrite -insert_union_r. 2: {
      eapply lookup_kmap_None; [by apply _|].
      rewrite /shift_loc. move => ? /=?. destruct d; simplify_eq/=. apply lookup_map_seqZ_None. lia.
    }
    rewrite right_id_L.
    enough (kmap (λ i : Z, d +ₗ i) (map_seqZ (Z.succ 0) hvs) =@{gmap _ _}
            kmap (λ i : Z, d +ₗ 1 +ₗ i) (map_seqZ 0 hvs)) as ->. {
      move => ?. apply: tsim_mono; [done|]. etrans; [|done]. apply ti_le_S.
    }
    apply map_eq => i. apply option_eq => v'. rewrite !lookup_kmap_Some.
    setoid_rewrite lookup_map_seqZ_Some. split; move => [j ?]; destruct_all?; simplify_eq.
    + eexists (Z.pred j).
      rewrite Z.sub_pred_l -Z.sub_succ_r. split!; [|lia].
      rewrite /shift_loc/=. f_equal. lia.
    + eexists (Z.succ j).
      rewrite Z.sub_succ_r Z.sub_succ_l Z.pred_succ. split!; [|lia].
      rewrite /shift_loc/=. f_equal. lia.
  - destruct (snoc_inv hvs) as [|[v[hvs' ?]]]; [naive_solver|]. simplify_eq. tstep_i.
    move: Hhvs Halive. rewrite app_length /=.
    have -> : (- (length hvs' + 1)%nat + 1) = - length hvs' by lia.
    move => Hhvs Halive.
    have := Hhvs (length hvs') v.
    have := Halive (length hvs') v.
    rewrite lookup_app_r // -minus_n_n /= !shift_loc_add_sub; [|lia..]. move => ??.
    split!; [naive_solver|].
    tstep_i. split!; [naive_solver|].
    tstep_i.
    tstep_i.
    tstep_i.
    tstep_i.
    tstep_i.
    tstep_i.
    tstep_i.
    have ->: ((length hvs' + 1)%nat + -1) = length hvs' by lia.
    apply: tsim_mono_to_tiS => ??. apply: IH; [done|eauto_tstep|done|by right|..].
    { have ->: d +ₗ -1 +ₗ (- length hvs' + 1) = d +ₗ (- length hvs'); [|done].
      rewrite /shift_loc /=. f_equal. lia. }
    { have ->: s +ₗ -1 +ₗ (- length hvs' + 1) = s +ₗ (- length hvs'); [|done].
      rewrite /shift_loc /=. f_equal. lia. }
    { move => /=. lia. }
    { move => i v' Hv' /=.  move: (Hv') => /(lookup_lt_Some _ _ _)?.
      rewrite lookup_alter_ne; [apply: Hhvs; apply lookup_app_Some; naive_solver|].
      destruct (decide (d.1 = s.1)); [|naive_solver].
      destruct d, s; rewrite /shift_loc => ?; simplify_eq/=. lia.
    } { move => ???. apply heap_alive_update. apply: Halive. apply lookup_app_Some; naive_solver. }
    simpl. tstep_i. split!.
    move: Hcont.
    rewrite /= heap_update_big_update app_length /=.
    have -> : (- (length hvs' + 1)%nat + 1) = - length hvs' by lia.
    rewrite map_seqZ_app /= kmap_union kmap_insert kmap_empty shift_loc_add_sub //.
    move => ?. apply: tsim_mono; [done|]. etrans; [|done]. apply ti_le_S.
Qed.

Definition memmove_itree : itree (moduleE imp_event unit) unit :=
  ITree.forever (
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, EICall f vs h));;;
    TAssume (f = "memmove");;;;
    '(d, s, n) ← TAll _;;;
    TAssume (vs = [ValLoc d; ValLoc s; ValNum n]);;;;
    hvs ← TAll (list val);;;
    TAssume (n = Z.of_nat (length hvs));;;;
    TAssume (∀ i v, hvs !! i = Some v → h_heap h !! (s +ₗ Z.of_nat i) = Some v);;;;
    TAssume (∀ i v, hvs !! i = Some v → heap_alive h (d +ₗ Z.of_nat i));;;;
    TVis (Outgoing, EIReturn 0 (heap_update_big h (kmap (λ i, d +ₗ i) (map_seqZ 0 hvs))) );;;;
    Ret ()).

Lemma memmove_refines_itree :
  trefines (MS (imp_prod {["memmove"; "memcpy"]} {["locle"]} imp_module (mod_itree _ _))
              (initial_imp_prod_state imp_module (mod_itree _ _)
              (initial_imp_state (memmove_prog ∪ memcpy_prog)) (locle_itree, tt)))
           (MS (mod_itree _ _) (memmove_itree, tt)).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember. { simpl. exact (λ _ '(σi, cs, Imp e h fns, (ti, _)) '(t, _),
    eqit eq true false ti locle_itree ∧
    t ≈ memmove_itree ∧
    cs = [] ∧
    σi = MLFNone ∧
    e = Waiting false ∧
    fns = (memmove_prog ∪ memcpy_prog)). }
  { split!. } { done. }
  move => n ? IH [[[??] [???]] [??]] [??] ?. destruct_all?; simplify_eq.
  tstep_i => *. case_match; destruct_all?; simplify_eq/=.
  go_s.
  go_s. eexists (_, _, _). rewrite -/memmove_itree. go.
  go_s. split!. go.
  go_s => ?. go.
  go_s => -[[??]?]. go.
  go_s => ?. go.
  go_s => hvs. go.
  go_s => ?. go.
  go_s => Hhvs. go.
  go_s => ?. go.
  simplify_map_eq/=. case_bool_decide; [|done].
  tstep_i. split!. move => *. simplify_map_eq.
  tstep_i. split!. move => ??. simplify_map_eq. split!.
  tstep_i => *. destruct_all?. simplify_eq/=. split!.
  tstep_i. split!. move => *. destruct_all?. simplify_eq. repeat case_bool_decide => //.
  tstep_i. rewrite -/locle_itree. go.
  go_i => -[[??]?]. go.
  go_i => *. simplify_eq. go.
  go_i. split!. go.
  go_i. eexists _. go.
  go_i. eexists _. go.
  go_i. split!. go.
  go_i => b. go.
  go_i => Heq. go.
  go_i => *. destruct_all?. simplify_eq. go.
  tstep_i. split!. move => *. simplify_eq.
  tstep_i.
  destruct b.
  - apply: memcpy_spec; [eauto_tstep|done|by left|by rewrite bool_decide_true|by rewrite bool_decide_true| |done|done|..].
    { rewrite bool_decide_true //. case_bool_decide; lia. }
    simpl. tstep_i. split!.
    tstep_i. move => *. destruct_all?; simplify_eq/=.
    go_s. split!. rewrite bind_ret_l. go.
    eapply IH; [done|]. split!.
  - tstep_i.
    tstep_i.
    tstep_i.
    tstep_i.
    tstep_i.
    tstep_i.
    apply: memcpy_spec; [eauto_tstep|done|by right|..].
    { rewrite bool_decide_false; [|done]. rewrite shift_loc_add_sub; [done|lia]. }
    { rewrite bool_decide_false; [|done]. rewrite shift_loc_add_sub; [done|lia]. }
    { rewrite bool_decide_false //=. case_bool_decide; lia. }
    { done. }
    { done. }
    simpl. tstep_i. split!.
    tstep_i. move => *. destruct_all?; simplify_eq/=.
    go_s. split!. rewrite bind_ret_l. go.
    eapply IH; [done|]. split!.
Qed.
