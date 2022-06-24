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

Local Open Scope Z_scope.

Local Coercion ImmediateOp: Z >-> asm_operand.
Local Coercion RegisterOp: string >-> asm_operand.

Definition yield_addr : Z := 2000.

Definition coro_state_addr : Z := 3000.

Definition coro_saved_regs : list string := "PC"::saved_registers.

Definition coro_get_regs (regs : gmap string Z) : list Z :=
  ((regs !!!.) <$> coro_saved_regs).
Arguments coro_get_regs : simpl never.

Definition coro_regs_mem (regs : gmap string Z) : gmap Z (option Z) :=
  map_seqZ coro_state_addr (Some <$> coro_get_regs regs).
Arguments coro_regs_mem : simpl never.

Definition coro_regs_regs (regs : gmap string Z) : gmap string Z :=
  list_to_map ((λ x, (x, regs !!! x)) <$> coro_saved_regs).
Arguments coro_regs_regs : simpl never.

Lemma coro_regs_regs_args_preserved rs rs':
 map_preserved args_registers rs (coro_regs_regs rs' ∪ rs).
Proof.
  rewrite /coro_regs_regs. cbn.
  rewrite -!insert_union_l left_id_L.
  repeat (apply map_preserved_insert_r_not_in; [compute_done|]).
  done.
Qed.

Lemma coro_regs_regs_touched_scramble rs rs' rs'':
  map_scramble touched_registers rs rs' →
  map_scramble touched_registers rs (coro_regs_regs rs'' ∪ rs').
Proof.
  move => ?.
  rewrite /coro_regs_regs. cbn.
  rewrite -!insert_union_l left_id_L.
  repeat (apply map_scramble_insert_r_in; [compute_done|]).
  done.
Qed.

Lemma coro_regs_regs_saved_preserved rs rs' rs'':
  map_preserved saved_registers rs rs'' →
  map_preserved saved_registers rs (coro_regs_regs rs'' ∪ rs').
Proof.
  move => Hp. rewrite /coro_regs_regs. cbn.
  rewrite -!insert_union_l left_id_L.
  apply map_preserved_insert_r_not_in; [compute_done|].
  repeat (apply map_preserved_insert_r_in; [compute_done|]; split; [apply: Hp; compute_done|]).
  apply map_preserved_nil'. compute_done.
Qed.

Lemma coro_regs_mem_dom rs rs':
  dom (gset Z) (coro_regs_mem rs) = dom (gset Z) (coro_regs_mem rs').
Proof.
  rewrite /coro_regs_mem/coro_get_regs. cbn. rewrite !dom_insert_L. done.
Qed.

Lemma coro_regs_regs_lookup_in r rs rs' :
  r ∈ "PC"::saved_registers →
  (coro_regs_regs rs ∪ rs') !!! r = rs !!! r.
Proof.
  move => ?. set_unfold. rewrite /coro_regs_regs. cbn.
  rewrite -!insert_union_l left_id_L.
  destruct_all?; simplify_eq.
  all: repeat (rewrite lookup_total_insert_ne; [|done]).
  all: by rewrite lookup_total_insert.
Qed.

Lemma coro_regs_regs_lookup_not_in r rs rs' :
  r ∉ "PC"::saved_registers →
  (coro_regs_regs rs ∪ rs') !!! r = rs' !!! r.
Proof.
  move => ?. set_unfold. rewrite /coro_regs_regs. cbn.
  rewrite -!insert_union_l left_id_L.
  by repeat (rewrite lookup_total_insert_ne; [|naive_solver]).
Qed.
Opaque coro_saved_regs.

Definition yield_swap_reg (r : string) (o : Z) : list deep_asm_instr := [
    Aload "R16" "R17" o;
    Astore r "R17" o;
    Amov r "R16"
  ].


Definition yield_asm: gmap Z asm_instr := deep_to_asm_instrs yield_addr (
  [Amov "R17" coro_state_addr] ++
  mjoin (imap (λ i r, yield_swap_reg r (Z.of_nat i)) (locked saved_registers)) ++ [
  Aload "R16" "R17" (Z.of_nat $ length saved_registers);
  Astore "R30" "R17" (Z.of_nat $ length saved_registers);
  Abranch true "R16"]).

Definition yield_asm_dom : gset Z := locked (dom _) yield_asm.

Definition yield_itree : itree (moduleE asm_event (gmap string Z)) unit :=
  ITree.forever (
  '(rs, mem) ← TReceive (λ '(rs, mem), (Incoming, EAJump rs mem));;;
  TAssume (rs !!! "PC" = yield_addr);;;;
  rsold ← TGet;;;
  TAssume (coro_regs_mem rsold ⊆ mem);;;;
  let rs' := (<["PC" := rs !!! "R30"]> rs) in
  TPut rs';;;;
  r16 ← TExist Z;;;
  r17 ← TExist Z;;;
  TVis (Outgoing, EAJump
                    (<["R16" := r16]> $ <["R17" := r17]> $ (coro_regs_regs rsold ∪ rs))
                    (coro_regs_mem rs' ∪ mem))).

Local Ltac go :=
  clear_itree.
Local Ltac go_s :=
  tstep_s; go.
Local Ltac go_i :=
  tstep_i; go.

Lemma yield_asm_refines_itree regs :
  trefines (MS asm_module (initial_asm_state yield_asm))
           (MS (mod_itree _ _) (yield_itree, regs)).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember. { simpl. exact (λ _ σa '(t, _),
    t ≈ yield_itree ∧
    σa.(asm_cur_instr) = AWaiting ∧
    σa.(asm_instrs) = yield_asm). }
  { split!. } { done. }
  move => n _ Hloop [????] [??] ?. destruct_all?; simplify_eq/=.
  tstep_i => ????? Hi. simpl.
  tstep_s. rewrite -/yield_itree. go.
  go_s. eexists (_, _). go.
  go_s. split!. go.
  go_s => ?. go.
  go_s.
  go_s => ?. go.
  go_s.
  tstep_i => ??. simplify_map_eq'.
  rewrite /yield_asm deep_to_asm_instrs_cons in Hi. simplify_map_eq.
  tstep_i.
  tstep_i. simplify_map_eq'.
Admitted.

Inductive coro_prod_filter_state :=
| CPFLeft (finit : option string) (started : bool)
| CPFRight
| CPFExited.

Global Instance coro_prod_filter_state_inhabited : Inhabited coro_prod_filter_state := populate CPFRight.

Definition coro_prod_filter (fns1 fns2 : gset string) : seq_product_state → coro_prod_filter_state → imp_ev → seq_product_state → coro_prod_filter_state → imp_ev → bool → Prop :=
  λ p s e p' s' e' ok,
    match s, p with
    | CPFLeft finit false, SPNone =>
        ∃ f vs h,
        e = EICall f vs h ∧
        e' = e ∧
        p' = SPLeft ∧
        ok = bool_decide (f ∈ fns1) ∧
        s' = CPFLeft finit true
    | CPFLeft _ true, SPNone
    | CPFRight, SPNone =>
        e' = e ∧
        p' = (if s is CPFRight then SPRight else SPLeft) ∧
        s' = s ∧
        ok = if e is EICall _ _ _ then false else true
    | CPFLeft finit _, _ =>
        (* p must be SPLeft *)
        p = SPLeft ∧
        match e with
        | EICall f vs h =>
            if bool_decide (f = "yield") then
              e' = (if finit is Some f then EICall f vs h else EIReturn (vs !!! 0%nat) h) ∧
              p' = SPRight ∧
              s' = CPFRight ∧
              ok = bool_decide (length vs = 1%nat)
            else
              e' = e ∧
              p' = (if bool_decide (f ∈ fns2) then SPRight else SPNone) ∧
              s' = s ∧
              ok = bool_decide (f ∉ fns2)
        | EIReturn v h =>
            e' = e ∧
            p' = SPNone ∧
            s' = CPFExited ∧
            ok = true
        end
    | CPFRight, _ =>
        (* p must be SPRight *)
        p = SPRight ∧
        match e with
        | EICall f vs h =>
            if bool_decide (f = "yield") then
              e' = EIReturn (vs !!! 0%nat) h ∧
              p' = SPLeft ∧
              s' = CPFLeft None true ∧
              ok = bool_decide (length vs = 1%nat)
            else
              e' = e ∧
              p' = (if bool_decide (f ∈ fns1) then SPLeft else SPNone) ∧
              s' = s ∧
              ok = bool_decide (f ∉ fns1)
        | EIReturn v h =>
            ok = false ∧
            e' = e ∧
            p' = SPRight ∧
            s' = s
        end
    | CPFExited, _ =>
        ok = false
    end.
Arguments coro_prod_filter _ _ _ _ _ _ _ _ /.

Definition coro_prod (fns1 fns2 : gset string) (m1 m2 : module imp_event) : module imp_event :=
  mod_link (coro_prod_filter fns1 fns2) m1 m2.

Definition initial_coro_prod_state (finit : string) (m1 m2 : module imp_event) (σ1 : m1.(m_state)) (σ2 : m2.(m_state)) :=
  (@MLFNone imp_ev, CPFLeft (Some finit) false, σ1, σ2).

Lemma coro_prod_trefines m1 m1' m2 m2' σ1 σ1' σ2 σ2' σ ins1 ins2 `{!VisNoAll m1} `{!VisNoAll m2}:
  trefines (MS m1 σ1) (MS m1' σ1') →
  trefines (MS m2 σ2) (MS m2' σ2') →
  trefines (MS (coro_prod ins1 ins2 m1 m2) (σ, σ1, σ2))
           (MS (coro_prod ins1 ins2 m1' m2') (σ, σ1', σ2')).
Proof. move => ??. by apply mod_link_trefines. Qed.

Ltac fast_set_solver := set_unfold; naive_solver.

Theorem coro_spec m1 m2 σ1 σ2 ins1 ins2 fns1 fns2 f2i1 f2i2 finit regs_init gp_init
  `{!VisNoAll m1} `{!VisNoAll m2}:
  let fns := {["yield"]} ∪ fns1 ∪ fns2 in
  let ins := yield_asm_dom ∪ ins1 ∪ ins2 in
  let f2i := f2i1 ∪ f2i2 in
  let mo := (i2a_mem_stack_mem (regs_init !!! "SP") gp_init ∪ coro_regs_mem regs_init) in
  f2i2 !! finit = Some (regs_init !!! "PC") →
  finit ∈ fns2 →
  "yield" ∉ fns1 ∪ fns2 →
  ins1 ## ins2 →
  fns1 ## fns2 →
  yield_asm_dom ## ins1 ∪ ins2 →
  f2i1 !! "yield" = Some yield_addr →
  f2i2 !! "yield" = Some yield_addr →
  (∀ f, f ∈ fns1 → ∃ i, i ∈ ins1 ∧ f2i1 !! f = Some i) →
  (∀ f, f ∈ fns2 → ∃ i, i ∈ ins2 ∧ f2i2 !! f = Some i) →
  (∀ f i1 i2, f2i1 !! f = Some i1 → f2i2 !! f = Some i2 → i1 = i2) →
  (∀ f i, f2i !! f = Some i → i ∈ ins2 → f ∈ fns2) →
  (∀ f i, f2i !! f = Some i → i ∈ ins1 → f ∈ fns1) →
  (∀ f i, f2i !! f = Some i → i ∈ yield_asm_dom → f = "yield") →
  i2a_mem_stack_mem (regs_init !!! "SP") gp_init ##ₘ coro_regs_mem regs_init →
  gp_init + GUARD_PAGE_SIZE ≤ regs_init !!! "SP" →
  trefines
    (MS (asm_prod yield_asm_dom (ins1 ∪ ins2) asm_module
           (asm_prod ins1 ins2 (imp_to_asm ins1 fns1 f2i1 m1) (imp_to_asm ins2 fns2 f2i2 m2)) )
        (initial_asm_prod_state asm_module (asm_prod _ _ _ _)
           (initial_asm_state yield_asm)
           (initial_asm_prod_state (imp_to_asm _ _ _ _) (imp_to_asm _ _ _ _)
              (initial_imp_to_asm_state ∅ m1 σ1)
              (initial_imp_to_asm_state ∅ m2 σ2))))
    (MS (imp_to_asm ins fns f2i (coro_prod fns1 fns2 m1 m2))
       (initial_imp_to_asm_state mo (coro_prod _ _ _ _)
          (initial_coro_prod_state finit _ _ σ1 σ2)))
.
Proof.
  move => fns ins f2i mo Hinit Hfinit Hyf Hidisj Hfdisj Hydisj Hy1 Hy2 Hi1 Hi2 Hag Hf1 Hf2 Hfy Hmo Hgp.
  have ? : ∀ f i1 i2, f2i1 !! f  = Some i1 → f2i !! f = Some i2 → i1 = i2.
  { move => ???. rewrite /f2i lookup_union_Some_raw. naive_solver. }
  etrans. { apply: asm_prod_trefines; [|done]. apply (yield_asm_refines_itree regs_init). }
  apply: tsim_implies_trefines => n0 /=.
  tstep_i => *. case_match; destruct_all?; simplify_eq/=.
  tstep_s. split!.
  tstep_s. move => -[] //= ? h gp vs avs ret f *.
  tstep_s. split!.
  tstep_s => ?.
  have ? : regs !!! "PC" ∈ ins1. { efeed pose proof Hi1; [done|]. destruct_all?. simplify_eq. naive_solver. }
  rewrite bool_decide_false; [|fast_set_solver].
  rewrite bool_decide_true; [|fast_set_solver].
  tstep_i => *. case_match; destruct_all?; simplify_eq/=.
  rewrite bool_decide_true; [|fast_set_solver].
  tstep_i => *. simplify_eq.
  tstep_i. eexists true. split; [done|]. eexists h, gp, vs, avs, ret, f.
  split!. { naive_solver. } { fast_set_solver. }
  { iSatMono. iIntros!. rewrite /i2a_mem_map/mo big_sepM_empty big_sepM_union //. iDestruct!. iFrame.
    iDestruct (i2a_mem_stack_init with "[$]") as "?"; [done|]. iAccu. }
  tsim_mirror m1 σ1. move => ??? Hcont.
  tstep_both. apply Hcont => κ ?? Hs. destruct κ.
  2: { tstep_s. eexists None. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|]. eauto. }
  clear Hcont Hs. move => ?. subst.
  tstep_s. eexists (Some (Incoming, _)). split!. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
  unshelve apply: tsim_remember. { simpl. exact (λ _
      '(σpy1, σpy2, (yt, yregs), (σpc1, σpc2, (σsm1, σ1, (pp1, (I2A cs1 lr1), x1)), (σsm2, σ2, (pp2, (I2A cs2 lr2), x2))))
      '(σsm', (σlc, σc, σ1', σ2'), (ppc, (I2A csc lrc), xc)),
       ∃ cret cregs,
       eqit eq true false yt yield_itree ∧
       σ1' = σ1 ∧
       σ2' = σ2 ∧
       σpy1 = MLFRight ∧
       σpy2 = None ∧
       σpc2 = None ∧
       σsm' = SMProg ∧
       ppc = PPInside ∧
       csc = [I2AI false cret cregs] ∧
       cret ∉ ins ∧
       match σc with
       (* Left side, not yet changed to right side *)
       | CPFLeft finit started =>
           ∃ gp,
           started = true ∧
           σpc1 = MLFLeft ∧
           σsm1 = SMProg ∧
           pp1 = PPInside ∧
           cs1 = csc ∧
           map_scramble touched_registers lrc lr1 ∧
           (x1 ⊣⊢ i2a_mem_stack (yregs !!! "SP") gp ∗ i2a_mem_map (coro_regs_mem yregs) ∗ x2 ∗ xc)%I ∧
           σsm2 = SMFilter ∧
           pp2 = PPOutside ∧
           (if finit is Some f then
              cs2 = [] else
              ∃ regs1 ret2 regs2,
                cs2 = [I2AI true (yregs !!! "PC") regs1; I2AI false ret2 regs2] ∧
                map_preserved saved_registers regs1 yregs) ∧
           σlc = MLFLeft ∧
           yregs !!! "PC" ∈ ins2 ∧
           (if finit is Some f then f2i2 !! f = Some (yregs !!! "PC") ∧ f ∈ fns2 else True)
       (* Right side *)
       | CPFRight =>
           ∃ gp regs1 ret2 regs2,
           σpc1 = MLFRight ∧
           σsm1 = SMFilter ∧
           pp1 = PPOutside ∧
           cs1 = [I2AI true (yregs !!! "PC") regs1; I2AI false cret cregs] ∧
           map_preserved saved_registers regs1 yregs ∧
           map_scramble touched_registers lrc lr2 ∧
           (x2 ⊣⊢ i2a_mem_stack (yregs !!! "SP") gp ∗ i2a_mem_map (coro_regs_mem yregs) ∗ x1 ∗ xc)%I ∧
           σsm2 = SMProg ∧
           pp2 = PPInside ∧
           cs2 = [I2AI false ret2 regs2] ∧
           σlc = MLFRight ∧
           yregs !!! "PC" ∈ ins1
       | _ => False
       end). }
  { split!. { iSplit; iIntros!; iFrame. by iApply big_sepM_empty. } naive_solver. } { done. }
  clear -Hyf Hidisj Hfdisj Hydisj Hy1 Hy2 Hi1 Hi2 Hag Hf1 Hf2 Hfy VisNoAll0 VisNoAll1.
  have ? : yield_addr ∈ yield_asm_dom by rewrite /yield_asm_dom /yield_asm; unlock; compute_done.
  move => n ? Hloop [[[σpy1 σpy2][yt yregs]][[[σpc1 σpc2][[σsm1 σ1][[pp1 [cs1 lr1]]x1]]][[σsm2 σ2][[pp2 [cs2 lr2]]x2]]]].
  move => [[σsm' [[[σlc σc] σ1'] σ2']][[ppc [csc lrc]] xc]] [state ?]. destruct_all?; simplify_eq.
  destruct σc as [finit| |] => //; destruct_all?; simplify_eq.
  - tsim_mirror m1 σ1. move => ??? Hcont.
    tstep_both. apply Hcont => κ ? Hstep Hs. destruct κ as [[? e]|].
    2: { tstep_s. eexists None. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|]. eauto. }
    clear Hcont Hs.
    tend. have [σ' Hσ'] := vis_no_all _ _ _ Hstep. eexists σ'. split; [naive_solver|].
    destruct i; [by tstep_i|].
    tstep_s. eexists (Some (Outgoing, e)).
    destruct e => /=; [case_bool_decide|]; split!.
    all: apply: steps_spec_step_end; [done|] => σ'' ?; assert (σ'' = σ') by naive_solver.
    + (* left to right *)
      tstep_s => ?.
      tstep_i => *. destruct_all?; simplify_map_eq'.
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_false. 2: fast_set_solver.
      move => /= *. destruct_all?; simplify_map_eq'.
      rewrite bool_decide_true; [|done].
      tstep_i. rewrite -/yield_itree. go.
      go_i => -[??]. go.
      go_i => ?. simplify_eq. go.
      go_i. split; [done|]. go.
      go_i.
      iSatStart. iIntros!. revert select (x1 ⊣⊢ _) => ->. iDestruct!.
      iDestruct select (i2a_mem_inv _ _ _) as "Hm".
      iDestruct (i2a_mem_lookup_big with "Hm [$]") as %?.
      iSatStop.
      go_i. split!. go.
      go_i.
      go_i => ?. go.
      go_i => ?. go.
      go_i => *. destruct_all?. simplify_map_eq'. go.
      rewrite (coro_regs_regs_lookup_in "PC"); [|compute_done].
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_true. 2: fast_set_solver.
      tstep_i => *. destruct_all?; simplify_eq/=. destruct_all?; simplify_map_eq'.
      rewrite (coro_regs_regs_lookup_in "PC"); [|compute_done].
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_true. 2: fast_set_solver.
      tstep_i => *. simplify_eq.
      tstep_i.
      destruct finit; destruct_all?; simplify_eq.
      * eexists true. split!.
        { apply: i2a_args_pure_mono; [|done].
          apply map_preserved_insert_r_not_in; [compute_done|].
          apply map_preserved_insert_r_not_in; [compute_done|].
          apply coro_regs_regs_args_preserved. } { done. }
        { simplify_map_eq'. rewrite (coro_regs_regs_lookup_in "PC"); [|compute_done]. done. }
        2: { rewrite /i2a_regs_call. simplify_map_eq'. apply (coro_regs_regs_lookup_not_in "R30"). compute_done. }
        { unfold i2a_regs_call in *. simplify_map_eq'. fast_set_solver. }
        { iSatMonoBupd. iFrame. simplify_map_eq'.
          rewrite (coro_regs_regs_lookup_in "SP"); [|compute_done].
          iDestruct (i2a_mem_swap_stack with "Hm [$]") as "[Hm ?]".
          iMod (i2a_mem_update_big with "Hm [$]") as "[? $]"; [apply coro_regs_mem_dom|].
          iModIntro. iAccu. }
        tsim_mirror m2 σ2. move => ??? Hcont.
        tstep_both. apply Hcont => κ ?? Hs. destruct κ.
        2: { tstep_s. eexists None. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|]. eauto. }
        clear Hs Hcont. move => ?. subst.
        tstep_s. eexists (Some (Incoming, _)). split!. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
        apply: Hloop. { etrans; [|done]. etrans; [|done]. apply ti_le_S. }
        split!.
        { simplify_map_eq'. revert select (i2a_regs_call _ _) => ->. done. }
        { apply map_preserved_insert_r_not_in; [compute_done|]. done. }
        { etrans; [done|]. etrans; [done|].
          apply map_scramble_insert_r_in; [compute_done|].
          apply map_scramble_insert_r_in; [compute_done|].
          by apply coro_regs_regs_touched_scramble. }
        { simplify_map_eq'. iSplit; iIntros!; iFrame. }
        { unfold i2a_regs_call in *. simplify_map_eq'. done. }
      * destruct args as [|? [|]] => //.
        eexists false. split!.
        { simplify_map_eq'. rewrite (coro_regs_regs_lookup_in "PC"); [|compute_done]. done. }
        { split. { simplify_map_eq'. rewrite (coro_regs_regs_lookup_not_in "R0"); [|compute_done]. done. }
          apply map_preserved_insert_r_not_in; [compute_done|].
          apply map_preserved_insert_r_not_in; [compute_done|].
          by apply coro_regs_regs_saved_preserved. }
        { iSatMonoBupd.
          iDestruct (i2a_args_intro with "[$]") as "?"; [done|].
          rewrite i2a_args_cons; [|done]. rewrite i2a_args_nil. iDestruct!. iFrame. simplify_map_eq'.
          rewrite (coro_regs_regs_lookup_in "SP"); [|compute_done].
          iDestruct (i2a_mem_swap_stack with "Hm [$]") as "[Hm ?]".
          iMod (i2a_mem_update_big with "Hm [$]") as "[? $]"; [apply coro_regs_mem_dom|].
          iModIntro. iAccu. }
        tsim_mirror m2 σ2. move => ??? Hcont.
        tstep_both. apply Hcont => κ ?? Hs. destruct κ.
        2: { tstep_s. eexists None. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|]. eauto. }
        clear Hs Hcont. move => ?. subst.
        tstep_s. eexists (Some (Incoming, _)). split!. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
        apply: Hloop. { etrans; [|done]. etrans; [|done]. apply ti_le_S. }
        split!.
        { simplify_map_eq'. revert select (i2a_regs_call _ _) => ->. done. }
        { apply map_preserved_insert_r_not_in; [compute_done|]. done. }
        { etrans; [done|]. etrans; [done|].
          apply map_scramble_insert_r_in; [compute_done|].
          apply map_scramble_insert_r_in; [compute_done|].
          by apply coro_regs_regs_touched_scramble. }
        { simplify_map_eq'. iSplit; iIntros!; iFrame. }
        { unfold i2a_regs_call in *. simplify_map_eq'. done. }
    + (* left call to outside *)
      case_bool_decide; [by tstep_s|].
      rewrite bool_decide_true //=.
      tstep_i => ? rs *. destruct_all?; simplify_eq.
      have ?: rs !!! "PC" ∉ ins. {
        set_unfold => -[[?|?]|?].
        - efeed pose proof Hfy; [apply lookup_union_Some_raw; naive_solver|done|done].
        - efeed pose proof Hf2; [apply lookup_union_Some_raw; naive_solver|done|done].
        - efeed pose proof Hf1; [apply lookup_union_Some_raw; naive_solver|done|done].
      }
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_false. 2: fast_set_solver.
      move => /= *. destruct_all?; simplify_eq/=.
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_false. 2: fast_set_solver.
      tstep_s. split!. { done. } { fast_set_solver. } { apply lookup_union_Some_raw. naive_solver. }
      { fast_set_solver. }
      { iSatMono. setoid_subst. iIntros!. iFrame. iAccu. }
      iSatClear.

      (* go back inside *)
      tstep_i => e *. destruct e; destruct_all?; simplify_eq.
      tstep_s. split!.
      tstep_s => -[] /= *. { tstep_s. split!. by tstep_s. }
      tstep_s. split!. destruct_all?; simplify_eq.
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_true. 2: fast_set_solver.
      tstep_i => /= *. destruct_all?; simplify_eq/=. destruct_all?; simplify_eq/=.
      rewrite bool_decide_true; [|done].
      tstep_i => *. simplify_eq.
      tstep_i => *. eexists false. split!.
      { iSatMono. iIntros!. iFrame. iAccu. }
      tsim_mirror m1 σ' => ??? Hcont.
      tstep_both. apply Hcont => -[?|] ?? Hs *. simplify_eq.
      2: { tstep_s. eexists None. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|]. eauto. }
      tstep_s. eexists (Some (Incoming, _)). split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop. { etrans; [|done]. etrans; [|done]. apply ti_le_S. }
      split!. iSplit; iIntros!; iFrame.
    + (* left return to outside *)
      tstep_i => *. destruct_all?; simplify_eq.
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_false. 2: fast_set_solver.
      move => /= *. destruct_all?; simplify_eq/=.
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_false. 2: fast_set_solver.
      tstep_s. split!.
      { iSatMono. setoid_subst. iIntros!. iFrame. iAccu. }
      iSatClear.

      (* going back inside leads to UB *)
      tstep_i => e *. tstep_s. split!.  destruct_all?; simplify_eq/=.
      destruct e; destruct_all?; simplify_eq. tstep_s => -[] /= *; tstep_s; split!; by tstep_s.
  - tsim_mirror m2 σ2. move => ??? Hcont.
    tstep_both. apply Hcont => κ ? Hstep Hs. destruct κ as [[? e]|].
    2: { tstep_s. eexists None. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|]. eauto. }
    clear Hcont Hs.
    tend. have [σ' Hσ'] := vis_no_all _ _ _ Hstep. eexists σ'. split; [naive_solver|].
    destruct i; [by tstep_i|].
    tstep_s. eexists (Some (Outgoing, e)).
    destruct e => /=; [case_bool_decide|]; split!.
    all: apply: steps_spec_step_end; [done|] => σ'' ?; assert (σ'' = σ') by naive_solver.
    + (* right to left *)
      tstep_s => ?.
      tstep_i => *. destruct_all?; simplify_map_eq'.
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_false. 2: fast_set_solver.
      move => /= *. destruct_all?; simplify_map_eq'.
      rewrite bool_decide_true. 2: done.
      tstep_i. rewrite -/yield_itree. go.
      go_i => -[??]. go.
      go_i => ?. simplify_eq. go.
      go_i. split; [done|]. go.
      go_i.
      iSatStart. iIntros!. revert select (x2 ⊣⊢ _) => ->. iDestruct!.
      iDestruct select (i2a_mem_inv _ _ _) as "Hm".
      iDestruct (i2a_mem_lookup_big with "Hm [$]") as %?.
      iSatStop.
      go_i. split!. go.
      go_i.
      go_i => ?. go.
      go_i => ?. go.
      go_i => *. destruct_all?. simplify_map_eq'. go.
      rewrite (coro_regs_regs_lookup_in "PC"); [|compute_done].
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_true. 2: fast_set_solver.
      tstep_i => *. destruct_all?; simplify_eq/=. destruct_all?; simplify_map_eq'.
      rewrite (coro_regs_regs_lookup_in "PC"); [|compute_done].
      rewrite bool_decide_true. 2: fast_set_solver.
      tstep_i => *. simplify_eq.
      tstep_i.
      destruct args as [|? [|]] => //.
      eexists false. split!.
      { simplify_map_eq'. rewrite (coro_regs_regs_lookup_in "PC"); [|compute_done]. done. }
      { split. { simplify_map_eq'. rewrite (coro_regs_regs_lookup_not_in "R0"); [|compute_done]. done. }
        apply map_preserved_insert_r_not_in; [compute_done|].
        apply map_preserved_insert_r_not_in; [compute_done|].
        by apply coro_regs_regs_saved_preserved. }
      { iSatMonoBupd.
        iDestruct (i2a_args_intro with "[$]") as "?"; [done|].
        rewrite i2a_args_cons; [|done]. rewrite i2a_args_nil. iDestruct!. iFrame. simplify_map_eq'.
        rewrite (coro_regs_regs_lookup_in "SP"); [|compute_done].
        iDestruct (i2a_mem_swap_stack with "Hm [$]") as "[Hm ?]".
        iMod (i2a_mem_update_big with "Hm [$]") as "[? $]"; [apply coro_regs_mem_dom|].
        iModIntro. iAccu. }
      tsim_mirror m1 σ1. move => ??? Hcont.
      tstep_both. apply Hcont => κ ?? Hs. destruct κ.
      2: { tstep_s. eexists None. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|]. eauto. }
      clear Hs Hcont. move => ?. subst.
      tstep_s. eexists (Some (Incoming, _)). split!. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop. { etrans; [|done]. etrans; [|done]. apply ti_le_S. }
      split!.
      { etrans; [done|]. etrans; [done|].
        apply map_scramble_insert_r_in; [compute_done|].
        apply map_scramble_insert_r_in; [compute_done|].
        by apply coro_regs_regs_touched_scramble. }
      { simplify_map_eq'. iSplit; iIntros!; iFrame. }
      { simplify_map_eq'. revert select (i2a_regs_call _ _) => ->. done. }
      { apply map_preserved_insert_r_not_in; [compute_done|]. done. }
      { unfold i2a_regs_call in *. simplify_map_eq'. done. }
    + (* right call to outside *)
      case_bool_decide; [by tstep_s|].
      rewrite bool_decide_true //=.
      tstep_i => ? rs *. destruct_all?; simplify_eq.
      have ? : f2i !! fn = Some (rs !!! "PC"). {
        apply lookup_union_Some_raw.
        destruct (f2i1 !! fn) eqn:?; naive_solver.
      }
      have ?: rs !!! "PC" ∉ ins. {
        set_unfold => -[[?|?]|?].
        - efeed pose proof Hfy; [done|done|done].
        - efeed pose proof Hf2; [done|done|done].
        - efeed pose proof Hf1; [done|done|done].
      }
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_false. 2: fast_set_solver.
      move => /= *. destruct_all?; simplify_eq/=.
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_false. 2: fast_set_solver.
      tstep_s. split!. { done. } { fast_set_solver. } { fast_set_solver. }
      { iSatMono. setoid_subst. iIntros!. iFrame. iAccu. }
      iSatClear.

      (* go back inside *)
      tstep_i => e *. destruct e; destruct_all?; simplify_eq.
      tstep_s. split!.
      tstep_s => -[] /= *. { tstep_s. split!. by tstep_s. }
      tstep_s. split!. destruct_all?; simplify_eq.
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_true. 2: fast_set_solver.
      tstep_i => /= *. destruct_all?; simplify_eq/=. destruct_all?; simplify_eq/=.
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_true; [|done].
      tstep_i => *. simplify_eq.
      tstep_i => *. eexists false. split!.
      { iSatMono. iIntros!. iFrame. iAccu. }
      tsim_mirror m2 σ' => ??? Hcont.
      tstep_both. apply Hcont => -[?|] ?? Hs *. simplify_eq.
      2: { tstep_s. eexists None. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|]. eauto. }
      tstep_s. eexists (Some (Incoming, _)). split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop. { etrans; [|done]. etrans; [|done]. apply ti_le_S. }
      split!. iSplit; iIntros!; iFrame.
    + (* right return to outside *) by tstep_s.
 Unshelve.
 all: apply: inhabitant.
Qed.
