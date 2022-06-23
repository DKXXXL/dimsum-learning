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

Local Coercion ImmediateOp: Z >-> asm_operand.
Local Coercion RegisterOp: string >-> asm_operand.


Definition yield_addr : Z := 2000.

Definition coro_state_addr : Z := 3000.

(*
Definition yield_asm: gmap Z asm_instr := deep_to_asm_instrs yield_addr
  [Amov "R9" 0;
   (** basic setup **)
   (* R17 := gtcur *)
   (* Aload "R17" "R9" (gtcur); *)
   (* R16 := gtnext *)
   Aslt "R16" "R17" 1;

   (* R15 := gttbl[gtcur] *)
   Amul "R9" "R17" 13;
   (* Aadd "R15" "R9" (gttbl); *)
   (* R14 := gttbl[gtnext] *)
   Amul "R9" "R16" 13;
   (* Aadd "R14" "R9" (gttbl); *)


   (** store registers to gttbl[gtcur] **)
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

   (** load gttbl[gtnext] to registers **)
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


   (** argument passing **)
   (** already handled; argument 0 register == return register == R0 **)
   (* Amov "R1" "R0"; *)
   (* Aload "R0" "R9" (yield_val); *)
   (* Astore "R1" "R9" (yield_val); *)

   Aret]
.
*)

Definition coro_saved_regs : list string := "PC"::saved_registers.
Opaque coro_saved_regs.

Definition yield_swap_reg (r : string) (o : Z) : list deep_asm_instr := [
    Aload "R17" "R18" o;
    Astore r "R18" o;
    Amov r "R17"
  ].


Definition yield_asm: gmap Z asm_instr := deep_to_asm_instrs yield_addr (
  [Amov "R18" coro_state_addr] ++
  mjoin (imap (λ i r, yield_swap_reg r (Z.of_nat i)) (locked saved_registers)) ++ [
  Aload "R17" "R18" (Z.of_nat $ length saved_registers);
  Astore "R30" "R18" (Z.of_nat $ length saved_registers);
  Abranch true "R17"]).

Definition coro_get_regs (regs : gmap string Z) : list Z :=
  ((regs !!!.) <$> coro_saved_regs).
Arguments coro_get_regs : simpl never.

Definition coro_regs_mem (regs : gmap string Z) : gmap Z (option Z) :=
  map_seqZ coro_state_addr (Some <$> coro_get_regs regs).
Arguments coro_regs_mem : simpl never.

Definition coro_regs_regs (regs : gmap string Z) : gmap string Z :=
  list_to_map ((λ x, (x, regs !!! x)) <$> coro_saved_regs).
Arguments coro_regs_regs : simpl never.

Lemma coro_regs_regs_lookup_in r rs rs' :
  r ∈ "PC"::saved_registers →
  (coro_regs_regs rs ∪ rs') !!! r = rs !!! r.
Proof.
Admitted.

Lemma coro_regs_regs_lookup_not_in r rs rs' :
  r ∉ "PC"::saved_registers →
  (coro_regs_regs rs ∪ rs') !!! r = rs' !!! r.
Proof.
Admitted.

Definition yield_itree : itree (moduleE asm_event (gmap string Z)) unit :=
  ITree.forever (
  '(rs, mem) ← TReceive (λ '(rs, mem), (Incoming, EAJump rs mem));;;
  TAssume (rs !!! "PC" = yield_addr);;;;
  rsold ← TGet;;;
  TAssume (coro_regs_mem rsold ⊆ mem);;;;
  let rs' := (<["PC" := rs !!! "R30"]> rs) in
  TPut rs';;;;
  r17 ← TExist Z;;;
  r18 ← TExist Z;;;
  TVis (Outgoing, EAJump
                    (<["R17" := r17]> $ <["R18" := r18]> $ (coro_regs_regs rsold ∪ rs))
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

(** simply set p->rsp to be stack, p->pc to be the function **)
(*
Definition gtgo_addr: Z := 200.

Definition gtgo_asm: gmap Z asm_instr := deep_to_asm_instrs gtgo_addr
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
*)


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
  fd_vars := [("x", -1); ("y", -1)];
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

Global Instance seq_product_eq_dec : EqDecision seq_product_state.
Proof. solve_decision. Qed.

Inductive coro_prod_filter_state :=
| CPFLeft (finit : option string) (started : bool)
| CPFRight
| CPFExited.

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
        (* p must be SPRight: Not *)
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
              p' = SPNone ∧
              s' = s ∧
              ok = bool_decide (f ∉ fns1)
        | EIReturn v h =>
            ok = false
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

Definition yield_asm_dom : gset Z := locked (dom _) yield_asm.

Definition initial_asm_prod_state (m1 m2 : module asm_event) (σ1 : m1.(m_state)) (σ2 : m2.(m_state)) :=
  (@MLFNone asm_ev, @None seq_product_state, σ1, σ2).

(* Definition coro_spec_inv m1 m2 *)
(*   (σ1 : (asm_prod yield_asm_dom ∅ asm_module (imp_to_asm ∅ ∅ ∅ (imp_prod ∅ ∅  m1 m2))).(m_state)) *)
(*   (σ2 : (imp_to_asm ∅ ∅ ∅ (coro_prod ∅ ∅ m1 m2)).(m_state)) : Prop := *)
(*   let '(σa, σap, (AsmState i _ _ yins) , (σsm, (σi, cs, σi1, σi2), _)) := σ1 in *)
(*   yins = yield_asm ∧ *)
(*   i *)
(*   . *)
(*   → mod_link_state asm_ev * option seq_product_state * asm_state * *)
(*     (mod_seq_map_state imp_event * (mod_link_state imp_ev * list seq_product_state * m_state m1 * m_state m2) * *)
(*      (pp_state * imp_to_asm_state * uPred imp_to_asmUR)) *)
(*     → mod_seq_map_state imp_event * (mod_link_state imp_ev * bool * m_state m1 * m_state m2) * *)
(*       (pp_state * imp_to_asm_state * uPred imp_to_asmUR) → Prop *)


  (* let 'Imp e1 h1 fns1' := σ1 in *)
  (* let '(σf, cs, Imp el hl fnsl, Imp er hr fnsr) := σ2 in *)
  (* ∃ n K Kl Kr e1' el' er' bl br, *)
  (* fns1' = fns1 ∪ fns2 ∧ *)
  (* fnsl = fns1 ∧ *)
  (* fnsr = fns2 ∧ *)
  (* imp_link_prod_combine_ectx n bl br σf cs K Kl Kr ∧ *)
  (* e1 = expr_fill K e1' ∧ *)
  (* el = expr_fill Kl el' ∧ *)
  (* er = expr_fill Kr er' ∧ *)
  (* match σf with *)
  (* | MLFLeft => e1' = el' ∧ is_static_expr true el' ∧ er' = Waiting br ∧ h1 = hl *)
  (*             ∧ (if bv then to_val el' = None else True) *)
  (* | MLFRight => e1' = er' ∧ is_static_expr true er' ∧ el' = Waiting bl ∧ h1 = hr *)
  (*              ∧ (if bv then to_val er' = None else True) *)
  (* | MLFNone => e1' = Waiting (bl || br) ∧ el' = Waiting bl ∧ er' = Waiting br *)
  (* | _ => False *)
  (* end. *)

Lemma i2a_mem_swap_stack sp1 gp1 sp2 gp2 mem:
  i2a_mem_inv sp1 gp1 mem -∗
  i2a_mem_stack sp2 gp2 -∗
  i2a_mem_inv sp2 gp2 mem ∗ i2a_mem_stack sp1 gp1.
Proof. iIntros "[??] ?". iFrame. Qed.

Lemma i2a_mem_update_big sp gp mem mo mo' :
  dom (gset _) mo = dom _ mo' →
  i2a_mem_inv sp gp mem -∗
  i2a_mem_map mo ==∗
  i2a_mem_map mo' ∗ i2a_mem_inv sp gp (mo' ∪ mem).
Proof.
  iIntros (Hdom) "[$ Hmem] Hconst".
  iMod (i2a_mem_delete_big' with "[$] [$]").
  iMod (i2a_mem_alloc_big' with "[$]") as "[? $]".
  { apply map_disjoint_spec => ???. rewrite !lookup_difference_Some -not_elem_of_dom Hdom not_elem_of_dom.  naive_solver. }
  iModIntro.
  by rewrite (map_difference_eq_dom_L _ mo mo') // -map_difference_union_r.
Qed.

(* We cannot use this lemma with imp_to_asm_combine since yield is not
part of fns but parts of ins, but maybe we don't care? *)
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
  (∀ f i, f2i1 !! f = Some i → i ∈ ins2 → f ∈ fns2) →
  (∀ f i, f2i2 !! f = Some i → i ∈ ins1 → f ∈ fns1) →
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
  move => fns ins f2i mo Hinit Hfinit Hyf Hidisj Hfdisj Hydisj Hy1 Hy2 Hi1 Hi2 Hag Hf1 Hf2 Hmo Hgp.
  have ? : ∀ f i1 i2, f2i1 !! f  = Some i1 → f2i !! f = Some i2 → i1 = i2. admit.
  etrans. { apply: asm_prod_trefines; [|done]. apply (yield_asm_refines_itree regs_init). }
  apply: tsim_implies_trefines => n0 /=.
  tstep_i => *. case_match; destruct_all?; simplify_eq/=.
  tstep_s. split!.
  tstep_s. move => -[] //= ? h gp vs avs ret f *.
  tstep_s. split!.
  tstep_s => ?.
  have ? : regs !!! "PC" ∈ ins1. { efeed pose proof Hi1; [done|]. destruct_all?. simplify_eq. naive_solver. }
  rewrite bool_decide_false; [|set_solver].
  rewrite bool_decide_true; [|set_solver].
  tstep_i => *. case_match; destruct_all?; simplify_eq/=.
  rewrite bool_decide_true; [|set_solver].
  tstep_i => *. simplify_eq.
  tstep_i. eexists true. split; [done|]. eexists h, gp, vs, avs, ret, f.
  split!. { admit. (* naive_solver. *) } { set_solver. }
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
           lrc = lr1 ∧
           (x1 ⊣⊢ i2a_mem_stack (yregs !!! "SP") gp ∗ i2a_mem_map (coro_regs_mem yregs) ∗ xc)%I ∧
           σsm2 = SMFilter ∧
           pp2 = PPOutside ∧
           (if finit is Some f then
              cs2 = [] else
              ∃ regs1 ret2 regs2,
                cs2 = [I2AI true (yregs !!! "PC") regs1; I2AI true ret2 regs2]) ∧
           lr2 = ∅ ∧
           (x2 ⊣⊢ emp)%I ∧
           σlc = MLFLeft ∧
           (if finit is Some f then f2i2 !! f = Some (yregs !!! "PC") ∧ f ∈ fns2 else True)
       (* Right side *)
       | CPFRight => False
       | _ => False
       end). }
  { split!. { iSplit; iIntros!; iFrame. } apply big_sepM_empty. } { done. }
  clear -Hyf Hidisj Hfdisj Hydisj Hy1 Hy2 Hi1 Hi2 Hag Hf1 Hf2 VisNoAll0 VisNoAll1.
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
      rewrite bool_decide_false. 2: set_solver.
      rewrite bool_decide_false. 2: admit. (* 2: set_solver. *)
      move => /= *. destruct_all?; simplify_map_eq'.
      rewrite bool_decide_true. 2: rewrite /yield_asm_dom; unlock; admit.
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
      rewrite bool_decide_false. 2: admit.
      rewrite bool_decide_true. 2: admit.
      tstep_i => *. destruct_all?; simplify_eq/=. destruct_all?; simplify_map_eq'.
      rewrite (coro_regs_regs_lookup_in "PC"); [|compute_done].
      rewrite bool_decide_false. 2: admit.
      rewrite bool_decide_true. 2: admit.
      tstep_i => *. simplify_eq.
      tstep_i.
      destruct finit; destruct_all?; simplify_eq.
      * eexists true. split!.
        { admit. } { done. }
        { simplify_map_eq'. rewrite (coro_regs_regs_lookup_in "PC"); [|compute_done]. done. }
        { admit. }
        { rewrite /i2a_regs_call. simplify_map_eq'. apply (coro_regs_regs_lookup_not_in "R30"). compute_done. }
        { iSatMonoBupd. setoid_subst. iFrame. simplify_map_eq'.
          rewrite (coro_regs_regs_lookup_in "SP"); [|compute_done].
          iDestruct (i2a_mem_swap_stack with "Hm [$]") as "[Hm ?]".
          iMod (i2a_mem_update_big with "Hm [$]") as "[? $]". admit.
          iModIntro. iAccu. }
        tsim_mirror m2 σ2. move => ??? Hcont.
        tstep_both. apply Hcont => κ ?? Hs. destruct κ.
        2: { tstep_s. eexists None. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|]. eauto. }
        clear Hs Hcont. move => ?. subst.
        tstep_s. eexists (Some (Incoming, _)). split!. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
        apply: Hloop. { etrans; [|done]. etrans; [|done]. apply ti_le_S. }
        split!. admit.
      * destruct args as [|? [|]] => //.
        eexists false. split!.
        { simplify_map_eq'. rewrite (coro_regs_regs_lookup_in "PC"); [|compute_done]. done. }
        { split. { simplify_map_eq'. rewrite (coro_regs_regs_lookup_not_in "R0"); [|compute_done]. done. }
          admit. }
        { iSatMonoBupd.
          iDestruct (i2a_args_intro with "[$]") as "?"; [done|].
          rewrite i2a_args_cons; [|done]. setoid_subst. iDestruct!. iFrame. simplify_map_eq'.
          rewrite (coro_regs_regs_lookup_in "SP"); [|compute_done].
          iDestruct (i2a_mem_swap_stack with "Hm [$]") as "[Hm ?]".
          iMod (i2a_mem_update_big with "Hm [$]") as "[? $]". admit.
          iModIntro. iAccu. }
        tsim_mirror m2 σ2. move => ??? Hcont.
        tstep_both. apply Hcont => κ ?? Hs. destruct κ.
        2: { tstep_s. eexists None. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|]. eauto. }
        clear Hs Hcont. move => ?. subst.
        tstep_s. eexists (Some (Incoming, _)). split!. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
        apply: Hloop. { etrans; [|done]. etrans; [|done]. apply ti_le_S. }
        split!. admit.
    + (* left call to outside *)
      case_bool_decide; [by tstep_s|].
      rewrite bool_decide_true //=.
      tstep_i => *. destruct_all?; simplify_eq.
      rewrite bool_decide_false. 2: admit.
      rewrite bool_decide_false. 2: admit.
      move => /= *. destruct_all?; simplify_eq/=.
      rewrite bool_decide_false. 2: admit.
      rewrite bool_decide_false. 2: admit.
      tstep_s. split!. done. set_solver. admit. 2: done. set_solver.
      { iSatMono. setoid_subst. iIntros!. iFrame. iAccu. }
      iSatClear.

      (* go back inside *)
      tstep_i => e *. destruct e; destruct_all?; simplify_eq.
      tstep_s. split!.
      tstep_s => -[] /= *. { tstep_s. split!. by tstep_s. }
      tstep_s. split!. destruct_all?; simplify_eq.
      rewrite bool_decide_false. 2: admit.
      rewrite bool_decide_true. 2: set_solver.
      tstep_i => /= *. destruct_all?; simplify_eq/=. destruct_all?; simplify_eq/=.
      rewrite bool_decide_true; [|done].
      tstep_i => *. simplify_eq.
      tstep_i => *. eexists false. split!. done.
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
      rewrite bool_decide_false. 2: set_solver.
      rewrite bool_decide_false. 2: set_solver.
      move => /= *. destruct_all?; simplify_eq/=.
      rewrite bool_decide_false. 2: set_solver.
      rewrite bool_decide_false. 2: set_solver.
      tstep_s. split!. done.
      { iSatMono. setoid_subst. iIntros!. iFrame. iAccu. }
      iSatClear.

      (* going back inside leads to UB *)
      tstep_i => e *. tstep_s. split!.  destruct_all?; simplify_eq/=.
      destruct e; destruct_all?; simplify_eq. tstep_s => -[] /= *; tstep_s; split!; by tstep_s.
Abort.
