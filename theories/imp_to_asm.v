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

Local Open Scope Z_scope.

(** * imp_to_asm *)
Definition imp_val_to_asm_val (pb : gmap prov (option Z)) (v : val) : option Z :=
  match v with
  | ValNum z => Some z
  | ValBool b => Some (bool_to_Z b)
  | ValLoc l => pb !! l.1 ≫= λ o, (λ x, x + l.2) <$> o
  end.

Definition args_registers : list string :=
  ["R0"; "R1"; "R2"; "R3"; "R4"; "R5"; "R6"; "R7" ; "R8"].

Definition tmp_registers : list string :=
  args_registers ++ ["R9"; "R10"; "R11"; "R12"; "R13"; "R14"; "R15"; "R16"; "R17"; "R30"; "PC"].

Definition saved_registers : list string :=
  ["R19"; "R20"; "R21"; "R22"; "R23"; "R24"; "R25"; "R26"; "R27"; "R28"; "R29"; "SP"].

Definition touched_registers : list string :=
  tmp_registers ++ saved_registers.

Definition imp_to_asm_args (pb : gmap prov (option Z)) (ret : Z) (rs : gmap string Z) (vs : list val) : Prop :=
  rs !! "R30" = Some ret ∧
  Forall2 (λ v r, imp_val_to_asm_val pb v = Some (rs !!! r)) vs (take (length vs) args_registers) ∧
  map_list_included tmp_registers rs ∧
  map_list_included saved_registers rs.


Definition imp_to_asm_ret (pb : gmap prov (option Z)) (rs rsold : gmap string Z) (v : val) : Prop :=
  imp_val_to_asm_val pb v = Some (rs !!! "R0") ∧
  map_list_included tmp_registers rs ∧
  map_preserved saved_registers rsold rs.

Definition imp_to_asm_mem_rel (sp : Z) (amem amemold : gmap Z Z) : Prop :=
  ∀ a, sp ≤ a → amem !!! a = amemold !!! a.

Definition imp_to_asm_phys_blocks_extend (p1 p2 : gmap prov (option Z)) : Prop :=
  p1 ⊆ p2.

Global Instance imp_to_asm_phys_blocks_extend_preorder : (PreOrder imp_to_asm_phys_blocks_extend).
Proof. apply _. Qed.
Global Typeclasses Opaque imp_to_asm_phys_blocks_extend.

Record imp_to_asm_stack_item := I2AI {
  i2as_extern : bool;
  i2as_ret : Z;
  i2as_regs : gmap string Z;
  i2as_mem : gmap Z Z;
  i2as_heap : heap_state;
}.
Add Printing Constructor imp_to_asm_stack_item.

Record imp_to_asm_state := I2A {
  i2a_calls : list imp_to_asm_stack_item;
  i2a_phys_blocks : gmap prov (option Z);
  i2a_last_regs : gmap string Z;
}.
Add Printing Constructor imp_to_asm_state.

Definition imp_to_asm_pre (ins : gset Z) (fns : gset string) (f2i : gmap string Z) (e : asm_event) (s : imp_to_asm_state) : prepost (imp_event * imp_to_asm_state) :=
  match e with
  | (i, EAJump pc rs mem) =>
      (* env chooses if this is a function call or return *)
      pp_quant (λ b,
        pp_prop (i = Incoming) $
        if b then
          (* env chooses return address *)
          pp_quant $ λ ret,
          (* env chooses function name *)
          pp_quant $ λ f,
          (* env chooses arguments *)
          pp_quant $ λ vs,
          (* env chooses heap *)
          pp_quant $ λ h,
          (* env chooses new physical blocks *)
          pp_quant $ λ pb,
          (* env proves that function name is valid *)
          pp_prop  (f ∈ fns) $
          (* env proves it calls the right address *)
          pp_prop (f2i !! f = Some pc) $
          (* env proves that ret is not in ins *)
          pp_prop (ret ∉ ins) $
          (* env proves pb is an increment *)
          pp_prop (imp_to_asm_phys_blocks_extend s.(i2a_phys_blocks) pb) $
          (* env proves that rs corresponds to vs and ret *)
          pp_prop (imp_to_asm_args pb ret rs vs) $
          (* track the registers and return address (false means ret belongs to env) *)
          pp_end ((i, EICall f vs h), I2A ((I2AI false ret rs mem h)::s.(i2a_calls)) pb rs)
        else
          (* env chooses return value *)
          pp_quant $ λ v,
          (* env chooses heap *)
          pp_quant $ λ h,
          (* env chooses new physical blocks *)
          pp_quant $ λ pb,
          (* env chooses old registers *)
          pp_quant $ λ rsold,
          (* env chooses old mem *)
          pp_quant $ λ memold,
          (* env chooses old heap *)
          pp_quant $ λ hold,
          (* env chooses rest of cs *)
          pp_quant $ λ cs',
          (* get registers from stack (true means pc belongs to the program) *)
          pp_prop (s.(i2a_calls) = (I2AI true pc rsold memold hold)::cs') $
          (* env proves pb is an increment *)
          pp_prop (imp_to_asm_phys_blocks_extend s.(i2a_phys_blocks) pb) $
          (* env proves that rs is updated correctly *)
          pp_prop (imp_to_asm_ret pb rs rsold v) $
          (* env proves memory is updated correctly *)
          pp_prop (imp_to_asm_mem_rel (rs !!! "SP") mem memold) $
          pp_end ((i, EIReturn v h), I2A cs' pb rs))
  end.

Definition imp_to_asm_post (ins : gset Z) (fns : gset string) (f2i : gmap string Z) (e : imp_event) (s : imp_to_asm_state) : prepost (asm_event * imp_to_asm_state) :=
  pp_prop (e.1 = Outgoing) $
  match e with
  | (i, EICall f vs h) =>
      pp_quant $ λ pc,
      pp_quant $ λ rs,
      pp_quant $ λ mem,
      (* program chooses return address *)
      pp_quant $ λ ret,
      (* program chooses new physical blocks *)
      pp_quant $ λ pb,
      (* program proves that this function is external *)
      pp_prop (f ∉ fns) $
      (* program proves that the address is correct *)
      pp_prop (f2i !! f = Some pc) $
      (* program proves that ret is in ins *)
      pp_prop (ret ∈ ins) $
      (* prog proves pb is an increment *)
      pp_prop (imp_to_asm_phys_blocks_extend s.(i2a_phys_blocks) pb) $
      (* program proves that rs corresponds to vs and ret  *)
      pp_prop (imp_to_asm_args pb ret rs vs) $
      (* program proves it only touched a specific set of registers *)
      pp_prop (map_scramble touched_registers s.(i2a_last_regs) rs) $
      (* track the registers and return address (true means ret belongs to program) *)
      pp_end ((Outgoing, EAJump pc rs mem), (I2A ((I2AI true ret rs mem h)::s.(i2a_calls)) pb s.(i2a_last_regs)))
  | (i, EIReturn v h) =>
      pp_quant $ λ pc,
      pp_quant $ λ rs,
      pp_quant $ λ mem,
      (* program chooses new physical blocks *)
      pp_quant $ λ pb,
      (* program chooses old registers *)
      pp_quant $ λ rsold,
      (* program chooses old mem *)
      pp_quant $ λ memold,
      (* program chooses old heap *)
      pp_quant $ λ hold,
      (* program chooses rest of cs *)
      pp_quant $ λ cs',
      (* get registers from stack (false means pc belongs to the env) *)
      pp_prop (s.(i2a_calls) = (I2AI false pc rsold memold hold)::cs') $
      (* prog proves pb is an increment *)
      pp_prop (imp_to_asm_phys_blocks_extend s.(i2a_phys_blocks) pb) $
      (* prog proves that rs is updated correctly *)
      pp_prop (imp_to_asm_ret pb rs rsold v) $
      (* prog proves memory is updated correctly *)
      pp_prop (imp_to_asm_mem_rel (rs !!! "SP") mem memold) $
      (* program proves it only touched a specific set of registers *)
      pp_prop (map_scramble touched_registers s.(i2a_last_regs) rs) $
      pp_end ((Outgoing, EAJump pc rs mem), (I2A cs' pb s.(i2a_last_regs)))
  end.

Definition imp_to_asm (ins : gset Z) (fns : gset string) (f2i : gmap string Z)
           (m : module imp_event) : module asm_event :=
  mod_prepost (imp_to_asm_pre ins fns f2i) (imp_to_asm_post ins fns f2i) m.

Definition initial_imp_to_asm_state (m : module imp_event) (σ : m.(m_state)) :=
  (@SMFilter imp_event, σ, (@PPOutside imp_event asm_event, I2A [] ∅ ∅)).

Lemma imp_to_asm_trefines m m' σ σ' ins fns f2i `{!VisNoAll m}:
  trefines (MS m σ) (MS m' σ') →
  trefines (MS (imp_to_asm ins fns f2i m) (initial_imp_to_asm_state m σ))
           (MS (imp_to_asm ins fns f2i m') (initial_imp_to_asm_state m' σ')).
Proof. move => ?. by apply: mod_prepost_trefines. Qed.

Inductive imp_to_asm_combine_stacks (ins1 ins2 : gset Z) :
  seq_product_state → list seq_product_state →
  list imp_to_asm_stack_item → list imp_to_asm_stack_item → list imp_to_asm_stack_item →
 Prop :=
| IAC_nil :
  imp_to_asm_combine_stacks ins1 ins2 SPNone [] [] [] []
| IAC_NoneLeft ret rs ics cs cs1 cs2 mem h:
  ret ∉ ins1 →
  ret ∉ ins2 →
  imp_to_asm_combine_stacks ins1 ins2 SPNone ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 SPLeft (SPNone :: ics) ((I2AI false ret rs mem h) :: cs) ((I2AI false ret rs mem h) :: cs1) cs2
| IAC_NoneRight ret rs ics cs cs1 cs2 mem h:
  ret ∉ ins1 →
  ret ∉ ins2 →
  imp_to_asm_combine_stacks ins1 ins2 SPNone ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 SPRight (SPNone :: ics) ((I2AI false ret rs mem h) :: cs) cs1 ((I2AI false ret rs mem h) :: cs2)
| IAC_LeftRight ret rs ics cs cs1 cs2 mem h:
  ret ∈ ins1 →
  imp_to_asm_combine_stacks ins1 ins2 SPLeft ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 SPRight (SPLeft :: ics) cs ((I2AI true ret rs mem h) :: cs1) ((I2AI false ret rs mem h) :: cs2)
| IAC_LeftNone ret rs ics cs cs1 cs2 mem h:
  ret ∈ ins1 →
  imp_to_asm_combine_stacks ins1 ins2 SPLeft ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 SPNone (SPLeft :: ics) ((I2AI true ret rs mem h) :: cs) ((I2AI true ret rs mem h) :: cs1) cs2
| IAC_RightLeft ret rs ics cs cs1 cs2 mem h:
  ret ∈ ins2 →
  imp_to_asm_combine_stacks ins1 ins2 SPRight ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 SPLeft (SPRight :: ics) cs ((I2AI false ret rs mem h) :: cs1) ((I2AI true ret rs mem h) :: cs2)
| IAC_RightNone ret rs ics cs cs1 cs2 mem h:
  ret ∈ ins2 →
  imp_to_asm_combine_stacks ins1 ins2 SPRight ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 SPNone (SPRight :: ics) ((I2AI true ret rs mem h) :: cs) cs1 ((I2AI true ret rs mem h) :: cs2)
.

Definition imp_to_asm_combine_inv (m1 m2 : module imp_event)
           (ins1 ins2 : gset Z) (fns1 fns2 : gset string) (f2i1 f2i2 : gmap string Z)
  (σ1 : (asm_prod ins1 ins2 (imp_to_asm ins1 fns1 f2i1 m1) (imp_to_asm ins2 fns2 f2i2 m2)).(m_state))
  (σ2 : (imp_to_asm (ins1 ∪ ins2) (fns1 ∪ fns2) (f2i1 ∪ f2i2) (imp_prod fns1 fns2 m1 m2)).(m_state)) : Prop :=
  let '(σfa, _, (σf1, σi1, (t1, I2A cs1 pb1 lr1)), (σf2, σi2, (t2, I2A cs2 pb2 lr2))) := σ1 in
  let '(σfs, (σpi, ics, σs1, σs2), (t, I2A cs pb lr)) := σ2 in
  let ins := (ins1 ∪ ins2) in
  let fns := (fns1 ∪ fns2) in
  let f2i := (f2i1 ∪ f2i2) in
  ∃ ips,
  σi1 = σs1 ∧
  σi2 = σs2 ∧
  imp_to_asm_combine_stacks ins1 ins2 ips ics cs cs1 cs2 ∧
  (( σfa = MLFNone ∧ σfs = SMFilter
     ∧ t = PPOutside
      ∧ t1 = PPOutside
      ∧ t2 = PPOutside
      ∧ σf1 = SMFilter ∧ σf2 = SMFilter
      ∧ σpi = MLFNone
      ∧ ips = SPNone
      ∧ imp_to_asm_phys_blocks_extend pb1 pb
      ∧ imp_to_asm_phys_blocks_extend pb2 pb
    ) ∨
  (( (∃ e, σpi = MLFRecvL e ∧ σf1 = SMProgRecv (Incoming, e))
      ∨ σpi = MLFLeft ∧ σf1 = SMProg)
      ∧ σfa = MLFLeft ∧ σfs = SMProg
      ∧ t = PPInside
      ∧ t1 = PPInside
      ∧ t2 = PPOutside
      ∧ σf2 = SMFilter
      ∧ ips = SPLeft
      ∧ map_scramble touched_registers lr lr1
      ∧ imp_to_asm_phys_blocks_extend pb pb1
      ∧ imp_to_asm_phys_blocks_extend pb2 pb1) ∨
  (((∃ e, σpi = MLFRecvR e ∧ σf2 = SMProgRecv (Incoming, e))
      ∨ σpi = MLFRight ∧ σf2 = SMProg)
      ∧ σfa = MLFRight ∧ σfs = SMProg
      ∧ t = PPInside
      ∧ t1 = PPOutside
      ∧ t2 = PPInside
      ∧ σf1 = SMFilter
      ∧ ips = SPRight
      ∧ map_scramble touched_registers lr lr2
      ∧ imp_to_asm_phys_blocks_extend pb pb2
      ∧ imp_to_asm_phys_blocks_extend pb1 pb2)).

Local Ltac go := repeat match goal with | x : asm_ev |- _ => destruct x end;
                 destruct_all?; simplify_eq/=; destruct_all?; simplify_eq/=.
Local Ltac go_i := tstep_i; intros; go.
Local Ltac go_s := tstep_s; go.

Local Ltac split_solve :=
  match goal with
  | |- imp_to_asm_args _ _ _ _ => eassumption
  | |- imp_to_asm_ret _ _ _ _ => eassumption
  | |- imp_to_asm_phys_blocks_extend ?a ?b =>
      assert_fails (has_evar a); assert_fails (has_evar b); by etrans
  | |- map_scramble ?r ?a ?b =>
      assert_fails (has_evar r); assert_fails (has_evar a); assert_fails (has_evar b); by etrans
  end.
Local Ltac split_tac ::=
  repeat (original_split_tac; try split_solve).

Lemma imp_to_asm_combine ins1 ins2 fns1 fns2 f2i1 f2i2 m1 m2 σ1 σ2 `{!VisNoAll m1} `{!VisNoAll m2}:
  ins1 ## ins2 →
  fns1 ## fns2 →
  (∀ f, f ∈ fns1 → ∃ i, i ∈ ins1 ∧ f2i1 !! f = Some i) →
  (∀ f, f ∈ fns2 → ∃ i, i ∈ ins2 ∧ f2i2 !! f = Some i) →
  (∀ f i1 i2, f2i1 !! f = Some i1 → f2i2 !! f = Some i2 → i1 = i2) →
  (∀ f i, f2i1 !! f = Some i → i ∈ ins2 → f ∈ fns2) →
  (∀ f i, f2i2 !! f = Some i → i ∈ ins1 → f ∈ fns1) →
  trefines (MS (asm_prod ins1 ins2 (imp_to_asm ins1 fns1 f2i1 m1) (imp_to_asm ins2 fns2 f2i2 m2))
               (MLFNone, tt, initial_imp_to_asm_state m1 σ1,
                 initial_imp_to_asm_state m2 σ2))
           (MS (imp_to_asm (ins1 ∪ ins2) (fns1 ∪ fns2) (f2i1 ∪ f2i2) (imp_prod fns1 fns2 m1 m2))
               (initial_imp_to_asm_state (imp_prod _ _ _ _)
                  (MLFNone, [], σ1, σ2) )
).
Proof.
  move => Hdisji Hdisjf Hin1 Hin2 Hagree Ho1 Ho2.
  unshelve apply: mod_prepost_link. { exact (λ ips '(I2A cs1 pb1 lr1) '(I2A cs2 pb2 lr2) '(I2A cs pb lr) _ ics,
  imp_to_asm_combine_stacks ins1 ins2 ips ics cs cs1 cs2 ∧
  ((ips = SPNone ∧ imp_to_asm_phys_blocks_extend pb1 pb ∧ imp_to_asm_phys_blocks_extend pb2 pb) ∨
  ((ips = SPLeft
      ∧ map_scramble touched_registers lr lr1
      ∧ imp_to_asm_phys_blocks_extend pb pb1
      ∧ imp_to_asm_phys_blocks_extend pb2 pb1) ∨
  (ips = SPRight
      ∧ map_scramble touched_registers lr lr2
      ∧ imp_to_asm_phys_blocks_extend pb pb2
      ∧ imp_to_asm_phys_blocks_extend pb1 pb2)))). }
  { move => ?? [] /=*. naive_solver. }
  { split!. econs. }
  all: move => [cs1 pb1 lr1] [cs2 pb2 lr2] [cs pb lr] [] ics.
  - move => [pc rs mem] [] [pc' rs' mem'] /= ?? b ?.
    destruct_all?; simplify_eq. destruct b => /=.
    + move => ret f vs h pb' Hin Hf2i /not_elem_of_union[??] ??.
      repeat case_bool_decide => //. eexists true => /=.
      move: Hin => /elem_of_union[?|/Hin2[?[??]]].
      2: { exfalso. move: Hf2i => /lookup_union_Some_raw. naive_solver. }
      split!.
      1: move: Hf2i => /lookup_union_Some_raw; naive_solver.
      1: by simpl_map_decide.
      1: by econs.
    + move => v h pb' rsold memold hold cs' ????.
      repeat case_bool_decide => //. eexists false => /=.
      revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; simplify_eq/= => //. 2: { exfalso. set_solver. }
      split!.
  - move => [pc rs mem] [] [pc' rs' mem'] /= ?? b ?.
    destruct_all?; simplify_eq. destruct b => /=.
    + move => ret f vs h pb' Hin Hf2i /not_elem_of_union[??] ??.
      repeat case_bool_decide => //. eexists true => /=.
      move: Hin => /elem_of_union[/Hin1[?[??]]|?].
      1: { exfalso. move: Hf2i => /lookup_union_Some_raw. naive_solver. }
      split!.
      1: move: Hf2i => /lookup_union_Some_raw; naive_solver.
      1: by simpl_map_decide.
      1: by econs.
    + move => v h pb' rsold memold hold cs' ????.
      repeat case_bool_decide => //. eexists false => /=.
      revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; simplify_eq/= => //.
      split!.
  - move => [? [f vs h|v h]] ? /= *.
    all: destruct_all?; simplify_eq/=.
    + repeat case_bool_decide => //. 2: { exfalso. set_solver. } eexists true => /=.
      split!.
      1: naive_solver.
      1: set_solver.
      1: by econs.
    + repeat case_bool_decide => //. eexists false => /=.
      revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; simplify_eq/= => //.
      split!.
  - move => [? [f vs h|v h]] ? /= *.
    all: destruct_all?; simplify_eq/=.
    + repeat case_bool_decide => //. 1: { exfalso. set_solver. }
      split!.
      1: set_solver.
      1: apply lookup_union_Some_raw; naive_solver.
      1: set_solver.
      1: by econs.
    + repeat case_bool_decide => //.
      revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; simplify_eq/= => //.
      split!.
  - move => [? [f vs h|v h]] ? /= *.
    all: destruct_all?; simplify_eq/=.
    + repeat case_bool_decide => //. 2: { exfalso. set_solver. } eexists true.
      split!.
      1: naive_solver.
      1: set_solver.
      1: by econs.
    + repeat case_bool_decide => //.
      revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; simplify_eq/= => //. eexists false.
      split!.
  - move => [? [f vs h|v h]] ? /= *.
    all: destruct_all?; simplify_eq/=.
    + repeat case_bool_decide => //. 1: { exfalso. set_solver. }
      split!.
      1: set_solver.
      1: apply lookup_union_Some_raw; destruct (f2i1 !! f) eqn:?; naive_solver.
      1: set_solver.
      1: by econs.
    + repeat case_bool_decide => //.
      revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; simplify_eq/= => //.
      split!.
Qed.

(* Lemma tsim_remember_stack {EV} {mi ms : module EV} (Pσ : _ → _ → Prop) σi σs b n : *)
(*   Pσ σi σs → *)
(*   (* (∀ n n' σi σs, tiS?b n' ⊆ n → Pσ n σi σs → Pσ n' σi σs) → *) *)
(*   (∀ n' σi σs, *)
(*       tiS?b n' ⊆ n → *)
(*       Pσ σi σs → *)

(*       σi ⪯{mi, ms, n'} σs. *)
(*  ) → *)
(*   σi ⪯{mi, ms, n, b} σs. *)
(* Proof. *)
(*   move => HP HPmono Hsim κs' n' Hn Ht /=. *)
(*   move: HP => /HPmono HP. move: (HP _ ltac:(done)) => {}HP. *)
(*   elim/ti_lt_ind: n' κs' σi σs Hn HP Ht. *)
(*   move => n' IHn κs' σi σs Hn HP Ht. *)
(*   apply: Hsim; [done| |done| |done]. 2: done. *)
(*   move => ??????? /=. eapply IHn; [done| | |done]. *)
(*   - etrans; [|done]. apply tiS_maybe_mono; [done|]. etrans; [|done]. apply ti_le_S. *)
(*   - apply: HPmono; [|done]. etrans; [|done]. by apply tiS_maybe_mono. *)
(* Qed. *)


Inductive imp_to_asm_proof_stack (n : trace_index) (ins : gmap Z asm_instr) (fns : gmap string fndef) (f2i : gmap string Z) :
  bool → list expr_ectx → imp_to_asm_state → Prop :=
| IAPSNil :
  imp_to_asm_proof_stack n ins fns f2i false [] (I2A [] ∅ ∅)
| IAPSStep c cs pb pb' lr lr' K' rs ret K b amem h:
  imp_to_asm_proof_stack n ins fns f2i b K (I2A cs pb lr) →
  imp_to_asm_phys_blocks_extend pb pb' →
  (∀ i rs' amem' pb'' h' v,
      rs' !! "PC" = Some ret →
      ins !! ret = Some i →
      imp_to_asm_ret pb'' rs' rs v →
      imp_to_asm_mem_rel (rs' !!! "SP") amem' amem →
      imp_to_asm_phys_blocks_extend pb' pb'' →
      AsmState (Some i) rs' amem' ins ⪯{asm_module, imp_to_asm (dom _ ins) (dom _ fns) f2i imp_module, n, true}
               (SMProg, Imp (expr_fill (K' ++ K) (Val v)) h' fns, (PPInside, I2A (c :: cs) pb'' rs'))) →
  imp_to_asm_proof_stack n ins fns f2i true (K' ++ K) (I2A ((I2AI true ret rs amem h) :: c :: cs) pb' lr')
.


Lemma imp_to_asm_proof ins fns ins_dom fns_dom f2i :
  ins_dom = dom _ ins →
  fns_dom = dom _ fns →
  (∀ n i rs mem K f fn vs h cs pc ret pb,
      rs !! "PC" = Some pc →
      ins !! pc = Some i →
      fns !! f = Some fn →
      f2i !! f = Some pc →
      imp_to_asm_args pb ret rs vs →
      length vs = length (fd_args fn) →
      (* Call *)
      (∀ K' rs' mem' f' es vs pc' i' ret' b h' pb' lr,
          Forall2 (λ e v, e = Val v) es vs →
          rs' !! "PC" = Some pc' →
          ins !! pc' = None →
          fns !! f' = None →
          f2i !! f' = Some pc' →
          imp_to_asm_args pb' ret' rs' vs →
          ins !! ret' = Some i' →
          imp_to_asm_phys_blocks_extend pb pb' →
          map_scramble touched_registers lr rs' →
          (∀ rs'' mem'' v h'' pb'',
              rs'' !! "PC" = Some ret' →
              imp_to_asm_ret pb'' rs'' rs' v →
              imp_to_asm_mem_rel (rs'' !!! "SP") mem'' mem' →
              imp_to_asm_phys_blocks_extend pb' pb'' →
              AsmState (Some i') rs'' mem'' ins ⪯{asm_module, imp_to_asm ins_dom fns_dom f2i imp_module, n, false}
               (SMProg, Imp (expr_fill K (expr_fill K' (Val v))) h'' fns, (PPInside, I2A cs pb'' rs''))) →
          AsmState (Some []) rs' mem' ins ⪯{asm_module, imp_to_asm ins_dom fns_dom f2i imp_module, n, b}
               (SMProg, Imp (expr_fill K (expr_fill K' (imp.Call f' es))) h' fns, (PPInside, I2A cs pb' lr))) →
      (* Return *)
      (∀ rs' mem' v h' b pb' lr,
          rs' !! "PC" = Some ret →
          imp_to_asm_ret pb' rs' rs v  →
          imp_to_asm_mem_rel (rs' !!! "SP") mem' mem →
          imp_to_asm_phys_blocks_extend pb pb' →
          map_scramble touched_registers lr rs' →
          AsmState (Some []) rs' mem' ins ⪯{asm_module, imp_to_asm ins_dom fns_dom f2i imp_module, n, b}
               (SMProg, Imp (expr_fill K (Val v)) h' fns, (PPInside, I2A cs pb' lr))) →
      AsmState (Some i) rs mem ins ⪯{asm_module, imp_to_asm ins_dom fns_dom f2i imp_module, n, false}
               (SMProg, Imp (expr_fill K (subst_l fn.(fd_args) vs fn.(fd_body))) h fns, (PPInside, I2A cs pb rs))
) →
  trefines (MS asm_module (initial_asm_state ins))
           (MS (imp_to_asm ins_dom fns_dom f2i imp_module) (initial_imp_to_asm_state imp_module
             (initial_imp_state fns))).
Proof.
  move => -> -> Hf.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { simpl. exact: (λ n' '(AsmState i rs mem ins') '(σfs, Imp e h fns', (t, I2A cs pb lr)),
     ∃ K b pb' lr', i = None ∧ ins = ins' ∧ e = expr_fill K (Waiting b) ∧ fns = fns' ∧
              t = PPOutside ∧ σfs = SMFilter ∧
              imp_to_asm_phys_blocks_extend pb' pb ∧
              imp_to_asm_proof_stack n' ins fns f2i b K (I2A cs pb' lr')
). }
  { eexists []. split!; [done|]. econs. } {
    clear => /= n n' [????] [[?[???]][?[???]]] Hsub ?. destruct_all?; simplify_eq. split!; [done..|].
    instantiate (1:=lr').
    elim: H7 n' Hsub; [by econs|].
    move => *. econs; [ naive_solver..|]. move => *. apply: tsim_mono; [|done]. naive_solver.
  }
  move => {}n _ /= IH [i rs mem ins'] [[?[???]][?[???]]] ?. destruct_all?; simplify_eq/=.
  tstep_i => ??????.
  go_s. split!.
  go_s => -[] ? /=.
  - move => ret fn vs h pb /elem_of_dom[??] ? /not_elem_of_dom ? ??.
    go_s. split!. case_bool_decide; [|by go_s].
    match goal with | |- context [ReturnExt b ?e] => change (ReturnExt b e) with (expr_fill [ReturnExtCtx b] e) end.
    rewrite -expr_fill_app.
    apply: tsim_mono_b.
    apply: Hf; [done..| |].
    + move => K' rs' mem' f' es vs' pc i' ret' ? h' ? lr Hall ???????? Hret. go.
      have ?: es = Val <$> vs'. { clear -Hall. elim: Hall; naive_solver. } subst.
      tstep_i => ??. simplify_map_eq. rewrite orb_true_r.
      go_s. right. split!.
      go_s. split!. { by apply not_elem_of_dom. } { by apply elem_of_dom. }
      apply IH; [done|].
      split!; [done..|reflexivity|].
      econs; [done..| |]. by etrans; [done|etrans]. move => *. simplify_map_eq.
      rewrite !expr_fill_app /=.
      apply: tsim_mono_b.
      apply Hret; [done..|].
      by etrans; [|done].
    + move => *. go.
      tstep_i => ??. simplify_map_eq. rewrite orb_true_r.
      go_s.
      go_s. split!; [done..|].
      apply IH; [done|]. split!; [done| |done]. by etrans; [done|etrans].
  - move => *.
    revert select (imp_to_asm_proof_stack _ _ _ _ _ _ _) => HK.
    inversion HK; clear HK; simplify_eq.
    go_s. split!.
    apply: H7; [done..|]. by etrans.
    Unshelve. apply: inhabitant.
Qed.
