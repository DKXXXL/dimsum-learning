Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.filter.
Require Import refframe.product.
Require Import refframe.seq_product.
Require Import refframe.proof_techniques.

Local Open Scope Z_scope.
(** * Assembly language *)
Inductive asm_instr_event :=
| WriteReg (r : string) (f : gmap string Z → Z).

Definition asm_instr := list asm_instr_event.

Inductive asm_state := AsmState {
  asm_cur_instr : option asm_instr;
  asm_regs : gmap string Z;
  asm_instrs : gmap Z asm_instr;
}.
Add Printing Constructor asm_state.

Definition initial_asm_state (instrs : gmap Z asm_instr) := AsmState None ∅ instrs.

Inductive asm_event :=
| EAJump (pc : Z) (regs : gmap string Z) | EARecvJump (pc : Z) (regs : gmap string Z).

Inductive asm_step : asm_state → option asm_event → (asm_state → Prop) → Prop :=
| SWriteReg regs instrs r f es:
  asm_step (AsmState (Some (WriteReg r f :: es)) regs instrs) None
           (λ σ', is_Some (regs !! r) ∧ σ' = AsmState (Some es) (<[r := f regs]>regs) instrs)
| SJumpInternal regs instrs pc es :
  (* TODO: Make it UB instead of NB if there is no PC in regs? *)
  regs !! "PC" = Some pc →
  instrs !! pc = Some es →
  asm_step (AsmState (Some []) regs instrs) None (λ σ', σ' = AsmState (Some es) regs instrs)
| SJumpExternal regs instrs pc :
  (* TODO: Make it UB instead of NB if there is no PC in regs? *)
  regs !! "PC" = Some pc →
  instrs !! pc = None →
  asm_step (AsmState (Some []) regs instrs) (Some (EAJump pc regs)) (λ σ', σ' = AsmState None regs instrs)
| SRecvJump regs regs' instrs pc es :
  regs' !! "PC" = Some pc →
  instrs !! pc = Some es →
  asm_step (AsmState None regs instrs) (Some (EARecvJump pc regs')) (λ σ', σ' = AsmState (Some es) regs' instrs)
.

Definition asm_module := Mod asm_step.
Global Hint Transparent asm_module : tstep.

Global Instance asm_vis_no_all: VisNoAll asm_module.
Proof. move => *. invert_all @m_step; naive_solver. Qed.

(** * tstep *)
Global Hint Transparent asm_instr : tstep.

Lemma asm_step_WriteReg_i r f es rs ins:
  TStepI asm_module (AsmState (Some (WriteReg r f::es)) rs ins)
            (λ G, G true None (λ G', is_Some (rs !! r) ∧ G' (AsmState (Some (es)) (<[r:=f rs]>rs) ins))).
Proof.
  constructor => ? ?. apply TDStep => ???. left.
  invert_all @m_step. eexists _. split; [done|].
  move => ? /=. naive_solver.
Qed.
Global Hint Resolve asm_step_WriteReg_i : tstep.

Lemma asm_step_WriteReg_s r f es rs ins:
  TStepS asm_module (AsmState (Some (WriteReg r f::es)) rs ins)
            (λ G, G None (λ G', is_Some (rs !! r) → G' (AsmState (Some (es)) (<[r:=f rs]>rs) ins))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= ?.
  tstep_None. { econs. }
  move => ? /= [? ->]. tend. naive_solver.
Qed.
Global Hint Resolve asm_step_WriteReg_s : tstep.

Lemma asm_step_Jump_i rs ins:
  TStepI asm_module (AsmState (Some []) rs ins) (λ G,
    ∀ pc, rs !! "PC" = Some pc →
          if ins !! pc is Some i then
            G true None (λ G', G' (AsmState (Some i) (rs) ins))
          else
            G true (Some (EAJump pc rs)) (λ G', G' (AsmState None (rs) ins))
   ).
Proof.
  constructor => ? HG. apply TDStep => ???. left.
  invert_all @m_step; specialize (HG _ ltac:(done)); simplify_option_eq.
  all: eexists _; split; [done|]; naive_solver.
Qed.
Global Hint Resolve asm_step_Jump_i : tstep.

Lemma asm_step_Jump_s rs ins:
  TStepS asm_module (AsmState (Some []) rs ins) (λ G,
    ∃ pc, rs !! "PC" = Some pc ∧
      if ins !! pc is Some i then
        G None (λ G', G' (AsmState (Some i) (rs) ins))
      else
        G (Some (EAJump pc rs)) (λ G', G' (AsmState None rs ins))).
Proof.
  constructor => ?[?[??]]. case_match.
  all: eexists _, _; split; [done|] => ? /= ?.
  - tstep_None. { by econs. } move => ? ->. tend.
  - tstep_Some. { by econs. } move => ? ->. tend.
Qed.
Global Hint Resolve asm_step_Jump_s : tstep.

Lemma asm_step_None_i rs ins:
  TStepI asm_module (AsmState None rs ins) (λ G,
    ∀ pc i rs', rs' !! "PC" = Some pc →
      ins !! pc = Some i →
      G true (Some (EARecvJump pc rs')) (λ G', G' (AsmState (Some i) rs' ins))
   ).
Proof.
  constructor => ? HG. apply TDStep => ???. left.
  invert_all @m_step. eexists _. split; [naive_solver|]. naive_solver.
Qed.
Global Hint Resolve asm_step_None_i : tstep.

Lemma asm_step_None_s rs ins:
  TStepS asm_module (AsmState None rs ins) (λ G,
    ∃ pc i rs', rs' !! "PC" = Some pc ∧
      ins !! pc = Some i ∧
      G (Some (EARecvJump pc rs')) (λ G', G' (AsmState (Some i) rs' ins))).
Proof.
  constructor => ??. destruct_all!. eexists _, _. split; [done|] => ? /= ?.
  tstep_Some. { by econs. } move => ? ->. tend.
Qed.
Global Hint Resolve asm_step_None_s : tstep.

(** * syntactic linking *)
Definition asm_link (instrs1 instrs2 : gmap Z asm_instr) : gmap Z asm_instr :=
  instrs1 ∪ instrs2.

Definition asm_ctx_refines (instrsi instrss : gmap Z asm_instr) :=
  ∀ C, trefines (MS asm_module (initial_asm_state (asm_link instrsi C)))
                (MS asm_module (initial_asm_state (asm_link instrss C))).

(** * semantic linking *)
Inductive asm_prod_filter_state :=
| APFLeft | APFRight | APFNone
| APFRecvL (pc : Z) (rs : gmap string Z) | APFRecvR (pc : Z) (rs : gmap string Z).

Inductive asm_prod_filter (ins1 ins2 : gset Z) :
  asm_prod_filter_state → (seq_product_event asm_event asm_event) → option asm_event → asm_prod_filter_state →  Prop :=
| APFJumpRecvL pc rs:
  pc ∉ ins1 →
  pc ∈ ins2 →
  asm_prod_filter ins1 ins2 APFLeft (SPELeft (EAJump pc rs) SPRight) None (APFRecvR pc rs)
| APFJumpRecvL2 pc rs:
  asm_prod_filter ins1 ins2 (APFRecvR pc rs) (SPERight (EARecvJump pc rs) SPRight) None APFRight
| APFJumpRecvR pc rs:
  pc ∈ ins1 →
  pc ∉ ins2 →
  asm_prod_filter ins1 ins2 APFRight (SPERight (EAJump pc rs) SPLeft) None (APFRecvL pc rs)
| APFJumpRecvR2 pc rs:
  asm_prod_filter ins1 ins2 (APFRecvL pc rs) (SPELeft (EARecvJump pc rs) SPLeft) None APFLeft
| APFJumpExtL pc rs:
  pc ∉ ins1 →
  pc ∉ ins2 →
  asm_prod_filter ins1 ins2 APFLeft (SPELeft (EAJump pc rs) SPNone) (Some (EAJump pc rs)) APFNone
| APFJumpExtR pc rs:
  pc ∉ ins1 →
  pc ∉ ins2 →
  asm_prod_filter ins1 ins2 APFRight (SPERight (EAJump pc rs) SPNone) (Some (EAJump pc rs)) APFNone
| APFRecvJumpL pc rs:
  pc ∈ ins1 →
  pc ∉ ins2 →
  rs !! "PC" = Some pc →
  asm_prod_filter ins1 ins2 APFNone (SPENone SPLeft) (Some (EARecvJump pc rs)) (APFRecvL pc rs)
| APFRecvJumpR pc rs:
  pc ∉ ins1 →
  pc ∈ ins2 →
  rs !! "PC" = Some pc →
  asm_prod_filter ins1 ins2 APFNone (SPENone SPRight) (Some (EARecvJump pc rs)) (APFRecvR pc rs)
.

Definition asm_prod (ins1 ins2 : gset Z) (m1 m2 : module asm_event) : module asm_event :=
  mod_map (mod_seq_product m1 m2) (asm_prod_filter ins1 ins2).
Global Hint Transparent asm_prod : tstep.

Definition asm_link_prod_inv (ins1 ins2 : gmap Z asm_instr) (σ1 : asm_module.(m_state)) (σ2 : ((seq_product_state * asm_state * asm_state) * asm_prod_filter_state)) : Prop :=
  let 'AsmState i1 rs1 ins1' := σ1 in
  let '((σsp, AsmState il rsl insl, AsmState ir rsr insr), σf) := σ2 in
  ins1' = ins1 ∪ ins2 ∧
  insl = ins1 ∧
  insr = ins2 ∧
  match σf with
  | APFLeft => σsp = SPLeft ∧ is_Some i1 ∧ il = i1 ∧ rsl = rs1 ∧ ir = None
  | APFRight => σsp = SPRight ∧ is_Some i1 ∧ ir = i1 ∧ rsr = rs1 ∧ il = None
  | APFNone => σsp = SPNone ∧ i1 = None ∧ ir = None ∧ il = None
  | _ => False
  end.


Lemma asm_link_refines_prod ins1 ins2:
  ins1 ##ₘ ins2 →
  trefines (MS asm_module (initial_asm_state (asm_link ins1 ins2)))
           (MS (asm_prod (dom _ ins1) (dom _ ins2) asm_module asm_module) (SPNone, initial_asm_state ins1, initial_asm_state ins2, APFNone)).
Proof.
  move => Hdisj.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { exact: (λ _, asm_link_prod_inv ins1 ins2). }
  { naive_solver. } { done. }
  move => /= {}n Hloop [i1 rs1 ins1'] [[[? [il rsl insl]] [ir rsr insr] σf]] [? [? [? Hinv]]].
  case_match; destruct_all?; simplify_eq.
  - revert select (is_Some i1) => -[[|[??]?] ->].
    + tstep_i => pc ?. case_match as Hunion. 1: move: Hunion => /lookup_union_Some_raw[Hl|[? Hl]].
      * tstep_s. eexists _. split; [done|]. simplify_option_eq.
        eexists _. split; [done|]. eexists _, _. split; [done|] => /=.
        apply: Hloop. naive_solver.
      * tstep_s. eexists _. split; [done|]. simplify_option_eq.
        eexists _. split; [done|]. eexists _, _. split; [econs|].
        { by apply not_elem_of_dom. } { by apply elem_of_dom. } simpl.
        tstep_s. eexists _, _, _. split; [done|]. split; [done|]. eexists _. split; [done|].
        eexists _, _. split; [econs|]. simpl.
        apply: Hloop. naive_solver.
      * move: Hunion => /lookup_union_None[??]. tstep_s. eexists _. split; [done|]. simplify_option_eq.
        eexists _. split; [done|]. eexists _, _. split; [by apply APFJumpExtL; apply not_elem_of_dom|] => /=.
        split; [done|]. apply: Hloop. naive_solver.
    + tstep_both. tstep_s. eexists _. split; [done|]. eexists _, _. split; [done|] => /= ?.
      tend. split; [done|]. apply: Hloop. naive_solver.
  - revert select (is_Some i1) => -[[|[??]?] ->].
    + tstep_i => pc ?. case_match as Hunion. 1: move: Hunion => /lookup_union_Some_raw[Hl|[? Hl]].
      * have ?: ins2 !! pc = None by apply: map_disjoint_Some_l.
        tstep_s. eexists _. split; [done|]. simplify_option_eq.
        eexists _. split; [done|]. eexists _, _. split; [econs|] => /=.
        { by apply elem_of_dom. } { by apply not_elem_of_dom. }
        tstep_s. eexists _, _, _. split; [done|]. split; [done|]. eexists _. split; [done|].
        eexists _, _. split; [econs|]. simpl.
        apply: Hloop. naive_solver.
      * tstep_s. eexists _. split; [done|]. simplify_option_eq.
        eexists _. split; [done|]. eexists _, _. split; [done|] => /=.
        apply: Hloop. naive_solver.
      * move: Hunion => /lookup_union_None[??]. tstep_s. eexists _. split; [done|]. simplify_option_eq.
        eexists _. split; [done|]. eexists _, _. split; [by apply APFJumpExtR; apply not_elem_of_dom|] => /=.
        split; [done|]. apply: Hloop. naive_solver.
    + tstep_both. tstep_s. eexists _. split; [done|]. eexists _, _. split; [done|] => /= ?.
      tend. split; [done|]. apply: Hloop. naive_solver.
  - tstep_i => pc??? /lookup_union_Some_raw[?|[??]].
    + have ?: ins2 !! pc = None by apply: map_disjoint_Some_l.
      tstep_s. eexists SPLeft, _, _. split; [econs|] => /=.
      { by apply elem_of_dom. } { by apply not_elem_of_dom. } { done. }
      split; [done|].
      tstep_s. eexists _, _, _. split; [done|]. split; [done|]. eexists _. split; [done|].
      eexists _, _. split; [econs|] => /=.
      apply: Hloop. naive_solver.
    + tstep_s. eexists SPRight, _, _. split; [econs|] => /=.
      { by apply not_elem_of_dom. } { by apply elem_of_dom. } { done. }
      split; [done|].
      tstep_s. eexists _, _, _. split; [done|]. split; [done|]. eexists _. split; [done|].
      eexists _, _. split; [econs|] => /=.
      apply: Hloop. naive_solver.
Qed.

Lemma asm_prod_refines_link ins1 ins2:
  ins1 ##ₘ ins2 →
  trefines (MS (asm_prod (dom _ ins1) (dom _ ins2) asm_module asm_module) (SPNone, initial_asm_state ins1, initial_asm_state ins2, APFNone))
           (MS asm_module (initial_asm_state (asm_link ins1 ins2))).
Proof.
  move => Hdisj.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { exact: (λ _, flip (asm_link_prod_inv ins1 ins2)). }
  { naive_solver. } { done. }
  move => /= {}n Hloop [[[σsp [il rsl insl]] [ir rsr insr]] σf] [i1 rs1 ins1'] [? [? [? Hinv]]].
  case_match; destruct_all?; simplify_eq.
  - revert select (is_Some i1) => -[[|[??]?] ->].
    + tstep_i => pc ?. case_match => *; destruct_all?; simplify_eq.
      * tstep_s. eexists _. split; [done|]. erewrite lookup_union_Some_l by done.
        apply: Hloop. naive_solver.
      * invert_all asm_prod_filter; tstep_s; eexists _; (split; [done|]).
        -- revert select (pc ∈ dom _ _) => /elem_of_dom[??].
           erewrite lookup_union_Some_r by done.
           tstep_i => *. invert_all asm_prod_filter.
           apply: Hloop. naive_solver.
        -- rewrite lookup_union_None_2; [by apply not_elem_of_dom..|]. split; [done|].
           apply: Hloop. naive_solver.
    + tstep_both => *. destruct_all!. simplify_eq.
      tstep_s => ?. tend. split; [done|].
      apply: Hloop. naive_solver.
  - revert select (is_Some i1) => -[[|[??]?] ->].
    + tstep_i => pc ?. case_match => *; destruct_all?; simplify_eq.
      * tstep_s. eexists _. split; [done|]. erewrite lookup_union_Some_r by done.
        apply: Hloop. naive_solver.
      * invert_all asm_prod_filter; tstep_s; eexists _; (split; [done|]).
        -- revert select (pc ∈ dom _ _) => /elem_of_dom[??].
           erewrite lookup_union_Some_l by done.
           tstep_i => *. invert_all asm_prod_filter.
           apply: Hloop. naive_solver.
        -- rewrite lookup_union_None_2; [by apply not_elem_of_dom..|]. split; [done|].
           apply: Hloop. naive_solver.
    + tstep_both => *. destruct_all!. simplify_eq.
      tstep_s => ?. tend. split; [done|].
      apply: Hloop. naive_solver.
  - tstep_i => *. invert_all asm_prod_filter; tstep_s.
    all: revert select (pc ∈ dom _ _) => /elem_of_dom[??].
    all: eexists _, _, _; split_and!; [done|by simplify_map_eq|done|].
    all: tstep_i => *; invert_all asm_prod_filter.
    all: apply: Hloop; try naive_solver.
Qed.

Lemma asm_trefines_implies_ctx_refines insi inss :
  dom (gset _) insi = dom (gset _) inss →
  trefines (MS asm_module (initial_asm_state insi)) (MS asm_module (initial_asm_state inss)) →
  asm_ctx_refines insi inss.
Proof.
  move => Hdom Href C. rewrite /asm_link map_difference_union_r (map_difference_union_r inss).
  etrans. { apply asm_link_refines_prod. apply map_disjoint_difference_r'. }
  etrans. 2: { apply asm_prod_refines_link. apply map_disjoint_difference_r'. }
  rewrite !dom_difference_L Hdom.
  apply mod_map_trefines.
  apply: mod_seq_product_trefines.
  - apply: Href.
  - erewrite map_difference_eq_dom_L => //. apply _.
Qed.

Require Import refframe.itree.
(* TODO: Get rid of Some in recursive call (maybe by passing an itree to t instead of the +'? ) *)
(* TODO: prove merging of two asm loops (should just be all choice between the two implementations ) *)
Definition asm_loop (ins : list Z)
   (t : Z → gmap string Z → itree (callE
     (option (Z * gmap string Z)) (Z * gmap string Z) +' moduleE asm_event unit) (Z * gmap string Z))
  : itree (moduleE asm_event unit) unit :=
  rec (λ a,
    '(pc, rs) ← (
       if a is Some (npc, nrs) then
         if bool_decide (npc ∈ ins) then
           Ret (npc, nrs)
         else
           translate (inr_) (TVis (EAJump npc nrs));;;;
           pc ← translate (inr_) (TExist Z);;;
           rs ← translate (inr_) (TExist _);;;
           translate (inr_) (TVis (EARecvJump pc rs));;;;
           Ret (pc, rs)
        else
          pc ← translate (inr_) (TExist Z);;;
          rs ← translate (inr_) (TExist _);;;
          translate (inr_) (TVis (EARecvJump pc rs));;;;
          Ret (pc, rs)
     );;;
    translate (inr_) (TAssert (pc ∈ ins));;;;
    (* The env can choose if this call should be treated as a call or a return. *)
    b ← translate (inr_) (TAll bool);;;
    if b then Ret (pc, rs) else
      r ← t pc rs;;;
      call (Some r)
    ) None;;;; TUb.

Lemma tsim_asm_loop n b rs ins t insaddrs:
  (∀ z, z ∈ insaddrs ↔ is_Some (ins !! z)) →
  (∀ n rc pc' rs' i k,
      rs' !! "PC" = Some pc' →
      ins !! pc' = Some i →
      (∀ pc'' rs1'' rs2'' h',
         rs1'' = rs2'' →
         rs1'' !! "PC" = Some pc'' →
          (∀ pc''' rs''' i,
              rs''' !! "PC" = Some pc''' → ins !! pc''' = Some i →
              AsmState (Some i) rs''' ins ⪯{asm_module, mod_itree asm_event (), n, b} (h' (pc''', rs'''), ())) →
          (AsmState (Some []) rs1'' ins)
            ⪯{asm_module, mod_itree asm_event (), n, true}
          (y ← rec rc (Some (pc'', rs2''));;; h' y, ())) →
      (∀ pc rs1 rs2,
          rs1 = rs2 →
          rs1 !! "PC" = Some pc →
          tsim n true asm_module (mod_itree asm_event ()) (AsmState (Some []) rs1 ins) tnil (k (pc, rs2), ())) →
    AsmState (Some i) rs' ins ⪯{asm_module, mod_itree asm_event (), n, true}
       (r ← interp (recursive rc) (t pc' rs');;; k r, ())) →
  (** Then we can prove an asm_loop *)
  AsmState None rs ins ⪯{asm_module, mod_itree asm_event (), n, b} (asm_loop insaddrs t, ()).
Proof.
  rewrite /asm_loop => Hins Hl. set rc := (X in (rec X)).
  apply (tsim_remember_rec (mi:=asm_module)
   (λ a σi s,
     if a is Some (pc, rs) then
       σi = AsmState (Some []) rs ins ∧ rs !! "PC" = Some pc
     else
       ∃ rs, σi = AsmState None rs ins
   )
   (λ σi '(pc, rs) s', ∃ i, σi = AsmState (Some i) rs ins ∧ rs !! "PC" = Some pc ∧ ins !! pc = Some i)).
  { naive_solver. }
  { move => ????. rewrite -(bind_ret_r TUb). by tstep_s. }
  move => {}n Hloop σi [] CONT a Ha HCONT.
  destruct a as [[pc' rs']|]. 2: {
    move: Ha => [{}rs ?]. subst.
    tstep_i => pc i {}rs HPC Hi.
    rewrite {1}rec_as_interp {2}/rc.
    rewrite bind_bind.
    tstep_s => ? <- /=. tstep_s. eexists _ => ? <- /=. rewrite bind_bind.
    tstep_s => ? <- /=. tstep_s. eexists _ => ? <- /=. rewrite bind_bind.
    tstep_s => ? <- /=. tstep_s. split; [done|] => ? <- /=. rewrite bind_ret_l.
    tstep_s => ? <- /=. tstep_s. split. { apply Hins. naive_solver. } move => ? <- /=.
    tstep_s => ? <- /=. tstep_s => -[] ? <- /=.
    { tstep_s => ? <- /=. apply: tsim_mono_b. apply HCONT. naive_solver. }
    rewrite interp_bind bind_bind.
    apply: Hl; [done..| |].
    - move => ???????. subst. apply Hloop; [done|].
      move => ? [rs' pc'] []. naive_solver.
    - move => ?????. rewrite interp_recursive_call.
      apply Hloop. { naive_solver. }
      move => ? [??] [] [?[??]]. apply: HCONT. naive_solver.
  }
  destruct Ha. simplify_eq.
  tstep_i => pc HPC. simplify_eq.
  case_match.
  - rewrite {1}rec_as_interp {2}/rc. rewrite bool_decide_true. { apply Hins. naive_solver. }
    rewrite bind_ret_l.
    tstep_s => ? <- /=. tstep_s. split. { apply Hins. naive_solver. } move => ? <- /=.
    tstep_s => ? <- /=. tstep_s => -[] ? <- /=.
    { tstep_s => ? <- /=. apply: tsim_mono_b. apply HCONT. naive_solver. }
    rewrite interp_bind bind_bind.
    apply: Hl; [done..| |].
    + move => ???????. subst. apply Hloop; [done|].
      move => ? [? ?] []. naive_solver.
    + move => ?????. rewrite interp_recursive_call.
      apply Hloop. { naive_solver. }
      move => ? [??] [] [?[??]]. apply: HCONT. naive_solver.
  - rewrite {1}rec_as_interp {2}/rc. rewrite bool_decide_false. { move => /Hins[??]. naive_solver. }
    rewrite bind_bind.
    tstep_s => ? <- /=. tstep_s. split; [done|] => ? <- /=. rewrite bind_bind.
    tstep_i => pc i {}rs HPC Hi.
    tstep_s => ? <- /=. tstep_s. eexists _ => ? <- /=. rewrite bind_bind.
    tstep_s => ? <- /=. tstep_s. eexists _ => ? <- /=. rewrite bind_bind.
    tstep_s => ? <- /=. tstep_s. split; [done|] => ? <- /=. rewrite bind_ret_l.
    tstep_s => ? <- /=. tstep_s. split. { apply Hins. naive_solver. } move  => ? <- /=.
    tstep_s => ? <- /=. tstep_s => -[] ? <- /=.
    { tstep_s => ? <- /=. apply: tsim_mono_b. apply HCONT. naive_solver. }
    rewrite interp_bind bind_bind.
    apply: Hl; [done..| |].
    + move => ???????. subst. apply Hloop; [done|].
      move => ? [? ?] []. naive_solver.
    + move => ?????. rewrite interp_recursive_call.
      apply Hloop. { naive_solver. }
      move => ? [??] [] [?[??]]. apply: HCONT. naive_solver.
Qed.

Module asm_examples.
  Local Open Scope Z_scope.
  Definition asm_mul : gmap Z asm_instr :=
    <[ 100 := [
          (* mul R1, R1, R2 *)
          WriteReg "R1" (λ rs, rs !!! "R1" * rs !!! "R2");
          WriteReg "PC" (λ rs, rs !!! "PC" + 4)
      ] ]> $
    <[ 104 := [
          (* ret *)
          WriteReg "PC" (λ rs, rs !!! "R30")
      ] ]> $ ∅.

  Definition itree_mul : itree (moduleE asm_event unit) unit :=
    asm_loop [100; 104] (λ pc rs,
       if bool_decide (pc = 100) then
         r1 ← translate (inr_) (TAssumeOpt (rs !! "R1"));;;
         r2 ← translate (inr_) (TAssumeOpt (rs !! "R2"));;;
         r30 ← translate (inr_) (TAssumeOpt (rs !! "R30"));;;
         Ret (r30, (<["PC":=r30]> $ <["R1":=r1 * r2]> $ rs))
       else if bool_decide (pc = 104) then
         translate (inr_) TUb
       else
         translate (inr_) TNb
    ).


  Lemma asm_mul_refines_itree :
    trefines (MS asm_module (initial_asm_state asm_mul)) (MS (mod_itree _ _) (itree_mul, tt)).
  Proof.
    apply tsim_implies_trefines => /= n. rewrite /initial_asm_state.
    rewrite {1}/itree_mul.
    apply tsim_asm_loop. {
      move => z. rewrite !elem_of_cons elem_of_nil.
      rewrite !lookup_insert_is_Some' lookup_empty -not_eq_None_Some.
      naive_solver.
    }
    move => {}n rc pc rs i CONT HPC Hi Hloop HCONT.
    move: Hi. rewrite !lookup_insert_Some !lookup_empty => Hi. destruct_all!; simplify_eq.
    all: repeat (rewrite bool_decide_false; [done|]); rewrite bool_decide_true //.
    all: try by tstep_s => ? <- /=; tstep_s.

    tstep_s => ? <- /=. tstep_s => r1 HR1 ? <- /=.
    tstep_s => ? <- /=. tstep_s => r2 HR2 ? <- /=.
    tstep_s => ? <- /=. tstep_s => r30 HR30 ? <- /=.
    tstep_s => ? <- /=.
    tstep_i. split. { by simplify_map_eq. }
    erewrite lookup_total_correct; [|done]. erewrite lookup_total_correct; [|done].
    tstep_i. split. { by simplify_map_eq. }
    erewrite lookup_total_correct; [|by simplify_map_eq].
    tstep_i => ??. simplify_map_eq.
    tstep_i. split. { by simplify_map_eq. }
    erewrite lookup_total_correct; [|by simplify_map_eq].
    apply HCONT; simplify_map_eq => //. by rewrite insert_insert.
  Qed.

  Definition asm_mul_client : gmap Z asm_instr :=
    <[ 200 := [
          (* mov R1, 2; mov R2, 2; *)
          WriteReg "R1" (λ rs, 2);
          WriteReg "R2" (λ rs, 2);
          WriteReg "PC" (λ rs, rs !!! "PC" + 4)
      ] ]> $
    <[ 204 := [
          (* mov R29, R30; *)
          WriteReg "R29" (λ rs, rs !!! "R30");
          WriteReg "PC" (λ rs, rs !!! "PC" + 4)
      ] ]> $
    <[ 208 := [
          (* bl 100; *)
          WriteReg "R30" (λ rs, rs !!! "PC" + 4);
          WriteReg "PC" (λ rs, 100)
      ] ]> $
    <[ 212 := [
          (* mov R30, R29; *)
          WriteReg "R30" (λ rs, rs !!! "R29");
          WriteReg "PC" (λ rs, rs !!! "PC" + 4)
      ] ]> $
    <[ 216 := [
          (* ret; *)
          WriteReg "PC" (λ rs, rs !!! "R30")
      ] ]> $ ∅.

  Definition itree_mul_client : itree (moduleE asm_event unit) unit :=
    asm_loop [200; 204; 208; 212; 216] (λ pc rs,
       if bool_decide (pc = 200) then
         translate (inr_) (TAssume (is_Some (rs !! "R1")));;;;
         translate (inr_) (TAssume (is_Some (rs !! "R2")));;;;
         translate (inr_) (TAssume (is_Some (rs !! "R29")));;;;
         r30 ← translate (inr_) (TAssumeOpt (rs !! "R30"));;;
         r29' ← translate (inr_) (TExist Z);;;
         (* translate (inr_) (TVis (EAJump 100 (<["PC":=100]> $ <["R30":= 212]> $ <["R29":= r29']> $ <["R2":= 2]> $ <["R1":= 2]> $ rs)));;;; *)
         '(pc', rs') ← call (Some (100, (<["PC":=100]> $ <["R30":= 212]> $ <["R29":= r29']> $ <["R2":= 2]> $ <["R1":= 2]> $ rs)));;;
         translate (inr_) (TAssume (pc' = 212));;;;
         translate (inr_) (TAssume (is_Some (rs' !! "R30")));;;;
         translate (inr_) (TAssume (rs' !! "R29" = Some r29'));;;;
         translate (inr_) (TAssume (r30 ≠ 200 ∧ r30 ≠ 204 ∧ r30 ≠ 208 ∧ r30 ≠ 212 ∧ r30 ≠ 216));;;;
         r30' ← translate (inr_) (TExist Z);;;
         (* translate (inr_) (TVis (EAJump r30 (<["PC":= r30]> $ <["R30":= r30']> rs')));;;; *)
         Ret (r30, (<["PC":= r30]> $ <["R30":= r30']> rs'))
       else if bool_decide (pc = 204) then translate (inr_) TUb
       else if bool_decide (pc = 208) then translate (inr_) TUb
       else if bool_decide (pc = 212) then translate (inr_) TUb
       else if bool_decide (pc = 216) then translate (inr_) TUb
       else translate (inr_) TNb
    ).


  Lemma asm_mul_client_refines_itree :
    trefines (MS asm_module (initial_asm_state asm_mul_client)) (MS (mod_itree _ _) (itree_mul_client, tt)).
  Proof.
    apply tsim_implies_trefines => /= n. rewrite /initial_asm_state.
    rewrite {1}/itree_mul_client.
    apply tsim_asm_loop. {
      move => z. rewrite !elem_of_cons elem_of_nil.
      rewrite !lookup_insert_is_Some' lookup_empty -not_eq_None_Some.
      naive_solver.
    }
    move=> {}n rc pc rs i CONT HPC Hi Hloop HCONT.
    move: Hi. rewrite !lookup_insert_Some !lookup_empty => Hi. destruct_all!; simplify_eq.
    all: repeat (rewrite bool_decide_false; [done|]); rewrite bool_decide_true //.
    all: try by tstep_s => ? <- /=; tstep_s.

    tstep_s => ? <- /=. tstep_s => -[r1 HR1] ? <- /=.
    tstep_s => ? <- /=. tstep_s => -[r2 HR2] ? <- /=.
    tstep_s => ? <- /=. tstep_s => -[r29 HR29] ? <- /=.
    tstep_s => ? <- /=. tstep_s => r30 HR30 ? <- /=.
    tstep_i. split; [ by simplify_map_eq|].
    tstep_i. split; [ by simplify_map_eq|].
    tstep_i. split; [ by simplify_map_eq|].
    erewrite lookup_total_correct; [|by simplify_map_eq].
    tstep_i => ??. simplify_map_eq.
    tstep_i. split; [ by simplify_map_eq|].
    erewrite lookup_total_correct; [|by simplify_map_eq].
    tstep_i. split; [ by simplify_map_eq|].
    erewrite lookup_total_correct; [|by simplify_map_eq].
    tstep_i => ??. simplify_map_eq.
    tstep_i. split; [ by simplify_map_eq|].
    erewrite lookup_total_correct; [|by simplify_map_eq].
    tstep_i. split; [ by simplify_map_eq|].
    rewrite insert_commute // insert_insert (insert_commute _ "PC") // insert_insert.
    tstep_s => ? <- /=. tstep_s. eexists r30 => ? <- /=.
    tstep_s => ? <- /=.
    apply Hloop. {
      apply map_eq => i. apply option_eq => ?.
      rewrite !lookup_insert_Some. naive_solver.
    } { by simplify_map_eq. }
    move => pc' rs'' i HPC' Hi'.
    tstep_s => ? <- /=. tstep_s => ? ? <- /=.
    unfold asm_mul_client in Hi'. simplify_map_eq.
    tstep_s => ? <- /=. tstep_s => -[r30'' HR30''] ? <- /=.
    tstep_s => ? <- /=. tstep_s => ? ? <- /=.
    tstep_s => ? <- /=. tstep_s => -[?[?[?[??]]]] ? <- /=.
    tstep_i. split; [ by simplify_map_eq|].
    erewrite lookup_total_correct; [|by simplify_map_eq].
    tstep_i. split; [ by simplify_map_eq|].
    erewrite lookup_total_correct; [|by simplify_map_eq].
    tstep_i => ??. simplify_map_eq.
    tstep_i. split; [ by simplify_map_eq|].
    erewrite lookup_total_correct; [|by simplify_map_eq].
    tstep_s => ? <- /=. tstep_s. eexists _ => ? <- /=.
    tstep_s => ? <- /=. apply HCONT. { by rewrite insert_insert. } { by simplify_map_eq. }
  Qed.
End asm_examples.
