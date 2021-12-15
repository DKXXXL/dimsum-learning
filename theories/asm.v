Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.filter.
Require Import refframe.product.
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
| EJump (pc : Z) (regs : gmap string Z) | ERecvJump (pc : Z) (regs : gmap string Z).

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
  asm_step (AsmState (Some []) regs instrs) (Some (EJump pc regs)) (λ σ', σ' = AsmState None regs instrs)
| SRecvJump regs regs' instrs pc es :
  regs' !! "PC" = Some pc →
  instrs !! pc = Some es →
  asm_step (AsmState None regs instrs) (Some (ERecvJump pc regs')) (λ σ', σ' = AsmState (Some es) regs' instrs)
.

Definition asm_module := Mod asm_step.

(** * syntactic linking *)
Definition asm_link (instrs1 instrs2 : gmap Z asm_instr) : gmap Z asm_instr :=
  instrs1 ∪ instrs2.

Definition asm_ctx_refines (instrsi instrss : gmap Z asm_instr) :=
  ∀ C, trefines (MS asm_module (initial_asm_state (asm_link instrsi C)))
                (MS asm_module (initial_asm_state (asm_link instrss C))).

(** * semantic linking *)
Inductive asm_prod_filter_state :=
| APFLeft | APFRight | APFNone.

Inductive asm_prod_filter_step (ins1 ins2 : gset Z) :
  asm_prod_filter_state → option ((option asm_event * option asm_event) * option asm_event) → (asm_prod_filter_state → Prop) →  Prop :=
| APFJumpRecvL pc rs:
  pc ∉ ins1 →
  pc ∈ ins2 →
  asm_prod_filter_step ins1 ins2
    APFLeft (Some ((Some (EJump pc rs), Some (ERecvJump pc rs)), None)) (λ σ, σ = APFRight)
| APFJumpRecvR pc rs:
  pc ∈ ins1 →
  pc ∉ ins2 →
  asm_prod_filter_step ins1 ins2
    APFRight (Some ((Some (ERecvJump pc rs), Some (EJump pc rs)), None)) (λ σ, σ = APFLeft)
| APFJumpExtL pc rs:
  pc ∉ ins1 →
  pc ∉ ins2 →
  asm_prod_filter_step ins1 ins2
    APFLeft (Some ((Some (EJump pc rs), None), Some (EJump pc rs))) (λ σ, σ = APFNone)
| APFJumpExtR pc rs:
  pc ∉ ins1 →
  pc ∉ ins2 →
  asm_prod_filter_step ins1 ins2
    APFRight (Some ((None, Some (EJump pc rs)), Some (EJump pc rs))) (λ σ, σ = APFNone)
| APFRecvJumpL pc rs:
  pc ∈ ins1 →
  pc ∉ ins2 →
  rs !! "PC" = Some pc →
  asm_prod_filter_step ins1 ins2
    APFNone (Some ((Some (ERecvJump pc rs), None), Some (ERecvJump pc rs))) (λ σ, σ = APFLeft)
| APFRecvJumpR pc rs:
  pc ∉ ins1 →
  pc ∈ ins2 →
  rs !! "PC" = Some pc →
  asm_prod_filter_step ins1 ins2
    APFNone (Some ((None, Some (ERecvJump pc rs)), Some (ERecvJump pc rs))) (λ σ, σ = APFRight)
.

Definition asm_prod_filter ins1 ins2 := Mod (asm_prod_filter_step ins1 ins2).

Definition asm_prod (ins1 ins2 : gset Z) (m1 m2 : module asm_event) : module asm_event :=
  mod_filter_mod (mod_product m1 m2) (asm_prod_filter ins1 ins2).

Definition asm_link_prod_inv (ins1 ins2 : gmap Z asm_instr) (σ1 : asm_module.(m_state)) (σ2 : (asm_state * asm_state * asm_prod_filter_state)) : Prop :=
  let 'AsmState i1 rs1 ins1' := σ1 in
  let '(AsmState il rsl insl, AsmState ir rsr insr, σf) := σ2 in
  ins1' = ins1 ∪ ins2 ∧
  insl = ins1 ∧
  insr = ins2 ∧
  match σf with
  | APFLeft => is_Some i1 ∧ il = i1 ∧ rsl = rs1 ∧ ir = None
  | APFRight => is_Some i1 ∧ ir = i1 ∧ rsr = rs1 ∧ il = None
  | APFNone => i1 = None ∧ ir = None ∧ il = None
  end.


Lemma asm_link_refines_prod ins1 ins2:
  ins1 ##ₘ ins2 →
  trefines (MS asm_module (initial_asm_state (asm_link ins1 ins2)))
           (MS (asm_prod (dom _ ins1) (dom _ ins2) asm_module asm_module) (initial_asm_state ins1, initial_asm_state ins2, APFNone)).
Proof.
  move => Hdisj.
  apply (inv_implies_trefines (MS _ _) (MS (asm_prod (dom _ ins1) (dom _ ins2) asm_module asm_module) _) (asm_link_prod_inv ins1 ins2)).
  { simpl. naive_solver. }
  move => /= [i1 rs1 ins1'] [[[il rsl insl] [ir rsr insr] σf]] Pσi κ [? [? [? Hinv]]] Hstep.
  inversion Hstep; clear Hstep; simplify_eq.
  - destruct σf; destruct_all!; simplify_eq.
    + tstep_None.
      { econs. { apply: ProductStepL. apply: ProductStepL. econs. } done. }
      move => /= *. destruct_all!; simplify_eq. tend. naive_solver.
    + tstep_None.
      { econs. { apply: ProductStepL. apply: ProductStepR. econs. } done. }
      move => /= *. destruct_all!; simplify_eq. tend. naive_solver.
  - destruct σf; destruct_and?; simplify_eq.
    + revert select ((_ ∪ _) !! _ = Some _) => /lookup_union_Some_raw[?|[??]].
      * tstep_None.
        { econs. { apply: ProductStepL. apply: ProductStepL. by apply: SJumpInternal. } done. }
        move => /= *. destruct_all!; simplify_eq. tend. naive_solver.
      * tstep_None. {
          econstructor. {
            apply: ProductStepBoth. {
              apply: ProductStepBoth. { by apply: SJumpExternal. } { by constructor. }
            }
            constructor; try eapply not_elem_of_dom; try eapply elem_of_dom_2; done.
          }
          done.
        }
        move => /= *. destruct_all!; simplify_eq. tend. naive_solver.
    + revert select ((_ ∪ _) !! _ = Some _) => /lookup_union_Some_raw[?|[??]].
      * tstep_None. {
          econs. {
            apply: ProductStepBoth. {
              apply: ProductStepBoth. { by constructor. }
              { apply: SJumpExternal; [done|]. by apply: map_disjoint_Some_l. }
            }
            constructor; try eapply not_elem_of_dom; try eapply elem_of_dom_2; try done.
            by apply: map_disjoint_Some_l.
          }
          done.
        }
        move => /= *. destruct_all!; simplify_eq. tend. naive_solver.
      * tstep_None.
        { econs. { apply: ProductStepL. apply: ProductStepR. by apply: SJumpInternal. } done. }
        move => /= *. destruct_all!; simplify_eq. tend. naive_solver.
  - revert select ((_ ∪ _) !! _ = None) => /lookup_union_None[??].
    destruct σf; destruct_all?; simplify_eq.
    + tstep_Some. {
        econs. {
          apply: ProductStepBoth. { apply: (ProductStepL (Some _)). by apply: SJumpExternal. }
          { by constructor; eapply not_elem_of_dom. }
        }
        done.
      }
      move => /= *. destruct_all!; simplify_eq. tend. naive_solver.
    + tstep_Some. {
        econs. {
          apply: ProductStepBoth. { apply: (ProductStepR (Some _)). by apply: SJumpExternal. }
          { by constructor; eapply not_elem_of_dom. }
        }
        done.
      }
      move => /= *. destruct_all!; simplify_eq. tend. naive_solver.
  - destruct σf; destruct_and?; unfold is_Some in *; simplify_eq; [naive_solver..|].
    revert select ((_ ∪ _) !! _ = Some _) => /lookup_union_Some_raw[?|[??]].
    + tstep_Some. {
        econs. {
          apply: ProductStepBoth. { apply: (ProductStepL (Some _)). by apply: SRecvJump. }
          constructor; try eapply not_elem_of_dom; try eapply elem_of_dom_2; try done.
          by apply: map_disjoint_Some_l.
        }
        done.
      }
      move => /= *. destruct_all!; simplify_eq. tend. naive_solver.
    + tstep_Some. {
        econstructor. {
          apply: ProductStepBoth. { apply: (ProductStepR (Some _)). by apply: SRecvJump. }
          constructor; try eapply not_elem_of_dom; try eapply elem_of_dom_2; done.
        }
        done.
      }
      move => /= *. destruct_all!; simplify_eq. tend. naive_solver.
Qed.

Lemma asm_prod_refines_link ins1 ins2:
  ins1 ##ₘ ins2 →
  trefines (MS (asm_prod (dom _ ins1) (dom _ ins2) asm_module asm_module) (initial_asm_state ins1, initial_asm_state ins2, APFNone))
           (MS asm_module (initial_asm_state (asm_link ins1 ins2))).
Proof.
  move => Hdisj.
  apply (inv_implies_trefines (MS (asm_prod (dom _ ins1) (dom _ ins2) asm_module asm_module) _) (MS _ _) (flip (asm_link_prod_inv ins1 ins2))).
  { simpl. naive_solver. }
  move => /= [[[il rsl insl] [ir rsr insr]] σf] [i1 rs1 ins1'] Pσi κ [? [? [? Hinv]]] Hstep.
  inversion Hstep; simplify_eq; clear Hstep. invert_all @m_step.
  all: try destruct σf; destruct_and?; simplify_eq.
  - tstep_None. { constructor. }
    move => /= *. destruct_all?; simplify_eq. tend. eexists (_, _, _). naive_solver.
  - tstep_None. { econs; [done|]. by apply lookup_union_Some_l. }
    move => /= *. destruct_all?; simplify_eq. tend. eexists (_, _, _). naive_solver.
  - tstep_None. { constructor. }
    move => /= *. destruct_all?; simplify_eq. tend. eexists (_, _, _). naive_solver.
  - tstep_None. { econs; [done|]. by apply lookup_union_Some_r. }
    move => /= *. destruct_all?; simplify_eq. tend. eexists (_, _, _). naive_solver.
  - tstep_None. { apply: SJumpInternal; [done|]. by apply lookup_union_Some_r. }
    move => /= *. destruct_all?; simplify_eq. tend. eexists (_, _, _). naive_solver.
  - tstep_None. { apply: SJumpInternal; [done|]. by apply lookup_union_Some_l. }
    move => /= *. destruct_all?; simplify_eq. tend. eexists (_, _, _). naive_solver.
  - tstep_Some. { apply: SJumpExternal; [done|]. apply lookup_union_None. by split; apply not_elem_of_dom. }
    move => /= *. destruct_all?; simplify_eq. tend. eexists (_, _, _). naive_solver.
  - tstep_Some. { apply: SJumpExternal; [done|]. apply lookup_union_None. by split; apply not_elem_of_dom. }
    move => /= *. destruct_all?; simplify_eq. tend. eexists (_, _, _). naive_solver.
  - tstep_Some. { apply: SRecvJump; [done|]. by apply lookup_union_Some_l. }
    move => /= *. destruct_all?; simplify_eq. tend. eexists (_, _, _). naive_solver.
  - tstep_Some. { apply: SRecvJump; [done|]. by apply lookup_union_Some_r. }
    move => /= *. destruct_all?; simplify_eq. tend. eexists (_, _, _). naive_solver.
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
  apply mod_filter_mod_trefines.
  apply mod_product_trefines.
  - apply: Href.
  - erewrite map_difference_eq_dom_L => //. apply _.
Qed.

Require refframe.itree.
Module asm_examples.
  Import refframe.itree.
  Local Open Scope Z_scope.
  Definition asm_mul : gmap Z asm_instr :=
    <[ 100 := [
          WriteReg "R3" (λ rs, rs !!! "R1" * rs !!! "R2");
          WriteReg "PC" (λ rs, rs !!! "PC" + 4)
      ] ]> $
    <[ 104 := [
          (* Dummy instruction such that we have two instructions *)
          WriteReg "PC" (λ rs, rs !!! "PC" + 4)
      ] ]> $ ∅.

  Definition itree_mul : itree (moduleE asm_event unit) unit :=
    ITree.forever (
       pc ← TExist Z;;;
       rs ← TExist _;;;
       TVis (ERecvJump pc rs);;;;
       if bool_decide (pc = 100) then
         Ret ()
       else if bool_decide (pc = 104) then
         TUb
       else
         TNb
    ).


  Lemma asm_mul_refines_itree :
    trefines (MS asm_module (initial_asm_state asm_mul)) (MS (mod_itree _ _) (itree_mul, tt)).
  Proof.
    apply wp_implies_refines => n /=. rewrite /initial_asm_state.
    move: (∅) => rs.
    elim/ti_lt_ind: n rs => n Hloop rs.
    apply Wp_step => ?????. invert_all @m_step.
    apply: itree_rel_intro. rewrite /itree_mul unfold_forever !bind_bind.
    rewrite {1}bind_trigger. eapply thas_trace_Exist.
    rewrite !bind_bind {1}bind_trigger. eapply thas_trace_Exist.
    rewrite !bind_bind {1}bind_trigger. eapply thas_trace_Vis.
    revert select (asm_mul !! _ = Some _) => /lookup_insert_Some[[??]|[? /lookup_insert_Some[[??]|[?/(lookup_empty_Some _ _) ?//]]]]; simplify_eq.
    2: {
      rewrite bool_decide_false // bool_decide_true //.
      rewrite !bind_bind {1}bind_trigger. by eapply thas_trace_All.
    }
    rewrite bool_decide_true //.
  Admitted.

End asm_examples.
