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

(** * tsim *)
Global Hint Transparent asm_instr : tsim.
Lemma asm_step_WriteReg_i r f es rs ins:
  TSimStepI asm_module (AsmState (Some (WriteReg r f::es)) rs ins)
            (λ G, is_Some (rs !! r) ∧ G None (AsmState (Some (es)) (<[r:=f rs]>rs) ins)).
Proof. constructor => ???????. destruct_and!. invert_all @m_step. naive_solver. Qed.
Global Hint Resolve asm_step_WriteReg_i : tsim.

Lemma asm_step_Jump_i rs ins:
  TSimStepI asm_module (AsmState (Some []) rs ins) (λ G,
    ∀ pc, rs !! "PC" = Some pc →
          if ins !! pc is Some i then
            G None (AsmState (Some i) (rs) ins)
          else
            G (Some (EJump pc rs)) (AsmState None (rs) ins)
   ).
Proof.
  constructor => ?????? HG. invert_all @m_step; specialize (HG _ ltac:(done)); simplify_option_eq.
  all: naive_solver.
Qed.
Global Hint Resolve asm_step_Jump_i : tsim.

Lemma asm_step_None_i rs ins:
  TSimStepI asm_module (AsmState None rs ins) (λ G,
    ∀ pc i rs', rs' !! "PC" = Some pc →
      ins !! pc = Some i →
      G (Some (ERecvJump pc rs')) (AsmState (Some i) rs' ins)
   ).
Proof. constructor => ?????? HG. invert_all @m_step. naive_solver. Qed.
Global Hint Resolve asm_step_None_i : tsim.

Require refframe.itree.
Module asm_examples.
  Import refframe.itree.
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

  (* For supporting recursion, we probably want to be able to
  non-deterministically break out of the loop. Breaking out at the top
  level would cause UB (or NB?) but it would be useful for the
  recursive call *)
  Definition itree_mul : itree (moduleE asm_event unit) unit :=
    ITree.forever (
       pc ← TExist Z;;;
       rs ← TExist _;;;
       TVis (ERecvJump pc rs);;;;
       if bool_decide (pc = 100) then
         r1 ← TAssumeOpt (rs !! "R1");;;
         r2 ← TAssumeOpt (rs !! "R2");;;
         r30 ← TAssumeOpt (rs !! "R30");;;
         TAssume (r30 ≠ 100 ∧ r30 ≠ 104);;;;
         TVis (EJump r30 (<["PC":=r30]> $ <["R1":=r1 * r2]> $ rs));;;;
         Ret ()
       else if bool_decide (pc = 104) then
         TUb
       else
         TNb
    ).


  Lemma asm_mul_refines_itree :
    trefines (MS asm_module (initial_asm_state asm_mul)) (MS (mod_itree _ _) (itree_mul, tt)).
  Proof.
    apply tsim_implies_trefines => /=. rewrite /initial_asm_state. move: (∅) => rs.
    move: rs. apply tsim_remember_all => rs.
    tsim_step_i => pc i rs' HPC Hi.
    rewrite {1}/itree_mul. rewrite unfold_forever. rewrite -/itree_mul.

    tsim_step_s.
    tsim_step_s. eexists _.
    tsim_step_s.
    tsim_step_s. eexists _.
    tsim_step_s.
    tsim_step_s. split; [done|].
    move: Hi. rewrite !lookup_insert_Some !lookup_empty => Hi. destruct_all!; simplify_eq.
    all: repeat (rewrite bool_decide_false; [done|]); rewrite bool_decide_true //.
    all: try by tsim_step_s.
    tsim_step_s. tsim_step_s => r1 HR1.
    tsim_step_s. tsim_step_s => r2 HR2.
    tsim_step_s. tsim_step_s => r30 HR30.
    tsim_step_s. tsim_step_s => -[??].
    tsim_step_i. split. { by simplify_map_eq. }
    erewrite lookup_total_correct; [|done]. erewrite lookup_total_correct; [|done].
    tsim_step_i. split. { by simplify_map_eq. }
    erewrite lookup_total_correct; [|by simplify_map_eq].
    tsim_step_i => ??. simplify_map_eq.
    tsim_step_i. split. { by simplify_map_eq. }
    erewrite lookup_total_correct; [|by simplify_map_eq].
    tsim_step_i => ??. rewrite {1}/asm_mul. simplify_map_eq.
    tsim_step_s. tsim_step_s. split. { by rewrite insert_insert. }
    tsim_step_s. tsim_step_s.
    rewrite -/itree_mul. apply tsim_close_loop. left. naive_solver.
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
    (rec-fix f _ :=
       b ← translate (inr_) (TAll bool);;;
       if b then Ret ()
       else
       pc ← translate (inr_) (TExist Z);;;
       rs ← translate (inr_) (TExist _);;;
       translate (inr_) (TVis (ERecvJump pc rs));;;;
       if bool_decide (pc = 200) then
         translate (inr_) (TAssume (is_Some (rs !! "R1")));;;;
         translate (inr_) (TAssume (is_Some (rs !! "R2")));;;;
         translate (inr_) (TAssume (is_Some (rs !! "R29")));;;;
         r30 ← translate (inr_) (TAssumeOpt (rs !! "R30"));;;
         r29' ← translate (inr_) (TExist Z);;;
         translate (inr_) (TVis (EJump 100 (<["PC":=100]> $ <["R30":= 212]> $ <["R29":= r29']> $ <["R2":= 2]> $ <["R1":= 2]> $ rs)));;;;
         f ();;;;
         pc' ← translate (inr_) (TExist Z);;;
         rs' ← translate (inr_) (TExist _);;;
         translate (inr_) (TVis (ERecvJump pc' rs'));;;;
         translate (inr_) (TAssume (pc' = 212));;;;
         translate (inr_) (TAssume (is_Some (rs' !! "R30")));;;;
         translate (inr_) (TAssume (rs' !! "R29" = Some r29'));;;;
         translate (inr_) (TAssume (r30 ≠ 200 ∧ r30 ≠ 204 ∧ r30 ≠ 208 ∧ r30 ≠ 212 ∧ r30 ≠ 216));;;;
         r30' ← translate (inr_) (TExist Z);;;
         translate (inr_) (TVis (EJump r30 (<["PC":= r30]> $ <["R30":= r30']> rs')));;;;
         f ()
       else if bool_decide (pc = 204) then translate (inr_) TUb
       else if bool_decide (pc = 208) then translate (inr_) TUb
       else if bool_decide (pc = 212) then translate (inr_) TUb
       else if bool_decide (pc = 216) then translate (inr_) TUb
       else translate (inr_) TNb
    ) ();;;; TUb.

    Lemma itree_step_recursive_bind_s EV S R Q A B (f : A → itree (callE A B +' _) _) (t : itree (moduleE EV S) R) (k : R → itree (_ +' moduleE EV S) Q) h s κs:
      TSimStepS (mod_itree EV S) (x ← interp (recursive f) (ITree.bind (translate inr_ t) k);;; h x, s) κs
            (λ G, G κs ((ITree.bind t (fun r => x ← interp (recursive f) (k r);;; h x)), s)).
    Proof.
      constructor => ????. eexists tnil, _. split; [done|].
      apply itree_rel_intro. rewrite interp_bind bind_bind interp_translate /= interp_trigger_h.
      tend => ? <-. done.
    Qed.
    Global Hint Resolve itree_step_recursive_bind_s : tsim.
    Lemma itree_step_recursive_s EV S R A B (f : A → itree (callE A B +' _) _) (t : itree (moduleE EV S) R) h s κs:
      TSimStepS (mod_itree EV S) (x ← interp (recursive f) (translate inr_ t);;; h x, s) κs
            (λ G, G κs ((x ← t;;; h x), s)).
    Proof.
      constructor => ????. eexists tnil, _. split; [done|].
      apply itree_rel_intro. rewrite interp_translate /= interp_trigger_h.
      tend => ? <- /=. done.
    Qed.
    Global Hint Resolve itree_step_recursive_s : tsim.
    Lemma itree_step_interp_ret_s EV S R E  (f : E ~> itree (moduleE EV S)) (a : R) h s κs:
      TSimStepS (mod_itree EV S) (x ← interp f (Ret a);;; h x, s) κs (λ G, G κs (h a, s)).
    Proof.
      constructor => ????. eexists tnil, _. split; [done|].
      apply itree_rel_intro. rewrite interp_ret bind_ret_l. tend => ? <-. done.
    Qed.
    Global Hint Resolve itree_step_interp_ret_s : tsim.

  Lemma tsim_remember_rec {EV S A B} {mi : module EV} σi r (h : B → _) Is s:
    (∀ x y, tsim mi (mod_itree EV S) (σi x) tnil (h y, s x) Is) →
    (∀ x h',
       (∀ x y, tsim mi (mod_itree EV S) (σi x) tnil (h' y, (s x)) Is) →
       tsim mi (mod_itree EV S) (σi x) tnil ((y ← rec r ();;; h' y), (s x))
       ((false, λ σ, ∃ x h',
          σ = (σi x, ((y ← rec r ();;; h' y), s x)) ∧
          ∀ x y, tsim mi (mod_itree EV S) (σi x) tnil (h' y, s x) Is)::Is)) →
    ∀ x : A, tsim mi (mod_itree EV S) (σi x) tnil ((y ← rec r ();;; h y), s x) Is.
  Proof.
    move => Hh Hsim x.
    eapply (tsim_remember (ms:=mod_itree _ _)
      (λ σ, ∃ x h', σ = (σi x, ((y ← rec r ();;; h' y), s x)) ∧
          ∀ x y, tsim mi (mod_itree EV S) (σi x) tnil (h' y, s x) Is)). { naive_solver. }
    move => ?? [?[?[[??]?]]]. subst.
    by apply: Hsim.
  Qed.

  Lemma tsim_drop_loop {EV} {mi ms : module EV} σi σs κs Is :
    tsim mi ms σi κs σs [] →
    tsim mi ms σi κs σs Is.
  Proof. move => Hsim κs' n _. by apply: Hsim. Qed.

  Lemma asm_mul_client_refines_itree :
    trefines (MS asm_module (initial_asm_state asm_mul_client)) (MS (mod_itree _ _) (itree_mul_client, tt)).
  Proof.
    apply tsim_implies_trefines => /=. rewrite /initial_asm_state. move: (∅) => rs.
    rewrite {1}/itree_mul_client /rec_fix. set rc := (X in (rec X)).
    move: rs. apply tsim_remember_rec. { move => ??. rewrite -(bind_ret_r TUb). by tsim_step_s. }
    move => rs CONT HCONT.
    rewrite {1}rec_as_interp {2}/rc.
    tsim_step_s. tsim_step_s => -[].
    { tsim_step_s. apply: tsim_drop_loop. apply: HCONT. }
    tsim_step_i => pc i rs' HPC Hi.
    tsim_step_s. tsim_step_s. eexists _.
    tsim_step_s. tsim_step_s. eexists _.
    tsim_step_s. tsim_step_s. split; [done|].
    move: Hi. rewrite !lookup_insert_Some !lookup_empty => Hi. destruct_all!; simplify_eq.
    all: repeat (rewrite bool_decide_false; [done|]); rewrite bool_decide_true //.
    all: try by tsim_step_s; tsim_step_s.

    tsim_step_s. tsim_step_s => -[r1 HR1].
    tsim_step_s. tsim_step_s => -[r2 HR2].
    tsim_step_s. tsim_step_s => -[r29 HR29].
    tsim_step_s. tsim_step_s => r30 HR30.
    tsim_step_i. split; [ by simplify_map_eq|].
    tsim_step_i. split; [ by simplify_map_eq|].
    tsim_step_i. split; [ by simplify_map_eq|].
    erewrite lookup_total_correct; [|by simplify_map_eq].
    tsim_step_i => ??. simplify_map_eq.
    tsim_step_i. split; [ by simplify_map_eq|].
    erewrite lookup_total_correct; [|by simplify_map_eq].
    tsim_step_i. split; [ by simplify_map_eq|].
    erewrite lookup_total_correct; [|by simplify_map_eq].
    tsim_step_i => ??. simplify_map_eq.
    tsim_step_i. split; [ by simplify_map_eq|].
    erewrite lookup_total_correct; [|by simplify_map_eq].
    tsim_step_i. split; [ by simplify_map_eq|].
    rewrite insert_commute // insert_insert (insert_commute _ "PC") // insert_insert.
    tsim_step_i => ??. simplify_map_eq.
    tsim_step_s. tsim_step_s. eexists r30.
    tsim_step_s. tsim_step_s. split. {
      f_equal. apply map_eq => i. apply option_eq => ?.
      rewrite !lookup_insert_Some. naive_solver.
    }
    (* tsim_step_s. *)

    rewrite interp_bind interp_recursive_call.
    tsim_step_s. apply tsim_close_loop. left. split; [done|]. eexists _, _. split; [done|].
    move => rs'' ?.
    tsim_step_i => pc' i rs''' HPC' Hi'.
    tsim_step_s. tsim_step_s. eexists _.
    tsim_step_s. tsim_step_s. eexists _.
    tsim_step_s. tsim_step_s. split; [done|].
    tsim_step_s. tsim_step_s => ?.
    unfold asm_mul_client in Hi'. simplify_map_eq.
    tsim_step_s. tsim_step_s => -[r30'' HR30''].
    tsim_step_s. tsim_step_s => ?.
    tsim_step_s. tsim_step_s => -[?[?[?[??]]]].
    tsim_step_i. split; [ by simplify_map_eq|].
    erewrite lookup_total_correct; [|by simplify_map_eq].
    tsim_step_i. split; [ by simplify_map_eq|].
    erewrite lookup_total_correct; [|by simplify_map_eq].
    tsim_step_i => ??. simplify_map_eq.
    tsim_step_i. split; [ by simplify_map_eq|].
    erewrite lookup_total_correct; [|by simplify_map_eq].
    tsim_step_i => ??. rewrite {1}/asm_mul_client. simplify_map_eq.
    tsim_step_s. tsim_step_s. eexists _.
    tsim_step_s. tsim_step_s. split. { f_equal. by rewrite insert_insert. }

    rewrite interp_recursive_call.
    apply tsim_close_loop.
  Qed.
End asm_examples.
