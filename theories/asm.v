Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.filter.
Require Import refframe.product.
Require Import refframe.proof_techniques.

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
  instrs !! pc = Some es →
  asm_step (AsmState None regs instrs) (Some (ERecvJump pc regs')) (λ σ', σ' = AsmState (Some es) regs' instrs)
.

Definition asm_module := Mod asm_step.

Definition asm_link (instrs1 instrs2 : gmap Z asm_instr) : gmap Z asm_instr :=
  instrs1 ∪ instrs2.

Definition asm_ctx_refines (instrsi instrss : gmap Z asm_instr) :=
  ∀ C, trefines (MS asm_module (initial_asm_state (asm_link instrsi C)))
                (MS asm_module (initial_asm_state (asm_link instrss C))).

Inductive asm_prod_filter_state :=
| APFLeft | APFRight | APFNone.

Inductive asm_prod_filter_step (ins1 ins2 : gset Z) :
  asm_prod_filter_state → option ((option asm_event * option asm_event) * option asm_event) → (asm_prod_filter_state → Prop) →  Prop :=
| APFJumpRecvL pc rs:
  pc ∉ ins1 →
  pc ∈ ins2 →
  asm_prod_filter_step ins1 ins2 APFLeft (Some ((Some (EJump pc rs), Some (ERecvJump pc rs)), None)) (λ σ, σ = APFRight)
| APFJumpRecvR pc rs:
  pc ∈ ins1 →
  pc ∉ ins2 →
  asm_prod_filter_step ins1 ins2 APFRight (Some ((Some (ERecvJump pc rs), Some (EJump pc rs)), None)) (λ σ, σ = APFLeft)
| APFJumpExtL pc rs:
  pc ∉ ins1 →
  pc ∉ ins2 →
  asm_prod_filter_step ins1 ins2 APFLeft (Some ((Some (EJump pc rs), None), Some (EJump pc rs))) (λ σ, σ = APFNone)
| APFJumpExtR pc rs:
  pc ∉ ins1 →
  pc ∉ ins2 →
  asm_prod_filter_step ins1 ins2 APFRight (Some ((None, Some (EJump pc rs)), Some (EJump pc rs))) (λ σ, σ = APFNone)
| APFRecvJumpL pc rs:
  pc ∈ ins1 →
  pc ∉ ins2 →
  asm_prod_filter_step ins1 ins2 APFNone (Some ((Some (ERecvJump pc rs), None), Some (ERecvJump pc rs))) (λ σ, σ = APFLeft)
| APFRecvJumpR pc rs:
  pc ∉ ins1 →
  pc ∈ ins2 →
  asm_prod_filter_step ins1 ins2 APFNone (Some ((None, Some (ERecvJump pc rs)), Some (ERecvJump pc rs))) (λ σ, σ = APFRight)
.

Definition asm_prod_filter ins1 ins2 := Mod (asm_prod_filter_step ins1 ins2).

Definition mod_filter_mod {EV1 EV2} (m : module EV1) (f : module (EV1 * option EV2)) : module EV2 :=
  mod_filter (mod_product m f) (λ e er, e.2 = (λ x, (x, er)) <$> e.1).

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

Lemma TTraceStepNil {EV} (m : module EV) σ1 Pσ2 Pσ3 κs:
  m_step m σ1 None Pσ2 →
  (∀ σ2, Pσ2 σ2 → σ2 ~{ m, κs }~>ₜ Pσ3) →
  σ1 ~{ m, κs }~>ₜ Pσ3.
Proof. move => ??. by apply: TTraceStep. Qed.

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
  - destruct σf; destruct_and?; simplify_eq.
    + apply: TTraceStepNil.
      { econstructor. { apply ProductStepL. apply ProductStepL. constructor. } done. }
      move => [[??]?] [[??]?]; simplify_eq. apply: TTraceEnd; [|done].
      naive_solver.
    + apply: TTraceStepNil.
      { econstructor. { apply ProductStepL. apply ProductStepR. constructor. } done. }
      move => [[??]?] [[?[??]]?]; simplify_eq. apply: TTraceEnd; [|done].
      naive_solver.
  - destruct σf; destruct_and?; simplify_eq.
    + revert select ((_ ∪ _) !! _ = Some _) => /lookup_union_Some_raw[?|[??]].
      * apply: TTraceStepNil.
        { econstructor. { apply ProductStepL. apply ProductStepL. by apply: SJumpInternal. } done. }
        move => [[??]?] [[??]?]; simplify_eq. apply: TTraceEnd; [|done].
        naive_solver.
      * apply: TTraceStepNil. {
          econstructor. {
            apply ProductStepBoth. {
              apply ProductStepBoth. { by apply: SJumpExternal. } { by constructor. }
            }
            constructor; try eapply not_elem_of_dom; try eapply elem_of_dom_2; done.
          }
          done.
        }
        move => [[??]?] [[??]?]; simplify_eq. apply: TTraceEnd; [|done].
        naive_solver.
    + revert select ((_ ∪ _) !! _ = Some _) => /lookup_union_Some_raw[?|[??]].
      * apply: TTraceStepNil. {
          econstructor. {
            apply ProductStepBoth. {
              apply ProductStepBoth. { by constructor. } { apply: SJumpExternal; [done|]. by apply: map_disjoint_Some_l. }
            }
            constructor; try eapply not_elem_of_dom; try eapply elem_of_dom_2; try done.
            by apply: map_disjoint_Some_l.
          }
          done.
        }
        move => [[??]?] [[??]?]; simplify_eq. apply: TTraceEnd; [|done].
        naive_solver.
      * apply: TTraceStepNil.
        { econstructor. { apply ProductStepL. apply ProductStepR. by apply: SJumpInternal. } done. }
        move => [[??]?] [[??]?]; simplify_eq. apply: TTraceEnd; [|done].
        naive_solver.
  - revert select ((_ ∪ _) !! _ = None) => /lookup_union_None[??].
    destruct σf; destruct_and?; simplify_eq.
    + apply: (TTraceStep _ _ _ _ _ _ tnil). {
        econstructor. {
          apply ProductStepBoth. { apply: (ProductStepL _ _ _ _ (Some _)). by apply: SJumpExternal. }
          { by constructor; eapply not_elem_of_dom. }
        }
        done.
      }
      2: done.
      move => [[??]?] [[??]?]; simplify_eq. apply: TTraceEnd; [|done].
      naive_solver.
    + apply: (TTraceStep _ _ _ _ _ _ tnil). {
        econstructor. {
          apply ProductStepBoth. { apply: (ProductStepR _ _ _ _ (Some _)). by apply: SJumpExternal. }
          { by constructor; eapply not_elem_of_dom. }
        }
        done.
      }
      2: done.
      move => [[??]?] [[??]?]; simplify_eq. apply: TTraceEnd; [|done].
      naive_solver.
  - destruct σf; destruct_and?; unfold is_Some in *; simplify_eq; [naive_solver..|].
    revert select ((_ ∪ _) !! _ = Some _) => /lookup_union_Some_raw[?|[??]].
    + apply: (TTraceStep _ _ _ _ _ _ tnil). {
        econstructor. {
          apply ProductStepBoth. { apply: (ProductStepL _ _ _ _ (Some _)). by apply: SRecvJump. }
          constructor; try eapply not_elem_of_dom; try eapply elem_of_dom_2; try done.
          by apply: map_disjoint_Some_l.
        }
        done.
      } 2: done.
      move => [[??]?] [[??]?]; simplify_eq. apply: TTraceEnd; [|done].
      naive_solver.
    + apply: (TTraceStep _ _ _ _ _ _ tnil). {
        econstructor. {
          apply ProductStepBoth. { apply: (ProductStepR _ _ _ _ (Some _)). by apply: SRecvJump. }
          constructor; try eapply not_elem_of_dom; try eapply elem_of_dom_2; done.
        }
        done.
      } 2: done.
      move => [[??]?] [[??]?]; simplify_eq. apply: TTraceEnd; [|done].
      naive_solver.
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
  - apply: TTraceStepNil. { constructor. }
    move => ? [??]; simplify_eq. apply: TTraceEnd; [|done]. eexists (_, _, _).
    naive_solver.
  - apply: TTraceStepNil. { econstructor; [done|]. by apply lookup_union_Some_l. }
    move => ? ?; simplify_eq/=. apply: TTraceEnd; [|done]. eexists (_, _, _).
    naive_solver.
  - apply: TTraceStepNil. { constructor. }
    move => ? ?; simplify_eq/=. apply: TTraceEnd; [|done]. eexists (_, _, _).
    naive_solver.
  - apply: TTraceStepNil. { econstructor; [done|]. by apply lookup_union_Some_r. }
    move => ? ?; simplify_eq/=. apply: TTraceEnd; [|done]. eexists (_, _, _).
    naive_solver.
  - apply: (TTraceStep _ _ _ _ _ _ tnil). { apply: SJumpInternal; [done|]. by apply lookup_union_Some_r. } 2: done.
    move => ? ?; simplify_eq/=. apply: TTraceEnd; [|done]. eexists (_, _, _).
    naive_solver.
  - apply: (TTraceStep _ _ _ _ _ _ tnil). { apply: SJumpInternal; [done|]. by apply lookup_union_Some_l. } 2: done.
    move => ? ?; simplify_eq/=. apply: TTraceEnd; [|done]. eexists (_, _, _).
    naive_solver.
  - apply: (TTraceStep _ _ _ _ _ _ tnil). {
      apply: SJumpExternal; [done|]. apply lookup_union_None.
      by split; apply not_elem_of_dom.
    } 2: done.
    move => ? ?; simplify_eq/=. apply: TTraceEnd; [|done]. eexists (_, _, _).
    naive_solver.
  - apply: (TTraceStep _ _ _ _ _ _ tnil). {
      apply: SJumpExternal; [done|]. apply lookup_union_None.
      by split; apply not_elem_of_dom.
    } 2: done.
    move => ? ?; simplify_eq/=. apply: TTraceEnd; [|done]. eexists (_, _, _).
    naive_solver.
  - apply: (TTraceStep _ _ _ _ _ _ tnil). {
      apply: SRecvJump; [done|]. by apply lookup_union_Some_l.
    } 2: done.
    move => ? ?; simplify_eq/=. apply: TTraceEnd; [|done]. eexists (_, _, _).
    naive_solver.
  - apply: (TTraceStep _ _ _ _ _ _ tnil). {
      apply: SRecvJump; [done|]. by apply lookup_union_Some_r.
    } 2: done.
    move => ? ?; simplify_eq/=. apply: TTraceEnd; [|done]. eexists (_, _, _).
    naive_solver.
Qed.

Lemma asm_trefines_implies_ctx_refines insi inss :
  dom (gset _) insi = dom (gset _) inss →
  trefines (MS asm_module (initial_asm_state insi)) (MS asm_module (initial_asm_state inss)) →
  asm_ctx_refines insi inss.
Proof.
  move => Hdom Href C. rewrite /asm_link map_difference_union_r (map_difference_union_r inss).
  etrans. { apply asm_link_refines_prod. apply map_disjoint_difference_r'. }
  etrans. 2: { apply asm_prod_refines_link. apply map_disjoint_difference_r'. }
  apply tmod_filter_refines.
  apply mod_product_trefines. 2: { rewrite !dom_difference_L Hdom. done. }
  apply mod_product_trefines. 2: { erewrite map_difference_eq_dom_L => //. apply _. }
  apply: Href.
Qed.
