From dimsum.core Require Export proof_techniques satisfiable seq_product.
From dimsum.core Require Import link.

Set Default Proof Using "Type".

(** * Prepost *)

(** * [prepost] *)
Section prepost.
Context {R : Type}.
Context {M : ucmra}.


Inductive prepost : Type :=
| pp_end (r : R)
| pp_prop (P : Prop) (pp : prepost)
| pp_quant {T} (pp : T → prepost)
| pp_star (P : uPred M) (pp : prepost)
.

Fixpoint pp_to_ex (pp : prepost) (Q : R → uPred M → Prop) : Prop :=
  match pp with
  | pp_end r => Q r True%I
  | pp_prop P pp' => P ∧ pp_to_ex pp' Q
  | pp_quant pp' => ∃ y, pp_to_ex (pp' y) Q
  | pp_star P pp' => pp_to_ex pp' (λ r y, Q r (P ∗ y)%I)
  end.

Fixpoint pp_to_all (pp : prepost) (Q : R → uPred M → Prop) : Prop :=
  match pp with
  | pp_end r => Q r True%I
  | pp_prop P pp' => P → pp_to_all pp' Q
  | pp_quant pp' => ∀ y, pp_to_all (pp' y) Q
  | pp_star P pp' => pp_to_all pp' (λ r y, Q r (P ∗ y)%I)
  end.

Lemma pp_to_ex_exists pp Q:
  pp_to_ex pp Q ↔ ∃ r y, Q r y ∧ pp_to_ex pp (λ r' y', r' = r ∧ y' = y).
Proof.
  elim: pp Q => /=; try naive_solver.
  move => ?? IH Q. rewrite IH.
  split; move => [?[?[? Hex]]].
  - eexists _, _. split; [done|]. rewrite IH. naive_solver.
  - move: Hex. rewrite IH. naive_solver.
Qed.

Lemma pp_to_all_forall pp Q:
  pp_to_all pp Q ↔ (∀ r y, pp_to_ex pp (λ r' y', r' = r ∧ y' = y) → Q r y).
Proof.
  elim: pp Q => /=; try naive_solver.
  move => ?? IH Q. rewrite IH.
  split; move => Hall ??.
  - rewrite pp_to_ex_exists => -[?[?[??]]]. naive_solver.
  - move => ?. apply Hall. rewrite pp_to_ex_exists. naive_solver.
Qed.

Lemma pp_to_all_forall_2 pp Q:
  pp_to_all pp Q →
  ∀ r y, pp_to_ex pp (λ r' y', r' = r ∧ y' = y) → Q r y.
Proof. apply pp_to_all_forall. Qed.

Lemma pp_to_all_mono pp (Q1 Q2 : _ → _ → Prop):
  pp_to_all pp Q1 →
  (∀ r y, Q1 r y → Q2 r y) →
  pp_to_all pp Q2.
Proof. rewrite !pp_to_all_forall. naive_solver. Qed.

Lemma pp_to_ex_mono pp (Q1 Q2 : _ → _ → Prop):
  pp_to_ex pp Q1 →
  (∀ r y, Q1 r y → Q2 r y) →
  pp_to_ex pp Q2.
Proof. rewrite !pp_to_ex_exists. naive_solver. Qed.

Lemma pp_to_all_ex pp Q1 Q2:
  pp_to_all pp Q1 →
  pp_to_ex pp Q2 →
  ∃ y r, Q1 r y ∧ Q2 r y.
Proof. move => /pp_to_all_forall ? /pp_to_ex_exists. naive_solver. Qed.

End prepost.

Arguments prepost : clear implicits.

(** * [mod_prepost] *)
Section prepost.
  Context {EV1 EV2 S : Type}.
  Context {M : ucmra}.
  Implicit Types (i : EV2 → S → prepost (EV1 * S) M) (o : EV1 → S → prepost (EV2 * S) M).

  Inductive pp_case : Type :=
  | PPOutside
  | PPRecv1 (e : EV2)
  | PPRecv2 (e : EV1)
  | PPInside
  | PPSend1 (e : EV1)
  | PPSend2 (e : EV2)
  .

  Inductive pp_filter_step i o :
    (pp_case * S * uPred M) → option (sm_event EV1 EV2) → ((pp_case * S * uPred M) → Prop) → Prop :=
  | PPOutsideS s x e:
    (* TODO: Add a user-defined predicate here to rule out choosing
    non-sensical events? E.g. allow only Incoming events or prevent
    syscall events. *)
    pp_filter_step i o (PPOutside, s, x) (Some (SMEEmit e)) (λ σ, σ = (PPRecv1 e, s, x))
  | PPRecv1S s x e:
    pp_filter_step i o (PPRecv1 e, s, x) None (λ σ,
        pp_to_ex (i e s) (λ r y, ∃ x', satisfiable (x ∗ y ∗ x') ∧ σ = (PPRecv2 r.1, r.2, x')))
  | PPRecv2S s x e:
    pp_filter_step i o (PPRecv2 e, s, x) (Some (SMEReturn (Some e))) (λ σ, σ = (PPInside, s, x))
  | PPInsideS s x e:
    pp_filter_step i o (PPInside, s, x) (Some (SMERecv e)) (λ σ, σ = (PPSend1 e, s, x))
  | PPSend1S s x e r y x':
    satisfiable (x' ∗ y ∗ x) →
    pp_to_ex (o e s) (λ r' y', r' = r ∧ y' = y) →
    pp_filter_step i o (PPSend1 e, s, x) None (λ σ, σ = (PPSend2 r.1, r.2, x'))
  | PPSend2S s x e:
    pp_filter_step i o (PPSend2 e, s, x) (Some (SMEEmit e)) (λ σ, σ = (PPOutside, s, x))
  .

  Definition prepost_filter_trans i o := ModTrans (pp_filter_step i o).

  Global Instance prepost_filter_vis_no_all i o : VisNoAll (prepost_filter_trans i o).
  Proof. move => ????. inv_all @m_step; naive_solver. Qed.

  Definition prepost_trans i o (m : mod_trans EV1) : mod_trans EV2 :=
    seq_map_trans m (prepost_filter_trans i o).

  Global Instance prepost_vis_no_all i o m `{!VisNoAll m}: VisNoAll (prepost_trans i o m).
  Proof. apply _. Qed.

  (* If one needs a version of prepost_mod that starts on the inside,
  one can define prepost_mod_inside or similar. *)
  Definition prepost_mod i o (m : module EV1) (s : S) (x : uPred M) : module EV2 :=
    Mod (prepost_trans i o m.(m_trans)) (SMFilter, m.(m_init), (PPOutside, s, x)).

  Lemma prepost_mod_trefines i o (m m' : module EV1) σm s `{!VisNoAll m.(m_trans)}:
    trefines m m' →
    trefines (prepost_mod i o m σm s) (prepost_mod i o m' σm s).
  Proof.
    move => ?. apply: (seq_map_mod_trefines (Mod _ _) (Mod _ _) (Mod _ _)). destruct m, m' => //.
  Qed.

  Lemma prepost_trans_step_Outside_i i o m σ s x:
    TStepI (prepost_trans i o m) (SMFilter, σ, (PPOutside, s, x)) (λ G,
        ∀ e, G true (Some e) (λ G', G' (SMFilter, σ, (PPRecv1 e, s, x)))).
  Proof.
    constructor => G /= ?. tstep_i.
    apply steps_impl_step_end => ???. inv_all @m_step => ???. split! => ?. split!; [naive_solver|done|].
    naive_solver.
  Qed.

  Lemma prepost_trans_step_Recv1_i i o m σ s e x:
    TStepI (prepost_trans i o m) (SMFilter, σ, (PPRecv1 e, s, x)) (λ G,
        pp_to_ex (i e s) (λ r y, ∃ x', satisfiable (x ∗ y ∗ x') ∧
                      G true None (λ G', G' (SMProgRecv r.1, σ, (PPInside, r.2, x'))))).
  Proof.
    constructor => G /= /pp_to_ex_exists[r [? [[?[? HG]]?]]]. tstep_i.
    apply steps_impl_step_next => ???. inv_all @m_step.
    eexists (_, _). split!. { apply pp_to_ex_exists. naive_solver. }
    apply steps_impl_step_end => ???. inv_all @m_step => ???. naive_solver.
  Qed.

  Lemma prepost_trans_step_Inside_i i o m σ s e x:
    TStepI (prepost_trans i o m) (SMFilterRecv e, σ, (PPInside, s, x)) (λ G,
        pp_to_all (o e s) (λ r y, ∀ x', satisfiable (x' ∗ y ∗ x) →
            G true (Some (r.1)) (λ G', G' (SMFilter, σ, (PPOutside, r.2, x'))))).
  Proof.
    constructor => G /= ?. apply steps_impl_step_trans. tstep_i.
    apply steps_impl_step_end => ???. inv_all @m_step => ? b *; simplify_eq. split! => ?. split!; [done|].
    tstep_i.
    apply steps_impl_step_next => ???. inv_all @m_step => *; simplify_eq. split!.
    apply steps_impl_step_end => ???. inv_all @m_step => *; simplify_eq. split! => ?.
    have [?[?[?[??]]]]:= pp_to_all_ex _ _ _ ltac:(done) ltac:(done); subst.
    split!; [naive_solver|by destruct b|]. naive_solver.
  Qed.

  Lemma prepost_trans_step_Outside_s i o m σ s x:
    TStepS (prepost_trans i o m) (SMFilter, σ, (PPOutside, s, x)) (λ G,
        ∃ e, G (Some e) (λ G', G' (SMFilter, σ, (PPRecv1 e, s, x)))).
  Proof.
    constructor => G /= [??]. split!; [done|] => /= ??. tstep_s. eexists (Some (SMEEmit _)). split!.
    apply: steps_spec_step_end; [by econs|]. naive_solver.
  Qed.


  Lemma prepost_trans_step_Recv1_s i o m σ s e x:
    TStepS (prepost_trans i o m) (SMFilter, σ, (PPRecv1 e, s, x)) (λ G,
        G None (λ G', pp_to_all (i e s) (λ r y, ∀ x', satisfiable (x ∗ y ∗ x') →
             G' (SMProgRecv r.1, σ, (PPInside, r.2, x'))))).
  Proof.
    constructor => G /= ?. split!; [done|] => /= ??. apply steps_spec_step_trans.
    tstep_s. eexists None. split!.
    apply: steps_spec_step_end; [by econs|] => ? /=?.
    have [?[?[?[?[??]]]]]:= pp_to_all_ex _ _ _ ltac:(done) ltac:(done); subst.
    tstep_s. eexists (Some (SMEReturn _)). split!.
    apply: steps_spec_step_end; [econs|]. naive_solver.
  Qed.

  Lemma prepost_trans_step_Inside_s i o m σ s e x:
    TStepS (prepost_trans i o m) (SMFilterRecv e, σ, (PPInside, s, x)) (λ G,
        pp_to_ex (o e s) (λ r y, ∃ x', satisfiable (x' ∗ y ∗ x) ∧
           G (Some (r.1)) (λ G', G' (SMFilter, σ, (PPOutside, r.2, x'))))).
  Proof.
    constructor => G /= /pp_to_ex_exists[?[?[[?[??]]?]]]. split!; [done|] => /= ??.
    apply steps_spec_step_trans. tstep_s. eexists (Some _). split!.
    apply: steps_spec_step_end; [by econs|] => /= ? ->. tstep_s. eexists (Some (SMEEmit _)). split!.
    apply: steps_spec_step; [by econs|] => /= ? ->.
    apply: steps_spec_step_end; [by econs|] => /= ? ->.
    naive_solver.
  Qed.
End prepost.

Global Hint Resolve
       prepost_trans_step_Outside_i
       prepost_trans_step_Recv1_i
       prepost_trans_step_Inside_i
       prepost_trans_step_Outside_s
       prepost_trans_step_Recv1_s
       prepost_trans_step_Inside_s
 | 3 : typeclass_instances.

(** * Lemmas for proving refinements of prepost  *)

Definition prepost_id {EV} : EV → unit → prepost (EV * unit) unitUR :=
  λ x _, pp_end (x, tt).

Lemma prepost_id_l M S EV1 EV2 (m : module EV1) i o s x:
  trefines (prepost_mod i o
              (prepost_mod prepost_id prepost_id m tt True) s x)
           (prepost_mod (M:=M) (S:=S) (EV2:=EV2) i o m s x).
Proof.
  apply tsim_implies_trefines => /= n.
  tstep_i => ?.
  tstep_s. split!.
  tstep_s. apply pp_to_all_forall => ?????.
  tstep_i. apply: pp_to_ex_mono; [done|].
  move => ?? [? ?]. subst. eexists _. split; [done|].
  tstep_i => ? <-.
  tstep_i. eexists True%I. split. { apply satisfiable_emp_valid. by iSplit. }
  unshelve apply: tsim_remember. { simpl. exact (λ _
      '(σf1, (σf1', σ1, (σpp1', _, x')), (σpp1, s1, x1)) '(σf2, σ2, (σpp2, s2, x2)),
         x' = True%I ∧ σf1 = SMProg ∧ σf1' = σf2 ∧ σ1 = σ2 ∧ σpp1 = PPInside ∧ x1 = x2
         ∧ σpp1' = PPInside ∧ σpp2 = PPInside ∧ s1 = s2 ∧
         ((∃ e, σf1' = SMProgRecv e) ∨ σf1' = SMProg)). }
  { split!. } { done. }
  move => {}n _ Hloop [[σf1 [[σf1' σ1] [[σpp1' []] ?]] [[σpp1 s1] x1]]] [[σf2 σ2] [[σpp2 s2] x2]] ?.
  destruct!.
  - tstep_both. apply: steps_impl_step_end => κ ??. case_match => *.
    + subst. tstep_s. eexists (Some _). split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [done|]. split!.
    + tstep_s. eexists None. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [done|]. split!.
  - tstep_both. apply: steps_impl_step_end => κ ??.
    tstep_s. eexists _. apply: steps_spec_step_end; [done|] => ??.
    case_match; tend; (split!; [done|]). 2: { apply: Hloop; [done|]. split!. }
    tstep_i => ??. tstep_i. apply pp_to_all_forall => ?????.
    tstep_s. apply: pp_to_ex_mono; [done|]. move => ?? [? ?]. split!; subst; [done..|].
    tstep_i => ?.
    tstep_s. split!.
    tstep_s. apply pp_to_all_forall => ?????.
    tstep_i. apply: pp_to_ex_mono; [done|]. move => ?? [??]; subst. split!; [done|].
    tstep_i => ? <-.
    tstep_i. split!; [done|].
    apply Hloop; [done|]. split!.
Qed.


Section prepost.

  Lemma prepost_link
        {EV1 EV2 S1 S2 S' Sr1 Sr2 : Type}
        {M : ucmra}
        (INV : seq_product_case → S1 → S2 → S' → uPred M → uPred M → uPred M → Sr1 → Sr2 → Prop)
        (i1 : io_event EV2 → S1 → prepost (io_event EV1 * S1) M)
        (o1 : io_event EV1 → S1 → prepost (io_event EV2 * S1) M)
        (i2 : io_event EV2 → S2 → prepost (io_event EV1 * S2) M)
        (o2 : io_event EV1 → S2 → prepost (io_event EV2 * S2) M)
        (i : io_event EV2 → S' → prepost (io_event EV1 * S') M)
        (o : io_event EV1 → S' → prepost (io_event EV2 * S') M)
        (R1 : seq_product_case → Sr1 → EV2 → seq_product_case → Sr1 → EV2 → bool → Prop)
        (R2 : seq_product_case → Sr2 → EV1 → seq_product_case → Sr2 → EV1 → bool → Prop)
        (m1 m2 : module (io_event EV1))
        s1 s2 x1 x2 x sr1 sr2 s
        `{!VisNoAll m1.(m_trans)} `{!VisNoAll m2.(m_trans)}
        :

       (∀ p s e p' s' e' ok1, R1 p s e p' s' e' ok1 → p ≠ p') →
       INV SPNone s1 s2 s x1 x2 x sr1 sr2 →
       (∀ s1 s2 s x1 x2 x sr1 sr2 e sr1' e' ok1,
          INV SPNone s1 s2 s x1 x2 x sr1 sr2 →
          R1 SPNone sr1 e SPLeft sr1' e' ok1 →
          pp_to_all (i (Incoming, e') s) (λ r1 y1,
          ∀ x', satisfiable (x ∗ y1 ∗ x') →
          ok1 ∧
          pp_to_ex (i1 (Incoming, e') s1) (λ r2 y2, ∃ e sr2' x'2 ok2,
            satisfiable (x1 ∗ y2 ∗ x'2) ∧
            r1.1.1 = Incoming ∧
            r2.1.1 = Incoming ∧
            r1.1.2 = r2.1.2 ∧
            R2 SPNone sr2 e SPLeft sr2' r1.1.2 ok2 ∧
            (ok2 → INV SPLeft r2.2 s2 r1.2 x'2 x2 x' sr1' sr2')))) →
       (∀ s1 s2 s x1 x2 x sr1 sr2 e sr1' e' ok1,
          INV SPNone s1 s2 s x1 x2 x sr1 sr2 →
          R1 SPNone sr1 e SPRight sr1' e' ok1 →
          pp_to_all (i (Incoming, e') s) (λ r1 y1,
          ∀ x', satisfiable (x ∗ y1 ∗ x') →
          ok1 ∧
          pp_to_ex (i2 (Incoming, e') s2) (λ r2 y2, ∃ e sr2' x'2 ok2,
            satisfiable (x2 ∗ y2 ∗ x'2) ∧
            r1.1.1 = Incoming ∧
            r2.1.1 = Incoming ∧
            r1.1.2 = r2.1.2 ∧
            R2 SPNone sr2 e SPRight sr2' r1.1.2 ok2 ∧
            (ok2 → INV SPRight s1 r2.2 r1.2 x1 x'2 x' sr1' sr2')))) →
       (∀ s1 s2 s x1 x2 x sr1 sr2 e ok1,
           INV SPLeft s1 s2 s x1 x2 x sr1 sr2 →
           pp_to_all (o1 e s1) (λ r1 y1, ∀ sr1' e' x',
             satisfiable (x' ∗ y1 ∗ x1) →
             r1.1.1 = Outgoing →
             R1 SPLeft sr1 r1.1.2 SPRight sr1' e' ok1 →
             ok1 ∧
             pp_to_ex (i2 (Incoming, e') s2) (λ r2 y2, ∃ sr2' x'2 ok2,
               satisfiable (x2 ∗ y2 ∗ x'2) ∧
               e.1 = Outgoing ∧
               r2.1.1 = Incoming ∧
               R2 SPLeft sr2 e.2 SPRight sr2' r2.1.2 ok2 ∧
               (ok2 → INV SPRight r1.2 r2.2 s x' x'2 x sr1' sr2')))) →
       (∀ s1 s2 s x1 x2 x sr1 sr2 e ok1,
           INV SPLeft s1 s2 s x1 x2 x sr1 sr2 →
           pp_to_all (o1 e s1) (λ r1 y1, ∀ sr1' e' x',
             satisfiable (x' ∗ y1 ∗ x1) →
             r1.1.1 = Outgoing →
             R1 SPLeft sr1 r1.1.2 SPNone sr1' e' ok1 →
             ∃ e'' sr2' ok2,
               e.1 = Outgoing ∧
               R2 SPLeft sr2 e.2 SPNone sr2' e'' ok2 ∧
               ok1 ∧
               (* There should not be ub when going out *)
               ok2 ∧
               pp_to_ex (o (Outgoing, e'') s) (λ r2 y2, ∃ x'2,
                 satisfiable (x'2 ∗ y2 ∗ x) ∧
                 r2.1.1 = Outgoing ∧
                 r2.1.2 = e' ∧
                 INV SPNone r1.2 s2 r2.2 x' x2 x'2 sr1' sr2'))) →
       (∀ s1 s2 s x1 x2 x sr1 sr2 e ok1,
           INV SPRight s1 s2 s x1 x2 x sr1 sr2 →
           pp_to_all (o2 e s2) (λ r1 y1, ∀ sr1' e' x',
             satisfiable (x' ∗ y1 ∗ x2) →
             r1.1.1 = Outgoing →
             R1 SPRight sr1 r1.1.2 SPLeft sr1' e' ok1 →
             ok1 ∧
             pp_to_ex (i1 (Incoming, e') s1) (λ r2 y2, ∃ sr2' x'2 ok2,
               satisfiable (x1 ∗ y2 ∗ x'2) ∧
               e.1 = Outgoing ∧
               r2.1.1 = Incoming ∧
               R2 SPRight sr2 e.2 SPLeft sr2' r2.1.2 ok2 ∧
               (ok2 → INV SPLeft r2.2 r1.2 s x'2 x' x sr1' sr2')))) →
       (∀ s1 s2 s x1 x2 x sr1 sr2 e ok1,
           INV SPRight s1 s2 s x1 x2 x sr1 sr2 →
           pp_to_all (o2 e s2) (λ r1 y1, ∀ sr1' e' x',
             satisfiable (x' ∗ y1 ∗ x2) →
             r1.1.1 = Outgoing →
             R1 SPRight sr1 r1.1.2 SPNone sr1' e' ok1 →
             ∃ e'' sr2' ok2,
               e.1 = Outgoing ∧
               R2 SPRight sr2 e.2 SPNone sr2' e'' ok2 ∧
               ok1 ∧
               (* There should not be ub when going out *)
               ok2 ∧
               pp_to_ex (o (Outgoing, e'') s) (λ r2 y2, ∃ x'2,
                 satisfiable (x'2 ∗ y2 ∗ x) ∧
                 r2.1.1 = Outgoing ∧
                 r2.1.2 = e' ∧
                 INV SPNone s1 r1.2 r2.2 x1 x' x'2 sr1' sr2'))) →
    trefines (link_mod R1 (prepost_mod i1 o1 m1 s1 x1) (prepost_mod i2 o2 m2 s2 x2) sr1)
             (prepost_mod i o (link_mod R2 m1 m2 sr2) s x).
    Proof.
      move => Hneq Hinv HN2L HN2R HL2R HL2N HR2L HR2N.
      apply tsim_implies_trefines => /= n.
      unshelve apply: tsim_remember. { simpl. exact (λ _
          '(σl1, sr1, (σf1, σ1, (σpp1, s1, x1)), (σf2, σ2, (σpp2, s2, x2)))
          '(σf, (σl2, sr2, σ1', σ2'), (σpp, s, x)),
           ∃ sp,
           σ1 = σ1' ∧ σ2 = σ2' ∧ INV sp s1 s2 s x1 x2 x sr1 sr2 ∧
          (( sp = SPNone ∧
              σl1 = MLFNone ∧ σf = SMFilter
            ∧ σpp1 = PPOutside ∧ σpp2 = PPOutside ∧ σpp = PPOutside
            ∧ σf1 = SMFilter ∧ σf2 = SMFilter
            ∧ σl2 = MLFNone)
           ∨ (sp = SPLeft ∧
              ((∃ e, σl2 = MLFRecvL e ∧ σf1 = SMProgRecv (Incoming, e))
               ∨ (σl2 = MLFLeft ∧ σf1 = SMProg))
            ∧ σpp1 = PPInside ∧ σpp2 = PPOutside ∧ σpp = PPInside
            ∧ σf = SMProg ∧ σf2 = SMFilter
            ∧ σl1 = MLFLeft)
           ∨ (sp = SPRight ∧
              ((∃ e, σl2 = MLFRecvR e ∧ σf2 = SMProgRecv (Incoming, e))
               ∨ (σl2 = MLFRight ∧ σf2 = SMProg))
            ∧ σpp1 = PPOutside ∧ σpp2 = PPInside ∧ σpp = PPInside
            ∧ σf = SMProg ∧ σf1 = SMFilter
            ∧ σl1 = MLFRight) )). }
      { split!. } { done. }
      move => {}n _ /= Hloop {Hinv}.
      move => [[[σl1 {}sr1] [[σf1 {}σ1] [[σpp1 {}s1] {}x1]]] [[σf2 {}σ2] [[σpp2 {}s2] {}x2]]].
      move => [[σf [[[σl2 {}sr2] σ1'] σ2']] [[σpp {}s] {}x]] ?. destruct!.
      - tstep_i => ? p' ?? ok1 ?.
        tstep_s. split!.
        tstep_s. apply pp_to_all_forall => ri xi Hi x' Hsat.
        destruct p' => /=. 3: clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver.
        + move: ri xi Hi x' Hsat. apply: pp_to_all_forall_2.
          apply: pp_to_all_mono; [by apply: HN2L|].
          move => [[??]?] ? /= Hcont ??.
          destruct ok1; [|clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver].
          tstep_i => ??. simplify_eq.
          tstep_i.
          apply: pp_to_ex_mono; [clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver|].
          move => [[??]?] ? /= *. destruct!. split!; [done|].
          tstep_s.
          split!; [done..|] => /=.
          destruct ok2; [|by tstep_s].
          apply: Hloop; [done|]. split!; eauto.
        + move: ri xi Hi x' Hsat. apply: pp_to_all_forall_2.
          apply: pp_to_all_mono; [by apply: HN2R|].
          move => [[??]?] ? /= Hcont ??.
          destruct ok1; [|clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver].
          tstep_i => ??. simplify_eq.
          tstep_i.
          apply: pp_to_ex_mono; [clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver|].
          move => [[??]?] ? /= *. destruct!. split!; [done|].
          tstep_s.
          split!; [done..|] => /=.
          destruct ok2; [|by tstep_s].
          apply: Hloop; [done|]. split!; eauto.
      - tsim_mirror m1.(m_trans) σ1'. (* TODO: use tsim_mirror more *)
        move => ??? Hs. tstep_both. apply Hs => ????.
        case_match.
        2: { tstep_s. eexists None. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|]. eauto. }
        move => ?. subst. tstep_s. eexists (Some (Incoming, _)). split!.
        apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
        apply: Hloop; [done|]. by split!.
      - tstep_both.
        apply steps_impl_step_end => κ Pσ2 ? *. destruct κ as [e|]. 2: {
          tstep_s. eexists None. split!.
          apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
          apply: Hloop; [done|]. by split!.
        }
        tend. have [σ' Hσ'] := vis_no_all _ _ _ ltac:(done).
        eexists σ'. split; [clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver|].
        tstep_i. apply pp_to_all_forall => ri xi Hi x' Hsat p' sr1' e' ok1 HR1 Hri.
        destruct p' => /=. 1: clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver.
        + move: ri xi Hi x' Hsat sr1' e' Hri HR1. apply: pp_to_all_forall_2.
          apply: pp_to_all_mono; [by apply: HL2R|].
          move => [[??]?] ? /= Hcont ??????.
          destruct ok1; [|clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver].
          tstep_i => ??; simplify_eq.
          tstep_i.
          apply: pp_to_ex_mono; [clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver|].
          move => [[??]?] ? /=?. destruct!. split!; [done|].
          tstep_s. eexists (Some (Outgoing, _)). split!; [done|].
          destruct e; simplify_eq/=.
          apply: steps_spec_step_end; [done|] => ??.
          destruct ok2; [|by tstep_s].
          apply: Hloop; [done|]. split!; eauto. clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver.
        + move: ri xi Hi x' Hsat sr1' e' Hri HR1. apply: pp_to_all_forall_2.
          apply: pp_to_all_mono; [by apply: HL2N|].
          move => [[??]?] ? /= Hcont ??????.
          have {}Hcont := Hcont _ _ _ ltac:(done) ltac:(done) ltac:(done). destruct!.
          destruct e; simplify_eq/=.
          destruct ok1, ok2 => //.
          tstep_s. eexists (Some (Outgoing, _)). split!; [done|].
          apply: steps_spec_step_end; [done|] => ??.
          tstep_s.
          apply: pp_to_ex_mono; [done|].
          move => [[??]?] ? /=?. destruct!. split!; [done|].
          apply: Hloop; [done|]. split!. clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver.
      - tstep_both.
        apply steps_impl_step_end => κ Pσ2 ?. case_match; intros; simplify_eq.
        + tstep_s. eexists (Some (Incoming, _)). split!.
          apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
          apply: Hloop; [done|]. by split!.
        + tstep_s. eexists None.
          apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
          apply: Hloop; [done|]. by split!.
      - tstep_both.
        apply steps_impl_step_end => κ Pσ2 ? *. destruct κ as [e|]. 2: {
          tstep_s. eexists None. split!.
          apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
          apply: Hloop; [done|]. by split!.
        }
        tend. have [σ' Hσ'] := vis_no_all _ _ _ ltac:(done).
        eexists σ'. split; [clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver|].
        tstep_i. apply pp_to_all_forall => ri xi Hi x' Hsat p' sr1' e' ok1 HR1 Hri.
        destruct p' => /=. 2: clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver.
        + move: ri xi Hi x' Hsat sr1' e' Hri HR1. apply: pp_to_all_forall_2.
          apply: pp_to_all_mono; [by apply: HR2L|].
          move => [[??]?] ? /= Hcont ??????.
          destruct ok1; [|clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver].
          tstep_i => ??; simplify_eq.
          tstep_i.
          apply: pp_to_ex_mono; [clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver|].
          move => [[??]?] ? /=?. destruct!. split!; [done|].
          tstep_s. eexists (Some (Outgoing, _)). split!; [done|].
          destruct e; simplify_eq/=.
          apply: steps_spec_step_end; [done|] => ??.
          destruct ok2; [|by tstep_s].
          apply: Hloop; [done|]. split!; eauto. clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver.
        + move: ri xi Hi x' Hsat sr1' e' Hri HR1. apply: pp_to_all_forall_2.
          apply: pp_to_all_mono; [by apply: HR2N|].
          move => [[??]?] ? /= Hcont ??????.
          have {}Hcont := Hcont _ _ _ ltac:(done) ltac:(done) ltac:(done). destruct!.
          destruct e; simplify_eq/=.
          destruct ok1, ok2 => //.
          tstep_s. eexists (Some (Outgoing, _)). split!; [done|].
          apply: steps_spec_step_end; [done|] => ??.
          tstep_s.
          apply: pp_to_ex_mono; [done|].
          move => [[??]?] ? /= ?. destruct!. split!; [done|].
          apply: Hloop; [done|]. split!. clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver.
    Qed.

  Lemma mod_prepost_combine
        {EV1 EV2 EV S1 S2 S : Type}
        {M1 M2 M : ucmra}
        (m : module EV)
        (INV : player → S1 → S2 → S → uPred M1 → uPred M2 → uPred M → Prop)
        (i1 : EV1 → S1 → prepost (EV2 * S1) M1)
        (o1 : EV2 → S1 → prepost (EV1 * S1) M1)
        (i2 : EV2 → S2 → prepost (EV * S2) M2)
        (o2 : EV → S2 → prepost (EV2 * S2) M2)
        (i : EV1 → S → prepost (EV * S) M)
        (o : EV → S → prepost (EV1 * S) M)
        s1 s2 s x1 x2 x
        `{!VisNoAll m.(m_trans)}
        :
        INV Env s1 s2 s x1 x2 x →
       (∀ s1 s2 s x1 x2 x e,
           INV Env s1 s2 s x1 x2 x →
           pp_to_all (i e s) (λ r y, ∀ x',
            satisfiable (x ∗ y ∗ x') →
             pp_to_ex (i1 e s1) (λ r1 y1, ∃ x1',
               satisfiable (x1 ∗ y1 ∗ x1') ∧
               pp_to_ex (i2 r1.1 s2) (λ r2 y2, ∃ x2',
                 satisfiable (x2 ∗ y2 ∗ x2') ∧
                 r.1 = r2.1 ∧
                 INV Prog r1.2 r2.2 r.2 x1' x2' x')))) →
       (∀ s1 s2 s x1 x2 x e,
           INV Prog s1 s2 s x1 x2 x →
           pp_to_all (o2 e s2) (λ r2 y2, ∀ x2',
             satisfiable (x2' ∗ y2 ∗ x2) →
             pp_to_all (o1 r2.1 s1) (λ r1 y1, ∀ x1',
             satisfiable (x1' ∗ y1 ∗ x1) →
               pp_to_ex (o e s) (λ r y, ∃ x',
                 satisfiable (x' ∗ y ∗ x) ∧
                 r.1 = r1.1 ∧
                 INV Env r1.2 r2.2 r.2 x1' x2' x')))) →
    trefines (prepost_mod i1 o1 (prepost_mod i2 o2 m s2 x2) s1 x1)
             (prepost_mod i o m s x).
    Proof.
      move => Hinv Henv Hprog.
      apply tsim_implies_trefines => /= n.
      unshelve apply: tsim_remember. { simpl. exact (λ _
          '(σf1, (σf2, σ1, (σpp2, s2, x2)), (σpp1, s1, x1))
          '(σf, σ, (σpp, s, x)),
           ∃ p, σ = σ1 ∧ INV p s1 s2 s x1 x2 x ∧
           ((p = Env ∧ σf1 = SMFilter ∧ σf2 = SMFilter ∧ σf = SMFilter ∧
              σpp1 = PPOutside ∧ σpp2 = PPOutside ∧ σpp = PPOutside) ∨
            (p = Prog ∧ σf1 = SMProg ∧ σpp1 = PPInside ∧ σpp2 = PPInside ∧ σpp = PPInside ∧
               (σf = SMProg ∧ σf2 = SMProg ∨ ∃ e, σf = SMProgRecv e ∧ σf2 = SMProgRecv e)))). }
      { split!. } { done. }
      move => {}n _ /= Hloop {Hinv}.
      move => [[σf1 [[σf2 σ1] [[σpp2 {}s2] {}x2]]] [[σpp1 {}s1] {}x1]].
      move => [[σf {}σ] [[σpp {}s] {}x]] ?. destruct!.
      - tstep_i => ?.
        tstep_s. split!.
        tstep_s. apply: pp_to_all_mono; [by apply: Henv|]. move => r y /= ???.
        tstep_i. apply: pp_to_ex_mono; [naive_solver|]. move => r1 y1 /= [?[??]]. split!; [done|].
        tstep_i => ??. subst.
        tstep_i. apply: pp_to_ex_mono; [done|]. move => r2 y2 /= [?[?[??]]]. split!; [done|].
        apply: Hloop; [done|]. split!. by f_equal.
      - tstep_both.
        apply steps_impl_step_end => κ Pσ2 ? *. destruct κ as [e'|]. 2: {
          tstep_s. eexists None.
          apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
          apply: Hloop; [done|]. by split!.
        }
        tend. have [σ' Hσ'] := vis_no_all _ _ _ ltac:(done). eexists σ'. split; [naive_solver|].
        tstep_i. apply: pp_to_all_mono; [by apply: Hprog|]. move => r2 y2 /= ???.
        tstep_i. apply: pp_to_all_mono; [naive_solver|]. move => r1 y1 /= ???.
        tstep_s. eexists _. apply: steps_spec_step_end; [done|] => ?? /=.
        tstep_s. apply: pp_to_ex_mono; [naive_solver|]. move => r y /= [?[?[??]]]. split!; [done|].
        apply: Hloop; [done|]. split!. naive_solver.
      - tstep_both.
        apply steps_impl_step_end => κ Pσ2 ? *. destruct κ as [e'|]. 2: {
          tstep_s. eexists None. split!.
          apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
          apply: Hloop; [done|]. by split!.
        }
        move => ->.
        tstep_s. eexists (Some _). split; [done|].
        apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
        apply: Hloop; [done|]. split!.
    Qed.

  Lemma mod_prepost_impl
        {EV1 EV2 Si Ss : Type}
        {Mi Ms : ucmra}
        (m : module EV2)
        (INV : player → Si → Ss → uPred Mi → uPred Ms → Prop)
        (i_i : EV1 → Si → prepost (EV2 * Si) Mi)
        (o_i : EV2 → Si → prepost (EV1 * Si) Mi)
        (i_s : EV1 → Ss → prepost (EV2 * Ss) Ms)
        (o_s : EV2 → Ss → prepost (EV1 * Ss) Ms)
        si ss xi xs
        `{!VisNoAll m.(m_trans)}
        :
        INV Env si ss xi xs →
       (∀ si ss xi xs e,
           INV Env si ss xi xs →
           pp_to_all (i_s e ss) (λ rs ys, ∀ xs',
            satisfiable (xs ∗ ys ∗ xs') →
             pp_to_ex (i_i e si) (λ ri yi, ∃ xi',
               satisfiable (xi ∗ yi ∗ xi') ∧
               rs.1 = ri.1 ∧
               INV Prog ri.2 rs.2 xi' xs'))) →
       (∀ si ss xi xs e,
           INV Prog si ss xi xs →
           pp_to_all (o_i e si) (λ ri yi, ∀ xi',
             satisfiable (xi' ∗ yi ∗ xi) →
             pp_to_ex (o_s e ss) (λ rs ys, ∃ xs',
               satisfiable (xs' ∗ ys ∗ xs) ∧
               rs.1 = ri.1 ∧
               INV Env ri.2 rs.2 xi' xs'))) →
    trefines (prepost_mod i_i o_i m si xi)
             (prepost_mod i_s o_s m ss xs).
    Proof.
      move => Hinv Henv Hprog.
      apply tsim_implies_trefines => /= n.
      unshelve apply: tsim_remember. { simpl. exact (λ _
          '(σfi, σi, (σppi, si, xi))
          '(σfs, σs, (σpps, ss, xs)),
           ∃ p, σi = σs ∧ INV p si ss xi xs ∧ σfi = σfs ∧ σppi = σpps ∧
           ((p = Env ∧ σfi = SMFilter ∧ σppi = PPOutside) ∨
            (p = Prog ∧ σppi = PPInside ∧
               (σfi = SMProg ∨ ∃ e, σfi = SMProgRecv e)))). }
      { split!. } { done. }
      move => {}n _ /= Hloop {Hinv}.
      move => [[σfi σi] [[σppi {}si] {}xi]].
      move => [[σfs {}σs] [[σpps {}ss] {}xs]] ?. destruct!.
      - tstep_i => ?.
        tstep_s. split!.
        tstep_s. apply: pp_to_all_mono; [by apply: Henv|]. move => r y /= ???.
        tstep_i. apply: pp_to_ex_mono; [naive_solver|]. move => r1 y1 /= [?[??]]. split!; [done|]. destruct!.
        apply: Hloop; [done|]. split!. by f_equal.
      - tstep_both.
        apply steps_impl_step_end => κ Pσ2 ? *. destruct κ as [e'|]. 2: {
          tstep_s. eexists None.
          apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
          apply: Hloop; [done|]. by split!.
        }
        tend. have [σ' Hσ'] := vis_no_all _ _ _ ltac:(done). eexists σ'. split; [naive_solver|].
        tstep_i. apply: pp_to_all_mono; [by apply: Hprog|]. move => r2 y2 /= ???.
        tstep_s. eexists _. apply: steps_spec_step_end; [done|] => ?? /=.
        tstep_s. apply: pp_to_ex_mono; [naive_solver|]. move => r y /= [?[?[??]]]. split!; [done|].
        apply: Hloop; [done|]. split!. naive_solver.
      - tstep_both.
        apply steps_impl_step_end => κ Pσ2 ? *. destruct κ as [e'|]. 2: {
          tstep_s. eexists None. split!.
          apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
          apply: Hloop; [done|]. by split!.
        }
        move => ->.
        tstep_s. eexists (Some _). split; [done|].
        apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
        apply: Hloop; [done|]. split!.
    Qed.

End prepost.
