Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.link.
Require Import refframe.seq_product.
Require Import refframe.state_transform.
Require Import refframe.proof_techniques.

Set Default Proof Using "Type".

(** * prepost *)
Section prepost.
Context {R : Type}.

Inductive prepost : Type :=
| pp_end (r : R)
| pp_prop (P : Prop) (pp : prepost)
| pp_quant {T} (pp : T → prepost)
.

Fixpoint pp_to_ex (pp : prepost) (Q : R → Prop) : Prop :=
  match pp with
  | pp_end r => Q r
  | pp_prop P pp' => P ∧ pp_to_ex pp' Q
  | pp_quant pp' => ∃ x, pp_to_ex (pp' x) Q
  end.

Fixpoint pp_to_all (pp : prepost) (Q : R → Prop) : Prop :=
  match pp with
  | pp_end r => Q r
  | pp_prop P pp' => P → pp_to_all pp' Q
  | pp_quant pp' => ∀ x, pp_to_all (pp' x) Q
  end.

Lemma pp_to_ex_exists pp Q:
  pp_to_ex pp Q ↔ ∃ r, Q r ∧ pp_to_ex pp (r =.).
Proof. elim: pp => /=; naive_solver. Qed.

Lemma pp_to_all_forall pp Q:
  pp_to_all pp Q ↔ (∀ r, pp_to_ex pp (r =.) → Q r).
Proof. elim: pp => /=; naive_solver. Qed.
Lemma pp_to_all_forall_2 pp Q:
  pp_to_all pp Q →
  ∀ r, pp_to_ex pp (r =.) → Q r.
Proof. apply pp_to_all_forall. Qed.

Lemma pp_to_all_mono pp (Q1 Q2 : _ → Prop):
  pp_to_all pp Q1 →
  (∀ r, Q1 r → Q2 r) →
  pp_to_all pp Q2.
Proof. elim: pp => /=; naive_solver. Qed.

Lemma pp_to_ex_mono pp (Q1 Q2 : _ → Prop):
  pp_to_ex pp Q1 →
  (∀ r, Q1 r → Q2 r) →
  pp_to_ex pp Q2.
Proof. elim: pp => /=; naive_solver. Qed.

Lemma pp_to_all_ex pp Q1 Q2:
  pp_to_all pp Q1 →
  pp_to_ex pp Q2 →
  ∃ r, Q1 r ∧ Q2 r.
Proof. move => /pp_to_all_forall ? /pp_to_ex_exists. naive_solver. Qed.
End prepost.

Arguments prepost : clear implicits.

(** * mod_prepost *)
Section prepost.
  Context {EV1 EV2 S : Type}.
  Implicit Types (i : EV2 → S → prepost (EV1 * S)) (o : EV1 → S → prepost (EV2 * S)).
  Implicit Types (m : module EV1).

  Inductive pp_state : Type :=
  | PPOutside
  | PPRecv1 (e : EV2)
  | PPRecv2 (e : EV1)
  | PPInside
  | PPSend1 (e : EV1)
  | PPSend2 (e : EV2)
  .

  Inductive pp_filter_step i o :
    (pp_state * S) → option (EV1 + EV2) → ((pp_state * S) → Prop) → Prop :=
  | PPOutsideS s e:
    pp_filter_step i o (PPOutside, s) (Some (inr e)) (λ σ, σ = (PPRecv1 e, s))
  | PPRecv1S s e:
    pp_filter_step i o (PPRecv1 e, s) None (λ σ, pp_to_ex (i e s) (λ r, σ = (PPRecv2 r.1, r.2)))
  | PPRecv2S s e:
    pp_filter_step i o (PPRecv2 e, s) (Some (inl e)) (λ σ, σ = (PPInside, s))
  | PPInsideS s e:
    pp_filter_step i o (PPInside, s) (Some (inl e)) (λ σ, σ = (PPSend1 e, s))
  | PPSend1S s e r:
    pp_to_ex (o e s) (r=.) →
    pp_filter_step i o (PPSend1 e, s) None (λ σ, σ = (PPSend2 r.1, r.2))
  | PPSend2S s e:
    pp_filter_step i o (PPSend2 e, s) (Some (inr e)) (λ σ, σ = (PPOutside, s))
  .

  Definition mod_prepost_filter i o :=
    Mod (pp_filter_step i o).

  Global Instance mod_prepost_filter_vis_no_all i o : VisNoAll (mod_prepost_filter i o).
  Proof. move => ????. invert_all @m_step; naive_solver. Qed.

  Definition mod_prepost i o m : module EV2 :=
    mod_seq_map m (mod_prepost_filter i o).

  Global Instance mod_prepost_vis_no_all i o m `{!VisNoAll m}: VisNoAll (mod_prepost i o m).
  Proof. apply _. Qed.

  Lemma mod_prepost_trefines i o m m' σ σ' σm s `{!VisNoAll m}:
    trefines (MS m σ) (MS m' σ') →
    trefines (MS (mod_prepost i o m) (σm, σ, s)) (MS (mod_prepost i o m') (σm, σ', s)).
  Proof.
    move => ?. apply mod_seq_map_trefines => //. apply _.
  Qed.

  Lemma mod_prepost_step_Outside_i i o m σ s:
    TStepI (mod_prepost i o m) (SMFilter, σ, (PPOutside, s)) (λ G,
        ∀ e, G true (Some e) (λ G', G' (SMFilter, σ, (PPRecv1 e, s)))).
  Proof.
    constructor => G /= ?. tstep_i.
    apply steps_impl_step_end => ???. invert_all @m_step => ???. split! => ?. split!; [naive_solver|done|].
    naive_solver.
  Qed.

  Lemma mod_prepost_step_Recv1_i i o m σ s e:
    TStepI (mod_prepost i o m) (SMFilter, σ, (PPRecv1 e, s)) (λ G,
        pp_to_ex (i e s) (λ r, G true None (λ G', G' (SMProgRecv r.1, σ, (PPInside, r.2))))).
  Proof.
    constructor => G /= /pp_to_ex_exists[r [HG Hex]]. tstep_i.
    apply steps_impl_step_next => ???. invert_all @m_step.
    eexists (_, _). split!. { apply pp_to_ex_exists. naive_solver. }
    apply steps_impl_step_end => ???. invert_all @m_step => ???. naive_solver.
  Qed.

  Lemma mod_prepost_step_Inside_i i o m σ s e:
    TStepI (mod_prepost i o m) (SMFilterRecv e, σ, (PPInside, s)) (λ G,
        pp_to_all (o e s) (λ r, G true (Some (r.1)) (λ G', G' (SMFilter, σ, (PPOutside, r.2))))).
  Proof.
    constructor => G /= ?. apply steps_impl_step_trans. tstep_i.
    apply steps_impl_step_end => ???. invert_all @m_step => ? b *; simplify_eq. split! => ?. split!; [done|].
    tstep_i.
    apply steps_impl_step_next => ???. invert_all @m_step => *; simplify_eq. split!.
    apply steps_impl_step_end => ???. invert_all @m_step => *; simplify_eq. split! => ?.
    have [?[??]]:= pp_to_all_ex _ _ _ ltac:(done) ltac:(done); subst.
    split!; [done|by destruct b|]. naive_solver.
  Qed.

  Lemma mod_prepost_step_Outside_s i o m σ s:
    TStepS (mod_prepost i o m) (SMFilter, σ, (PPOutside, s)) (λ G,
        ∃ e, G (Some e) (λ G', G' (SMFilter, σ, (PPRecv1 e, s)))).
  Proof.
    constructor => G /= [??]. split!; [done|] => /= ??. tstep_s. eexists (Some (inr _)). split!.
    apply: steps_spec_step_end; [by econs|]. naive_solver.
  Qed.


  Lemma mod_prepost_step_Recv1_s i o m σ s e:
    TStepS (mod_prepost i o m) (SMFilter, σ, (PPRecv1 e, s)) (λ G,
        G None (λ G', pp_to_all (i e s) (λ r, G' (SMProgRecv r.1, σ, (PPInside, r.2))))).
  Proof.
    constructor => G /= ?. split!; [done|] => /= ??. apply steps_spec_step_trans.
    tstep_s. eexists None. split!.
    apply: steps_spec_step_end; [by econs|] => ? /=?.
    have [?[??]]:= pp_to_all_ex _ _ _ ltac:(done) ltac:(done); subst.
    tstep_s. eexists (Some (inl _)). split!.
    apply: steps_spec_step_end; [by econs|]. naive_solver.
  Qed.

  Lemma mod_prepost_step_Inside_s i o m σ s e:
    TStepS (mod_prepost i o m) (SMFilterRecv e, σ, (PPInside, s)) (λ G,
        pp_to_ex (o e s) (λ r, G (Some (r.1)) (λ G', G' (SMFilter, σ, (PPOutside, r.2))))).
  Proof.
    constructor => G /= /pp_to_ex_exists[?[??]]. split!; [done|] => /= ??.
    apply steps_spec_step_trans. tstep_s. eexists (Some _). split!.
    apply: steps_spec_step_end; [by econs|] => /= ? ->. tstep_s. eexists (Some (inr _)). split!.
    apply: steps_spec_step; [by econs|] => /= ? ->.
    apply: steps_spec_step_end; [by econs|] => /= ? ->.
    done.
  Qed.
End prepost.

Global Hint Resolve
       mod_prepost_step_Outside_i
       mod_prepost_step_Recv1_i
       mod_prepost_step_Inside_i
       mod_prepost_step_Outside_s
       mod_prepost_step_Recv1_s
       mod_prepost_step_Inside_s
 | 3 : tstep.

Definition prepost_id {EV} : EV → unit → prepost (EV * unit) :=
  λ x _, pp_end (x, tt).

Lemma prepost_id_l S EV1 EV2 (m : module EV1) σ i o s:
  trefines (MS (mod_prepost i o (mod_prepost prepost_id prepost_id m))
               (SMFilter, (SMFilter, σ, (PPOutside, tt)), (PPOutside, s)))
           (MS (mod_prepost (S:=S) (EV2:=EV2) i o m) (SMFilter, σ, (PPOutside, s))).
Proof.
  apply tsim_implies_trefines => /= n.
  tstep_i => ?.
  tstep_s. split!.
  tstep_s. apply pp_to_all_forall => ??.
  tstep_i. apply: pp_to_ex_mono; [done|].
  move => ? <-.
  tstep_i => ? <-.
  tstep_i.
  unshelve apply: tsim_remember. { simpl. exact (λ _
      '(σf1, (σf1', σ1, (σpp1', _)), (σpp1, s1)) '(σf2, σ2, (σpp2, s2)),
         σf1 = SMProg ∧ σf1' = σf2 ∧ σ1 = σ2 ∧ σpp1 = PPInside
         ∧ σpp1' = PPInside ∧ σpp2 = PPInside ∧ s1 = s2 ∧
         ((∃ e, σf1' = SMProgRecv e) ∨ σf1' = SMProg)). }
  { split!. } { done. }
  move => {}n _ Hloop [[σf1 [[σf1' σ1] [σpp1' []]] [σpp1 s1]]] [[σf2 σ2] [σpp2 s2]] ?.
  destruct_all?; simplify_eq.
  - tstep_both. apply: steps_impl_step_end => κ ??. case_match => *.
    + subst. tstep_s. eexists (Some _). split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [done|]. split!.
    + tstep_s. eexists None. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [done|]. split!.
  - tstep_both. apply: steps_impl_step_end => κ ??.
    tstep_s. eexists _. apply: steps_spec_step_end; [done|] => ??.
    case_match; tend; (split!; [done|]). 2: { apply: Hloop; [done|]. split!. }
    tstep_i. tstep_i. apply pp_to_all_forall => ??.
    tstep_s. apply: pp_to_ex_mono; [done|]. move => ? <-. split!.
    tstep_i => ?.
    tstep_s. split!.
    tstep_s. apply pp_to_all_forall => ??.
    tstep_i. apply: pp_to_ex_mono; [done|]. move => ? <-.
    tstep_i => ? <-.
    tstep_i.
    apply Hloop; [done|]. split!.
Qed.

(* Lemma prepost_id_l EV (m : module EV) σ s: *)
(*   trefines (MS (mod_prepost prepost_id prepost_id m) (SMFilter, σ, (PPOutside, s))) (MS m σ). *)
(* Proof. *)
  (* apply tsim_implies_trefines => /= n. *)
  (* tstep_i. *)


Section prepost.

  Lemma mod_prepost_link
        {EV1 EV2 S1 S2 S' Sr1 Sr2 : Type}
        (INV : seq_product_state → S1 → S2 → S' → Sr1 → Sr2 → Prop)
        (i1 : io_event EV2 → S1 → prepost (io_event EV1 * S1))
        (o1 : io_event EV1 → S1 → prepost (io_event EV2 * S1))
        (i2 : io_event EV2 → S2 → prepost (io_event EV1 * S2))
        (o2 : io_event EV1 → S2 → prepost (io_event EV2 * S2))
        (i : io_event EV2 → S' → prepost (io_event EV1 * S'))
        (o : io_event EV1 → S' → prepost (io_event EV2 * S'))
        (R1 : seq_product_state → Sr1 → EV2 → seq_product_state → Sr1 → EV2 → Prop)
        (R2 : seq_product_state → Sr2 → EV1 → seq_product_state → Sr2 → EV1 → Prop)
        (m1 m2 : module (io_event EV1))
        σ1 σ2 s1 s2 sr1 sr2 s
        `{!VisNoAll m1} `{!VisNoAll m2}
        :

       (∀ p s e p' s' e', R1 p s e p' s' e' → p ≠ p') →
       INV SPNone s1 s2 s sr1 sr2 →
       (∀ s1 s2 s sr1 sr2 e sr1' e',
          R1 SPNone sr1 e SPLeft sr1' e' →
          INV SPNone s1 s2 s sr1 sr2 →
          pp_to_all (i (Incoming, e') s) (λ r1,
          pp_to_ex (i1 (Incoming, e') s1) (λ r2, ∃ e sr2',
            r1.1.1 = Incoming ∧
            r2.1.1 = Incoming ∧
            r1.1.2 = r2.1.2 ∧
            R2 SPNone sr2 e SPLeft sr2' r1.1.2 ∧
            INV SPLeft r2.2 s2 r1.2 sr1' sr2'))) →
       (∀ s1 s2 s sr1 sr2 e sr1' e',
          R1 SPNone sr1 e SPRight sr1' e' →
          INV SPNone s1 s2 s sr1 sr2 →
          pp_to_all (i (Incoming, e') s) (λ r1,
          pp_to_ex (i2 (Incoming, e') s2) (λ r2, ∃ e sr2',
            r1.1.1 = Incoming ∧
            r2.1.1 = Incoming ∧
            r1.1.2 = r2.1.2 ∧
            R2 SPNone sr2 e SPRight sr2' r1.1.2 ∧
            INV SPRight s1 r2.2 r1.2 sr1' sr2'))) →
       (∀ s1 s2 s sr1 sr2 e,
           INV SPLeft s1 s2 s sr1 sr2 →
           pp_to_all (o1 e s1) (λ r1, ∀ sr1' e',
             r1.1.1 = Outgoing →
             R1 SPLeft sr1 r1.1.2 SPRight sr1' e' →
             pp_to_ex (i2 (Incoming, e') s2) (λ r2, ∃ sr2',
               e.1 = Outgoing ∧
               r2.1.1 = Incoming ∧
               INV SPRight r1.2 r2.2 s sr1' sr2' ∧
               R2 SPLeft sr2 e.2 SPRight sr2' r2.1.2))) →
       (∀ s1 s2 s sr1 sr2 e,
           INV SPLeft s1 s2 s sr1 sr2 →
           pp_to_all (o1 e s1) (λ r1, ∀ sr1' e',
             r1.1.1 = Outgoing →
             R1 SPLeft sr1 r1.1.2 SPNone sr1' e' →
             ∃ e'' sr2',
               e.1 = Outgoing ∧
               R2 SPLeft sr2 e.2 SPNone sr2' e'' ∧
               pp_to_ex (o (Outgoing, e'') s) (λ r2,
                 r2.1.1 = Outgoing ∧
                 r2.1.2 = e' ∧
                 INV SPNone r1.2 s2 r2.2 sr1' sr2'))) →
       (∀ s1 s2 s sr1 sr2 e,
           INV SPRight s1 s2 s sr1 sr2 →
           pp_to_all (o2 e s2) (λ r1, ∀ sr1' e',
             r1.1.1 = Outgoing →
             R1 SPRight sr1 r1.1.2 SPLeft sr1' e' →
             pp_to_ex (i1 (Incoming, e') s1) (λ r2, ∃ sr2',
               e.1 = Outgoing ∧
               r2.1.1 = Incoming ∧
               INV SPLeft r2.2 r1.2 s sr1' sr2' ∧
               R2 SPRight sr2 e.2 SPLeft sr2' r2.1.2))) →
       (∀ s1 s2 s sr1 sr2 e,
           INV SPRight s1 s2 s sr1 sr2 →
           pp_to_all (o2 e s2) (λ r1, ∀ sr1' e',
             r1.1.1 = Outgoing →
             R1 SPRight sr1 r1.1.2 SPNone sr1' e' →
             ∃ e'' sr2',
               e.1 = Outgoing ∧
               R2 SPRight sr2 e.2 SPNone sr2' e'' ∧
               pp_to_ex (o (Outgoing, e'') s) (λ r2,
                 r2.1.1 = Outgoing ∧
                 r2.1.2 = e' ∧
                 INV SPNone s1 r1.2 r2.2 sr1' sr2'))) →
    trefines (MS (mod_link R1 (mod_prepost i1 o1 m1) (mod_prepost i2 o2 m2))
                 (MLFNone, sr1, (SMFilter, σ1, (PPOutside, s1)), (SMFilter, σ2, (PPOutside, s2))))
             (MS (mod_prepost i o (mod_link R2 m1 m2))
                 (SMFilter, (MLFNone, sr2, σ1, σ2), (PPOutside, s))).
    Proof.
      move => Hneq Hinv HN2L HN2R HL2R HL2N HR2L HR2N.
      apply tsim_implies_trefines => /= n.
      unshelve apply: tsim_remember. { simpl. exact (λ _
          '(σl1, sr1, (σf1, σ1, (σpp1, s1)), (σf2, σ2, (σpp2, s2)))
          '(σf, (σl2, sr2, σ1', σ2'), (σpp, s)),
           ∃ sp,
           σ1 = σ1' ∧ σ2 = σ2' ∧ INV sp s1 s2 s sr1 sr2 ∧
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
      move => [[[σl1 {}sr1] [[σf1 {}σ1] [σpp1 {}s1]]] [[σf2 {}σ2] [σpp2 {}s2]]].
      move => [[σf [[[σl2 {}sr2] σ1'] σ2']] [σpp {}s]] ?. destruct_all?; simplify_eq.
      - tstep_i => ? p' ???.
        tstep_s. split!.
        tstep_s. apply pp_to_all_forall => ri Hi.
        destruct p' => /=. 3: naive_solver.
        + tstep_i => ??. simplify_eq.
          tstep_i. move: ri Hi. apply pp_to_all_forall.
          apply: pp_to_all_mono; [by apply: HN2L|].
          move => [[??]?] /= Hcont. apply: pp_to_ex_mono; [done|].
          move => [[??]?] /= *. destruct_all?; simplify_eq.
          tstep_s.
          split!; [done..|] => /=.
          apply: Hloop; [done|]. by split!.
        + tstep_i => ??. simplify_eq.
          tstep_i. move: ri Hi. apply pp_to_all_forall.
          apply: pp_to_all_mono; [by apply: HN2R|].
          move => [[??]?] /= Hcont. apply: pp_to_ex_mono; [done|].
          move => [[??]?] /= *. destruct_all?; simplify_eq.
          tstep_s.
          split!; [done..|] => /=.
          apply: Hloop; [done|]. by split!.
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
        tend. have [σ' Hσ'] := vis_no_all _ _ _ ltac:(done). eexists σ'. split; [naive_solver|].
        tstep_i. apply pp_to_all_forall => ri Hi p' sr1' e' HR1 Hri.
        destruct p' => /=. 1: naive_solver.
        + tstep_i => ??; simplify_eq.
          tstep_i.
          move: ri Hi sr1' e' Hri HR1. apply: pp_to_all_forall_2.
          apply: pp_to_all_mono; [ by apply: HL2R|].
          move => [[??]?] /= Hcont ????.
          apply: pp_to_ex_mono; [ by apply: Hcont|].
          move => [[??]?] /=?. destruct_all?; simplify_eq.
          tstep_s. eexists (Some (Outgoing, _)). split!; [done|].
          destruct e; simplify_eq/=.
          apply: steps_spec_step_end; [done|] => ??.
          apply: Hloop; [done|]. split!; [naive_solver|done..].
        + move: ri Hi sr1' e' Hri HR1. apply: pp_to_all_forall_2.
          apply: pp_to_all_mono; [by apply: HL2N|].
          move => [[??]?] /= Hcont ????.
          have {}Hcont := Hcont _ _ ltac:(done) ltac:(done). destruct_all?.
          destruct e; simplify_eq/=.
          tstep_s. eexists (Some (Outgoing, _)). split!; [done|].
          apply: steps_spec_step_end; [done|] => ??.
          tstep_s.
          apply: pp_to_ex_mono; [done|].
          move => [[??]?] /= *. destruct_all?; simplify_eq. split!.
          apply: Hloop; [done|]. split!; [naive_solver|done..].
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
        tend. have [σ' Hσ'] := vis_no_all _ _ _ ltac:(done). eexists σ'. split; [naive_solver|].
        tstep_i. apply pp_to_all_forall => ri Hi p' sr1' e' HR1 Hri.
        destruct p' => /=. 2: naive_solver.
        + tstep_i => ??; simplify_eq.
          tstep_i.
          move: ri Hi sr1' e' Hri HR1. apply: pp_to_all_forall_2.
          apply: pp_to_all_mono; [ by apply: HR2L|].
          move => [[??]?] /= Hcont ????.
          apply: pp_to_ex_mono; [ by apply: Hcont|].
          move => [[??]?] /= *. destruct_all?; simplify_eq.
          tstep_s. eexists (Some (Outgoing, _)). split!; [done|].
          destruct e; simplify_eq/=.
          apply: steps_spec_step_end; [done|] => ??.
          apply: Hloop; [done|]. split!; [naive_solver|done..].
        + move: ri Hi sr1' e' Hri HR1. apply: pp_to_all_forall_2.
          apply: pp_to_all_mono; [by apply: HR2N|].
          move => [[??]?] /= Hcont ????.
          have {}Hcont := Hcont _ _ ltac:(done) ltac:(done). destruct_all?.
          destruct e; simplify_eq/=.
          tstep_s. eexists (Some (Outgoing, _)). split!; [done|].
          apply: steps_spec_step_end; [done|] => ??.
          tstep_s.
          apply: pp_to_ex_mono; [done|].
          move => [[??]?] /= *. destruct_all?; simplify_eq. split!.
          apply: Hloop; [done|]. split!; [naive_solver|done..].
    Qed.
End prepost.
