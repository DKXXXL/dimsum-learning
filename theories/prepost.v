Require Export iris.algebra.cmra.
Require Export iris.algebra.updates.
Require Export iris.base_logic.base_logic.
Require Export iris.proofmode.proofmode.
Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.link.
Require Import refframe.seq_product.
Require Import refframe.state_transform.
Require Import refframe.proof_techniques.

Set Default Proof Using "Type".

Section updates.
  Context {A : cmra}.
  Lemma cmra_update_included (x y : A) :
    x ≼ y → y ~~> x.
  Proof. move => [? ->]. apply cmra_update_op_l. Qed.
End updates.

Section total_updates.
  Local Set Default Proof Using "Type*".
  Context {A : cmra}.
  Lemma cmra_update_valid (x y : A) :
    x ~~> y → ✓ x → ✓ y.
  Proof.
    move => Hupd /cmra_valid_validN Hvalid.
    apply /cmra_valid_validN => n.
    by apply (Hupd n None).
  Qed.
End total_updates.

Section included.
  Context {A : cmra}.
  Implicit Types (x y z : A).
  Lemma cmra_included_op_l x y z : x ≼ y → x ≼ y ⋅ z.
  Proof. intros ?. etrans; [done|]. apply cmra_included_l. Qed.
  Lemma cmra_included_op_r x y z : x ≼ y → x ≼ z ⋅ y.
  Proof. intros ?. etrans; [done|]. apply cmra_included_r. Qed.
End included.

Section satisfiable.
  Context {M : ucmra}.

  Definition satisfiable (P: uPred M) := ∃ x : M, ✓{0} x ∧ uPred_holds P 0 x.

  Global Instance satisfiable_proper : Proper ((≡) ==> iff) satisfiable.
  Proof.
    move => ?? Hequiv. unfold satisfiable. f_equiv => ?.
    split => -[??]. all: split; [done|]. all: apply: uPred_holds_ne; [| |done..]; [|done]; by rewrite Hequiv.
  Qed.

  Lemma satisfiable_valid x:
    satisfiable (uPred_ownM x) → ✓{0} x.
  Proof. unfold satisfiable; uPred.unseal. move => [?[??]]. by apply: cmra_validN_includedN. Qed.

  Lemma satisfiable_pure_1 (ϕ : Prop):
    ϕ →
    satisfiable ⌜ϕ⌝.
  Proof. move => ?. unfold satisfiable; uPred.unseal. eexists ε. split; [|done]. apply ucmra_unit_validN. Qed.

  Lemma satisfiable_pure_2 (ϕ : Prop):
    satisfiable ⌜ϕ⌝ →
    ϕ.
  Proof. unfold satisfiable; uPred.unseal. naive_solver. Qed.

  Lemma satisfiable_bupd_2 x:
    satisfiable (|==> x) →
    satisfiable x.
  Proof.
    unfold satisfiable; uPred.unseal.
    move => -[x'[Hv HP]].
    destruct (HP 0 ε) as [y HP']; [done|by rewrite right_id|].
    move: HP'. rewrite right_id; eauto.
  Qed.

  Lemma satisfiable_mono x y:
    satisfiable x →
    (x ⊢ y) →
    satisfiable y.
  Proof. move => [?[??]] Hentails. eexists _. split; [done|]. by apply Hentails. Qed.

  Lemma satisfiable_bmono x y:
    satisfiable x →
    (x ==∗ y) →
    satisfiable y.
  Proof. move => ??. apply satisfiable_bupd_2. by apply: satisfiable_mono. Qed.
End satisfiable.

(** * prepost *)
Section prepost.
Context {R : Type}.
Context {M : ucmra}.

Inductive prepost : Type :=
| pp_end (r : R)
| pp_prop (P : Prop) (pp : prepost)
| pp_quant {T} (pp : T → prepost)
| pp_add (P : uPred M) (pp : prepost)
| pp_remove (P : uPred M) (pp : prepost)
(* | pp_update (pp : prepost) *)
.

Fixpoint pp_to_ex (pp : prepost) (x : uPred M) (Q : R → uPred M → Prop) : Prop :=
  match pp with
  | pp_end r => Q r x
  | pp_prop P pp' => P ∧ pp_to_ex pp' x Q
  | pp_quant pp' => ∃ y, pp_to_ex (pp' y) x Q
  | pp_add P pp' => satisfiable (P ∗ x) ∧ pp_to_ex pp' (P ∗ x) Q
  (* We could also put and ≡ here but that makes it more annoying for
  the users because they probably always want an update. *)
  | pp_remove P pp' => ∃ y, (x ==∗ (P ∗ y)) ∧ pp_to_ex pp' y Q
  (* | pp_update pp' => ∃ y, x ~~> y ∧ pp_to_ex pp' y Q *)
  end.

Fixpoint pp_to_all (pp : prepost) (x : uPred M) (Q : R → uPred M → Prop) : Prop :=
  match pp with
  | pp_end r => Q r x
  | pp_prop P pp' => P → pp_to_all pp' x Q
  | pp_quant pp' => ∀ y, pp_to_all (pp' y) x Q
  | pp_add P pp' => satisfiable (P ∗ x) → pp_to_all pp' (P ∗ x) Q
  | pp_remove P pp' => ∀ y, (x ==∗ P ∗ y) → pp_to_all pp' y Q
  (* | pp_update pp' => ∀ y, x ~~> y → pp_to_all pp' y Q *)
  end.

Lemma pp_to_ex_exists pp Q x:
  pp_to_ex pp x Q ↔ ∃ r y, Q r y ∧ pp_to_ex pp x (λ r' y', r' = r ∧ y' = y).
Proof. elim: pp x => /=; naive_solver. Qed.

Lemma pp_to_all_forall pp Q x:
  pp_to_all pp x Q ↔ (∀ r y, pp_to_ex pp x (λ r' y', r' = r ∧ y' = y) → Q r y).
Proof. elim: pp x => /=; naive_solver. Qed.
Lemma pp_to_all_forall_2 pp Q x:
  pp_to_all pp x Q →
  ∀ r y, pp_to_ex pp x (λ r' y', r' = r ∧ y' = y) → Q r y.
Proof. apply pp_to_all_forall. Qed.

Lemma pp_to_all_mono pp (Q1 Q2 : _ → _ → Prop) x:
  pp_to_all pp x Q1 →
  (∀ r y, Q1 r y → Q2 r y) →
  pp_to_all pp x Q2.
Proof. elim: pp x => /=; naive_solver. Qed.

Lemma pp_to_ex_mono pp (Q1 Q2 : _ → _ → Prop) x:
  pp_to_ex pp x Q1 →
  (∀ r y, Q1 r y → Q2 r y) →
  pp_to_ex pp x Q2.
Proof. elim: pp x => /=; naive_solver. Qed.

Lemma pp_to_all_ex pp Q1 Q2 x:
  pp_to_all pp x Q1 →
  pp_to_ex pp x Q2 →
  ∃ y r, Q1 r y ∧ Q2 r y.
Proof. move => /pp_to_all_forall ? /pp_to_ex_exists. naive_solver. Qed.

Definition pp_res_equiv (Q : R → uPred M → Prop) (r : R) (x : uPred M) : Prop :=
  ∀ x', satisfiable x' → x' ≡ x → Q r x'.

Lemma pp_to_ex_mono_res pp (Q : _ → _ → Prop) x x':
  x' ≡ x →
  satisfiable x' →
  pp_to_ex pp x (pp_res_equiv Q) →
  pp_to_ex pp x' Q.
Proof.
  elim: pp x x' => /=.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - move => P pp IH x x' Hequiv Hvalid [??]. rewrite {1}Hequiv.
    split; [done|]. by apply: IH; [rewrite Hequiv..|done].
  - move => P pp IH x x' Hequiv Hvalid [?[??]]. eexists _.
    rewrite Hequiv. split; [done|]. apply: IH; [..|done]; [done|].
    apply: satisfiable_bmono; [done|]. rewrite Hequiv. etrans; [done|].
    by iIntros ">[_ $]".
Qed.

Lemma pp_to_all_mono_res pp (Q : _ → _ → Prop) x x':
  x' ≡ x →
  satisfiable x' →
  pp_to_all pp x (pp_res_equiv Q) →
  pp_to_all pp x' Q.
Proof.
  elim: pp x x' => /=.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - move => P pp IH x x' Hequiv Hvalid ?. rewrite {1}Hequiv => ?.
    apply: IH; [..|naive_solver]; by rewrite Hequiv.
  - move => P pp IH x x' Hequiv Hvalid Hpp ?. rewrite Hequiv => ?.
    apply: IH; [reflexivity| |naive_solver].
    apply: satisfiable_bmono; [done|]. rewrite Hequiv. etrans; [done|].
    by iIntros ">[_ $]".
Qed.

(*
Definition pp_res_upd (Q : R → A → Prop) (r : R) (x : A) : Prop :=
  ∀ x', ✓ x' → x' ~~> x → Q r x'.

Lemma pp_to_ex_mono_upd pp (Q : _ → _ → Prop) x x':
  x' ~~> x →
  ✓ x' →
  pp_to_ex pp x (pp_res_upd Q) →
  pp_to_ex pp x' Q.
Proof.
  elim: pp x x' => /=.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - move => P pp IH x x' Hupd Hvalid [?[?[??]]]. eexists _.
    split_and!.
    + etrans; [by apply cmra_update_op|]. done.
    + done.
    + apply: IH; [..|done]; done.
  - move => P pp IH x x' Hupd Hvalid [?[??]]. eexists _.
    split.
    + by etrans.
    + apply: IH; [..|done].
      done.
      admit.
Admitted.

Definition pp_res_upd' (Q : R → A → Prop) (r : R) (x : A) : Prop :=
  ∀ x', ✓ x → x ~~> x' → Q r x'.

Lemma pp_to_all_mono_upd pp (Q : _ → _ → Prop) x x':
  x ~~> x' →
  ✓ x →
  pp_to_all pp x (pp_res_upd' Q) →
  pp_to_all pp x' Q.
Proof.
  elim: pp x x' => /=.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - move => P pp IH x x' Hupd Hvalid Hpp ???.
    apply: IH; [| |apply Hpp].
    + reflexivity.
    + done.
    + etrans; [by apply cmra_update_op|]. done.
    + done.
  - move => P pp IH x x' Hupd Hvalid Hpp y Hup2.
    apply: IH; [| |apply Hpp].
    + reflexivity.
    + admit.
    + by etrans.
Admitted.

Lemma pp_to_all_valid pp (Q : _ → _ → Prop) x:
  ✓ x →
  pp_to_all pp x (λ r x', ✓ x' → Q r x') →
  pp_to_all pp x Q.
Proof.
  elim: pp x => /=.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - move => P pp IH x Hvalid Hpp x' Hupd ?.
    by apply: IH; [|apply Hpp].
  - move => P pp IH x Hvalid Hpp x' Hupd.
    apply: IH; [|apply Hpp].
    + admit.
    + done.
Admitted.
*)
End prepost.

Arguments prepost : clear implicits.

(** * mod_prepost *)
Section prepost.
  Context {EV1 EV2 S : Type}.
  Context {M : ucmra}.
  Implicit Types (i : EV2 → S → prepost (EV1 * S) M) (o : EV1 → S → prepost (EV2 * S) M).
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
    (pp_state * S * uPred M) → option (EV1 + EV2) → ((pp_state * S * uPred M) → Prop) → Prop :=
  | PPOutsideS s x e:
    pp_filter_step i o (PPOutside, s, x) (Some (inr e)) (λ σ, σ = (PPRecv1 e, s, x))
  | PPRecv1S s x e:
    pp_filter_step i o (PPRecv1 e, s, x) None (λ σ, pp_to_ex (i e s) x (λ r y, σ = (PPRecv2 r.1, r.2, y)))
  | PPRecv2S s x e:
    pp_filter_step i o (PPRecv2 e, s, x) (Some (inl e)) (λ σ, σ = (PPInside, s, x))
  | PPInsideS s x e:
    pp_filter_step i o (PPInside, s, x) (Some (inl e)) (λ σ, σ = (PPSend1 e, s, x))
  | PPSend1S s x e r y:
    pp_to_ex (o e s) x (λ r' y', r' = r ∧ y' = y) →
    pp_filter_step i o (PPSend1 e, s, x) None (λ σ, σ = (PPSend2 r.1, r.2, y))
  | PPSend2S s x e:
    pp_filter_step i o (PPSend2 e, s, x) (Some (inr e)) (λ σ, σ = (PPOutside, s, x))
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

  Lemma mod_prepost_step_Outside_i i o m σ s x:
    TStepI (mod_prepost i o m) (SMFilter, σ, (PPOutside, s, x)) (λ G,
        ∀ e, G true (Some e) (λ G', G' (SMFilter, σ, (PPRecv1 e, s, x)))).
  Proof.
    constructor => G /= ?. tstep_i.
    apply steps_impl_step_end => ???. invert_all @m_step => ???. split! => ?. split!; [naive_solver|done|].
    naive_solver.
  Qed.

  Lemma mod_prepost_step_Recv1_i i o m σ s e x:
    TStepI (mod_prepost i o m) (SMFilter, σ, (PPRecv1 e, s, x)) (λ G,
        pp_to_ex (i e s) x (λ r y, G true None (λ G', G' (SMProgRecv r.1, σ, (PPInside, r.2, y))))).
  Proof.
    constructor => G /= /pp_to_ex_exists[r [HG Hex]]. tstep_i.
    apply steps_impl_step_next => ???. invert_all @m_step.
    eexists (_, _). split!. { apply pp_to_ex_exists. naive_solver. }
    apply steps_impl_step_end => ???. invert_all @m_step => ???. naive_solver.
  Qed.

  Lemma mod_prepost_step_Inside_i i o m σ s e x:
    TStepI (mod_prepost i o m) (SMFilterRecv e, σ, (PPInside, s, x)) (λ G,
        pp_to_all (o e s) x (λ r y, G true (Some (r.1)) (λ G', G' (SMFilter, σ, (PPOutside, r.2, y))))).
  Proof.
    constructor => G /= ?. apply steps_impl_step_trans. tstep_i.
    apply steps_impl_step_end => ???. invert_all @m_step => ? b *; simplify_eq. split! => ?. split!; [done|].
    tstep_i.
    apply steps_impl_step_next => ???. invert_all @m_step => *; simplify_eq. split!.
    apply steps_impl_step_end => ???. invert_all @m_step => *; simplify_eq. split! => ?.
    have [?[?[?[??]]]]:= pp_to_all_ex _ _ _ _ ltac:(done) ltac:(done); subst.
    split!; [done|by destruct b|]. naive_solver.
  Qed.

  Lemma mod_prepost_step_Outside_s i o m σ s x:
    TStepS (mod_prepost i o m) (SMFilter, σ, (PPOutside, s, x)) (λ G,
        ∃ e, G (Some e) (λ G', G' (SMFilter, σ, (PPRecv1 e, s, x)))).
  Proof.
    constructor => G /= [??]. split!; [done|] => /= ??. tstep_s. eexists (Some (inr _)). split!.
    apply: steps_spec_step_end; [by econs|]. naive_solver.
  Qed.


  Lemma mod_prepost_step_Recv1_s i o m σ s e x:
    TStepS (mod_prepost i o m) (SMFilter, σ, (PPRecv1 e, s, x)) (λ G,
        G None (λ G', pp_to_all (i e s) x (λ r y, G' (SMProgRecv r.1, σ, (PPInside, r.2, y))))).
  Proof.
    constructor => G /= ?. split!; [done|] => /= ??. apply steps_spec_step_trans.
    tstep_s. eexists None. split!.
    apply: steps_spec_step_end; [by econs|] => ? /=?.
    have [?[?[??]]]:= pp_to_all_ex _ _ _ _ ltac:(done) ltac:(done); subst.
    tstep_s. eexists (Some (inl _)). split!.
    apply: steps_spec_step_end; [by econs|]. naive_solver.
  Qed.

  Lemma mod_prepost_step_Inside_s i o m σ s e x:
    TStepS (mod_prepost i o m) (SMFilterRecv e, σ, (PPInside, s, x)) (λ G,
        pp_to_ex (o e s) x (λ r y, G (Some (r.1)) (λ G', G' (SMFilter, σ, (PPOutside, r.2, y))))).
  Proof.
    constructor => G /= /pp_to_ex_exists[?[?[??]]]. split!; [done|] => /= ??.
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

Definition prepost_id {EV} : EV → unit → prepost (EV * unit) unitUR :=
  λ x _, pp_end (x, tt).

Lemma prepost_id_l M S EV1 EV2 (m : module EV1) σ i o s x:
  trefines (MS (mod_prepost i o (mod_prepost prepost_id prepost_id m))
               (SMFilter, (SMFilter, σ, (PPOutside, tt, True%I)), (PPOutside, s, x)))
           (MS (mod_prepost (M:=M) (S:=S) (EV2:=EV2) i o m) (SMFilter, σ, (PPOutside, s, x))).
Proof.
  apply tsim_implies_trefines => /= n.
  tstep_i => ?.
  tstep_s. split!.
  tstep_s. apply pp_to_all_forall => ???.
  tstep_i. apply: pp_to_ex_mono; [done|].
  move => ?? [<- <-].
  tstep_i => ? <-.
  tstep_i.
  unshelve apply: tsim_remember. { simpl. exact (λ _
      '(σf1, (σf1', σ1, (σpp1', _, _)), (σpp1, s1, x1)) '(σf2, σ2, (σpp2, s2, x2)),
         σf1 = SMProg ∧ σf1' = σf2 ∧ σ1 = σ2 ∧ σpp1 = PPInside ∧ x1 = x2
         ∧ σpp1' = PPInside ∧ σpp2 = PPInside ∧ s1 = s2 ∧
         ((∃ e, σf1' = SMProgRecv e) ∨ σf1' = SMProg)). }
  { split!. } { done. }
  move => {}n _ Hloop [[σf1 [[σf1' σ1] [[σpp1' []] ?]] [[σpp1 s1] x1]]] [[σf2 σ2] [[σpp2 s2] x2]] ?.
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
    tstep_i. tstep_i. apply pp_to_all_forall => ???.
    tstep_s. apply: pp_to_ex_mono; [done|]. move => ?? [<- <-]. split!.
    tstep_i => ?.
    tstep_s. split!.
    tstep_s. apply pp_to_all_forall => ???.
    tstep_i. apply: pp_to_ex_mono; [done|]. move => ?? [<- <-].
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
        {M : ucmra}
        (INV : seq_product_state → S1 → S2 → S' → uPred M → uPred M → Sr1 → Sr2 → Prop)
        (i1 : io_event EV2 → S1 → prepost (io_event EV1 * S1) M)
        (o1 : io_event EV1 → S1 → prepost (io_event EV2 * S1) M)
        (i2 : io_event EV2 → S2 → prepost (io_event EV1 * S2) M)
        (o2 : io_event EV1 → S2 → prepost (io_event EV2 * S2) M)
        (i : io_event EV2 → S' → prepost (io_event EV1 * S') M)
        (o : io_event EV1 → S' → prepost (io_event EV2 * S') M)
        (R1 : seq_product_state → Sr1 → EV2 → seq_product_state → Sr1 → EV2 → Prop)
        (R2 : seq_product_state → Sr2 → EV1 → seq_product_state → Sr2 → EV1 → Prop)
        (m1 m2 : module (io_event EV1))
        σ1 σ2 s1 s2 x1 x2 x sr1 sr2 s
        `{!VisNoAll m1} `{!VisNoAll m2}
        :

       (∀ p s e p' s' e', R1 p s e p' s' e' → p ≠ p') →
       (x ⊣⊢ x1 ∗ x2) →
       satisfiable x →
       INV SPNone s1 s2 s x1 x2 sr1 sr2 →
       (∀ s1 s2 s x1 x2 sr1 sr2 e sr1' e',
          INV SPNone s1 s2 s x1 x2 sr1 sr2 →
          satisfiable (x1 ∗ x2) →
          R1 SPNone sr1 e SPLeft sr1' e' →
          pp_to_all (i (Incoming, e') s) (x1 ∗ x2) (λ r1 y1,
          pp_to_ex (i1 (Incoming, e') s1) x1 (λ r2 y2, ∃ e sr2',
            r1.1.1 = Incoming ∧
            r2.1.1 = Incoming ∧
            r1.1.2 = r2.1.2 ∧
            (y1 ==∗ y2 ∗ x2) ∧
            R2 SPNone sr2 e SPLeft sr2' r1.1.2 ∧
            INV SPLeft r2.2 s2 r1.2 y2 x2 sr1' sr2'))) →
       (∀ s1 s2 s x1 x2 sr1 sr2 e sr1' e',
          INV SPNone s1 s2 s x1 x2 sr1 sr2 →
          satisfiable (x1 ∗ x2) →
          R1 SPNone sr1 e SPRight sr1' e' →
          pp_to_all (i (Incoming, e') s) (x1 ∗ x2) (λ r1 y1,
          pp_to_ex (i2 (Incoming, e') s2) x2 (λ r2 y2, ∃ e sr2',
            r1.1.1 = Incoming ∧
            r2.1.1 = Incoming ∧
            r1.1.2 = r2.1.2 ∧
            (y1 ==∗ x1 ∗ y2) ∧
            R2 SPNone sr2 e SPRight sr2' r1.1.2 ∧
            INV SPRight s1 r2.2 r1.2 x1 y2 sr1' sr2'))) →
       (∀ s1 s2 s x1 x2 sr1 sr2 e,
           INV SPLeft s1 s2 s x1 x2 sr1 sr2 →
           satisfiable (x1 ∗ x2) →
           pp_to_all (o1 e s1) x1 (λ r1 y1, ∀ sr1' e',
             r1.1.1 = Outgoing →
             R1 SPLeft sr1 r1.1.2 SPRight sr1' e' →
             pp_to_ex (i2 (Incoming, e') s2) x2 (λ r2 y2, ∃ sr2',
               e.1 = Outgoing ∧
               r2.1.1 = Incoming ∧
               (x1 ∗ x2 ==∗ y1 ∗ y2) ∧
               INV SPRight r1.2 r2.2 s y1 y2 sr1' sr2' ∧
               R2 SPLeft sr2 e.2 SPRight sr2' r2.1.2))) →
       (∀ s1 s2 s x1 x2 sr1 sr2 e,
           INV SPLeft s1 s2 s x1 x2 sr1 sr2 →
           satisfiable (x1 ∗ x2) →
           ∀ x, (x ==∗ (x1 ∗ x2)) →
           pp_to_all (o1 e s1) x1 (λ r1 y1, ∀ sr1' e',
             r1.1.1 = Outgoing →
             R1 SPLeft sr1 r1.1.2 SPNone sr1' e' →
             ∃ e'' sr2',
               e.1 = Outgoing ∧
               R2 SPLeft sr2 e.2 SPNone sr2' e'' ∧
               pp_to_ex (o (Outgoing, e'') s) x (λ r2 y2,
                 r2.1.1 = Outgoing ∧
                 r2.1.2 = e' ∧
                 (* This = instead of ≡ is fine because the pp_to_ex
                 must have a update in it. *)
                 y2 = (y1 ∗ x2)%I ∧
                 INV SPNone r1.2 s2 r2.2 y1 x2 sr1' sr2'))) →
       (∀ s1 s2 s x1 x2 sr1 sr2 e,
           INV SPRight s1 s2 s x1 x2 sr1 sr2 →
           satisfiable (x1 ∗ x2) →
           pp_to_all (o2 e s2) x2 (λ r1 y1, ∀ sr1' e',
             r1.1.1 = Outgoing →
             R1 SPRight sr1 r1.1.2 SPLeft sr1' e' →
             pp_to_ex (i1 (Incoming, e') s1) x1 (λ r2 y2, ∃ sr2',
               e.1 = Outgoing ∧
               r2.1.1 = Incoming ∧
               (x1 ∗ x2 ==∗ y2 ∗ y1) ∧
               INV SPLeft r2.2 r1.2 s y2 y1 sr1' sr2' ∧
               R2 SPRight sr2 e.2 SPLeft sr2' r2.1.2))) →
       (∀ s1 s2 s x1 x2 sr1 sr2 e,
           INV SPRight s1 s2 s x1 x2 sr1 sr2 →
           satisfiable (x1 ∗ x2) →
           ∀ x, (x ==∗ (x1 ∗ x2)) →
           pp_to_all (o2 e s2) x2 (λ r1 y1, ∀ sr1' e',
             r1.1.1 = Outgoing →
             R1 SPRight sr1 r1.1.2 SPNone sr1' e' →
             ∃ e'' sr2',
               e.1 = Outgoing ∧
               R2 SPRight sr2 e.2 SPNone sr2' e'' ∧
               pp_to_ex (o (Outgoing, e'') s) x (λ r2 y2,
                 r2.1.1 = Outgoing ∧
                 r2.1.2 = e' ∧
                 (* This = instead of ≡ is fine because the pp_to_ex
                 must have a update in it. *)
                 y2 = (x1 ∗ y1)%I ∧
                 INV SPNone s1 r1.2 r2.2 x1 y1 sr1' sr2'))) →
    trefines (MS (mod_link R1 (mod_prepost i1 o1 m1) (mod_prepost i2 o2 m2))
                 (MLFNone, sr1, (SMFilter, σ1, (PPOutside, s1, x1)), (SMFilter, σ2, (PPOutside, s2, x2))))
             (MS (mod_prepost i o (mod_link R2 m1 m2))
                 (SMFilter, (MLFNone, sr2, σ1, σ2), (PPOutside, s, x))).
    Proof.
      move => Hneq Hequiv Hvalid Hinv HN2L HN2R HL2R HL2N HR2L HR2N.
      apply tsim_implies_trefines => /= n.
      unshelve apply: tsim_remember. { simpl. exact (λ _
          '(σl1, sr1, (σf1, σ1, (σpp1, s1, x1)), (σf2, σ2, (σpp2, s2, x2)))
          '(σf, (σl2, sr2, σ1', σ2'), (σpp, s, x)),
           ∃ sp,
           σ1 = σ1' ∧ σ2 = σ2' ∧ INV sp s1 s2 s x1 x2 sr1 sr2 ∧ satisfiable x ∧
          (* Here we have an ≡ instead of a ==∗ since we know that the
          resources in the spec must be up to date because the last
          interaction was with the environment *)
          (( sp = SPNone ∧ (x ⊣⊢ x1 ∗ x2) ∧
              σl1 = MLFNone ∧ σf = SMFilter
            ∧ σpp1 = PPOutside ∧ σpp2 = PPOutside ∧ σpp = PPOutside
            ∧ σf1 = SMFilter ∧ σf2 = SMFilter
            ∧ σl2 = MLFNone)
           ∨ (sp = SPLeft ∧ (x ==∗ x1 ∗ x2) ∧
              ((∃ e, σl2 = MLFRecvL e ∧ σf1 = SMProgRecv (Incoming, e))
               ∨ (σl2 = MLFLeft ∧ σf1 = SMProg))
            ∧ σpp1 = PPInside ∧ σpp2 = PPOutside ∧ σpp = PPInside
            ∧ σf = SMProg ∧ σf2 = SMFilter
            ∧ σl1 = MLFLeft)
           ∨ (sp = SPRight ∧ (x ==∗ x1 ∗ x2) ∧
              ((∃ e, σl2 = MLFRecvR e ∧ σf2 = SMProgRecv (Incoming, e))
               ∨ (σl2 = MLFRight ∧ σf2 = SMProg))
            ∧ σpp1 = PPOutside ∧ σpp2 = PPInside ∧ σpp = PPInside
            ∧ σf = SMProg ∧ σf1 = SMFilter
            ∧ σl1 = MLFRight) )). }
      { split!. } { done. }
      move => {}n _ /= Hloop {Hinv Hequiv Hvalid}.
      move => [[[σl1 {}sr1] [[σf1 {}σ1] [[σpp1 {}s1] {}x1]]] [[σf2 {}σ2] [[σpp2 {}s2] {}x2]]].
      move => [[σf [[[σl2 {}sr2] σ1'] σ2']] [[σpp {}s] {}x]] ?. destruct_all?; simplify_eq.
      - revert select (satisfiable x) => Hvalid. revert select (x ⊣⊢ _) => Hequiv.
        move: (Hvalid) => Hvalid2. rewrite Hequiv in Hvalid2.
        tstep_i => ? p' ???.
        tstep_s. split!.
        tstep_s. apply pp_to_all_forall => ri xi Hi.
        destruct p' => /=. 3: naive_solver.
        + tstep_i => ??. simplify_eq.
          tstep_i. move: ri xi Hi. apply pp_to_all_forall.
          apply: pp_to_all_mono_res; [done..|].
          apply: pp_to_all_mono; [by apply: HN2L|].
          move => [[??]?] ? /= Hcont ? ? Hequiv2. apply: pp_to_ex_mono; [done|].
          move => [[??]?] ? /= *. destruct_all?; simplify_eq.
          tstep_s.
          split!; [done..|] => /=.
          apply: Hloop; [done|]. split!. by rewrite Hequiv2.
        + tstep_i => ??. simplify_eq.
          tstep_i. move: ri xi Hi. apply pp_to_all_forall.
          apply: pp_to_all_mono_res; [done..|].
          apply: pp_to_all_mono; [by apply: HN2R|].
          move => [[??]?] ? /= Hcont ? ? Hequiv2. apply: pp_to_ex_mono; [done|].
          move => [[??]?] ? /= *. destruct_all?; simplify_eq.
          tstep_s.
          split!; [done..|] => /=.
          apply: Hloop; [done|]. split!. by rewrite Hequiv2.
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
        tstep_i. apply pp_to_all_forall => ri xi Hi p' sr1' e' HR1 Hri.
        have ?:= satisfiable_bmono _ _ ltac:(done) ltac:(done).
        destruct p' => /=. 1: naive_solver.
        + tstep_i => ??; simplify_eq.
          tstep_i.
          move: ri xi Hi sr1' e' Hri HR1. apply: pp_to_all_forall_2.
          apply: pp_to_all_mono; [by apply: HL2R|].
          move => [[??]?] ? /= Hcont ????.
          apply: pp_to_ex_mono; [ by apply: Hcont|].
          move => [[??]?] ? /=?. destruct_all?; simplify_eq.
          tstep_s. eexists (Some (Outgoing, _)). split!; [done|].
          destruct e; simplify_eq/=.
          apply: steps_spec_step_end; [done|] => ??.
          apply: Hloop; [done|]. split!; [naive_solver|done..| ].
          etrans; [done|]. etrans; [|apply bupd_trans]. by apply bupd_mono.
        + move: ri xi Hi sr1' e' Hri HR1. apply: pp_to_all_forall_2.
          apply: pp_to_all_mono; [by apply: HL2N|].
          move => [[??]?] ? /= Hcont ????.
          have {}Hcont := Hcont _ _ ltac:(done) ltac:(done). destruct_all?.
          destruct e; simplify_eq/=.
          tstep_s. eexists (Some (Outgoing, _)). split!; [done|].
          apply: steps_spec_step_end; [done|] => ??.
          tstep_s.
          apply: pp_to_ex_mono_res; [done..|].
          apply: pp_to_ex_mono; [done|].
          move => [[??]?] ? /= ????. destruct_all?; simplify_eq. split!.
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
        tstep_i. apply pp_to_all_forall => ri xi Hi p' sr1' e' HR1 Hri.
        have ?:= satisfiable_bmono _ _ ltac:(done) ltac:(done).
        destruct p' => /=. 2: naive_solver.
        + tstep_i => ??; simplify_eq.
          tstep_i.
          move: ri xi Hi sr1' e' Hri HR1. apply: pp_to_all_forall_2.
          apply: pp_to_all_mono; [by apply: HR2L|].
          move => [[??]?] ? /= Hcont ????.
          apply: pp_to_ex_mono; [ by apply: Hcont|].
          move => [[??]?] ? /=?. destruct_all?; simplify_eq.
          tstep_s. eexists (Some (Outgoing, _)). split!; [done|].
          destruct e; simplify_eq/=.
          apply: steps_spec_step_end; [done|] => ??.
          apply: Hloop; [done|]. split!; [naive_solver|done..| ].
          etrans; [done|]. etrans; [|apply bupd_trans]. by apply bupd_mono.
        + move: ri xi Hi sr1' e' Hri HR1. apply: pp_to_all_forall_2.
          apply: pp_to_all_mono; [by apply: HR2N|].
          move => [[??]?] ? /= Hcont ????.
          have {}Hcont := Hcont _ _ ltac:(done) ltac:(done). destruct_all?.
          destruct e; simplify_eq/=.
          tstep_s. eexists (Some (Outgoing, _)). split!; [done|].
          apply: steps_spec_step_end; [done|] => ??.
          tstep_s.
          apply: pp_to_ex_mono_res; [done..|].
          apply: pp_to_ex_mono; [done|].
          move => [[??]?] ? /= ????. destruct_all?; simplify_eq. split!.
          apply: Hloop; [done|]. split!; [naive_solver|done..].
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
        σ s1 s2 s x1 x2 x
        `{!VisNoAll m}
        :
        INV Env s1 s2 s x1 x2 x →
       (∀ s1 s2 s x1 x2 x e,
           INV Env s1 s2 s x1 x2 x →
           pp_to_all (i e s) x (λ r y,
             pp_to_ex (i1 e s1) x1 (λ r1 y1,
               pp_to_ex (i2 r1.1 s2) x2 (λ r2 y2,
                 r.1 = r2.1 ∧
                 INV Prog r1.2 r2.2 r.2 y1 y2 y)))) →
       (∀ s1 s2 s x1 x2 x e,
           INV Prog s1 s2 s x1 x2 x →
           pp_to_all (o2 e s2) x2 (λ r2 y2,
             pp_to_all (o1 r2.1 s1) x1 (λ r1 y1,
               pp_to_ex (o e s) x (λ r y,
                 r.1 = r1.1 ∧
                 INV Env r1.2 r2.2 r.2 y1 y2 y)))) →
    trefines (MS ((mod_prepost i1 o1 (mod_prepost i2 o2 m)) )
                 (SMFilter, (SMFilter, σ, (PPOutside, s2, x2)), (PPOutside, s1, x1)))
             (MS (mod_prepost i o m)
                 (SMFilter, σ, (PPOutside, s, x))).
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
      move => [[σf {}σ] [[σpp {}s] {}x]] ?. destruct_all?; simplify_eq.
      - tstep_i => ?.
        tstep_s. split!.
        tstep_s. apply: pp_to_all_mono; [by apply: Henv|]. move => r y /= ?.
        tstep_i. apply: pp_to_ex_mono; [done|]. move => r1 y1 /= ?.
        tstep_i => ??. subst.
        tstep_i. apply: pp_to_ex_mono; [done|]. move => r2 y2 /= [??].
        apply: Hloop; [done|]. split!. by f_equal.
      - tstep_both.
        apply steps_impl_step_end => κ Pσ2 ? *. destruct κ as [e'|]. 2: {
          tstep_s. eexists None.
          apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
          apply: Hloop; [done|]. by split!.
        }
        tend. have [σ' Hσ'] := vis_no_all _ _ _ ltac:(done). eexists σ'. split; [naive_solver|].
        tstep_i. apply: pp_to_all_mono; [by apply: Hprog|]. move => r2 y2 /= ?.
        tstep_i. apply: pp_to_all_mono; [done|]. move => r1 y1 /= ?.
        tstep_s. eexists _. apply: steps_spec_step_end; [done|] => ?? /=.
        tstep_s. apply: pp_to_ex_mono; [done|]. move => r y /= [??]. split!.
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
