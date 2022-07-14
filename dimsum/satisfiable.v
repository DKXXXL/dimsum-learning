Require Export iris.algebra.cmra.
Require Export iris.algebra.updates.
Require Export iris.base_logic.base_logic.
Require Export iris.proofmode.proofmode.
Require Import iris.proofmode.environments.
Require Import iris.proofmode.reduction.

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

  Lemma satisfiable_mono x y:
    satisfiable x →
    (x ⊢ y) →
    satisfiable y.
  Proof. move => [?[??]] Hentails. eexists _. split; [done|]. by apply Hentails. Qed.

  Lemma satisfiable_emp_valid y:
    (⊢ y) →
    satisfiable y.
  Proof.
    move => Hentails.
    apply: satisfiable_mono; [|done].
    unfold satisfiable; uPred.unseal.
    eexists ε. split; [|done].
    apply ucmra_unit_validN.
  Qed.

  Lemma satisfiable_pure_1 (ϕ : Prop):
    ϕ →
    satisfiable ⌜ϕ⌝.
  Proof. move => ?. apply satisfiable_emp_valid. by iPureIntro. Qed.

  Lemma satisfiable_pure_2 (ϕ : Prop):
    satisfiable ⌜ϕ⌝ →
    ϕ.
  Proof. unfold satisfiable; uPred.unseal. naive_solver. Qed.

  Lemma satisfiable_exist_1 {A} P:
    (∃ x : A, satisfiable (P x)) →
    satisfiable (∃ x, P x).
  Proof. move => [??]. apply: satisfiable_mono; [done|]. iIntros "?". by iExists _. Qed.

  Lemma satisfiable_exist_2 {A} P:
    satisfiable (∃ x, P x) →
    ∃ x : A, satisfiable (P x).
  Proof. unfold satisfiable; uPred.unseal. move => [? [? [??]]]. naive_solver. Qed.

  Lemma satisfiable_sep_2 P1 P2:
    satisfiable (P1 ∗ P2) →
    satisfiable P1 ∧ satisfiable P2.
  Proof. move => ?. split; (apply: satisfiable_mono; [done|]); by iIntros "[??]". Qed.

  Lemma satisfiable_and_2 P1 P2:
    satisfiable (P1 ∧ P2) →
    satisfiable P1 ∧ satisfiable P2.
  Proof. move => ?. split; (apply: satisfiable_mono; [done|]); eauto using bi.and_elim_l, bi.and_elim_r. Qed.

  Lemma satisfiable_bupd_2 x:
    satisfiable (|==> x) →
    satisfiable x.
  Proof.
    unfold satisfiable; uPred.unseal.
    move => -[x'[Hv HP]].
    destruct (HP 0 ε) as [y HP']; [done|by rewrite right_id|].
    move: HP'. rewrite right_id; eauto.
  Qed.

  Lemma satisfiable_bmono x y:
    satisfiable x →
    (x ==∗ y) →
    satisfiable y.
  Proof. move => ??. apply satisfiable_bupd_2. by apply: satisfiable_mono. Qed.

  Lemma satisfiable_init x y:
    ✓ x →
    (uPred_ownM x ==∗ y) →
    satisfiable y.
  Proof.
    move => /cmra_valid_validN Hvalid Hentails.
    apply: satisfiable_bmono; [|done].
    unfold satisfiable; uPred.unseal.
    eexists x. split; [done|]. rewrite /uPred_holds/=. done.
  Qed.

  (* The following two lemmas don't seem provable. But they would be
  very useful to be able to use frame preserving updates in the
  prepost because this would allow concurrency. (i.e. in the
  postcondition require proving an frame preserving update from the
  initial predicate.) But for this, one always needs to maintain a P1
  ==∗ P_cur during the proof and that seems annoying without the
  lemmas below. An idea would be to add angelic steps that allow
  updating the P1 at arbitrary points with a bupd but that seems a bit
  annoying to add.

  See 083546b88cf853dad1f06a8d819059f5c20fc708 for the framepreserving
 update approach *)
  (*
  Lemma sat_wand_ex A P1 P2 :
    satisfiable P1 →
    (P1 -∗ ∃ x : A, P2 x) →
    ∃ x, (P1 -∗ P2 x).
  Proof.
    move => /satisfiable_mono Hsat Hw. move: (Hsat _ Hw) => /satisfiable_exist_2[??].

  Lemma sat_exist P1 P2 (φ : Prop) :
    (P1 ==∗ P2) →
    satisfiable P1 →
    (P2 ==∗ ∃ P3, P3 ∗ ⌜(P1 ==∗ P3) → φ⌝) →
    φ.
  Proof.
    move => Hw1 Hsat Hw2.
    have Hw3 : (P1 ==∗ ∃ P3, P3 ∗ ⌜(P1 ==∗ P3) → φ⌝).
    { etrans; [done|]. iIntros ">?". by iApply Hw2. }
    *)


End satisfiable.


Section tactics.
  Context {M : ucmra}.
  Implicit Types (P : uPred M).

  Definition iSat_end (Φ : Prop) : uPred M :=
    ∃ P', P' ∗ ⌜satisfiable P' → Φ⌝.

  Lemma sat_start_bupd_intro_tac P (Φ : Prop) :
    satisfiable P →
    (P ==∗ iSat_end Φ) →
    Φ.
  Proof.
    move => /satisfiable_mono/[apply].
    move => /satisfiable_bupd_2/satisfiable_exist_2[?]/satisfiable_sep_2[?/satisfiable_pure_2].
    by apply.
  Qed.

  Lemma sat_start_intro_tac P (Φ : Prop) :
    satisfiable P →
    (P -∗ iSat_end Φ) →
    Φ.
  Proof.
    move => /satisfiable_mono/[apply].
    move => /satisfiable_exist_2[?]/satisfiable_sep_2[?/satisfiable_pure_2].
    by apply.
  Qed.
End tactics.

Definition sat_of_envs {PROP : bi} (Δ : envs PROP) : PROP := of_envs Δ.
Global Arguments sat_of_envs : simpl never.

Section tactics.
Context {PROP : bi}.
Implicit Types Γ : env PROP.
Implicit Types Δ : envs PROP.
Implicit Types P Q : PROP.
Lemma tac_sat_accu Δ P :
  sat_of_envs Δ = P →
  envs_entails Δ P.
Proof. rewrite envs_entails_eq=><-. done. Qed.

Lemma tac_sat_start_proof Δ P :
  envs_entails Δ P →
  sat_of_envs Δ -∗ P.
Proof. rewrite envs_entails_eq=><-. done. Qed.

End tactics.

Notation "Γ '--------------------------------------' □ Δ '--------------------------------------' ∗ " :=
  (sat_of_envs (Envs Γ Δ _))
  (at level 1, left associativity,
  format "'[' Γ '--------------------------------------' □ '//' Δ '--------------------------------------' ∗ ']'", only printing) :
  stdpp_scope.
Notation "Δ '--------------------------------------' ∗ " :=
  (sat_of_envs (Envs Enil Δ _))
  (at level 1, left associativity,
  format "'[' Δ '--------------------------------------' ∗ ']'", only printing) : stdpp_scope.
Notation "Γ '--------------------------------------' □ " :=
  (sat_of_envs (Envs Γ Enil _))
  (at level 1, left associativity,
  format "'[' Γ '--------------------------------------' □ ']'", only printing)  : stdpp_scope.
Notation "'--------------------------------------' ∗" := (sat_of_envs (Envs Enil Enil _))
  (at level 1, format "'[' '--------------------------------------' ∗ ']'", only printing) : stdpp_scope.


(** internal tactics *)
Ltac iSatStartProof :=
  lazymatch goal with
  | |- sat_of_envs _ -∗ _ => apply tac_sat_start_proof
  | _ => idtac
  end.
Tactic Notation "iSatAccu" :=
  iStartProof; eapply tac_sat_accu; [pm_reflexivity || fail "iSatAccu: not an evar"].

(** tactics for the user *)
Tactic Notation "iSatStart" ident(H) :=
  apply (sat_start_intro_tac _ _ H); clear H; iSatStartProof.
Tactic Notation "iSatStart" :=
  lazymatch goal with
  | H1 : satisfiable _, H2 : satisfiable _ |- _ => fail "Multiple satisfiable! Pick one via iSatStart H."
  | H : satisfiable _ |- _ => iSatStart H
  end.

Tactic Notation "iSatStartBupd" ident(H) :=
  apply (sat_start_bupd_intro_tac _ _ H); clear H; iSatStartProof.
Tactic Notation "iSatStartBupd" :=
  lazymatch goal with
  | H1 : satisfiable _, H2 : satisfiable _ |- _ => fail "Multiple satisfiable! Pick one via iSatStartBupd H."
  | H : satisfiable _ |- _ => iSatStartBupd H
  end.

Tactic Notation "iSatStop" ident(H) :=
  lazymatch goal with
  | |- environments.envs_entails _ (iSat_end _) =>
      iExists _; iSplitL; [iSatAccu|iPureIntro => H]
  | |- _ => fail "unknown goal!"
  end.
Tactic Notation "iSatStop" :=
  let H := fresh in
  iSatStop H;
  move: H => ?.

Ltac iSatClear :=
  repeat match goal with | H : satisfiable _ |- _ => clear H end.

Tactic Notation "iSatMono" ident(H) :=
  apply (satisfiable_mono _ _ H); iSatStartProof.
Tactic Notation "iSatMono" :=
  lazymatch goal with
  | H1 : @satisfiable ?M _, H2 : @satisfiable ?M _ |- @satisfiable ?M _ => fail "Multiple satisfiable! Pick one via iSatMono H"
  | H : @satisfiable ?M _ |- @satisfiable ?M _ => iSatMono H
  end.

Tactic Notation "iSatMonoBupd" ident(H) :=
  apply (satisfiable_bmono _ _ H); iSatStartProof.
Tactic Notation "iSatMonoBupd" :=
  lazymatch goal with
  | H1 : @satisfiable ?M _, H2 : @satisfiable ?M _ |- @satisfiable ?M _ => fail "Multiple satisfiable! Pick one via iSatMonoBupd H"
  | H : @satisfiable ?M _ |- @satisfiable ?M _ => iSatMonoBupd H
  end.
