From dimsum.core Require Export module.
From dimsum.core Require Import srefines filter refinement_examples.

(** * Relationship between [filter] and [srefines]  *)

(** * Example why filter does not preserve srefines unconditionally  *)
Module filter_example.
  (* This example shows that filter does not preserve refinement if
  the filter function is not functional, i.e. if it can introduce
  non-determinism. The intuitive reason for the failure of refinement
  preservation is that angelic choice can be commuted before filtering
  but not after. *)
  Definition test_filter (n1 : nat) (n2 : option nat) :=
    (n1 = 1 ∧ (n2 = Some 4 ∨ n2 = Some 5)) ∨
    (n1 = 2 ∧ (n2 = Some 2)) ∨
    (n1 = 3 ∧ (n2 = Some 3)).
  Arguments test_filter _ _ /.

Lemma mod_ang_comm1_filter_traces Pκs:
  0 ~{filter_trans mod_ang_comm1_trans test_filter, Pκs}~>ₛ (λ _, True) ↔
    Pκs [] ∧
  (Pκs [Nb] ∨
   ∃ n, (n = 4 ∨ n = 5) ∧
   (Pκs [Vis n] ∧
    (Pκs [Vis n; Nb] ∨
     (Pκs [Vis n; Vis 2] ∧ Pκs [Vis n; Vis 2; Nb] ∧
      Pκs [Vis n; Vis 3] ∧ Pκs [Vis n; Vis 3; Nb])))).
Proof.
  split.
  - inversion 1; simplify_eq. 1: naive_solver.
    inv_all @m_step => //. specialize_hyps.
    split; [naive_solver|]. right.
    have [κ' ?]: ∃ κ', κ = Some κ' by naive_solver. subst.
    eexists κ'.
    inversion H1; simplify_eq. 1: naive_solver.
    inv_all @m_step => //.

    have {}H := (H3 3 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    inv_all @m_step => //. specialize_hyps.
    inversion H6; simplify_eq. 2: inv_all @m_step => //.

    have {}H := (H3 5 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    inv_all @m_step => //. specialize_hyps.
    inversion H11; simplify_eq. 1: naive_solver.
    inv_all @m_step => //.
  - move => [?[?|[n [? [? HP]]]]]. 1: by apply: STraceEnd.
    apply: STraceStep. { apply: (FilterStep _ _ _ _ (Some n)). econstructor. naive_solver. }
    2: naive_solver.
    move => /= ??; simplify_eq.
    move: HP => [?|?]. 1: by apply: STraceEnd.
    apply: STraceStep; [by econstructor; constructor| |done].
    move => /= ? [?|?]; simplify_eq.
    + apply: STraceStep.
      { econstructor; [constructor|]. naive_solver. }
      2: naive_solver.
      move => /= ? ->. apply: STraceEnd; [done | naive_solver].
    + apply: STraceStep.
      { econstructor; [constructor|]. naive_solver. }
      2: naive_solver.
      move => /= ? ->. apply: STraceEnd; [done | naive_solver].
Qed.

Lemma mod_ang_comm2_filter_traces Pκs:
  0 ~{filter_trans mod_ang_comm2_trans test_filter, Pκs}~>ₛ (λ _, True) ↔
    Pκs [] ∧
  (Pκs [Nb] ∨
   ∃ n1 n2, (n1 = 4 ∨ n1 = 5) ∧ (n2 = 4 ∨ n2 = 5) ∧
   (Pκs [Vis n1] ∧ Pκs [Vis n2] ∧
    ∃ b1 b2 : bool,
      (if b1 then Pκs [Vis n1; Nb] else Pκs [Vis n1; Vis 2] ∧ Pκs [Vis n1; Vis 2; Nb])
      ∧
      (if b2 then Pκs [Vis n2; Nb] else Pκs [Vis n2; Vis 3] ∧ Pκs [Vis n2; Vis 3; Nb]))).
Proof.
  split.
  - inversion 1; simplify_eq. 1: naive_solver.
    inv_all @m_step => //.
    split; [naive_solver|].

    have {}H := (H1 2 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    inv_all @m_step => //.

    have {}H := (H1 5 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    inv_all @m_step => //. right. specialize_hyps.

    have [κ' ?]: ∃ κ', κ = Some κ' by naive_solver. subst.
    have [κ'' ?]: ∃ κ', κ0 = Some κ' by naive_solver. subst.
    eexists κ', κ''. split; [naive_solver|].
    split; [naive_solver|]. split; [naive_solver|]. split; [naive_solver|].

    inversion H3; simplify_eq. 1: {
      eexists true.
      inversion H5; simplify_eq. 1: eexists true; naive_solver.
      inv_all @m_step => //. specialize_hyps.

      inversion H11; simplify_eq. 2: inv_all @m_step => //.
      eexists false; naive_solver.
    }
    eexists false.
    inv_all @m_step => //. specialize_hyps.

    inversion H8; simplify_eq. 2: inv_all @m_step => //.

    inversion H5; simplify_eq. 1: eexists true; naive_solver.
    inv_all @m_step => //. specialize_hyps.

    inversion H14; simplify_eq. 2: inv_all @m_step => //.
    eexists false; naive_solver.
  - move => [?[?|[n1 [n2 [? [? [? [? [b1 [b2 [??]]]]]]]]]]]. 1: by apply: STraceEnd.
    apply: STraceStep. { econstructor; [constructor|]. naive_solver. } 2: naive_solver.
    move => /= ? [?|?]; simplify_eq.
    + apply: STraceStep. { apply: (FilterStep _ _ _ _ (Some n1)). econstructor. naive_solver. } 2: naive_solver.
      move => /=??. simplify_eq.
      destruct b1. 1: by apply: STraceEnd.
      apply: STraceStep. { econstructor; [constructor|]. naive_solver. } 2: naive_solver.
      move => /=??. simplify_eq. by apply: STraceEnd.
    + apply: STraceStep. { apply: (FilterStep _ _ _ _ (Some n2)). econstructor. naive_solver. } 2: naive_solver.
      move => /=??. simplify_eq.
      destruct b2. 1: by apply: STraceEnd.
      apply: STraceStep. { econstructor; [constructor|]. naive_solver. } 2: naive_solver.
      move => /=??. simplify_eq. by apply: STraceEnd.
Qed.

Lemma mod_ang_comm2_filter_not_refines_mod_ang_comm1_filter:
  ¬ srefines (filter_mod mod_ang_comm2 test_filter) (filter_mod mod_ang_comm1 test_filter).
Proof.
  move => [/=].
  setoid_rewrite mod_ang_comm1_filter_traces.
  setoid_rewrite mod_ang_comm2_filter_traces.
  move => Hr.
  move: (Hr (λ κs, κs = [] ∨
                   κs = [Vis 4] ∨ κs = [Vis 4; Vis 2] ∨ κs = [Vis 4; Vis 2; Nb] ∨
                   κs = [Vis 5] ∨ κs = [Vis 5; Vis 3] ∨ κs = [Vis 5; Vis 3; Nb])).
  move => [|].
  - split; [ naive_solver|].
    right. eexists 4, 5.
    split_and!; [ naive_solver..|].
    eexists false, false. naive_solver.
  - naive_solver.
Qed.
End filter_example.

(** * [filter] preserves [srefines]  *)
Inductive filter_trace_rel {EV1 EV2} (R : EV1 → option EV2 → Prop) : list (event EV1) → list (event EV2) → Prop :=
| FTRNil :
    filter_trace_rel R [] []
| FTREnd :
    filter_trace_rel R [Nb] [Nb]
| FTRStep κ κ' κs κs':
    R κ κ' →
    filter_trace_rel R κs κs' →
    filter_trace_rel R (Vis κ :: κs) (option_list (Vis <$> κ') ++ κs')
| FTRUb κs':
    filter_trace_rel R [Ub] κs'
.

Lemma mod_filter_to_mod {EV1 EV2} (m : mod_trans EV1) (R : EV1 → option EV2 → Prop) σ Pκs Pσ:
  σ ~{ filter_trans m R, Pκs }~>ₛ Pσ →
  σ ~{ m, λ κs, ∃ κs', filter_trace_rel R κs κs' ∧ Pκs κs' }~>ₛ Pσ.
Proof.
  elim.
  - move => ????[??]. apply: STraceEnd; [done|].
    split; eexists _; (split; [ by constructor | done]).
  - move => ????? Hstep ? IH [??]. inversion Hstep; simplify_eq.
    apply: STraceStep; [done| |].
    + move => σ2 ?. apply: shas_trace_mono; [by apply: IH | |done] => /=.
      move => κs [κs' [? ?]].
      eexists _. split; [|done].
      destruct e; simplify_eq/=; [|done]. by apply: FTRStep.
    + destruct e => /=; split; eexists _.
      all: try by split; [by constructor|].
      split; [constructor => //; constructor|]. by rewrite right_id_L.
Qed.

Lemma mod_to_mod_filter {EV1 EV2} (m : mod_trans EV1) (R : EV1 → option EV2 → Prop) σ Pκs Pκs' Pσ:
(* The first condition states that [mod_filter] does not add more
non-determinism. This condition (or maybe something slightly weaker)
sadly is necessary, because this definition of refinement allows to
commute angelic choice and visible events. Consider the modules I and S

I :       A     B
    /- 2 --- 4 --- 6
1 -∀
    \- 3 --- 5 --- 7
          A     C

S :              B
         A      /- 6
1 --- 2 --- 4 -∀
                \- 7
                C

and a relation R with [R A (Some A1)], [R A (Some A2)], [R B (Some B)], [R C (Some C)].
Then we have I ⊑ S but not mod_filter R I ⊑ mod_filter R S since the trace
 [A1; B] ∨ [A2; C] can be produced by mod_filter R I, but not by mod_filter R S.
The cruicial difference is that I can pick two different elements of R for A, while S
can only pick one and whatever it picks, the angelic choice could resolve in the wrong way.
See also the example above.
 *)
  (∀ κ1 κ2 κ2', R κ1 κ2 → R κ1 κ2' → κ2 = κ2') →
  σ ~{ m, Pκs }~>ₛ Pσ →
  (∀ x, Pκs x → (λ κs, ∃ κs', filter_trace_rel R κs κs' ∧ Pκs' κs') x) →
  σ ~{ filter_trans m R, Pκs' }~>ₛ Pσ.
Proof.
  move => HR Ht. elim: Ht Pκs'.
  - move => ????[??]? HP.
    have [//|? [Hf ?]]:= HP [] _. inversion Hf; simplify_eq.
    have [//|? [Hf2 ?]]:= HP [Nb] _. inversion Hf2; simplify_eq.
    by apply: STraceEnd.
  - move => σ1?? Pσ3 κ ?? IH [??] Pκs' HP.
    destruct κ; simplify_eq/=.
    + have [?[Hf HP']]:= HP [_] ltac:(done).
      inversion Hf; simplify_eq.
      have [?[Hf2 ?]]:= HP [] ltac:(done).
      inversion Hf2; simplify_eq.
      revert select (filter_trace_rel _ _ κs'). inversion 1; simplify_eq.
      rewrite right_id in HP'.
      apply: STraceStep; [ econstructor; [done | simpl;done] | | done].
      move => σ2 ?. apply: IH; [done| ] => κs'' HP''.
      have [?[ Hf' ?]]:= HP _ HP''. inversion Hf'; simplify_eq.
      eexists _. split; [done|]. have := HR _ _ _ H1 H2. naive_solver.
    + have [?[Hf ?]]:= HP _ ltac:(done). inversion Hf; simplify_eq.
      apply: STraceStep; [ by econstructor | | simplify_eq/=; done]; simplify_eq/=.
      move => σ2 ?. by apply: IH.
Qed.

Lemma mod_filter_srefines {EV1 EV2} (m1 m2 : module EV1) (R : EV1 → option EV2 → Prop) :
  (∀ κ1 κ2 κ2', R κ1 κ2 → R κ1 κ2' → κ2 = κ2') →
  srefines m1 m2 →
  srefines (filter_mod m1 R) (filter_mod m2 R).
Proof.
  move => ? [/= Hr]. constructor => /= ? /mod_filter_to_mod/Hr Hm. apply: mod_to_mod_filter; [done|done|].
  move => ??. naive_solver.
Qed.
