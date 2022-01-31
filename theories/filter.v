Require Export refframe.module.
Require Import refframe.srefines.
Require Import refframe.trefines.
Require Import refframe.example_modules.
Require Import refframe.proof_techniques.

Inductive filter_step {EV1 EV2} (m : module EV1) (R : EV1 → option EV2 → Prop) :
  m.(m_state) → option EV2 → (m.(m_state) → Prop) → Prop :=
| FilterStep σ e e' Pσ:
    m.(m_step) σ e Pσ →
    (* TODO: is there a better way to formulate this? E.g. assume
    that there is no R None None Some in the theorem? *)
    (if e is Some κ then R κ e' else e' = None) →
    filter_step m R σ e' Pσ.

Definition mod_filter {EV1 EV2} (m : module EV1) (R : EV1 → option EV2 → Prop) : module EV2 :=
  Mod (filter_step m R).

Global Hint Transparent mod_filter : tstep.

Global Instance filter_vis_no_all {EV1 EV2} (m : module EV1) (R : EV1 → option EV2 → Prop) `{!VisNoAll m}:
  VisNoAll (mod_filter m R).
Proof. move => *. invert_all @m_step; case_match; simplify_eq. by apply: vis_no_all. Qed.

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
  0 ~{mod_filter mod_ang_comm1 test_filter, Pκs}~>ₛ (λ _, True) ↔
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
    invert_all @m_step => //.
    split; [naive_solver|]. right.
    have [κ' ?]: ∃ κ', κ = Some κ' by naive_solver. subst.
    eexists κ'.
    inversion H1; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.

    have {}H := (H3 3 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
    inversion H6; simplify_eq. 2: invert_all @m_step => //.

    have {}H := (H3 5 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
    inversion H11; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
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
  0 ~{mod_filter mod_ang_comm2 test_filter, Pκs}~>ₛ (λ _, True) ↔
    Pκs [] ∧
  (Pκs [Nb] ∨
   ∃ n1 n2, (n1 = 4 ∨ n1 = 5) ∧ (n2 = 4 ∨ n2 = 5) ∧
   (Pκs [Vis n1] ∧ Pκs [Vis n2] ∧
    ∃ b1 b2,
      (if b1 then Pκs [Vis n1; Nb] else Pκs [Vis n1; Vis 2] ∧ Pκs [Vis n1; Vis 2; Nb])
      ∧
      (if b2 then Pκs [Vis n2; Nb] else Pκs [Vis n2; Vis 3] ∧ Pκs [Vis n2; Vis 3; Nb]))).
Proof.
  split.
  - inversion 1; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
    split; [naive_solver|].

    have {}H := (H1 2 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.

    have {}H := (H1 5 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    invert_all @m_step => //. right.

    have [κ' ?]: ∃ κ', κ = Some κ' by naive_solver. subst.
    have [κ'' ?]: ∃ κ', κ0 = Some κ' by naive_solver. subst.
    eexists κ', κ''. split; [naive_solver|].
    split; [naive_solver|]. split; [naive_solver|]. split; [naive_solver|].

    inversion H3; simplify_eq. 1: {
      eexists true.
      inversion H5; simplify_eq. 1: eexists true; naive_solver.
      invert_all @m_step => //.

      inversion H11; simplify_eq. 2: invert_all @m_step => //.
      eexists false; naive_solver.
    }
    eexists false.
    invert_all @m_step => //.

    inversion H8; simplify_eq. 2: invert_all @m_step => //.

    inversion H5; simplify_eq. 1: eexists true; naive_solver.
    invert_all @m_step => //.

    inversion H14; simplify_eq. 2: invert_all @m_step => //.
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
  ¬ srefines (MS (mod_filter mod_ang_comm2 test_filter) 0) (MS (mod_filter mod_ang_comm1 test_filter) 0).
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

Lemma mod_filter_to_mod {EV1 EV2} (m : module EV1) (R : EV1 → option EV2 → Prop) σ Pκs Pσ:
  σ ~{ mod_filter m R, Pκs }~>ₛ Pσ →
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

Lemma mod_to_mod_filter {EV1 EV2} (m : module EV1) (R : EV1 → option EV2 → Prop) σ Pκs Pκs' Pσ:
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
  σ ~{ mod_filter m R, Pκs' }~>ₛ Pσ.
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

Lemma mod_filter_srefines {EV1 EV2} (m1 m2 : module EV1) (R : EV1 → option EV2 → Prop) σ1 σ2 :
  (∀ κ1 κ2 κ2', R κ1 κ2 → R κ1 κ2' → κ2 = κ2') →
  srefines (MS m1 σ1) (MS m2 σ2) →
  srefines (MS (mod_filter m1 R) σ1) (MS (mod_filter m2 R) σ2).
Proof.
  move => ? [/= Hr]. constructor => /= ? /mod_filter_to_mod/Hr Hm. apply: mod_to_mod_filter; [done|done|].
  move => ??. naive_solver.
Qed.

(*** trefines for [mod_filter] *)

Fixpoint trace_bind {EV1 EV2} (f : EV1 → trace EV2) (κs : trace EV1) : trace EV2 :=
  match κs with
  | tnil => tnil
  | tcons κ κs => tapp (f κ) (trace_bind f κs)
  | tex T f' => tex T (λ x, trace_bind f (f' x))
  | tall T f' => tall T (λ x, trace_bind f (f' x))
  end.

Lemma trace_bind_mono {EV1 EV2} (f : EV1 → trace EV2) κs1 κs2 :
  κs1 ⊆ κs2 →
  trace_bind f κs1 ⊆ trace_bind f κs2.
Proof.
  elim => //=.
  - move => ?????. by apply: tapp_mono.
  - move => ?????. constructor. naive_solver.
  - move => ?????. econstructor. naive_solver.
  - move => ??????. econstructor. naive_solver.
  - move => ??????. econstructor. naive_solver.
Qed.


Definition filtered_trace {EV1 EV2} (R : EV1 → option EV2 → Prop)
  : trace EV1 → trace EV2 :=
  trace_bind (λ κ, tall ({ κ' | R κ κ'}) (λ x, option_trace (`x))).

Lemma filtered_trace_mono {EV1 EV2} (R : EV1 → option EV2 → Prop) κs1 κs2 :
  κs1 ⊆ κs2 →
  filtered_trace R κs1 ⊆ filtered_trace R κs2.
Proof. apply trace_bind_mono. Qed.

Lemma tmod_filter_to_mod {EV1 EV2} (m : module EV1) (R : EV1 → option EV2 → Prop) σi Pσ κs:
  σi ~{ mod_filter m R, κs }~>ₜ Pσ →
  ∃ κs', filtered_trace R κs' ⊆ κs ∧ σi ~{ m, κs' }~>ₜ Pσ.
Proof.
  elim.
  - move => ?????. eexists tnil => /=. split; [done|]. by constructor.
  - move => ??? κ ?? Hstep ? IH Hs.
    inversion Hstep; simplify_eq.
    have [f Hf]:= CHOICE IH.
    eexists (tapp (option_trace e) (tex _ f)). split.
    + etrans; [|done].
      destruct e => /=; simplify_option_eq.
      * rewrite /filtered_trace/=-/(filtered_trace _).
        apply: (subtrace_all_l (exist _ _ _)); [done|] => ?.
        apply: tapp_mono; [done|].
        constructor => -[??]. naive_solver.
      * rewrite /filtered_trace/=-/(filtered_trace _).
        constructor => -[??]. naive_solver.
    + apply: TTraceStep; [done | |done].
      move => ??/=. eapply thas_trace_ex. naive_solver.
      Unshelve. done.
  - move => T f ???? IH ?.
    have [fx Hfx]:= AxCHOICE _ _ _ IH.
    eexists (tall T (λ x, fx x)) => /=.
    rewrite /filtered_trace/=-/(filtered_trace _).
    split.
    + etrans; [|done]. constructor => ?. econstructor. naive_solver.
    + apply: thas_trace_all. naive_solver.
Qed.

Lemma tmod_to_mod_filter {EV1 EV2} (m : module EV1) (R : EV1 → option EV2 → Prop) σi Pσ κs:
  σi ~{ m, κs }~>ₜ Pσ →
  σi ~{ mod_filter m R, filtered_trace R κs }~>ₜ Pσ.
Proof.
  elim.
  - move => ?????. constructor. done. by apply: (filtered_trace_mono _ tnil).
  - move => ??? κ ?? Hstep ? IH Hs.
    apply: thas_trace_mono; [| by apply: filtered_trace_mono |done].
    destruct κ => /=.
    + rewrite /filtered_trace/=-/(filtered_trace _).
      apply thas_trace_all => -[??].
      apply: TTraceStep; [econstructor;[done| simpl;done] |done |done].
    + apply: TTraceStep; [by econstructor | done | simpl;done].
  - move => ????????.
    apply: thas_trace_mono; [| by apply: filtered_trace_mono |done].
    rewrite /filtered_trace/=-/(filtered_trace _).
    apply: thas_trace_all. naive_solver.
Qed.

Lemma mod_filter_trefines {EV1 EV2} (R : EV1 → option EV2 → Prop) mi ms σi σs:
  trefines (MS mi σi) (MS ms σs) →
  trefines (MS (mod_filter mi R) σi) (MS (mod_filter ms R) σs).
Proof.
  move => [/=Hr]. constructor => /=? /tmod_filter_to_mod[?[? /Hr/tmod_to_mod_filter?]].
  by apply: thas_trace_mono.
Qed.


(** showing that [trefines1_implies_trefines2] is useful by proving
[tmod_filter_refines] with a siginificantly simpler proof. *)
Lemma tmod_filter_refines' {EV1 EV2} (R : EV1 → option EV2 → Prop) mi ms σi σs:
  trefines (MS mi σi) (MS ms σs) →
  trefines (MS (mod_filter mi R) σi) (MS (mod_filter ms R) σs).
Proof.
  move => Hr. eapply (trefines1_implies_trefines2 (MS mi _) (MS ms _) (MS (mod_filter mi R) _) (MS (mod_filter ms R) _) (λ σ1 σ2, σ1 = σ2) (λ σ1 σ2, σ1 = σ2)); [done.. | |] => /=.
  - move => ???? -> Hstep. inversion Hstep; simplify_eq. eexists e.
    split.
    + case_match; simplify_eq => //.
      move => ??? -> ?. apply: TTraceStep; [| |by erewrite tapp_tnil_r].
      { econstructor; [done| simpl; done]. }
      move => ??. apply: TTraceEnd; naive_solver.
    + apply: TTraceStep; [done| |by erewrite tapp_tnil_r].
      move => ??. apply: TTraceEnd; [|done]. naive_solver.
  - move => ??? -> ?.
    apply: TTraceStep; [by econstructor| |simpl; done].
    move => ??. apply: TTraceEnd; [|done]. naive_solver.
Qed.
