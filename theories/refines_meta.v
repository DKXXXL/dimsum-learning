Require Export refframe.module.
Require Import refframe.srefines.
Require Import refframe.trefines.
Require Import refframe.lrefines.
Require Import refframe.dem_module.
Require Import refframe.example_modules.

(*** Proof that trefines implies srefines *)
Inductive thas_trace_rel {EV} : (list (event EV) → Prop) → (trace EV) → Prop :=
| TRel_nil (Pκs : _ → Prop) κs:
   κs ⊆ tnil →
   Pκs [] →
   Pκs [Nb] →
   thas_trace_rel Pκs κs
| TRel_cons (Pκs : _ → Prop) κ κs κs':
   κs' ⊆ tcons κ κs →
   Pκs [] →
   Pκs [Vis κ] →
   thas_trace_rel (λ κs, Pκs (Vis κ::κs)) κs →
   thas_trace_rel Pκs κs'
| TRel_ex (Pκs : _ → Prop) T f κs:
   κs ⊆ tex T f →
   Pκs [] →
   (∀ x, thas_trace_rel Pκs (f x)) →
   thas_trace_rel Pκs κs
.

Lemma thas_trace_rel_mono_l {EV} (Pκs1 Pκs2 : _ → Prop) (κs : trace EV) :
  thas_trace_rel Pκs1 κs →
  (∀ x, Pκs1 x → Pκs2 x) →
  thas_trace_rel Pκs2 κs.
Proof.
  move => Ht. elim: Ht Pκs2.
  - move => ?????? Hsub. apply: TRel_nil => //; by apply: Hsub.
  - move => *. apply: TRel_cons; naive_solver.
  - move => *. apply: TRel_ex; naive_solver.
Qed.

Lemma thas_trace_rel_mono_r {EV} Pκs (κs1 κs2 : trace EV) :
  thas_trace_rel Pκs κs1 →
  κs2 ⊆ κs1 →
  thas_trace_rel Pκs κs2.
Proof.
  move => Ht. elim: Ht κs2.
  - move => ???????. apply: TRel_nil => //. by etrans.
  - move => *. apply: TRel_cons; [|done..]. by etrans.
  - move => *. apply: TRel_ex; [|done..]. by etrans.
Qed.

Lemma thas_trace_rel_tnil {EV} Pκs (κs : trace EV) :
  thas_trace_rel Pκs κs →
  tnil ⊆ κs →
  Pκs [] ∧ Pκs [Nb].
Proof.
  elim.
  - done.
  - move => ???? Hsub1 ???? Hsub2.
    pose proof (transitivity Hsub2 Hsub1) as Ht. inversion Ht; simplify_K.
  - move => ???? Hsub1 ??? Hsub2.
    pose proof (transitivity Hsub2 Hsub1) as Ht. inversion Ht; simplify_K. naive_solver.
Qed.

Lemma thas_trace_rel_tcons {EV} Pκs (κs : trace EV) κs' κ :
  thas_trace_rel Pκs κs →
  tcons κ κs' ⊆ κs →
  Pκs [Vis κ] ∧ thas_trace_rel (λ κs, Pκs (Vis κ :: κs)) κs'.
Proof.
  elim.
  - move => ?? Hsub1 ?? Hsub2.
    pose proof (transitivity Hsub2 Hsub1) as Ht. inversion Ht; simplify_K.
  - move => ???? Hsub1 ???? Hsub2.
    pose proof (transitivity Hsub2 Hsub1) as Ht. inversion Ht; simplify_K.
    split; [done|]. by apply: thas_trace_rel_mono_r.
  - move => ???? Hsub1 ??? Hsub2.
    pose proof (transitivity Hsub2 Hsub1) as Ht. inversion Ht; simplify_K. naive_solver.
Qed.

Lemma thas_trace_rel_tall {EV} Pκs (κs : trace EV) T f :
  thas_trace_rel Pκs κs →
  tall T f ⊆ κs →
  ∃ x, thas_trace_rel Pκs (f x).
Proof.
  elim.
  - move => ?? Hsub1 ?? Hsub2.
    pose proof (transitivity Hsub2 Hsub1) as Ht. inversion Ht; simplify_K. eexists _.
    by apply: TRel_nil.
  - move => ???? Hsub1???? Hsub2.
    pose proof (transitivity Hsub2 Hsub1) as Ht. inversion Ht; simplify_K. eexists _.
    by apply: TRel_cons.
  - move => ???? Hsub1 ??? Hsub2.
    pose proof (transitivity Hsub2 Hsub1) as Ht.
    inversion Ht; simplify_K.
    + naive_solver.
    + eexists _. by apply: TRel_ex.
Qed.

Lemma thas_trace_rel_nil {EV} Pκs (κs : trace EV) :
  thas_trace_rel Pκs κs →
  Pκs [].
Proof. inversion 1; by simplify_eq. Qed.

Lemma shas_trace_thas_trace {EV} (m : module EV) σ Pσ (Pκs : _ → Prop):
  σ ~{ m, Pκs }~>ₛ Pσ ↔ ∃ κs, thas_trace_rel Pκs κs ∧ σ ~{ m, κs }~>ₜ Pσ.
Proof.
  split.
  - elim.
    + move => ???? [??]. eexists tnil. split; [by constructor|]. by apply: TTraceEnd.
    + move => ?? Pσ2 ? κ Hstep ? IH [??].
      have [f Hf] := CHOICE IH.
      eexists (tapp (option_trace κ) (tex _ f)).
      split.
      * destruct κ => /=.
        -- apply: TRel_cons; [done..|]. apply: TRel_ex; [done..|] => -[??]. naive_solver.
        -- apply: TRel_ex; [done..|] => -[??]. naive_solver.
      * apply: TTraceStep; [done..| |done].
        move => ??. apply: thas_trace_ex. naive_solver.
  - move => [κs [Hκs Ht]].
    elim: Ht Pκs Hκs.
    + move => ???????. apply: STraceEnd; [done|].
      by apply: thas_trace_rel_tnil.
    + move => ??? κ ???? IH ?? Hrel.
      move: (Hrel) => /thas_trace_rel_nil?.
      apply: STraceStep; [done| |].
      * move => ??. apply: IH; [done| ].
        destruct κ => //; simplify_eq/=. 2: by apply: thas_trace_rel_mono_r.
        efeed pose proof @thas_trace_rel_tcons as H; [done..|]. naive_solver.
      * split; [done|]. destruct κ => //; simplify_eq/=.
        efeed pose proof @thas_trace_rel_tcons as H; [done..|]. naive_solver.
    + move => ?????? IH Hall ??.
      have := thas_trace_rel_tall _ _ _ _ ltac:(done) ltac:(done).
      naive_solver.
      Unshelve. done.
Qed.

Lemma trefines_srefines {EV} (m1 m2 : mod_state EV):
  trefines m1 m2 → srefines m1 m2.
Proof.
  move => [?]. constructor => ? /shas_trace_thas_trace[?[??]].
  apply/shas_trace_thas_trace. naive_solver.
Qed.
(* Print Assumptions trefines_refines. *)

Fixpoint trace_to_set {EV} (κs : trace EV) : list (event EV) → Prop :=
  match κs with
  | tnil => λ κs, κs = [] ∨ κs = [Nb]
  | tcons κ κs => λ κs', κs' = [] ∨ ∃ κs'', κs' = Vis κ::κs'' ∧ trace_to_set κs κs''
  | tex T f => λ κs, ∃ x, trace_to_set (f x) κs
  | tall T f => λ κs, ∀ x, trace_to_set (f x) κs
  end.

(* The following cannot be provable since [refines m1 m2 → trefines m1 m2] does not hold. *)
Lemma thas_trace_has_trace {EV} (m : module EV) σ Pσ κs:
  σ ~{ m, κs }~>ₜ Pσ ↔ σ ~{ m, trace_to_set κs }~>ₛ Pσ.
Proof.
  rewrite shas_trace_thas_trace. split.
  - move => ?. eexists _. split; [|done].
    clear. elim: κs => /=.
    + apply: TRel_nil; naive_solver.
    + move => ???. apply: TRel_cons; [done|naive_solver| |].
      * right. eexists _. split; [done|]. by apply: thas_trace_rel_nil.
      * apply: thas_trace_rel_mono_l; [done|]. naive_solver.
    + move => ?? IH.
      apply: TRel_ex; [done| |]. admit.
      move => ?. apply: thas_trace_rel_mono_l. done. naive_solver.
    + move => ?? IH.
      admit.
  - move => [κs' [Hrel Ht]]. apply: thas_trace_mono; [done| |done]. clear Ht.
    move: Hrel. move HPκs: (trace_to_set _) => Pκs Ht.
    have : ∀ x, Pκs x → trace_to_set κs x by rewrite HPκs => ?.
    elim: Ht κs {HPκs}.
    + move => ???? Hnb κs Hsub. etrans; [done|].
      move: Hnb => /Hsub /=. elim: κs {Hsub} => //=.
      * naive_solver.
      * move => ??? [??]. econstructor. naive_solver.
      * move => ????. econstructor. naive_solver.
    + move => ???????????. etrans; [done|].
      admit.
    + move => ??????????. etrans; [done|].
      constructor. naive_solver.
Abort.

Lemma srefines_not_trefines:
  ¬ (∀ EV (m1 m2 : mod_state EV), srefines m1 m2 → trefines m1 m2).
Proof.
  move => Hr. apply: mod_ang_comm_not_trefines. apply: Hr.
  apply mod_ang_comm_sequiv.
Qed.

(*** Equivalence between refines and dem_refines *)

Inductive dem_trace_to_set {EV} : list (dem_event EV) → (list (event EV) → Prop) → Prop :=
| DT2S_nil (Pκs : _ → Prop):
    Pκs [] →
    Pκs [Nb] →
    dem_trace_to_set [] Pκs
| DT2S_vis κ κs (Pκs : _ → Prop):
    Pκs [] →
    dem_trace_to_set κs (λ κs, Pκs (Vis κ::κs)) →
    dem_trace_to_set (DVis κ :: κs) Pκs
| DT2S_ub κs (Pκs : _ → Prop):
    Pκs [] →
    dem_trace_to_set (DUb :: κs) Pκs
.

Lemma dem_trace_to_set_nil {EV} (κs : list (dem_event EV)) Pκs:
  dem_trace_to_set κs Pκs → Pκs [].
Proof. inversion 1 => //; simplify_eq; naive_solver.  Qed.

Lemma dem_trace_to_set_mono {EV} (κs : list (dem_event EV)) (Pκs Pκs' : _ → Prop):
  dem_trace_to_set κs Pκs →
  (∀ x, Pκs x → Pκs' x) →
  dem_trace_to_set κs Pκs'.
Proof.
  move => Ht. elim: Ht Pκs'.
  - move => ???? Hsub. constructor; by apply: Hsub.
  - move => ????? IH ? Hsub. constructor. { by apply: Hsub. }
    apply: IH => ??. by apply: Hsub.
  - move => ???? Hsub. constructor. by apply: Hsub.
Qed.

Lemma shas_trace_dem_has_trace {EV} (m : dem_module EV) σ Pσ Pκs:
  σ ~{ m, Pκs }~>ₛ Pσ ↔ ∃ κs, dem_trace_to_set κs Pκs ∧ σ ~{ m, κs }~>ₘ Pσ.
Proof.
  split.
  - elim.
    + move => ???? [??]. eexists [] => /=. split;[by constructor|]. by constructor.
    + move => ???? κ Hstep _ IH ?.
      inversion Hstep; simplify_eq.
      * have [κs [Hsub ?]]:= IH _ ltac:(done).
        eexists (option_list (DVis <$> _) ++ κs).
        split. 2: by apply: DTraceStep.
        destruct κ => //=. constructor => //. naive_solver.
      * eexists [DUb]. split; [constructor| by apply: DTraceUb]. naive_solver.
  - move => [κs [HP Ht]].
    elim: Ht Pκs HP.
    + move => ???? Ht. inversion Ht; simplify_eq. by constructor.
    + move => σ1 σ2 Pσ3 κ κs' Hstep _ IH Pκs Ht.
      apply: STraceStep. { by constructor. } 2: {
        move: (Ht) => /dem_trace_to_set_nil ?.
        destruct κ => //. inversion Ht; simplify_eq/=.
        split; [done|]. move: H3 => /dem_trace_to_set_nil. done.
       }
      move => ? ->. apply: IH.
      destruct κ => //; simplify_eq/=. by inversion Ht; simplify_eq.
    + move => ????? Ht. apply: STraceStep; [ by constructor | done | ].
      split; by apply: dem_trace_to_set_nil.
Qed.


Fixpoint events_to_set {EV} (κs : list (dem_event EV)) : list (event EV) → Prop :=
  match κs with
  | [] => λ κs'', κs'' = [] ∨ κs'' = [Nb]
  | DUb::_ => λ κs'', κs'' = [] ∨ κs'' = [Ub]
  | DVis κ::κs' => λ κs'', (κs'' = []) ∨ ∃ κs''', κs'' = Vis κ::κs''' ∧ events_to_set κs' κs'''
  end.

(* Compute events_to_set [Vis 1]. *)
(* Compute events_to_set [Vis 1; Ub]. *)
(* Compute events_to_set [Ub]. *)

Lemma events_to_set_nil {EV} (κs : list (dem_event EV)) :
  events_to_set κs [].
Proof. destruct κs as [|[|]] => //; naive_solver. Qed.

Lemma dem_trace_to_set_events {EV} (κs : list (dem_event EV)) :
  dem_trace_to_set κs (events_to_set κs).
Proof.
  elim: κs. 1: constructor; naive_solver.
  move => [|κ] κs IH /=. 1: constructor; by left.
  constructor.
  - by left.
  - apply: dem_trace_to_set_mono; [done|] => ??. naive_solver.
Qed.

Lemma dem_trace_to_set_inj {EV} (κs1 κs2 : list (dem_event EV)):
  dem_trace_to_set κs2 (events_to_set κs1) →
  κs1 = κs2 ∨ ∃ κs, κs ++ [DUb] `prefix_of` κs2 ∧ κs `prefix_of` κs1.
Proof.
  elim: κs2 κs1 => [|[|κ2] κs2] /=.
  - move => [|[|κ] κs] Hdem.
    + naive_solver.
    + inversion Hdem; simplify_eq/=. naive_solver.
    + inversion Hdem; simplify_eq/=.
      have := events_to_set_nil κs. naive_solver.
  - move => IH κs1 /= Hdem. right. eexists [].
    split; [apply: prefix_cons|]; apply: prefix_nil.
  - move => IH [|[|κ] κs] /=; inversion 1; simplify_eq/=.
    + move: H4 => /dem_trace_to_set_nil. naive_solver.
    + move: H4 => /dem_trace_to_set_nil. naive_solver.
    + move: (H4) => /dem_trace_to_set_nil [//|[?[??]]]; simplify_eq.
      have [| |]:= IH κs.
      -- apply: dem_trace_to_set_mono; [done|] => ??. naive_solver.
      -- naive_solver.
      -- move => [κs1 [??]]. right.
         eexists (_:: _) => /=. split; by apply: prefix_cons.
Qed.

Lemma dem_has_trace_shas_trace {EV} (m : dem_module EV) σ Pσ κs:
  σ ~{ m, κs }~>ₘ Pσ ↔ σ ~{ m, events_to_set κs}~>ₛ Pσ.
Proof.
  rewrite shas_trace_dem_has_trace.
  split.
  - move => ?. eexists _. split; [|done]. apply: dem_trace_to_set_events.
  - move => [κs2[/dem_trace_to_set_inj[->//|[?[[?->][?->]]]]]].
    move => /dem_has_trace_app_inv/dem_has_trace_ub_app_inv ?.
    by apply: dem_has_trace_trans.
Qed.

Lemma dem_refines_srefines {EV} (m1 m2 : dem_mod_state EV):
  dem_refines m1 m2 → srefines m1 m2.
Proof.
  move => [?]. constructor => ? /shas_trace_dem_has_trace?.
  apply/shas_trace_dem_has_trace. naive_solver.
Qed.

Lemma srefines_dem_refines {EV} (m1 m2 : dem_mod_state EV):
  srefines m1 m2 → dem_refines m1 m2.
Proof.
  move => [?]. constructor => ?.
  move => /dem_has_trace_shas_trace?.
  apply/dem_has_trace_shas_trace. naive_solver.
Qed.

(*** Proof that trefines implies lrefines *)
Fixpoint list_to_trace {EV} (κs : list EV) : trace EV :=
  match κs with
  | [] => tnil
  | κ::κs => tcons κ (list_to_trace κs)
  end.

Lemma lhas_trace_thas_trace {EV} (m : module EV) σ κs Pσ:
  σ ~{m, κs}~>ₗ Pσ ↔ ∃ κs', κs' ⊆ list_to_trace κs ∧ σ ~{m, κs'}~>ₜ Pσ.
Proof.
  split.
  - move => Ht. split!; [done|]. elim: Ht. { tend. }
    move => ??? κ ???? IH ?. subst. tstep; [done|done|destruct κ => /=; done].
  - move => [κs' [Hsub Ht]]. elim: Ht κs Hsub.
    + move => ???? Hs1 κs Hs2. pose proof (transitivity Hs1 Hs2) as Hs. destruct κs; [by econs|by inversion Hs].
    + move => ??? κ ???? IH Hs1 κs Hs2. pose proof (transitivity Hs1 Hs2) as Hs.
      destruct κ; simplify_eq/=.
      * destruct κs; inversion Hs; simplify_eq/=. econs; [done| |done]. naive_solver.
      * econs; naive_solver.
    + move => ??????? Hs1 κs Hs2. pose proof (transitivity Hs1 Hs2) as Hs.
      inversion Hs; simplify_K; try by destruct κs. naive_solver.
Qed.

Lemma trefines_lrefines {EV} (m1 m2 : mod_state EV):
  trefines m1 m2 → lrefines m1 m2.
Proof.
  move => [?]. constructor => ? /lhas_trace_thas_trace[?[??]].
  apply/lhas_trace_thas_trace. naive_solver.
Qed.

(* Print Assumptions trefines_lrefines. *)

(*** Proof that srefines implies lrefines *)

Lemma lhas_trace_shas_trace {EV} (m : module EV) σ κs Pσ:
  σ ~{m, κs}~>ₗ Pσ ↔ ∃ Pκs' : _ → Prop, (∀ κs', Pκs' κs' → events_to_set (DVis <$> κs) κs') ∧ σ ~{m, Pκs'}~>ₛ Pσ.
Proof.
  split.
  - move => Ht. split!; [done|]. elim: Ht. { econs; [done|]. split!. }
    move => ??? κ κs' ??? IH ?. subst. apply: STraceStep; [done| |].
    + move => ??. apply: shas_trace_mono; [naive_solver| |done]. move => ??. destruct κ => //=. naive_solver.
    + destruct κ; csimpl; split!; apply events_to_set_nil.
  - move => [Pκs' [Hsub Ht]]. elim: Ht κs Hsub.
    + move => ???? Hs1 κs Hs2. destruct κs; [by econs|naive_solver].
    + move => ???? κ ?? IH Hs1 κs Hs2.
      destruct κ; simplify_eq/=.
      * destruct κs; [naive_solver|]; simplify_eq/=. econs; [done| |simpl; naive_solver]. naive_solver.
      * econs; naive_solver.
Qed.

Lemma srefines_lrefines {EV} (m1 m2 : mod_state EV):
  srefines m1 m2 → lrefines m1 m2.
Proof.
  move => [?]. constructor => ? /lhas_trace_shas_trace[?[??]].
  apply/lhas_trace_shas_trace. naive_solver.
Qed.

(* Print Assumptions srefines_lrefines. *)
