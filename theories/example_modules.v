Require Export refframe.module.
Require Import refframe.srefines.

(*
    1
 0 --- 1
*)
Inductive mod1_step : nat → option nat → (nat → Prop) → Prop :=
| T1S0: mod1_step 0 (Some 1) (λ σ', σ' = 1).

Definition mod1 : module nat := {|
  m_state := nat;
  m_step := mod1_step;
|}.

Lemma mod1_traces Pκs:
  0 ~{mod1, Pκs}~>ₛ (λ _, True) ↔
  (Pκs [] ∧ Pκs [Nb]) ∨
  (Pκs [] ∧ Pκs [Vis 1] ∧ Pκs [Vis 1; Nb]).
Proof.
  split.
  - inversion 1; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
    have {}H := (H1 _ ltac:(done)).
    inversion H; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
  - move => [?|[??]]. 1: by apply: STraceEnd.
    apply: STraceStep; [by constructor| | naive_solver ].
    move => ??. simplify_eq.
    by apply: STraceEnd.
Qed.

Inductive mod2_step : nat → option nat → (nat → Prop) → Prop :=
| T2S0: mod2_step 0 (Some 1) (λ σ', σ' = 1)
| T2S1: mod2_step 1 (Some 2) (λ σ', σ' = 2)
.

Definition mod2 : module nat := {|
  m_state := nat;
  m_step := mod2_step;
|}.

Lemma mod2_traces Pκs:
  0 ~{mod2, Pκs}~>ₛ (λ _, True) ↔
     (Pκs [] ∧ Pκs [Nb])
  ∨ (Pκs [] ∧ Pκs [Vis 1] ∧ Pκs [Vis 1; Nb])
  ∨ (Pκs [] ∧ Pκs [Vis 1] ∧ Pκs [Vis 1; Vis 2] ∧ Pκs [Vis 1; Vis 2; Nb]).
Proof.
  split.
  - inversion 1; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
    have {}H := (H1 _ ltac:(done)).
    inversion H; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
    have {}H := (H3 _ ltac:(done)).
    inversion H; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
  - move => [?|[[??]|[?[??]]]].
    + by apply: STraceEnd.
    + apply: STraceStep; [by constructor| |naive_solver].
      move => ??. simplify_eq.
      by apply: STraceEnd.
    + apply: STraceStep; [by constructor| |done].
      move => ??. simplify_eq/=.
      apply: STraceStep; [by constructor| |naive_solver].
      move => ??. simplify_eq/=.
      by apply: STraceEnd.
Qed.

Inductive mod3_step : nat → option nat → (nat → Prop) → Prop :=
| T3S0: mod3_step 0 (Some 1) (λ σ', σ' = 1)
| T3S1: mod3_step 1 (Some 2) (λ σ', σ' = 2)
| T3S2: mod3_step 1 (Some 3) (λ σ', σ' = 3)
.

Definition mod3 : module nat := {|
  m_state := nat;
  m_step := mod3_step;
|}.

Inductive mod3'_step : nat → option nat → (nat → Prop) → Prop :=
| T3'S0: mod3'_step 0 (Some 3) (λ σ', σ' = 1)
.

Definition mod3' : module nat := {|
  m_state := nat;
  m_step := mod3'_step;
|}.

Inductive mod1_ub_step : nat → option nat → (nat → Prop) → Prop :=
| T1US0: mod1_ub_step 0 (Some 1) (λ σ', σ' = 1)
| T1US1: mod1_ub_step 1 None (λ σ', False)
.

Definition mod1_ub : module nat := {|
  m_state := nat;
  m_step := mod1_ub_step;
|}.

Lemma mod1ub_traces Pκs:
  0 ~{mod1_ub, Pκs}~>ₛ (λ _, True) ↔
     (Pκs [] ∧ Pκs [Nb])
  ∨ (Pκs [] ∧ Pκs [Vis 1]).
Proof.
  split.
  - inversion 1; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
    have {}H := (H1 _ ltac:(done)).
    inversion H; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
    naive_solver.
  - move => [?|[??]].
    + by apply: STraceEnd.
    + apply: STraceStep; [by constructor| |done].
      move => ? ->.
      apply: STraceStep; [by constructor| |done].
      done.
Qed.

Inductive mod_ub_step {EV} : nat → option EV → (nat → Prop) → Prop :=
| TUS0: mod_ub_step 0 None (λ σ', False)
.

Definition mod_ub EV : module EV := {|
  m_state := nat;
  m_step := mod_ub_step;
|}.

Lemma modub_traces EV Pκs:
  (* Note that without [event EV], for EV not inhabited, this would be
  equivalent to the program that does not do anything (but does not
  have UB). *)
  0 ~{mod_ub EV, Pκs}~>ₛ (λ _, True) ↔ Pκs [].
Proof.
  split.
  - inversion 1; simplify_eq. 1: naive_solver.
    naive_solver.
  - move => ?.
    apply: STraceStep; [by constructor| |done]. done.
Qed.

Inductive mod_nb_step {EV} : nat → option EV → (nat → Prop) → Prop :=
.

Definition mod_nb EV : module EV := {|
  m_state := nat;
  m_step := mod_nb_step;
|}.

Lemma modnb_traces EV Pκs:
  0 ~{mod_nb EV, Pκs}~>ₛ (λ _, True) ↔ Pκs [] ∧ Pκs [Nb].
Proof.
  split.
  - inversion 1; simplify_eq. 1: naive_solver.
    invert_all @m_step.
  - move => ?. by apply: STraceEnd.
Qed.

(*        1
    /- 1 --- 3
0 -∀
    \- 2 --- 3
          2
*)

Inductive mod12_ang_step : nat → option nat → (nat → Prop) → Prop :=
| T12AS0: mod12_ang_step 0 None (λ σ', σ' = 1 ∨ σ' = 2)
| T12AS1: mod12_ang_step 1 (Some 1) (λ σ', σ' = 3)
| T12AS2: mod12_ang_step 2 (Some 2) (λ σ', σ' = 3)
.

Definition mod12_ang : module nat := {|
  m_state := nat;
  m_step := mod12_ang_step;
|}.

Lemma mod12_ang_traces Pκs:
  0 ~{mod12_ang, Pκs}~>ₛ (λ _, True) ↔
     (Pκs [] ∧ Pκs [Nb])
  ∨ (Pκs [] ∧ Pκs [Vis 1] ∧ Pκs [Vis 1; Nb] ∧ Pκs [Vis 2] ∧ Pκs [Vis 2; Nb] ).
Proof.
  split.
  - inversion 1; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
    have {}H := (H1 1 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
    have {}H := (H3 _ ltac:(naive_solver)).
    inversion H; simplify_eq. 2: invert_all @m_step => //.
    have {}H := (H1 2 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
    have {}H := (H7 _ ltac:(naive_solver)).
    inversion H; simplify_eq. 2: invert_all @m_step => //.
    naive_solver.
  - move => [?|[?[??]]].
    + by apply: STraceEnd.
    + apply: STraceStep; [by constructor| |done].
      move => ? [?|?]; simplify_eq.
      * apply: STraceStep; [by constructor | | naive_solver].
        move => ? ->.  apply: STraceEnd; [done| naive_solver].
      * apply: STraceStep; [by constructor | |naive_solver].
        move => ? ->. apply: STraceEnd; [done| naive_solver].
Qed.

Lemma mod1_refines_mod2 :
  srefines (MS mod1 0) (MS mod2 0).
Proof.
  constructor => Pκs /= Hs.
  inversion Hs; simplify_eq. 1: by apply: STraceEnd.
  invert_all @m_step => //.
  have H := (H0 _ ltac:(done)).
  apply: STraceStep. { constructor. } 2: done.
  move => ? ->.
  inversion H; simplify_eq. 1: by apply: STraceEnd.
  invert_all @m_step => //.
Qed.

Lemma mod2_refines_mod3 :
  srefines (MS mod2 0) (MS mod3 0).
Proof.
  constructor => Pκs /= Hs.
  inversion Hs; simplify_eq. 1: by apply: STraceEnd.
  invert_all @m_step => //.
  have H := (H0 _ ltac:(done)).
  apply: STraceStep. { constructor. } 2: done.
  move => ? ->. simplify_eq.
  inversion H; simplify_eq. 1: by apply: STraceEnd.
  invert_all @m_step => //.
  have {}H := (H3 _ ltac:(done)).
  apply: STraceStep. { constructor. } 2: done.
  move => ? ->. simplify_eq.
  inversion H; simplify_eq. 1: by apply: STraceEnd.
  invert_all @m_step => //.
Qed.

Lemma mod2_refines_mod1_ub :
  srefines (MS mod2 0) (MS mod1_ub 0).
Proof.
  constructor => Pκs /= Hs.
  inversion Hs; simplify_eq. 1: by apply: STraceEnd.
  invert_all @m_step => //.
  have H := (H0 _ ltac:(done)).
  apply: STraceStep. { constructor. } 2: done.
  move => ? ->. simplify_eq.
  inversion H; simplify_eq. 1: by apply: STraceEnd.
  apply: STraceStep. { constructor. } 2: naive_solver.
  done.
Qed.

Lemma mod2_refines_mod1 :
  srefines (MS mod2 0) (MS mod1 0).
Proof.
  constructor => Pκs /= Hs.
  inversion Hs; simplify_eq. 1: by apply: STraceEnd.
  invert_all @m_step => //.
  have H := (H0 _ ltac:(done)).
  apply: STraceStep. { constructor. } 2: done.
  move => ? ->. simplify_eq.
  inversion H; simplify_eq.
  { simplify_eq/=. apply: STraceEnd; [done|].
    done.
    (* split. 2: move => <-.  *)
  }
  invert_all @m_step => //.
  have {}H := (H0 _ ltac:(done)).
  apply: STraceStep; [| | ]. Fail constructor.
  (* Undo. Undo. apply: STraceEnd; [done|]. *)
Abort.


Lemma mod12_ang_refines_mod1 :
  srefines (MS mod12_ang 0) (MS mod1 0).
Proof.
  constructor => Pκs /= Hs.
  inversion Hs; simplify_eq. 1: by apply: STraceEnd.
  invert_all @m_step => //.
  have H := (H0 1 ltac:(naive_solver)).
  inversion H; simplify_eq. 1: by apply: STraceEnd.
  invert_all @m_step => //.
  have {}H := (H3 _ ltac:(naive_solver)).
  inversion H; simplify_eq.
  2: invert_all @m_step => //.
  apply: STraceStep; [by constructor| | naive_solver].
  move => ?->. by apply: STraceEnd.
Qed.

Lemma mod12_ang_refines_mod3' :
  srefines (MS mod12_ang 0) (MS mod3' 0).
Proof.
  constructor => Pκs /= Hs.
  inversion Hs; simplify_eq. 1: by apply: STraceEnd.
  invert_all @m_step => //.
  have H := (H0 1 ltac:(naive_solver)).
Abort.
  (* inversion H; simplify_eq. *)
  (* 2: invert_all @m_step => //. *)
  (* have {}H := (H0 _ (Some 2) ltac:(naive_solver)). *)
  (* inversion H; simplify_eq. *)
  (* 2: invert_all @m_step => //. *)
  (* exfalso. simplify_eq/=. *)
  (* move: (H3 [2]). move: (H5 []). *)
(* Abort. *)

(** Angelic choice commutes with events: *)

(*               B
    A      /- 3 --- 4
 1 --- 2 -∀
           \- 5 --- 6
                 C
 *)
Inductive mod_ang_comm1_step : nat → option nat → (nat → Prop) → Prop :=
| TAC1S1: mod_ang_comm1_step 0 (Some 1) (λ σ', σ' = 2)
| TAC1S2: mod_ang_comm1_step 2 None     (λ σ', σ' = 3 ∨ σ' = 5)
| TAC1S3: mod_ang_comm1_step 3 (Some 2) (λ σ', σ' = 4)
| TAC1S5: mod_ang_comm1_step 5 (Some 3) (λ σ', σ' = 6)
.

Definition mod_ang_comm1 : module nat := {|
  m_state := nat;
  m_step := mod_ang_comm1_step;
|}.

(*         A     B
     /- 2 --- 3 --- 4
 1 -∀
     \- 5 --- 6 --- 7
           A     C
 *)
Inductive mod_ang_comm2_step : nat → option nat → (nat → Prop) → Prop :=
| TAC2S1: mod_ang_comm2_step 0 None     (λ σ', σ' = 2 ∨ σ' = 5)
| TAC2S2: mod_ang_comm2_step 2 (Some 1) (λ σ', σ' = 3)
| TAC2S3: mod_ang_comm2_step 3 (Some 2) (λ σ', σ' = 4)
| TAC2S5: mod_ang_comm2_step 5 (Some 1) (λ σ', σ' = 6)
| TAC2S6: mod_ang_comm2_step 6 (Some 3) (λ σ', σ' = 7)
.

Definition mod_ang_comm2 : module nat := {|
  m_state := nat;
  m_step := mod_ang_comm2_step;
|}.


Lemma mod_ang_comm1_traces Pκs:
  0 ~{mod_ang_comm1, Pκs}~>ₛ (λ _, True) ↔
    Pκs [] ∧
  (Pκs [Nb] ∨
   (Pκs [Vis 1] ∧
    (Pκs [Vis 1; Nb] ∨
     (Pκs [Vis 1; Vis 2] ∧ Pκs [Vis 1; Vis 2; Nb] ∧
      Pκs [Vis 1; Vis 3] ∧ Pκs [Vis 1; Vis 3; Nb])))).
Proof.
  split.
  - inversion 1; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
    split; [naive_solver|].
    have {}H := (H1 _ ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.

    have {}H := (H3 3 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
    have {}H := (H5 _ ltac:(naive_solver)).
    inversion H; simplify_eq. 2: invert_all @m_step => //.

    have {}H := (H3 5 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
    have {}H := (H9 _ ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
  - move => [?[?|[? HP]]]. 1: by apply: STraceEnd.
    apply: STraceStep; [by constructor| |done].
    move => /= ??; simplify_eq.
    move: HP => [?|?]. 1: by apply: STraceEnd.
    apply: STraceStep; [by constructor| |done].
    move => /= ? [?|?]; simplify_eq.
    + apply: STraceStep; [by constructor | |naive_solver].
      move => /= ? ->. apply: STraceEnd; [done | naive_solver].
    + apply: STraceStep; [by constructor | |naive_solver].
      move => /= ? ->. apply: STraceEnd; [done | naive_solver].
Qed.

Lemma mod_ang_comm2_traces Pκs:
  0 ~{mod_ang_comm2, Pκs}~>ₛ (λ _, True) ↔
    Pκs [] ∧
  (Pκs [Nb] ∨
   (Pκs [Vis 1] ∧
    (Pκs [Vis 1; Nb] ∨
     (Pκs [Vis 1; Vis 2] ∧ Pκs [Vis 1; Vis 2; Nb] ∧
      Pκs [Vis 1; Vis 3] ∧ Pκs [Vis 1; Vis 3; Nb])))).
Proof.
  split.
  - inversion 1; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
    split; [naive_solver|].

    have {}H := (H1 2 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
    have {}H := (H3 _ ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
    have {}H := (H5 _ ltac:(naive_solver)).
    inversion H; simplify_eq. 2: invert_all @m_step => //.

    have {}H := (H1 5 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
    have {}H := (H9 _ ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    invert_all @m_step => //.
    have {}H := (H11 _ ltac:(naive_solver)).
    inversion H; simplify_eq. 2: invert_all @m_step => //.
    naive_solver.
  - move => [?[?|[? HP]]]. 1: by apply: STraceEnd.
    apply: STraceStep; [by constructor| |done].
    move => /= ?[?|?]; simplify_eq.
    + apply: STraceStep; [by constructor| |done].
      move => /= ? ->.
      move: HP => [?|?]. 1: by apply: STraceEnd.
      apply: STraceStep; [by constructor | |naive_solver].
      move => /= ? ->. apply: STraceEnd; [done | naive_solver].
    + apply: STraceStep; [by constructor| |done].
      move => /= ? ->.
      move: HP => [?|?]. 1: by apply: STraceEnd.
      apply: STraceStep; [by constructor | |naive_solver].
      move => /= ? ->. apply: STraceEnd; [done | naive_solver].
Qed.

Lemma mod_ang_comm_equiv:
  srefines_equiv (MS mod_ang_comm1 0) (MS mod_ang_comm2 0).
Proof. apply: srefines_equiv_equiv => ?. rewrite mod_ang_comm1_traces mod_ang_comm2_traces. done. Qed.
