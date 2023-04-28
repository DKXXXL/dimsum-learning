From dimsum.core Require Export proof_techniques.
From dimsum.core Require Import product seq_product state_transform.

Set Default Proof Using "Type".

(** * Linking *)

Section link.
  Context {EV : Type} {S : Type}.
  Implicit Types (R : seq_product_case → S → EV → seq_product_case → S → EV → bool → Prop).

(*
  Inductive link_case :=
  | MLFLeft | MLFRight | MLFNone
  | MLFEmit (e : io_event EV) (s : link_case)
  | MLFExpect (e : seq_product_event (io_event EV) (io_event EV)) (s : link_case)
  | MLFReturn (s : link_case)
  .
  Fixpoint mod_link_state_to_product_state (s : link_case) : seq_product_case :=
    match s with
    | MLFLeft => SPLeft
    | MLFRight => SPRight
    | MLFNone => SPNone
    | MLFEmit e s => mod_link_state_to_product_state s
    | MLFExpect e s => mod_link_state_to_product_state s
    | MLFReturn s => mod_link_state_to_product_state s
    end.

  Definition mod_link_to_state (s : seq_product_case) (e : EV) : link_case :=
    match s with
    | SPNone => MLFEmit (Outgoing, e) (MLFReturn MLFNone)
    | SPLeft => MLFReturn (MLFExpect (SPELeft (Incoming, e) SPLeft) (MLFReturn MLFLeft))
    | SPRight => MLFReturn (MLFExpect (SPERight (Incoming, e) SPRight) (MLFReturn MLFRight))
    end.

  Inductive mod_link_filter_step R :
    (link_case * S) → option (sm_event (seq_product_event (io_event EV) (io_event EV)) (io_event EV)) →
    ((link_case * S) → Prop) → Prop :=
  | MLFLeftS s e p' s' e':
    R SPLeft s e p' s' e' →
    mod_link_filter_step R (MLFLeft, s) (Some (SMERecv (SPELeft (Outgoing, e) p')))
      (λ σ, σ = (mod_link_to_state p' e', s'))
  | MLFRightS s e p' s' e':
    R SPRight s e p' s' e' →
    mod_link_filter_step R (MLFRight, s) (Some (SMERecv (SPERight (Outgoing, e) p')))
      (λ σ, σ = (mod_link_to_state p' e', s'))
  | MLFNoneS s e p' s' e':
    R SPNone s e p' s' e' →
    mod_link_filter_step R (MLFNone, s) (Some (SMERecv (SPENone p')))
      (λ σ, σ = (MLFEmit (Incoming, e') (mod_link_to_state p' e'), s'))
  | MLFEmitS s' s e:
    mod_link_filter_step R (MLFEmit e s', s) (Some (SMEEmit e))
      (λ σ, σ = (s', s))
  | MLFExpectS s' s e:
    mod_link_filter_step R (MLFExpect e s', s) (Some (SMERecv e))
      (λ σ, σ = (s', s))
  | MLFReturnS s' s:
    mod_link_filter_step R (MLFReturn s', s) (Some (SMEReturn None))
      (λ σ, σ = (s', s))
  .
  Definition mod_link_filter R := Mod (mod_link_filter_step R).

  Definition mod_link_trans R m1 m2 (σ :
      seq_map_case (seq_product_event (io_event EV) (io_event EV)) *
      link_case * S * m1.(m_state) * m2.(m_state)) :
    seq_map_case (seq_product_event (io_event EV) (io_event EV)) *
           (seq_product_case * m_state m1 * m_state m2) * (link_case * S) :=
    (σ.1.1.1.1, (mod_link_state_to_product_state σ.1.1.1.2, σ.1.2, σ.2), (σ.1.1.1.2, σ.1.1.2)).
  Arguments mod_link_trans _ _ _ _ /.

  Definition mod_link R m1 m2 : module (io_event EV) :=
    mod_state_transform (mod_seq_map (mod_seq_product m1 m2) (mod_link_filter R))
                        (λ σ σ', σ' = mod_link_trans R m1 m2 σ).
*)
  Inductive link_case :=
  | MLFLeft | MLFRight | MLFNone
  | MLFRecvL (e : EV) | MLFRecvR (e : EV)
  | MLFUb (sp : seq_product_case).

  Definition link_to_case (ok : bool) (s : seq_product_case) (e : EV) : link_case :=
    if ok then
      match s with
      | SPNone => MLFNone
      | SPLeft => MLFRecvL e
      | SPRight => MLFRecvR e
      end
    else
      MLFUb s.
  Inductive link_filter R : map_mod_fn (seq_product_event (io_event EV) (io_event EV)) (io_event EV) (link_case * S) :=
  | MLFLeftS s e p' s' e' ok:
    R SPLeft s e p' s' e' ok →
    link_filter R (MLFLeft, s) (SPELeft (Outgoing, e) p')
                    (if p' is SPNone then Some (Outgoing, e') else None)
                    (link_to_case ok p' e', s') ok
  | MLFLeftRecvS s e:
    link_filter R (MLFRecvL e, s) (SPELeft (Incoming, e) SPLeft) None (MLFLeft, s) true

  | MLFRightS s e p' s' e' ok:
    R SPRight s e p' s' e' ok →
    link_filter R (MLFRight, s) (SPERight (Outgoing, e) p')
                    (if p' is SPNone then Some (Outgoing, e') else None)
                    (link_to_case ok p' e', s') ok
  | MLFRightRecvS s e:
    link_filter R (MLFRecvR e, s) (SPERight (Incoming, e) SPRight) None (MLFRight, s) true
    
  | MLFNoneS s e p' s' e' ok:
    R SPNone s e p' s' e' ok →
    link_filter R (MLFNone, s) (SPENone p')
                    (Some (Incoming, e'))
                    (link_to_case ok p' e', s') ok
  .

  Definition link_state_trans R (m1 m2 : mod_trans (io_event EV)) (σ : link_case * S * m1.(m_state) * m2.(m_state)) :=
    (match σ.1.1.1 with
          | MLFLeft | MLFRecvL _ => SPLeft
          | MLFRight | MLFRecvR _ => SPRight
          | MLFNone => SPNone
          | MLFUb sp => sp
          end, σ.1.2, σ.2, (σ.1.1, if σ.1.1.1 is MLFUb _ then false else true)).
  Arguments link_state_trans _ _ _ _ /.

  Definition link_trans R (m1 m2 : mod_trans (io_event EV)) : mod_trans (io_event EV) :=
    state_transform_trans (map_trans (seq_product_trans m1 m2) (link_filter R))
      (λ σ σ', σ' = link_state_trans R m1 m2 σ).

  Global Instance link_trans_transform_wf R (m1 m2 : mod_trans (io_event EV)) :
    StateTransformWf (map_trans (seq_product_trans m1 m2) (link_filter R))
      (λ σ σ', σ' = link_state_trans R m1 m2 σ).
  Proof.
    constructor; [naive_solver|].
    move => [[??]?] [[[??]?][[??]?]] [[[??]?][[??]?]] ?????; simplify_eq.
    inv_all/= @m_step; inv_all @link_filter; destruct!.
    all: eexists (_, _, _); do 3 f_equal; repeat case_match => //; simplify_eq/= => //.
    all: unfold link_to_case in *; repeat case_match; simplify_eq => //.
  Qed.

  Global Instance link_vis_no_all R (m1 m2 : mod_trans _) `{!VisNoAng m1} `{!VisNoAng m2}:
    VisNoAng (link_trans R m1 m2).
  Proof.
    apply: mod_state_transform_vis_no_all.
    move => ??? [[[sp σ1]σ2][[σ s] ok]] ??.
    eexists (σ, s, σ1, σ2) => -[[[??]?]?]/=.
    split => ?; simplify_eq => //.
    inv_all/= @m_step; inv_all @link_filter; destruct!.
    all: unfold link_to_case in *; repeat case_match => //; simplify_eq => //.
  Qed.

  Definition link_mod R (m1 m2 : module (io_event EV)) (σ : S) : module (io_event EV) :=
    Mod (link_trans R m1.(m_trans) m2.(m_trans)) (MLFNone, σ, m1.(m_init), m2.(m_init)).

  Lemma link_mod_trefines R m1 m2 m1' m2' σ `{!VisNoAng m1.(m_trans)} `{!VisNoAng m2.(m_trans)}:
    trefines m1 m1' →
    trefines m2 m2' →
    trefines (link_mod R m1 m2 σ) (link_mod R m1' m2' σ).
  Proof.
    move => ??.
    apply: (state_transform_mod_trefines (Mod (map_trans _ _) _) (Mod (map_trans _ _) _)); [simpl; apply _| |done..].
    apply: (map_mod_trefines (Mod (seq_product_trans _ _) _) (Mod (seq_product_trans _ _) _)) => /=.
    by apply seq_product_mod_trefines.
  Qed.

  Lemma link_trans_step_left_i R m1 m2 s σ1 σ2 P `{!TStepI m1 σ1 P} :
    TStepI (link_trans R m1 m2) (MLFLeft, s, σ1, σ2) (λ G, P (λ b κ P',
      match κ with
      | None => G b None (λ G', P' (λ x, G' (MLFLeft, s, x, σ2)))
      | Some κ' => ∀ p' s' e' ok, R SPLeft s κ'.2 p' s' e' ok → κ'.1 = Outgoing →
                              G b (if p' is SPNone then Some (Outgoing, e') else None)
                               (λ G', P' (λ x, G' (link_to_case ok p' e', s', x, σ2)))
      end)).
  Proof.
    constructor => G /(@tstepi_proof _ _ _ _ ltac:(done))?. clear TStepI0.
    apply: (steps_impl_submodule _ (link_trans _ _ _) (λ x, (MLFLeft, s, x, σ2))); [done| |].
    - naive_solver.
    - move => /= ??? Hs. inv_all @state_transform_step. inv_all/= @m_step.
      + case_match; simplify_eq. naive_solver.
      + case_match; simplify_eq. inv_all @link_filter.
        split!; [done| |done] => /=?. destruct!.
        split!; [naive_solver..|]. move => /= ? HP. move: HP => /H2[?[??]]. eexists (_, _, _, _).
        split!; [by destruct ok, s0|done|by destruct ok, s0|naive_solver].
  Qed.

  Lemma link_trans_step_right_i R m1 m2 s σ1 σ2 P `{!TStepI m2 σ2 P} :
    TStepI (link_trans R m1 m2) (MLFRight, s, σ1, σ2) (λ G, P (λ b κ P',
      match κ with
      | None => G b None (λ G', P' (λ x, G' (MLFRight, s, σ1, x)))
      | Some κ' => ∀ p' s' e' ok, R SPRight s κ'.2 p' s' e' ok → κ'.1 = Outgoing →
                              G b (if p' is SPNone then Some (Outgoing, e') else None)
                               (λ G', P' (λ x, G' (link_to_case ok p' e', s', σ1, x)))
      end)).
  Proof.
    constructor => G /(@tstepi_proof _ _ _ _ ltac:(done))?. clear TStepI0.
    apply: (steps_impl_submodule _ (link_trans _ _ _) (λ x, (MLFRight, s, σ1, x))); [done| |].
    - naive_solver.
    - move => /= ??? Hs. inv_all @state_transform_step. inv_all/= @m_step.
      + case_match; simplify_eq. naive_solver.
      + case_match; simplify_eq. inv_all @link_filter.
        split!; [done| |done] => /=?. destruct!.
        split!; [naive_solver..|]. move => /= ? HP. move: HP => /H2[?[??]]. eexists (_, _, _, _).
        split!; [by destruct s0, ok|done|by destruct s0, ok|naive_solver] => /=.
  Qed.

  Lemma link_trans_step_left_recv_i R m1 m2 s σ1 σ2 e P `{!TStepI m1 σ1 P} :
    TStepI (link_trans R m1 m2) (MLFRecvL e, s, σ1, σ2) (λ G, P (λ b κ P',
      match κ with
      | None => G b None (λ G', P' (λ x, G' (MLFRecvL e, s, x, σ2)))
      | Some κ' => κ' = (Incoming, e) → G b None (λ G', P' (λ x, G' (MLFLeft, s, x, σ2)))
      end)).
  Proof.
    constructor => G /(@tstepi_proof _ _ _ _ ltac:(done))?. clear TStepI0.
    apply: (steps_impl_submodule _ (link_trans _ _ _) (λ x, (MLFRecvL e, s, x, σ2))); [done| |].
    - naive_solver.
    - move => /= ??? Hs. inv_all @state_transform_step. inv_all/= @m_step.
      + case_match; simplify_eq. naive_solver.
      + case_match; simplify_eq. inv_all @link_filter; naive_solver.
  Qed.

  Lemma link_trans_step_right_recv_i R m1 m2 s σ1 σ2 e P `{!TStepI m2 σ2 P} :
    TStepI (link_trans R m1 m2) (MLFRecvR e, s, σ1, σ2) (λ G, P (λ b κ P',
      match κ with
      | None => G b None (λ G', P' (λ x, G' (MLFRecvR e, s, σ1, x)))
      | Some κ' => κ' = (Incoming, e) → G b None (λ G', P' (λ x, G' (MLFRight, s, σ1, x)))
      end)).
  Proof.
    constructor => G /(@tstepi_proof _ _ _ _ ltac:(done))?. clear TStepI0.
    apply: (steps_impl_submodule _ (link_trans _ _ _) (λ x, (MLFRecvR e, s, σ1, x))); [done| |].
    - naive_solver.
    - move => /= ??? Hs. inv_all @state_transform_step. inv_all/= @m_step.
      + case_match; simplify_eq. naive_solver.
      + case_match; simplify_eq. inv_all @link_filter; naive_solver.
  Qed.

  Lemma link_trans_step_none_i R m1 m2 s σ1 σ2 :
    TStepI (link_trans R m1 m2) (MLFNone, s, σ1, σ2) (λ G, ∀ e p' s' e' ok, R SPNone s e p' s' e' ok →
      G true (Some (Incoming, e')) (λ G', G' (link_to_case ok p' e', s', σ1, σ2))).
  Proof.
    constructor => G HG. apply steps_impl_step_end => ???.
    inv_all/= @m_step; inv_all/= link_filter.
    split!; [naive_solver|done|] => /= ??. eexists (_, _, _, _). split!; by destruct s0, ok.
  Qed.

  Lemma link_trans_step_left_s R m1 m2 s σ1 σ2 P `{!TStepS m1 σ1 P} :
    TStepS (link_trans R m1 m2) (MLFLeft, s, σ1, σ2) (λ G, P (λ κ P',
      match κ with
      | None => G None (λ G', P' (λ x, G' (MLFLeft, s, x, σ2)))
      | Some (Outgoing, e) => ∃ p' s' e' ok, R SPLeft s e p' s' e' ok ∧
                              G (if p' is SPNone then Some (Outgoing, e') else None)
                               (λ G', P' (λ σ', G' (link_to_case ok p' e', s', σ', σ2)))
      | Some _ => False
      end)).
  Proof.
    constructor => G /(@tsteps_proof _ _ _ _ ltac:(done)) [κ [? [? HG']]]. clear TStepS0.
    destruct κ as [[[] e]|] => //; destruct!.
    all: eexists _, _; split; [done|] => G' /= /HG'?; tstep_s.
    all: split!; [..|apply: steps_spec_mono; [done|]] => //=; try by econs.
    all: move => ?? [[[p?]?]?]//=?; destruct p => //; by simplify_eq/=.
  Qed.

  Lemma link_trans_step_right_s R m1 m2 s σ1 σ2 P `{!TStepS m2 σ2 P} :
    TStepS (link_trans R m1 m2) (MLFRight, s, σ1, σ2) (λ G, P (λ κ P',
      match κ with
      | None => G None (λ G', P' (λ x, G' (MLFRight, s, σ1, x)))
      | Some (Outgoing, e) => ∃ p' s' e' ok, R SPRight s e p' s' e' ok ∧
                              G (if p' is SPNone then Some (Outgoing, e') else None)
                               (λ G', P' (λ σ', G' (link_to_case ok p' e', s', σ1, σ')))
      | Some _ => False
      end)).
  Proof.
    constructor => G /(@tsteps_proof _ _ _ _ ltac:(done)) [κ [? [? HG']]]. clear TStepS0.
    destruct κ as [[[] e]|] => //; destruct!.
    all: eexists _, _; split; [done|] => G' /= /HG'?; tstep_s.
    all: split!; [..|apply: steps_spec_mono; [done|]] => //=; try by econs.
    all: move => ?? [[[p?]?]?]//=?; destruct p => //; by simplify_eq/=.
  Qed.

  Lemma link_trans_step_left_recv_s R m1 m2 s σ1 σ2 e P `{!TStepS m1 σ1 P} :
    TStepS (link_trans R m1 m2) (MLFRecvL e, s, σ1, σ2) (λ G, P (λ κ P',
      match κ with
      | None => G None (λ G', P' (λ x, G' (MLFRecvL e, s, x, σ2)))
      | Some (Incoming, e') => G None (λ G', e = e' ∧ P' (λ x, G' (MLFLeft, s, x, σ2)))
      | Some _ => False
      end)).
  Proof.
    constructor => G /(@tsteps_proof _ _ _ _ ltac:(done)) [κ [? [? HG']]]. clear TStepS0.
    destruct κ as [[[] e']|] => //; destruct!.
    all: eexists _, _; split; [done|] => G' /=; try move => [?]; move => /HG'?; tstep_s; simplify_eq.
    all: split!; [..|apply: steps_spec_mono; [done|]] => //=; try by econs.
    all: move => ?? [[[p?]?]?]//=?; destruct p => //; by simplify_eq/=.
  Qed.

  Lemma link_trans_step_right_recv_s R m1 m2 s σ1 σ2 e P `{!TStepS m2 σ2 P} :
    TStepS (link_trans R m1 m2) (MLFRecvR e, s, σ1, σ2) (λ G, P (λ κ P',
      match κ with
      | None => G None (λ G', P' (λ x, G' (MLFRecvR e, s, σ1, x)))
      | Some (Incoming, e') => G None (λ G', e = e' ∧ P' (λ x, G' (MLFRight, s, σ1, x)))
      | Some _ => False
      end)).
  Proof.
    constructor => G /(@tsteps_proof _ _ _ _ ltac:(done)) [κ [? [? HG']]]. clear TStepS0.
    destruct κ as [[[] e']|] => //; destruct!.
    all: eexists _, _; split; [done|] => G' /=; try move => [?]; move => /HG'?; tstep_s; simplify_eq.
    all: split!; [..|apply: steps_spec_mono; [done|]] => //=; try by econs.
    all: move => ?? [[[p?]?]?]//=?; destruct p => //; by simplify_eq/=.
  Qed.

  Lemma link_trans_step_none_s R m1 m2 s σ1 σ2 :
    TStepS (link_trans R m1 m2) (MLFNone, s, σ1, σ2) (λ G, ∃ e p' s' e' ok, R SPNone s e p' s' e' ok ∧
      G (Some (Incoming, e')) (λ G', G' (link_to_case ok p' e', s', σ1, σ2))).
  Proof.
    constructor => G [?[?[?[?[?[??]]]]]]. split!; [done|] => /=??.
    tstep_s. split!; [by econs|]. move => [[[??]?]?] /=. unfold link_to_case.
    repeat case_match; naive_solver.
  Qed.

  Lemma link_trans_step_ub_s R m1 m2 s σ1 σ2 sp :
    TStepS (link_trans R m1 m2) (MLFUb sp, s, σ1, σ2) (λ G, G None (λ G', True)).
  Proof. constructor => G ?. split!; [done|] => /=??. by tstep_s. Qed.

  Lemma link_trans_step_link_to_case_s R m1 m2 s σ1 σ2 sp P `{!Decision P} e :
    TStepS (link_trans R m1 m2) (link_to_case (bool_decide P) sp e, s, σ1, σ2) (λ G, G None
         (λ G', P → G' (link_to_case true sp e, s, σ1, σ2) )).
  Proof.
    constructor => G ?.
    split!; [done|] => /=??. case_bool_decide; [|by tstep_s].
    apply steps_spec_end. naive_solver.
 Qed.
End link.
Arguments link_state_trans _ _ _ _ _ /.
Arguments link_case : clear implicits.

Global Hint Resolve
       link_trans_step_left_i
       link_trans_step_right_i
       link_trans_step_left_recv_i
       link_trans_step_right_recv_i
       link_trans_step_none_i
       link_trans_step_left_s
       link_trans_step_right_s
       link_trans_step_left_recv_s
       link_trans_step_right_recv_s
       link_trans_step_none_s
       link_trans_step_ub_s
| 2 : typeclass_instances.
Global Hint Resolve
  link_trans_step_link_to_case_s
| 3 : typeclass_instances.
