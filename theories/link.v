Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.filter.
Require Import refframe.product.
Require Import refframe.seq_product.
Require Import refframe.proof_techniques.
Require Import refframe.state_transform.

Set Default Proof Using "Type".

Section mod_link.
  Context {EV : Type} {S : Type}.
  Implicit Types (R : seq_product_state → S → EV → seq_product_state → S → EV → Prop).
  Implicit Types (m : module (io_event EV)).

  Inductive mod_link_state :=
  | MLFLeft | MLFRight | MLFNone
  | MLFRecvL (e : EV) | MLFRecvR (e : EV).

  Definition mod_link_to_state (s : seq_product_state) (e : EV) : mod_link_state :=
    match s with
    | SPNone => MLFNone
    | SPLeft => MLFRecvL e
    | SPRight => MLFRecvR e
    end.
  Inductive mod_link_filter R : mod_map_fn (seq_product_event (io_event EV) (io_event EV)) (io_event EV) (mod_link_state * S) :=
  | MLFLeftS s e p' s' e':
    R SPLeft s e p' s' e' →
    mod_link_filter R (MLFLeft, s) (SPELeft (Outgoing, e) p')
                    (if p' is SPNone then Some (Outgoing, e') else None)
                    (mod_link_to_state p' e', s')
  | MLFLeftRecvS s e:
    mod_link_filter R (MLFRecvL e, s) (SPELeft (Incoming, e) SPLeft) None (MLFLeft, s)
  | MLFRightS s e p' s' e':
    R SPRight s e p' s' e' →
    mod_link_filter R (MLFRight, s) (SPERight (Outgoing, e) p')
                    (if p' is SPNone then Some (Outgoing, e') else None)
                    (mod_link_to_state p' e', s')
  | MLFRightRecvS s e:
    mod_link_filter R (MLFRecvR e, s) (SPERight (Incoming, e) SPRight) None (MLFRight, s)
  | MLFNoneS s e p' s' e':
    R SPNone s e p' s' e' →
    mod_link_filter R (MLFNone, s) (SPENone p')
                    (Some (Incoming, e'))
                    (mod_link_to_state p' e', s')
  .

  Definition mod_link_trans R m1 m2 (σ : mod_link_state * S * m1.(m_state) * m2.(m_state)) :=
    (match σ.1.1.1 with
          | MLFLeft | MLFRecvL _ => SPLeft
          | MLFRight | MLFRecvR _ => SPRight
          | MLFNone => SPNone
          end, σ.1.2, σ.2, σ.1.1).
  Arguments mod_link_trans _ _ _ _ /.

  Definition mod_link R m1 m2 : module (io_event EV) :=
    mod_state_transform (mod_map (mod_seq_product m1 m2) (mod_link_filter R))
                        (λ σ σ', σ' = mod_link_trans R m1 m2 σ).

  Global Instance mod_link_vis_no_all R m1 m2 `{!VisNoAll m1} `{!VisNoAll m2}:
    VisNoAll (mod_link R m1 m2).
  Proof.
    apply: mod_state_transform_vis_no_all.
    move => ??? [[[sp σ1]σ2][σ s]] ?.
    eexists (σ, s, σ1, σ2) => -[[[??]?]?]/=.
    split => ?; simplify_eq => //.
    invert_all @m_step; invert_all @mod_link_filter; destruct_all?; simplify_eq.
    all: unfold mod_link_to_state in *; repeat case_match => //; by simplify_eq.
  Qed.

  Lemma mod_link_trefines R m1 m2 m1' m2' σ1 σ2 σ1' σ2' σ `{!VisNoAll m1} `{!VisNoAll m2}:
    trefines (MS m1 σ1) (MS m1' σ1') →
    trefines (MS m2 σ2) (MS m2' σ2') →
    trefines (MS (mod_link R m1 m2) (σ, σ1, σ2)) (MS (mod_link R m1' m2') (σ, σ1', σ2')).
  Proof.
    move => ??.
    apply: mod_state_transform_trefines; [| | |done..].
    - move => [[??]?] [[[??]?]?] [[[??]?]?] /=. naive_solver.
    - move => [[??]?] [[[??]?][??]] [[[??]?][??]] ?????; simplify_eq.
      invert_all @m_step; invert_all @mod_link_filter; destruct_all?; simplify_eq.
      all: eexists (_, _, _); do 3 f_equal; repeat case_match => //; simplify_eq/= => //.
      all: unfold mod_link_to_state in *; by repeat case_match.
    - apply mod_map_trefines => /=. by apply mod_seq_product_trefines.
  Qed.

  Lemma mod_link_step_left_i R m1 m2 s σ1 σ2 P `{!TStepI m1 σ1 P} :
    TStepI (mod_link R m1 m2) (MLFLeft, s, σ1, σ2) (λ G, P (λ b κ P',
      match κ with
      | None => G b None (λ G', P' (λ x, G' (MLFLeft, s, x, σ2)))
      | Some κ' => ∀ p' s' e', R SPLeft s κ'.2 p' s' e' → κ'.1 = Outgoing →
                              G b (if p' is SPNone then Some (Outgoing, e') else None)
                               (λ G', P' (λ x, G' (mod_link_to_state p' e', s', x, σ2)))
      end)).
  Proof.
    constructor => G /tstepi_proof?. clear TStepI0.
    apply: (steps_impl_submodule _ (mod_link _ _ _) (λ x, (MLFLeft, s, x, σ2))); [done| |].
    - naive_solver.
    - move => /= ??? Hs. invert_all' @state_transform_step; simplify_eq. invert_all' @m_step; simplify_eq/=.
      + case_match; simplify_eq. naive_solver.
      + case_match; simplify_eq. invert_all @mod_link_filter.
        split!; [done| |done] => /=?. destruct_all?.
        split!; [naive_solver..|]. move => /= ? HP. move: HP => /H2[?[??]]. eexists (_, _, _, _).
        split!; [|done|naive_solver] => /=. by destruct s0.
  Qed.

  Lemma mod_link_step_right_i R m1 m2 s σ1 σ2 P `{!TStepI m2 σ2 P} :
    TStepI (mod_link R m1 m2) (MLFRight, s, σ1, σ2) (λ G, P (λ b κ P',
      match κ with
      | None => G b None (λ G', P' (λ x, G' (MLFRight, s, σ1, x)))
      | Some κ' => ∀ p' s' e', R SPRight s κ'.2 p' s' e' → κ'.1 = Outgoing →
                              G b (if p' is SPNone then Some (Outgoing, e') else None)
                               (λ G', P' (λ x, G' (mod_link_to_state p' e', s', σ1, x)))
      end)).
  Proof.
    constructor => G /tstepi_proof?. clear TStepI0.
    apply: (steps_impl_submodule _ (mod_link _ _ _) (λ x, (MLFRight, s, σ1, x))); [done| |].
    - naive_solver.
    - move => /= ??? Hs. invert_all' @state_transform_step; simplify_eq. invert_all' @m_step; simplify_eq/=.
      + case_match; simplify_eq. naive_solver.
      + case_match; simplify_eq. invert_all @mod_link_filter.
        split!; [done| |done] => /=?. destruct_all?.
        split!; [naive_solver..|]. move => /= ? HP. move: HP => /H2[?[??]]. eexists (_, _, _, _).
        split!; [|done|naive_solver] => /=. by destruct s0.
  Qed.

  Lemma mod_link_step_left_recv_i R m1 m2 s σ1 σ2 e P `{!TStepI m1 σ1 P} :
    TStepI (mod_link R m1 m2) (MLFRecvL e, s, σ1, σ2) (λ G, P (λ b κ P',
      match κ with
      | None => G b None (λ G', P' (λ x, G' (MLFRecvL e, s, x, σ2)))
      | Some κ' => κ' = (Incoming, e) → G b None (λ G', P' (λ x, G' (MLFLeft, s, x, σ2)))
      end)).
  Proof.
    constructor => G /tstepi_proof?. clear TStepI0.
    apply: (steps_impl_submodule _ (mod_link _ _ _) (λ x, (MLFRecvL e, s, x, σ2))); [done| |].
    - naive_solver.
    - move => /= ??? Hs. invert_all' @state_transform_step; simplify_eq. invert_all' @m_step; simplify_eq/=.
      + case_match; simplify_eq. naive_solver.
      + case_match; simplify_eq. invert_all @mod_link_filter; naive_solver.
  Qed.

  Lemma mod_link_step_right_recv_i R m1 m2 s σ1 σ2 e P `{!TStepI m2 σ2 P} :
    TStepI (mod_link R m1 m2) (MLFRecvR e, s, σ1, σ2) (λ G, P (λ b κ P',
      match κ with
      | None => G b None (λ G', P' (λ x, G' (MLFRecvR e, s, σ1, x)))
      | Some κ' => κ' = (Incoming, e) → G b None (λ G', P' (λ x, G' (MLFRight, s, σ1, x)))
      end)).
  Proof.
    constructor => G /tstepi_proof?. clear TStepI0.
    apply: (steps_impl_submodule _ (mod_link _ _ _) (λ x, (MLFRecvR e, s, σ1, x))); [done| |].
    - naive_solver.
    - move => /= ??? Hs. invert_all' @state_transform_step; simplify_eq. invert_all' @m_step; simplify_eq/=.
      + case_match; simplify_eq. naive_solver.
      + case_match; simplify_eq. invert_all @mod_link_filter; naive_solver.
  Qed.

  Lemma mod_link_step_none_i R m1 m2 s σ1 σ2 :
    TStepI (mod_link R m1 m2) (MLFNone, s, σ1, σ2) (λ G, ∀ e p' s' e', R SPNone s e p' s' e' →
      G true (Some (Incoming, e')) (λ G', G' (mod_link_to_state p' e', s', σ1, σ2))).
  Proof.
    constructor => G HG. apply steps_impl_step_end => ???.
    invert_all' @m_step; simplify_eq/=; invert_all' mod_link_filter; simplify_eq/=.
    split!; [naive_solver|done|] => /= ??. eexists (_, _, _, _). split!. by destruct s0.
  Qed.

  Lemma mod_link_step_left_s R m1 m2 s σ1 σ2 P `{!TStepS m1 σ1 P} :
    TStepS (mod_link R m1 m2) (MLFLeft, s, σ1, σ2) (λ G, P (λ κ P',
      match κ with
      | None => G None (λ G', P' (λ x, G' (MLFLeft, s, x, σ2)))
      | Some (Outgoing, e) => ∃ p' s' e', R SPLeft s e p' s' e' ∧
                              G (if p' is SPNone then Some (Outgoing, e') else None)
                               (λ G', P' (λ σ', G' (mod_link_to_state p' e', s', σ', σ2)))
      | Some _ => False
      end)).
  Proof.
    constructor => G /tsteps_proof [κ [? [? HG']]]. clear TStepS0.
    destruct κ as [[[] e]|] => //; destruct_all?.
    all: eexists _, _; split; [done|] => G' /= /HG'?; tstep_s.
    all: split!; [..|apply: steps_spec_mono; [done|]] => //=; try by econs.
    all: move => ?? [[[p?]?]?]//=?; destruct p => //; by simplify_eq/=.
  Qed.

  Lemma mod_link_step_right_s R m1 m2 s σ1 σ2 P `{!TStepS m2 σ2 P} :
    TStepS (mod_link R m1 m2) (MLFRight, s, σ1, σ2) (λ G, P (λ κ P',
      match κ with
      | None => G None (λ G', P' (λ x, G' (MLFRight, s, σ1, x)))
      | Some (Outgoing, e) => ∃ p' s' e', R SPRight s e p' s' e' ∧
                              G (if p' is SPNone then Some (Outgoing, e') else None)
                               (λ G', P' (λ σ', G' (mod_link_to_state p' e', s', σ1, σ')))
      | Some _ => False
      end)).
  Proof.
    constructor => G /tsteps_proof [κ [? [? HG']]]. clear TStepS0.
    destruct κ as [[[] e]|] => //; destruct_all?.
    all: eexists _, _; split; [done|] => G' /= /HG'?; tstep_s.
    all: split!; [..|apply: steps_spec_mono; [done|]] => //=; try by econs.
    all: move => ?? [[[p?]?]?]//=?; destruct p => //; by simplify_eq/=.
  Qed.

  Lemma mod_link_step_left_recv_s R m1 m2 s σ1 σ2 e P `{!TStepS m1 σ1 P} :
    TStepS (mod_link R m1 m2) (MLFRecvL e, s, σ1, σ2) (λ G, P (λ κ P',
      match κ with
      | None => G None (λ G', P' (λ x, G' (MLFRecvL e, s, x, σ2)))
      | Some (Incoming, e') => G None (λ G', e = e' ∧ P' (λ x, G' (MLFLeft, s, x, σ2)))
      | Some _ => False
      end)).
  Proof.
    constructor => G /tsteps_proof [κ [? [? HG']]]. clear TStepS0.
    destruct κ as [[[] e']|] => //; destruct_all?.
    all: eexists _, _; split; [done|] => G' /=; try move => [?]; move => /HG'?; tstep_s; simplify_eq.
    all: split!; [..|apply: steps_spec_mono; [done|]] => //=; try by econs.
    all: move => ?? [[[p?]?]?]//=?; destruct p => //; by simplify_eq/=.
  Qed.

  Lemma mod_link_step_right_recv_s R m1 m2 s σ1 σ2 e P `{!TStepS m2 σ2 P} :
    TStepS (mod_link R m1 m2) (MLFRecvR e, s, σ1, σ2) (λ G, P (λ κ P',
      match κ with
      | None => G None (λ G', P' (λ x, G' (MLFRecvR e, s, σ1, x)))
      | Some (Incoming, e') => G None (λ G', e = e' ∧ P' (λ x, G' (MLFRight, s, σ1, x)))
      | Some _ => False
      end)).
  Proof.
    constructor => G /tsteps_proof [κ [? [? HG']]]. clear TStepS0.
    destruct κ as [[[] e']|] => //; destruct_all?.
    all: eexists _, _; split; [done|] => G' /=; try move => [?]; move => /HG'?; tstep_s; simplify_eq.
    all: split!; [..|apply: steps_spec_mono; [done|]] => //=; try by econs.
    all: move => ?? [[[p?]?]?]//=?; destruct p => //; by simplify_eq/=.
  Qed.

  Lemma mod_link_step_none_s R m1 m2 s σ1 σ2 :
    TStepS (mod_link R m1 m2) (MLFNone, s, σ1, σ2) (λ G, ∃ e p' s' e', R SPNone s e p' s' e' ∧
      G (Some (Incoming, e')) (λ G', G' (mod_link_to_state p' e', s', σ1, σ2))).
  Proof.
    constructor => G [?[?[?[?[??]]]]]. split!; [done|] => /=??.
    tstep_s. split!; [by econs|]. move => [[[??]?]?] /=. unfold mod_link_to_state.
    repeat case_match; naive_solver.
  Qed.
End mod_link.
Arguments mod_link_trans _ _ _ _ _ /.
Arguments mod_link_state : clear implicits.

Global Hint Resolve
       mod_link_step_left_i
       mod_link_step_right_i
       mod_link_step_left_recv_i
       mod_link_step_right_recv_i
       mod_link_step_none_i
       mod_link_step_left_s
       mod_link_step_right_s
       mod_link_step_left_recv_s
       mod_link_step_right_recv_s
       mod_link_step_none_s
| 2 : tstep.
