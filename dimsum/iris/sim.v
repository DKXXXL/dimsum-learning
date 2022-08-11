From iris.bi Require Import bi fixpoint.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Export fancy_updates.
From iris.base_logic.lib Require Export ghost_var.
From iris.bi Require Export weakestpre.
From dimsum.core Require Export module trefines.
From dimsum.core.iris Require Export ord_later.
Set Default Proof Using "Type".

Definition option_prefix {A} (o1 o2 : option A) : Prop :=
  match o1 with
  | Some x1 => o2 = Some x1
  | None => True
  end.

Definition option_drop {A} (o1 o2 : option A) : option A :=
  match o1 with
  | Some _ => None
  | None => o2
  end.

Lemma option_prefix_option_trace {A} (κ1 κ2 : option A) :
  option_prefix κ1 κ2 →
  option_trace κ2 = tapp (option_trace κ1) (option_trace (option_drop κ1 κ2)).
Proof. destruct κ1, κ2 => //=; naive_solver. Qed.

(** * [sim_steps] *)
Section sim_steps.
  Context {Σ : gFunctors} {EV : Type} `{!invGS_gen HasNoLc Σ}.
  Context (m : mod_trans EV).

  Definition sim_steps_pre
    (sim_steps : leibnizO (m.(m_state)) -d> leibnizO (option EV) -d>
                   (leibnizO (m.(m_state)) -d> iPropO Σ) -d> iPropO Σ) :
    leibnizO (m.(m_state)) -d> leibnizO (option EV) -d>
      (leibnizO (m.(m_state)) -d> iPropO Σ) -d> iPropO Σ := λ σ κ Φ,
  (|={∅}=> (⌜κ = None⌝ ∗ Φ σ) ∨
        ∃ κ' Pσ, ⌜σ ~{m, option_trace κ'}~>ₜ Pσ⌝ ∗ ⌜option_prefix κ' κ⌝ ∗
         ∀ σ', ⌜Pσ σ'⌝ ={∅}=∗ sim_steps σ' (option_drop κ' κ) Φ)%I.

  Global Instance sim_steps_pre_ne n:
    Proper ((dist n ==> dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n ==> dist n) sim_steps_pre.
  Proof.
    move => ?? Hsim ?? -> ?? -> ?? HΦ. rewrite /sim_steps_pre.
    repeat (f_equiv || eapply Hsim || eapply HΦ || reflexivity).
  Qed.

  Lemma sim_steps_pre_mono sim1 sim2:
    ⊢ □ (∀ σ κ Φ, sim1 σ κ Φ -∗ sim2 σ κ Φ)
    → ∀ σ κ Φ , sim_steps_pre sim1 σ κ Φ -∗ sim_steps_pre sim2 σ κ Φ.
  Proof.
    iIntros "#Hinner" (σ κ Φ) "Hsim".
    iMod "Hsim" as "[[% ?]|[% [% [% [% Hsim]]]]]"; [by iLeft; iFrame| iRight].
    iModIntro. iExists _, _. iSplit; [done|]. iSplit; [done|].
    iIntros (??). iMod ("Hsim" with "[//]"). iModIntro. by iApply "Hinner".
  Qed.

  Local Instance sim_steps_pre_monotone :
    BiMonoPred (λ sim_steps : prodO (prodO (leibnizO (m.(m_state))) (leibnizO (option EV))) ((leibnizO (m.(m_state))) -d> iPropO Σ) -d> iPropO Σ, uncurry3 (sim_steps_pre (curry3 sim_steps))).
  Proof.
    constructor.
    - iIntros (Φ Ψ ??) "#Hinner". iIntros ([[??]?]) "Hsim" => /=. iApply sim_steps_pre_mono; [|done].
      iIntros "!>" (???) "HΦ". by iApply ("Hinner" $! (_, _, _)).
    - move => sim_steps Hsim n [[σ1 κ1] Φ1] [[σ2 κ2] Φ2] /= [[/=??]?].
      apply sim_steps_pre_ne; eauto. move => ????????? /=. by apply: Hsim.
  Qed.

  Definition sim_steps : m.(m_state) → option EV → (m.(m_state) → iProp Σ) → iProp Σ :=
    curry3 (bi_least_fixpoint (λ sim_steps : prodO (prodO (leibnizO (m.(m_state))) (leibnizO (option EV))) ((leibnizO (m.(m_state))) -d> iPropO Σ) -d> iPropO Σ, uncurry3 (sim_steps_pre (curry3 sim_steps)))).

  Global Instance sim_steps_ne n:
    Proper ((=) ==> (=) ==> ((=) ==> dist n) ==> dist n) sim_steps.
  Proof. move => ?? -> ?? -> ?? HΦ. unfold sim_steps. f_equiv. intros ?. by apply HΦ. Qed.
End sim_steps.

Notation " σ '≈{' m , κ '}≈>' P " := (sim_steps m σ κ P)
  (at level 70, format "σ  '≈{'  m ,  κ  '}≈>'  P ") : bi_scope.

Section sim_steps.
  Context {Σ : gFunctors} {EV : Type} `{!invGS_gen HasNoLc Σ}.
  Context (m : mod_trans EV).
  Implicit Types Φ : m.(m_state) → iProp Σ.

  Local Existing Instance sim_steps_pre_monotone.
  Lemma sim_steps_unfold σ κ Φ:
    σ ≈{ m, κ }≈> Φ ⊣⊢ sim_steps_pre m (sim_steps m) σ κ Φ.
  Proof. rewrite /sim_steps /curry3. apply: least_fixpoint_unfold. Qed.

  Lemma sim_steps_strong_ind (R: leibnizO (m.(m_state)) -d> leibnizO (option EV) -d> (leibnizO (m.(m_state)) -d> iPropO Σ) -d> iPropO Σ):
    NonExpansive3 R →
    ⊢ (□ ∀ σ κ Φ, sim_steps_pre m (λ σ κ Ψ, R σ κ Ψ ∧ σ ≈{ m, κ }≈> Ψ) σ κ Φ -∗ R σ κ Φ)
      -∗ ∀ σ κ Φ, σ ≈{ m, κ }≈> Φ -∗ R σ κ Φ.
  Proof.
    iIntros (Hne) "#HPre". iIntros (σ κ Φ) "Hsim".
    rewrite {2}/sim_steps {1}/curry3.
    iApply (least_fixpoint_ind _ (uncurry3 R) with "[] Hsim").
    iIntros "!>" ([[??]?]) "Hsim" => /=. by iApply "HPre".
  Qed.

  Lemma sim_steps_ind (R: leibnizO (m.(m_state)) -d> leibnizO (option EV) -d> (leibnizO (m.(m_state)) -d> iPropO Σ) -d> iPropO Σ) :
    NonExpansive3 R →
    ⊢ (□ ∀ σ κ Φ, sim_steps_pre m R σ κ Φ -∗ R σ κ Φ)
      -∗ ∀ σ κ Φ, σ ≈{ m, κ }≈> Φ -∗ R σ κ Φ.
  Proof.
    iIntros (Hne) "#HPre". iApply sim_steps_strong_ind. iIntros "!>" (σ κ Φ) "Hsim".
    iApply "HPre". iApply (sim_steps_pre_mono with "[] Hsim").
    iIntros "!>" (???) "[? _]". by iFrame.
  Qed.

  Lemma sim_steps_wand_strong σ κ Φ Ψ:
    σ ≈{ m, κ }≈> Φ -∗
    (∀ σ, Φ σ ={∅}=∗ Ψ σ) -∗
    σ ≈{ m, κ }≈> Ψ.
  Proof.
    iIntros "Hsim Hwand".
    pose (F := (λ σ κ Ψ, ∀ Φ, (∀ σ', Ψ σ' ={∅}=∗ Φ σ') -∗ σ ≈{ m, κ }≈> Φ)%I).
    iAssert (∀ Φ, σ ≈{ m, κ }≈> Φ -∗ F σ κ Φ)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"). done. }
    iIntros (?) "Hsim".
    iApply (sim_steps_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (?? ?) "Hsim". iIntros (?) "Hc".
    rewrite sim_steps_unfold. iMod "Hsim" as "[[% ?]|[% [% [% [% Hsim]]]]]"; [iLeft| iRight].
    - iMod ("Hc" with "[$]") as "$". done.
    - iModIntro. iExists _, _. iSplit; [done|]. iSplit; [done|].
      iIntros (??). iMod ("Hsim" with "[//]") as "Hsim". iModIntro. by iApply "Hsim".
  Qed.

  Lemma sim_steps_wand σ κ Φ Ψ:
    σ ≈{ m, κ }≈> Φ -∗
    (∀ σ, Φ σ -∗ Ψ σ) -∗
    σ ≈{ m, κ }≈> Ψ.
  Proof.
    iIntros "Hsim Hwand".
    iApply (sim_steps_wand_strong with "Hsim"). iIntros (?) "?". iModIntro. by iApply "Hwand".
  Qed.

  Lemma sim_steps_stop σ Φ :
    Φ σ -∗
    σ ≈{ m, None }≈> Φ.
  Proof. iIntros "?". rewrite sim_steps_unfold. iLeft. by iFrame. Qed.

  Lemma sim_steps_step κ' Pσ κ σ Φ :
    σ ~{m, option_trace κ'}~>ₜ Pσ →
    option_prefix κ' κ →
    (∀ σ', ⌜Pσ σ'⌝ ={∅}=∗ σ' ≈{ m, option_drop κ' κ }≈> Φ) -∗
    σ ≈{ m, κ }≈> Φ.
  Proof.
    iIntros (??) "HΦ". rewrite sim_steps_unfold.
    iRight. iModIntro. iExists _, _. iSplit; [done|]. iSplit; [done|].
    iIntros (??). by iMod ("HΦ" with "[//]").
  Qed.

  (* One should be able to get rid of the [HasNoLc] if one uses classical logic. *)
  (* TODO: Is it possible to get a stronger adequacy lemma? *)
  Lemma sim_steps_elim E Pσ κ σ Φ κs :
    σ ≈{ m, κ }≈> Φ -∗
    (∀ σ', Φ σ' -∗ |={E}=> ⌜σ' ~{m, κs}~>ₜ Pσ⌝ ) -∗
    |={E}=> ⌜σ ~{m, tapp (option_trace κ) κs}~>ₜ Pσ⌝.
  Proof.
    iIntros "Hsim HΦ".
    pose (F := (λ σ κ Φ,
      (∀ σ', Φ σ' -∗ |={E}=> ⌜σ' ~{m, κs}~>ₜ Pσ⌝ ) -∗
        |={E}=> ⌜σ ~{m, tapp (option_trace κ) κs}~>ₜ Pσ⌝)%I).
    iAssert (∀ Φ, σ ≈{ m, κ }≈> Φ -∗ F σ κ Φ)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"). done. }
    iIntros (?) "Hsim".
    iApply (sim_steps_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (?? ?) "Hsim". iIntros "Hc".
    iMod (fupd_mask_subseteq ∅) as "He"; [set_solver|].
    iMod "Hsim" as "[[% ?]|[% [% [% [% Hsim]]]]]"; iMod "He" as "_".
    { subst. by iApply "Hc". }
    erewrite option_prefix_option_trace; [|done]. rewrite -assoc_L.
    iApply (fupd_mono _ _ ⌜_⌝). { iPureIntro. by apply thas_trace_trans. }
    iIntros (??).
    iMod (fupd_mask_subseteq ∅) as "He"; [set_solver|].
    iMod ("Hsim" with "[//]") as "Hsim". iMod "He" as "_".
    by iApply "Hsim".
  Qed.
End sim_steps.

(** * mod_lang *)
Structure mod_lang EV Σ := ModLang {
  mexpr : Type;
  mtrans : mod_trans EV;
  mexpr_rel : mtrans.(m_state) → mexpr → Prop;
  mstate_interp : mtrans.(m_state) → iProp Σ;
}.
Global Arguments mexpr {_ _} _.
Global Arguments mtrans {_ _} _.
Global Arguments mexpr_rel {_ _} _ _ _.
Global Arguments mstate_interp {_ _} _ _.

Definition mexprO {Σ EV} {Λ : mod_lang Σ EV} := leibnizO (mexpr Λ).

(** * dimsumGS *)
Class dimsumPreG (Σ : gFunctors) (E_s : Type) := RefirisPreG {
  dimsum_pre_invG :> invGpreS Σ;
  dimsum_pre_ord_laterG :> ord_laterPreG Σ;
  dimsum_pre_ghost_varG_s :> ghost_varG Σ E_s;
}.

Class dimsumGS (EV : Type) (Σ : gFunctors) (Λ_t Λ_s : mod_lang EV Σ) := DimsumGS {
  dimsum_invGS :> invGS_gen HasNoLc Σ;
  dimsum_ord_laterGS :> ord_laterGS Σ;
  dimsum_ghost_varG_s :> ghost_varG Σ (mexpr Λ_s);
  dimsum_ghost_var_s_name : gname;
}.
Global Opaque dimsum_invGS.

(** * [sim_expr_s] *)
Definition sim_expr_s `{!dimsumGS EV Σ Λ_t Λ_s} (q : Qp) (e : mexpr Λ_s) : iProp Σ :=
  ghost_var dimsum_ghost_var_s_name q e.

Notation "'⤇{' q } e" := (sim_expr_s q e)
  (at level 20, format "'⤇{' q }  e") : bi_scope.
Notation "'⤇' e" := (sim_expr_s (1/2) e)
  (at level 20, format "'⤇'  e") : bi_scope.
Notation "'⤇?' e" := (if e is Some e' then sim_expr_s (1/2) e' else True)%I
  (at level 20, format "'⤇?'  e") : bi_scope.

Section sim_expr.
  Context `{!dimsumGS EV Σ Λ_t Λ_s}.

  Lemma sim_expr_s_agree e1 e2 :
    ⤇ e1 -∗ ⤇ e2 -∗ ⌜e1 = e2⌝.
  Proof. iIntros "??". by iDestruct (ghost_var_agree with "[$] [$]") as %->. Qed.

  Lemma sim_expr_s_update e' e1 e2 :
    ⤇ e1 -∗ ⤇ e2 ==∗ ⤇ e' ∗ ⤇ e'.
  Proof. iApply ghost_var_update_halves. Qed.
End sim_expr.

(** * [sim_pre] *)
Definition sim_pre `{!dimsumGS EV Σ Λ_t Λ_s}
    (sim : leibnizO coPset -d> mexprO -d> (mexprO -d> iPropO Σ) -d> iPropO Σ) :
    leibnizO coPset -d> mexprO -d> (mexprO -d> iPropO Σ) -d> iPropO Σ := λ E e_t Φ,
  (∀ σ_t σ_s e_s, ⌜mexpr_rel Λ_t σ_t e_t⌝ -∗ ⌜mexpr_rel Λ_s σ_s e_s⌝ -∗ ord_later_ctx -∗
              ⤇ e_s -∗ mstate_interp Λ_t σ_t -∗ mstate_interp Λ_s σ_s ={E}=∗
      (⤇ e_s ∗ mstate_interp Λ_t σ_t ∗
         mstate_interp Λ_s σ_s ∗ Φ e_t) ∨
      (∀ κ Pσ_t, ⌜(mtrans Λ_t).(m_step) σ_t κ Pσ_t⌝ ={E,∅}=∗ ▷ₒ
         (σ_s ≈{ mtrans Λ_s, κ }≈> (λ σ_s', ∃ σ_t' e_t' e_s', ⌜Pσ_t σ_t'⌝ ∗
            ⌜mexpr_rel Λ_t σ_t' e_t'⌝ ∗ ⌜mexpr_rel Λ_s σ_s' e_s'⌝ ∗ ⤇ e_s' ∗
            |={∅, E}=> mstate_interp Λ_t σ_t' ∗ mstate_interp Λ_s σ_s' ∗ sim E e_t' Φ)))
      ∨ |={E,∅}=> σ_s ≈{ mtrans Λ_s, None }≈> (λ σ_s', ∃ e_s', ⌜mexpr_rel Λ_s σ_s' e_s'⌝ ∗ ⤇ e_s' ∗
            |={∅, E}=> mstate_interp Λ_t σ_t ∗ mstate_interp Λ_s σ_s' ∗ sim E e_t Φ))%I.

Global Instance sim_pre_ne `{!dimsumGS EV Λ_t Λ_s Σ} n:
  Proper ((dist n ==> dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n ==> dist n) sim_pre.
Proof.
  move => ?? Hsim ?? -> ?? -> ?? HΦ. rewrite /sim_pre.
  repeat (f_equiv || eapply Hsim || eapply HΦ || reflexivity || intros ?? ->).
Qed.

Lemma sim_pre_mono `{!dimsumGS EV Λ_t Λ_s Σ} sim1 sim2:
  ⊢ □ (∀ E e_t Φ, sim1 E e_t Φ -∗ sim2 E e_t Φ )
  → ∀ E e_t Φ , sim_pre sim1 E e_t Φ -∗ sim_pre sim2 E e_t Φ.
Proof.
  iIntros "#Hinner" (E e_t Φ) "Hsim".
  iIntros (σ_t σ_s e_s ??) "#? ? Hσ_t Hσ_s".
  iMod ("Hsim" with "[//] [//] [//] [$] Hσ_t Hσ_s") as "[Hsim|[Hsim|Hsim]]";
    [by iLeft|iRight; iLeft| iRight; iRight].
  - iModIntro. iIntros (κ Pσ_t ?). iMod ("Hsim" with "[//]") as "Hsim". do 2 iModIntro.
    iApply (sim_steps_wand with "Hsim"). iIntros (?) "(%&%&%&%&%&%&?&Hsim)".
    iSplit!; [done..|]. iFrame. iMod "Hsim" as "[? [??]]". iModIntro. iFrame. by iApply "Hinner".
  - iModIntro. iMod "Hsim" as "Hsim". iModIntro.
    iApply (sim_steps_wand with "Hsim"). iIntros (?) "(%&%&?&Hsim)".
    iExists _. iSplit; [done|]. iFrame. iMod "Hsim" as "[? [??]]". iModIntro. iFrame. by iApply "Hinner".
Qed.

Local Instance sim_pre_monotone `{!dimsumGS EV Σ Λ_t Λ_s} :
  BiMonoPred (λ sim : prodO (prodO (leibnizO coPset) mexprO) (mexprO -d> iPropO Σ) -d> iPropO Σ, uncurry3 (sim_pre (curry3 sim))).
Proof.
  constructor.
  - iIntros (Φ Ψ ??) "#Hinner". iIntros ([[??]?]) "Hsim" => /=. iApply sim_pre_mono; [|done].
    iIntros "!>" (???) "HΦ". by iApply ("Hinner" $! (_, _, _)).
  - move => sim Hsim n [[E1 e_t1] Φ1] [[E2 e_t2] Φ2] /= [[/=??]?].
    apply sim_pre_ne; eauto. move => ????????? /=. by apply: Hsim.
Qed.

Definition sim_def `{!dimsumGS EV Σ Λ_t Λ_s} : coPset → mexpr Λ_t → (mexpr Λ_t → iProp Σ) → iProp Σ :=
  curry3 (bi_least_fixpoint (λ sim : prodO (prodO (leibnizO coPset) mexprO) (mexprO -d> iPropO Σ) -d> iPropO Σ, uncurry3 (sim_pre (curry3 sim)))).
Definition sim_aux : seal (@sim_def). Proof. by eexists. Qed.
Definition sim := sim_aux.(unseal).
Global Arguments sim {EV Σ Λ_t Λ_s _}.
Lemma sim_eq `{!dimsumGS EV Σ Λ_t Λ_s} : sim = @sim_def EV Σ Λ_t Λ_s _.
Proof. rewrite -sim_aux.(seal_eq) //. Qed.

Notation "'TGT' et @ E {{ Φ } }" := (sim E et Φ%I) (at level 70, Φ at level 200,
  format "'[hv' 'TGT'  et  '/' @  E  {{  '[ ' Φ  ']' } } ']'") : bi_scope.

(** * [sim_both] *)
Definition sim_both `{!dimsumGS EV Σ Λ_t Λ_s} (E : coPset) (e_t : mexpr Λ_t) (e_s : mexpr Λ_s) (Φ : mexpr Λ_t → mexpr Λ_s → iProp Σ) : iProp Σ :=
  ⤇ e_s -∗ TGT e_t @ E {{ λ e_t', ∃ e_s', ⤇ e_s' ∗ Φ e_t' e_s' }}.
Notation "et '⪯{' E '}' es {{ Φ } }" := (sim_both E et es Φ%I) (at level 70, Φ at level 200,
  format "'[hv' et  '/' '⪯{' E '}'  '/' es  '/' {{  '[ ' Φ  ']' } } ']'") : bi_scope.

(** * [sim_src] *)
Definition sim_src `{!dimsumGS EV Σ Λ_t Λ_s}
  (E : coPset) (κ : option EV) (e_s : mexpr Λ_s) (Φ : mexpr Λ_s → iProp Σ) : iProp Σ :=
  ∀ σ_s, ⌜mexpr_rel Λ_s σ_s e_s⌝ -∗ ord_later_ctx -∗ mstate_interp Λ_s σ_s ={E,∅}=∗
    σ_s ≈{ mtrans Λ_s, κ }≈> (λ σ_s', ∃ e_s', ⌜mexpr_rel Λ_s σ_s' e_s'⌝ ∗
       |={∅, E}=> mstate_interp Λ_s σ_s' ∗ Φ e_s').

Notation "'SRC' e @ κ ; E {{ Φ } }" := (sim_src E κ e Φ%I) (at level 70, Φ at level 200,
  format "'[hv' 'SRC'  e  '/' @  κ ;  E  {{  '[ ' Φ  ']' } } ']'") : bi_scope.

Notation "'SRC' e @ E {{ Φ } }" := (sim_src E None e Φ%I) (at level 70, Φ at level 200,
  format "'[hv' 'SRC'  e  '/' @  E  {{  '[ ' Φ  ']' } } ']'") : bi_scope.


Section sim.
Context `{!dimsumGS EV Σ Λ_t Λ_s}.
Implicit Types P : iProp Σ.

(** * Lemmas about [sim] *)
Lemma sim_unfold E e_t Φ:
  TGT e_t @ E {{ Φ }} ⊣⊢ sim_pre sim E e_t Φ.
Proof. rewrite sim_eq /sim_def /curry3. apply: least_fixpoint_unfold. Qed.

Lemma sim_strong_ind (R: leibnizO coPset -d> mexprO -d> (mexprO -d> iPropO Σ) -d> iPropO Σ):
  NonExpansive3 R →
  ⊢ (□ ∀ E e_t Φ, sim_pre (λ E e_t Ψ, R E e_t Ψ ∧ TGT e_t @ E {{ Ψ }}) E e_t Φ -∗ R E e_t Φ)
    -∗ ∀ E e_t Φ, TGT e_t @ E {{ Φ }} -∗ R E e_t Φ.
Proof.
  iIntros (Hne) "#HPre". iIntros (E e_t Φ) "Hsim".
  rewrite sim_eq {2}/sim_def {1}/curry3.
  iApply (least_fixpoint_ind _ (uncurry3 R) with "[] Hsim").
  iIntros "!>" ([[??]?]) "Hsim" => /=. by iApply "HPre".
Qed.

Lemma sim_ind (R: leibnizO coPset -d> mexprO -d> (mexprO -d> iPropO Σ) -d> iPropO Σ):
  NonExpansive3 R →
  ⊢ (□ ∀ E e_t Φ, sim_pre R E e_t Φ -∗ R E e_t Φ)
    -∗ ∀ E e_t Φ, TGT e_t @ E {{ Φ }} -∗ R E e_t Φ .
Proof.
  iIntros (Hne) "#HPre". iApply sim_strong_ind. iIntros "!>" (E e_t Φ) "Hsim".
  iApply "HPre". iApply (sim_pre_mono with "[] Hsim").
  iIntros "!>" (???) "[? _]". by iFrame.
Qed.

Lemma sim_wand e_t E Φ Ψ:
  TGT e_t @ E {{ Φ }} -∗
  (∀ e_t, Φ e_t -∗ Ψ e_t) -∗
  TGT e_t @ E {{ Ψ }}.
Proof.
  iIntros "Hsim Hwand".
  pose (F := (λ E e_t Ψ, ∀ Φ, (∀ e_t', Ψ e_t' -∗ Φ e_t') -∗ TGT e_t @ E {{ Φ }})%I).
  iAssert (∀ Φ, TGT e_t @ E {{ Φ }} -∗ F E e_t Φ)%I as "Hgen"; last first.
  { iApply ("Hgen" with "Hsim"). done. }
  iIntros (?) "Hsim".
  iApply (sim_ind with "[] Hsim"). { solve_proper. }
  iIntros "!>" (?? ?) "Hsim". iIntros (?) "Hc".
  rewrite sim_unfold. iIntros (?????) "#? ? Hσ_t Hσ_s".
  iMod ("Hsim" with "[//] [//] [$] [$] Hσ_t Hσ_s") as "[[?[?[??]]]|[Hsim|Hsim]]".
  - iModIntro. iLeft. iFrame. by iApply "Hc".
  - iModIntro. iRight. iLeft. iIntros (???). iMod ("Hsim" with "[//]") as "Hsim". do 2 iModIntro.
    iApply (sim_steps_wand with "Hsim"). iIntros (?) "(%&%&%&%&%&%&?&Hsim)".
    iSplit!; [done..|]. iFrame. iMod "Hsim" as "[? [?Hsim]]". iModIntro. iFrame. by iApply "Hsim".
  - iModIntro. iRight. iRight. iMod "Hsim" as "Hsim". iModIntro.
    iApply (sim_steps_wand with "Hsim"). iIntros (?) "(%&%&?&Hsim)".
    iExists _. iSplit; [done|]. iFrame. iMod "Hsim" as "[? [?Hsim]]". iModIntro. iFrame. by iApply "Hsim".
Qed.

Lemma sim_bind e_t E Φ:
  TGT e_t @ E {{ λ e_t', TGT e_t' @ E {{ Φ }} }} -∗
  TGT e_t @ E {{ Φ }}.
Proof.
  iIntros "Hsim".
  pose (F := (λ E e_t Ψ, ∀ Φ, (∀ e_t', Ψ e_t' -∗ TGT e_t' @ E {{ Φ }}) -∗ TGT e_t @ E {{ Φ }})%I).
  iAssert (∀ Φ, TGT e_t @ E {{ Φ }} -∗ F E e_t Φ)%I as "Hgen"; last first.
  { iApply ("Hgen" with "Hsim"). iIntros (?) "?". done. }
  iIntros (?) "Hsim".
  iApply (sim_ind with "[] Hsim"). { solve_proper. }
  iIntros "!>" (?? ?) "Hsim". iIntros (?) "Hc".
  rewrite sim_unfold. iIntros (?????) "#? ? Hσ_t Hσ_s".
  iMod ("Hsim" with "[//] [//] [$] [$] Hσ_t Hσ_s") as "[[?[?[??]]]|[Hsim|Hsim]]".
  - iDestruct ("Hc" with "[$]") as "Hc". rewrite {1}sim_unfold.
    iApply ("Hc" with "[//] [//] [$] [$] [$] [$]").
  - iModIntro. iRight. iLeft. iIntros (???). iMod ("Hsim" with "[//]") as "Hsim". do 2 iModIntro.
    iApply (sim_steps_wand with "Hsim"). iIntros (?) "(%&%&%&%&%&%&?&Hsim)".
    iSplit!; [done..|]. iFrame. iMod "Hsim" as "[? [?Hsim]]". iModIntro. iFrame. by iApply "Hsim".
  - iModIntro. iRight. iRight. iMod "Hsim" as "Hsim". iModIntro.
    iApply (sim_steps_wand with "Hsim"). iIntros (?) "(%&%&?&Hsim)".
    iExists _. iSplit; [done|]. iFrame. iMod "Hsim" as "[? [?Hsim]]". iModIntro. iFrame. by iApply "Hsim".
Qed.

Lemma sim_stop E e_t Φ:
  Φ e_t -∗ TGT e_t @ E {{ Φ }}.
Proof. rewrite sim_unfold. iIntros "HΦ" (σ_t σ_s e_s' ??) "? ? Hσ_t Hσ_s". iLeft. by iFrame. Qed.

(** * Lemmas about [sim_both] *)
Lemma sim_both_to_tgt E e_t e_s Φ:
  (⤇ e_s -∗ TGT e_t @ E {{ λ e_t', ∃ e_s', ⤇ e_s' ∗ Φ e_t' e_s' }}) -∗ e_t ⪯{E} e_s {{ Φ }}.
Proof. done. Qed.

Lemma sim_tgt_to_both E e_t e_s Φ:
  ⤇ e_s -∗
  e_t ⪯{E} e_s {{ λ e_t' e_s', ⤇ e_s' -∗ Φ e_t' }} -∗
  TGT e_t @ E {{ Φ }}.
Proof.
  iIntros "He Hsim".
  iDestruct ("Hsim" with "He") as "Hsim".
  iApply (sim_wand with "Hsim"). iIntros (?) "[%[? Hsim]]".
  by iApply "Hsim".
Qed.

Lemma sim_both_stop E e_t e_s Φ:
  Φ e_t e_s -∗ e_t ⪯{E} e_s {{ Φ }}.
Proof. iIntros "HΦ ?". iApply sim_stop. iExists _. iFrame. Qed.

(** * Lemmas about [sim_src] *)
Lemma sim_tgt_to_src E e_t e_s Φ:
  ⤇ e_s -∗
  SRC e_s @ E {{ λ e_s', ⤇ e_s' -∗ TGT e_t @ E {{ Φ }} }} -∗
  TGT e_t @ E {{ Φ }}.
Proof.
  iIntros "He Hsim".
  rewrite {2}sim_unfold. iIntros (?????) "#? ???". iModIntro.
  iDestruct (sim_expr_s_agree with "[$] [$]") as %->.
  iRight. iRight. iMod ("Hsim" with "[//] [$] [$]") as "Hsim".
  iModIntro. iApply (sim_steps_wand_strong with "Hsim"). iIntros (?) "(%&%&Hsim)".
  iMod (sim_expr_s_update with "[$] [$]") as "[? ?]". iModIntro.
  iExists _. iSplit; [done|]. iFrame.
  iMod "Hsim" as "[$ Hsim]". iModIntro. by iApply "Hsim".
Qed.

Lemma sim_src_stop E e_s Φ:
  Φ e_s -∗ SRC e_s @ E {{ Φ }}.
Proof.
  iIntros "HΦ" (σ_s ?) "??".
  iApply fupd_mask_intro; [set_solver|]. iIntros "He".
  iApply sim_steps_stop. iExists _. iSplit; [done|].
  iMod "He". by iFrame.
Qed.

Lemma sim_src_step E e_s Φ κ:
  (∀ σ_s, ⌜mexpr_rel Λ_s σ_s e_s⌝ -∗ mstate_interp Λ_s σ_s ==∗
    ∃ κ' Pσ_s, ⌜σ_s ~{mtrans Λ_s, option_trace κ'}~>ₜ Pσ_s⌝ ∗ ⌜option_prefix κ' κ⌝ ∗
     ∀ σ_s', ⌜Pσ_s σ_s'⌝ ={E}=∗ ∃ e_s', ⌜mexpr_rel Λ_s σ_s' e_s'⌝ ∗
       mstate_interp Λ_s σ_s' ∗ SRC e_s' @ option_drop κ' κ; E {{ Φ }}) -∗
  SRC e_s @ κ; E {{ Φ }}.
Proof.
  iIntros "HΦ" (σ_s ?) "??".
  iMod ("HΦ" with "[//] [$]") as (????) "HΦ".
  iApply fupd_mask_intro; [set_solver|]. iIntros "He".
  iApply sim_steps_step; [done..|]. iIntros (??).
  iMod "He" as "_". iMod ("HΦ" with "[//]") as (??) "[? HΦ]".
  iMod ("HΦ" with "[//] [$] [$]") as "HΦ". by iModIntro.
Qed.

Lemma sim_src_bind E e_s Φ κ:
  SRC e_s @ E {{ λ e_s', SRC e_s' @ κ; E {{ Φ }} }} -∗
  SRC e_s @ κ; E {{ Φ }}.
Proof.
Admitted.

(* From dimsum Require Import axioms. *)
(* Lemma thas_trace_post κs (m : mod_trans EV) σ1 Pσ2: *)
(*   σ1 ~{ m, κs }~>ₜ Pσ2 → *)
(*   ∃ Pσ2' σ,  *)
(*   σ1 ~{ m, κs }~>ₜ (λ _, False) ∨ ∃ σ, Pσ2 σ. *)
(* Proof. *)
(*   elim; clear. *)
(*   - naive_solver. *)
(*   - move => σ1 Pσ2 Pσ3 κ κs κs' ? ? IH ?. *)
(*     have [?|HF]:= AxClassic (∀ σ2 : m_state m, Pσ2 σ2 → σ2 ~{ m, κs' }~>ₜ (λ _ : m_state m, False)). *)
(*     + left. by tstep. *)
(*     + have [?|?]:= AxClassic (∃ σ2, Pσ2 σ2 ∧ ¬ σ2 ~{ m, κs' }~>ₜ (λ _ : m_state m, False)). *)
(*       naive_solver. *)
(*       exfalso. apply: HF => σ3?. *)
(*       have [//|?]:= AxClassic (σ3 ~{ m, κs' }~>ₜ (λ _ : m_state m, False)). naive_solver. *)
(*   - move => T f σ κs Pσ _ IH Hsub. *)
(*     have [[x ?]|?]:= AxClassic (∃ x : T, ¬ σ ~{ m, f x }~>ₜ (λ _, False)). naive_solver. *)
(*     left. eapply TTraceAll; [|done] => x. *)
(*     have [|]:= AxClassic (σ ~{ m, f x }~>ₜ (λ _ : m_state m, False)); naive_solver. *)
(* Qed. *)


(* TODO: Is this provable? Seems tricky since we need to go inside and
outside of pure quantifiers. So if this is not provable, it might be
necessary to define sim_src as a fixpoint. This would be a bit more
annoying for the adequacy proofs but should be fine. *)
(*
Lemma sim_src_bind E e_s Φ κ:
  SRC e_s @ E {{ λ e_s', SRC e_s' @ κ; E {{ Φ }} }} -∗
  SRC e_s @ κ; E {{ Φ }}.
Proof.
  iIntros "HΦ" (σ_s ?) "#??".
  iMod ("HΦ" with "[//] [$] [$]") as (? Ht) "Hsim".
  (* iExists (locked _). iSplitR. 2: { *)
    (* iModIntro. iIntros (? HP). unlock in HP. apply HP. } *)
  (* iModIntro. iPureIntro. apply: (thas_trace_trans tnil); [done|]. *)
  (* move => ??. unlock. *)
  iAssert (|={∅}=> ∃ Pσ_s0, ∀ σ_s', ⌜Pσ_s σ_s'⌝ -∗
                             ⌜σ_s' ~{ mtrans Λ_s, option_trace κ }~>ₜ Pσ_s0⌝ ∗ (∀ σ_s', ⌜Pσ_s0 σ_s'⌝ ={∅}=∗
         ∃ e_s', ⌜mexpr_rel Λ_s σ_s' e_s'⌝ ∗ (|={∅,E}=> mstate_interp Λ_s σ_s' ∗ Φ e_s')))%I
    with "[-]" as "Hs"; last first.
  { iMod "Hs" as (Pσ_s') "Hs". iModIntro. iExists Pσ_s'. iSplit. {
      admit: "provable".
    }
    iIntros (??). admit: "provable by discarding the first part of Hs".
  }
  admit: "How to swap these quantifiers?".
Abort.
*)
(*
  move: (Ht) => /thas_trace_post[?|[??]].
  { iModIntro. iExists (λ _, False). iSplit. { iPureIntro. by apply: (thas_trace_trans tnil). }
    by iIntros (??). }
  iMod ("Hsim" with "[//]") as (??) ">[? Hsim]".
  iMod ("Hsim" with "[//] [$] [$]") as (??) "?". iModIntro.
  iExists _. iSplit. { iPureIntro. apply: (thas_trace_trans tnil); [done|].

 iModIntro.

  iApply fupd_mask_intro; [set_solver|]. iIntros "He".
  iExists (σ_s =.). iSplit; [iPureIntro; tend|]. iIntros (? <-) "!>".
  iExists _. iSplit; [done|]. iMod "He". by iFrame.
Qed.
*)

(*
Lemma sim_step E e_t e_s Φ:
  (∀ σ_t σ_s κ Pσ_t, ⌜(mtrans Λ_t).(m_step) σ_t κ Pσ_t⌝ -∗ ⤇ₜ e_t -∗ ⤇ₛ e_s -∗ σ⤇ₜ σ_t -∗ σ⤇ₛ σ_s ={E,∅}=∗ ▷ₒ
      ∃ Pσ_s, ⌜σ_s ~{mtrans Λ_s, option_trace κ}~>ₜ Pσ_s⌝ ∗
         ∀ σ_s', ⌜Pσ_s σ_s'⌝ ={∅, E}=∗
           ∃ σ_t' e_t' e_s', ⌜Pσ_t σ_t'⌝ ∗ ⤇ₜ e_t' ∗ ⤇ₛ e_s' ∗ σ⤇ₜ σ_t' ∗ σ⤇ₛ σ_s' ∗ e_t' ⪯{E} e_s' {{ Φ }}) -∗
  e_t ⪯{E} e_s {{ Φ }}.
Proof.
  iIntros "Hsim".
  rewrite sim_unfold. iIntros (??) "#? ?? Hσ_t Hσ_s !>". iRight. iIntros (???).
  iMod ("Hsim" with "[//] [$] [$] [$] [$]") as "Hsim". do 2 iModIntro.
  iDestruct "Hsim" as (??) "Hsim". iExists _. iSplit; [done|].
  iIntros (??). iMod ("Hsim" with "[//]") as (????) "[? Hsim]".
  iModIntro. iSplit!; [done..|]. iFrame.
Qed.
*)

(*
Lemma sim_bind E e_t e_s Φ:
  e_t ⪯{E} e_s {{ λ e_t' e_s', e_t' ⪯{E} e_s' {{ Φ }} }} -∗ e_t ⪯{E} e_s {{ Φ }}.
Proof.
  iIntros "HΦ".
  pose (F := (λ E e_t e_s Ψ, ∀ Φ, (∀ e_t e_s, Ψ e_t e_s -∗ e_t ⪯{E} e_s {{ Φ }}) -∗ e_t ⪯{E} e_s {{ Φ }})%I).
  iAssert (∀ Φ, e_t ⪯{E} e_s {{ Φ }} -∗ F E e_t e_s Φ)%I as "Hgen"; last first.
  { iApply ("Hgen" with "HΦ"). iIntros (??) "$". }
  iIntros (?) "Hsim".
  iApply (sim_ind with "[] Hsim"). { solve_proper. }
  iIntros "!>" (????) "Hsim". iIntros (?) "Hc".
  rewrite sim_unfold. iIntros (??) "#? ?? Hσ_t Hσ_s".
  iMod ("Hsim" with "[//] [$] [$] Hσ_t Hσ_s") as "[[? [?[?[??]]]]|Hsim]".
  - iDestruct ("Hc" with "[$]") as "Hc". rewrite sim_unfold.
    iApply ("Hc" with "[//] [$] [$] [$] [$]").
  - iModIntro. iRight. iIntros (???). iMod ("Hsim" with "[//]") as "Hsim". do 2 iModIntro.
    iDestruct "Hsim" as (??) "Hsim".
    iExists _. iSplit; [done|]. iIntros (??). iMod ("Hsim" with "[//]") as (????) "[? [? [? [? HF]]]]".
    iModIntro. iSplit!; [done..|]. iFrame. by iApply "HF".
Qed.
*)

(*
Lemma sim_bind_src E e_t e_s Φ:
  sim_src E None e_s (λ e_t' e_s', e_t' ⪯{E} e_s' {{ Φ }}) -∗ e_t ⪯{E} e_s {{ Φ }}.
Proof.
  iIntros "Hsrc".
  rewrite sim_unfold. iIntros (??) "#? ?? Hσ_t Hσ_s".
  iModIntro. iRight.
  iIntros (???).
  iMod ("Hsrc" with "[$] [$] [$]") as (??) "Hsim". iModIntro.
  iMod ("Hsim" with "[//] [//] [//] [$] [$] Hσ_t Hσ_s") as "[[? [?[?[??]]]]|Hsim]".
  - iDestruct ("Hc" with "[$]") as "Hc". rewrite sim_unfold.
    iApply ("Hc" with "[//] [//] [//] [$] [$] [$] [$]").
  - iModIntro. iRight. iIntros (???). iMod ("Hsim" with "[//]") as "Hsim". do 2 iModIntro.
    iDestruct "Hsim" as (??) "Hsim".
    iExists _. iSplit; [done|]. iIntros (??). iMod ("Hsim" with "[//]") as (??????) "[? [? [? [? HF]]]]".
    iModIntro. iSplit!; [done..|]. iFrame. by iApply "HF".
Qed.
*)

End sim.

Theorem sim_adequacy Σ EV m_t m_s expr_t expr_s `{!dimsumPreG Σ expr_s} `{!Inhabited (expr_s)} :
  (∀ `{Hinv : !invGS_gen HasNoLc Σ} `{Hord : !ord_laterGS Σ} γ_s,
    ⊢ |={⊤}=>
     ∃ (expr_rel_t : (m_trans m_t).(m_state) → expr_t → Prop),
     ∃ (expr_rel_s : (m_trans m_s).(m_state) → expr_s → Prop),
     ∃ (stateI_t : (m_trans m_t).(m_state) → iProp Σ),
     ∃ (stateI_s : (m_trans m_s).(m_state) → iProp Σ),
       let Λ_t := ModLang EV Σ expr_t (m_trans m_t) expr_rel_t stateI_t in
       let Λ_s := ModLang EV Σ expr_s (m_trans m_s) expr_rel_s stateI_s in
       let _ : dimsumGS EV Σ Λ_t Λ_s := DimsumGS _ _ _ _ _ _ _ γ_s
       in
       ∃ e_t e_s,
       ⌜mexpr_rel Λ_t m_t.(m_init) e_t⌝ ∗ ⌜mexpr_rel Λ_s m_s.(m_init) e_s⌝ ∗
       stateI_t m_t.(m_init) ∗ stateI_s m_s.(m_init) ∗
       e_t ⪯{⊤} e_s {{ λ _ _, |={⊤, ∅}=> False }}) →
  trefines m_t m_s.
Proof.
  intros Hsim. constructor => κs /thas_trace_n [n Htrace].
  apply (step_fupdN_soundness_no_lc _ 0 0) => ? /=. simpl in *. iIntros "_".
  iMod (ord_later_alloc n) as (?) "Ha". iDestruct (ord_later_ctx_alloc with "Ha") as "#?".
  iMod (ghost_var_alloc inhabitant) as (γ_s) "Hs".
  iMod Hsim as "(% & % & %stateI_t & %stateI_s & % & % & %He_t & %He_s & Hσ_t & Hσ_s & Hsim)".
  clear Hsim.
  set (Λ_t := ModLang EV Σ expr_t (m_trans m_t) expr_rel_t stateI_t).
  set (Λ_s := ModLang EV Σ expr_s (m_trans m_s) expr_rel_s stateI_s).
  set (X := DimsumGS _ _ _ _ _ _ _ γ_s : dimsumGS EV Σ Λ_t Λ_s).
  iAssert (|==> ⤇ (e_s : mexpr Λ_s) ∗ ⤇ (e_s : mexpr Λ_s))%I with "[Hs]" as ">[He1 He2]".
  { by iMod (ghost_var_update e_s with "Hs") as "[$ $]". }
  pose (F := (λ E e_t Ψ,
               ∀ n κs σ_s σ_t e_s,
               ⌜σ_t ~{ m_trans m_t, κs, n }~>ₜ -⌝ -∗
               ⌜expr_rel_t σ_t e_t⌝ -∗
               ⌜expr_rel_s σ_s e_s⌝ -∗
               ⌜E = ⊤⌝ -∗
               ord_later_auth n -∗
               ⤇ (e_s : mexpr Λ_s) -∗
               stateI_t σ_t -∗
               stateI_s σ_s -∗
               (∀ e_t' : mexpr Λ_t, Ψ e_t' ={⊤,∅}=∗ False) -∗
               |={⊤,∅}=> ⌜σ_s ~{ m_trans m_s, κs }~>ₜ -⌝)%I
          : coPset → mexpr Λ_t → _ → iProp Σ ).
  iAssert (∀ Φ, TGT (e_t : mexpr Λ_t) @ ⊤ {{ Φ }} -∗ F ⊤ e_t Φ)%I as "Hgen"; last first. {
    iApply ("Hgen" with "[He1 Hsim] [//] [//] [//] [//] [$] [$] [$] [$]").
    - by iApply "Hsim".
    - iIntros (?) "[% [?$]]".
  }
  clear n κs Htrace e_s He_s He_t. iIntros (?) "Hsim".
  iApply (sim_ind with "[] Hsim"). { solve_proper. }
  iIntros "!>" (?? ?) "Hsim". iIntros (n κs σ_s σ_t e_s Htrace He_t He_s ->) "Ha He Hσ_t Hσ_s Hc".
  iMod ("Hsim" with "[//] [//] [$] [$] Hσ_t Hσ_s") as "[[?[?[??]]]|[Hsim|Hsim]]".
  - by iMod ("Hc" with "[$]").
  - move: Htrace => /tnhas_trace_inv Htrace.
    iApply (fupd_mono _ _ ⌜_⌝). { iPureIntro. by apply: thas_trace_under_tall. }
    iIntros (?[[??]|[?[?[?[?[?[?[<- ?]]]]]]]]).
    { iApply fupd_mask_intro; [done|]. iIntros "_". iPureIntro. tend. }
    iMod ("Hsim" with "[//]") as "Hsim" => /=.
    iMod (ord_later_elim with "Hsim Ha [-]"); [|done]. iIntros "Ha".
    iMod (ord_later_update with "Ha"); [shelve|].
    iModIntro. iExists _. iFrame. iSplit; [done|]. iIntros "Ha Hsteps". iModIntro.
    iApply (sim_steps_elim with "Hsteps"). iIntros (?) "(%&%&%&%&%&%&?&>[? [? Hsim]])".
    iMod (ord_later_update with "Ha") as "Ha"; [by apply: o_le_choice_r|].
    iApply ("Hsim" with "[//] [//] [//] [//] Ha [$] [$] [$] [$]").
  - iMod "Hsim" as "Hsteps".
    iApply (sim_steps_elim with "Hsteps"). iIntros (?) "(%&%&?&>[? [? Hsim]])".
    iApply ("Hsim" with "[//] [//] [//] [//] [$] [$] [$] [$] [$]").
  Unshelve.
  + apply _.
  + etrans; [|done]. apply o_le_S.
  + done.
Qed.
