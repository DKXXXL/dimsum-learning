From iris.program_logic Require Export language.
From iris.program_logic Require Import weakestpre lifting.
From dimsum.core.iris Require Export sim.
From dimsum.core Require Import axioms.
Set Default Proof Using "Type".

Definition nb_step EV (_ : unit) (_ : option EV) (_ : unit → Prop) : Prop := False.
Definition nb_trans EV : mod_trans EV := ModTrans (nb_step EV).
Canonical Structure nb_mod_lang EV Σ : mod_lang EV Σ := {|
  mexpr := unit;
  mtrans := nb_trans EV;
  mexpr_rel _ _ := True;
  mstate_interp _ := True%I;
|}.

Inductive lang_step (Λ : language) :
  (expr Λ * state Λ) → option (observation Λ) → ((expr Λ * state Λ) → Prop) → Prop :=
| LangStep e σ e' σ' efs κs :
  prim_step e σ κs e' σ' efs →
  lang_step Λ (e, σ) (head κs) (λ σ'', σ'' = (e', σ'))
| LangUbStep e σ :
  ¬ reducible e σ →
  lang_step Λ (e, σ) None (λ σ'', False).

Definition lang_trans (Λ : language) : mod_trans (observation Λ) :=
  ModTrans (lang_step Λ).

Canonical Structure lang_mod_lang {Σ} (Λ : language) (stateI : state Λ → iProp Σ) : mod_lang (observation Λ) Σ := {|
  mexpr := expr Λ;
  mtrans := lang_trans Λ;
  mexpr_rel σ e := e = σ.1;
  mstate_interp σ := stateI σ.2;
|}.

Section wp.
  Context {Λ : language}.
  Context `{!irisGS_gen HasNoLc Λ Σ}.

  Lemma sim_wp_adequacy e E `{!ord_laterPreG Σ}
    `{!ghost_varG Σ unit}:
    (∀ (e : expr Λ) σ κ e2 σ2 efs, prim_step e σ κ e2 σ2 efs → efs = []) →
    (∀ σ ns κs nt, state_interp σ ns κs nt ⊣⊢ state_interp σ 0 [] 0) →
    (∀ (Hord : ord_laterGS Σ) γ_s,
      let Λ_t := lang_mod_lang Λ (λ σ, state_interp σ 0 [] 0) in
      let _ : dimsumGS _ _ Λ_t (nb_mod_lang _ _) := DimsumGS _ _ _ _ _ _ _ γ_s in
     (e : mexpr Λ_t) ⪯{E} tt {{ λ e _, ∃ v, ⌜to_val e = Some v⌝ }}) -∗
    WP e @ E {{ _, True }}.
  Proof.
    iIntros (Hnofork Hstate) "Hsim".
    iAssert (∃ n : nat, ▷^n False)%I as (n) "Hend".
    { iLöb as "IH". iDestruct "IH" as (?) "IH". by iExists (S n). }
    iMod (ord_later_alloc (nat_to_ord n)) as (?) "Hord".
    iDestruct (ord_later_ctx_alloc with "[$]") as "#?".
    iMod (ghost_var_alloc tt) as (γ_s) "Hs".
    set (Λ_t := lang_mod_lang Λ (λ σ, state_interp σ 0 [] 0)).
    set (X := DimsumGS _ _ _ _ _ _ _ γ_s : dimsumGS _ _ Λ_t (nb_mod_lang _ _)).
    iAssert (|==> ⤇ tt ∗ ⤇ tt)%I with "[Hs]" as ">[He1 He2]".
    { by iMod (ghost_var_update tt with "Hs") as "[$ $]". }
    pose (F := (λ E e_t Ψ,
               ∀ n,
                 ▷^n False -∗
                 ord_later_auth (nat_to_ord n) -∗
                 ⤇ () -∗
                 (∀ e_t' : mexpr Λ_t, Ψ e_t' -∗ ∃ v, ⌜to_val e_t' = Some v⌝) -∗
                 WP e_t @ E {{ _, True }})%I
                 : coPset → mexpr Λ_t → _ → iProp Σ ).
  iAssert (∀ Φ, TGT e @ E {{ Φ }} -∗ F E e Φ)%I as "Hgen"; last first. {
    iApply ("Hgen" with "[He1 Hsim] [$] [$] [$]").
    - by iApply "Hsim".
    - iIntros (?) "[% [?$]]".
  }
  iClear "Hend". clear n. iIntros (?) "Hsim".
  iApply (sim_ind with "[] Hsim"). { solve_proper. }
  iIntros "!>" (? e_t ?) "Hsim". iIntros (n) "Hend Hord He Hc".
  destruct (to_val e_t) eqn:He.
  { apply of_to_val in He. subst. by iApply wp_value'. }
  rewrite wp_unfold /wp_pre. simplify_option_eq.
  iIntros (σ ????) "Hσ".
  iMod ("Hsim" $! (_, _) with "[//] [//] [//] [$] [Hσ] [//]") as "[[?[?[??]]]|[Hsim|Hsim]]".
  { simpl. by rewrite -Hstate. }
  { iDestruct ("Hc" with "[$]") as %[??]. simplify_eq. }
  - destruct n; [done|] => /=.
    have [Hred|Hnotred] := AxClassic (reducible e_t σ).
    + iApply fupd_mask_intro; [set_solver|]. iIntros "He". iSplit; [done|].
      iIntros (????) "_ !> !> !>". iApply step_fupdN_intro; [done|]. iModIntro. iMod "He".
      iMod ("Hsim" with "[%]") as "Hsim". { by econstructor. }
      iMod (ord_later_elim with "Hsim Hord [-]"); [|done]. iIntros "Hord /=".
      iMod (ord_later_update with "Hord"); [by apply o_le_S|].
      iModIntro. iExists _. iFrame. iSplit; [done|]. iIntros "Hod".
      iDestruct 1 as (? Ht) "Hsim". iModIntro.
      iMod ("Hsim" $! tt with "[%]") as (?????) "[?[? >[Hσ [? Hsim]]]]". {
          destruct κ.
          - apply thas_trace_nil_inv in Ht. by inv Ht.
          - apply thas_trace_cons_inv in Ht.
            apply thas_trace_nil_inv in Ht. inv Ht => //. destruct!.
            inv_all @m_step.
        }
        exploit Hnofork; [done|] => ?. simplify_eq/=. destruct_all unit. iModIntro.
        iSplitL "Hσ". { by iApply Hstate. }
        iSplit; [|done]. iApply ("Hsim" with "[$] [$] [$] [$]").
      + iMod ("Hsim" with "[%]") as "Hsim". { by constructor. }
        iMod (ord_later_elim with "Hsim Hord [-]"); [|done]. iIntros "Hord/=".
        iMod (ord_later_update with "Hord"); [by apply o_le_S|].
        iModIntro. iExists _. iFrame. iSplit; [done|]. iIntros "Hod".
        iDestruct 1 as (? Ht) "Hsim". iModIntro.
        iMod ("Hsim" $! tt with "[%]") as (??????) "[? ?]".
        { apply thas_trace_nil_inv in Ht. by inv Ht. }
        done.
  - iMod "Hsim" as (? Ht) "Hsim".
    iMod ("Hsim" $! tt with "[%]") as (??) "[? >[?[? Hsim]]]".
    { apply thas_trace_nil_inv in Ht. by inv Ht. } simplify_eq/=. destruct_all unit.
    iDestruct ("Hsim" with "[$] [$] [$] [$]") as "Hsim".
    rewrite wp_unfold /wp_pre. simplify_option_eq.
    iMod ("Hsim" with "[-]") as "Hsim".
    { by rewrite -Hstate. }
    done.
  Qed.
End wp.
