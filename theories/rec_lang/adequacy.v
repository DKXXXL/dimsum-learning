From iris.proofmode Require Import tactics.
From iris.program_logic Require Export adequacy weakestpre.
From iris.algebra Require Import csum excl auth cmra_big_op gmap.
From refframe.rec_lang Require Import heap lifting.
From iris.program_logic Require Export language.
Set Default Proof Using "Type".

Class reclangPreG Σ := PreRecLangG {
  reclang_pre_invG :> invPreG Σ;
  reclang_pre_moduleG :> modulePreG rec_event Σ;
  reclang_heap_fntbl_inG :> inG Σ fntblUR;
}.

Definition reclangΣ : gFunctors :=
  #[invΣ; moduleΣ rec_event; GFunctor (constRF fntblUR)].

Instance subG_reclangPreG {Σ} : subG reclangΣ Σ → reclangPreG Σ.
Proof. solve_inG. Qed.

Definition iris_module (Λ : language) : module (Λ.(observation)) := {|
  m_state := cfg Λ;
  m_step σ e σ' := step σ (option_list e) σ';
  m_is_ub σ := ∃ e, e ∈ σ.1 ∧ stuck e σ.2;
|}.

Definition single_event_head_step (Λ : ectxiLanguage) : Prop :=
  ∀ κs e σ e' σ' efs, head_step (e:=Λ) e σ κs e' σ' efs → κs = option_list (head κs).

Definition single_event_prim_step (Λ : language) : Prop :=
  ∀ κs e σ e' σ' efs, prim_step (l:=Λ) e σ κs e' σ' efs → κs = option_list (head κs).

Lemma single_event_head_prim_step Λ:
  single_event_head_step Λ →
  single_event_prim_step Λ.
Proof. move => Hev ?????? [*]. by apply: Hev. Qed.

Lemma single_event_step Λ κs σ σ' :
  single_event_prim_step Λ →
  step (Λ:=Λ) σ κs σ' → κs = option_list (head κs).
Proof. move => Hev [*]. subst. by apply: Hev. Qed.

Lemma has_non_ub_trace_nsteps Λ σ1 κs σ2:
  single_event_prim_step Λ →
  σ1 ~{ iris_module Λ, κs }~>ₙ σ2 ↔ ∃ n, nsteps n σ1 κs σ2.
Proof.
  move => Hev.
  split.
  - elim; eauto using nsteps_refl.
    move => /= ??????? [??]. eexists _. by econstructor.
  - move => [n Hsteps].
    elim: Hsteps; eauto using NUBTraceEnd.
    move => /= ???? κ????. erewrite (single_event_step _ κ) => //.
    apply: NUBTraceStep => //=. by erewrite <-(single_event_step _ κ).
Qed.

Theorem module_adequacy Σ Λ (mspec : mod_state _) `{!invPreG Σ} `{!modulePreG Λ.(observation) Σ} es σ1:
  (∀ κs, LEM (mspec.(ms_state) ~{ mspec, κs }~> (λ _, True))) →
  single_event_prim_step Λ →
  (∀ `{Hinv : !invG Σ} γm κsfull,
       let _ : moduleG Λ.(observation) Σ := ModuleG Λ.(observation) Σ mspec _ γm κsfull in
     ⊢ spec_ctx κsfull -∗
       own_module module_spec_name mspec mspec.(ms_state) ={⊤}=∗
       ∃ (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ Hinv stateI fork_post in
       stateI σ1 κsfull 0 ∗
       ([∗ list] e ∈ es, WP e @ ⊤ {{ _, True }}) ∗
       (∀ σ2 n, stateI σ2 [] n ={⊤,∅}=∗ spec_ctx [])) →
  MS (iris_module Λ) (es, σ1) ⊑ mspec.
Proof.
  move => HLEM Hev /= Hwp.
  constructor => κsfull Htrace. case: (HLEM κsfull) => // Hnoub.
  move: Htrace => /has_trace_to_non_ub_trace[κs' [[??] [Hpre [Htrace Hor]]]].
  move: Htrace => /has_non_ub_trace_nsteps[//|?] /=.
  apply: wp_strong_adequacy => ?.
  iMod (ghost_var_alloc (MS mspec mspec.(ms_state))) as (γm) "[Hm1 Hm2]".
  iMod (Hwp _ γm κs' with "[Hm1] Hm2") as (stateI fork_post) "(Hσ&Hwp&Hend)". {
    iExists [], _. iFrame. iPureIntro. split_and! => //. { by constructor. }
    contradict Hnoub => /=. move: Hpre => [? ->].
    by apply: has_trace_trans.
  }
  iModIntro. iExists NotStuck, stateI, (replicate (length es) (λ _, True%I)), fork_post.
  rewrite big_sepL2_replicate_r //. iFrame.
  iIntros (es' ts' ?? Hnonstuck) "Hs _ _".
  iMod ("Hend" with "Hs") as (κs σscur Hmodful Htrace _) "_". iPureIntro.
  rewrite app_nil_r in Hmodful. simpl in *. subst.
  case: Hor => [[<- ?]|[? [? /not_not_stuck Hstuck]]].
  - by apply: has_trace_mono.
  - naive_solver.
Qed.



Lemma reclang_adequacy Σ `{!reclangPreG Σ} (mspec : mod_state _) (mains : list lang.expr) (fns : gmap fn_name fndef):
  (∀ κs, LEM (mspec.(ms_state) ~{ mspec, κs }~> (λ _, True))) →
  (∀ {HrecG : reclangG Σ},
    ⊢ @own_module _ rec_event (module_ghostvarG) module_spec_name mspec mspec.(ms_state) -∗
      fntbl fns
      ={⊤}=∗ [∗ list] main ∈ mains, WP main {{ _, True }}) →
 MS (iris_module rec_lang) (mains, {| st_fns := fns |}) ⊑ mspec.
Proof.
  move => HLEM Hwp. apply: module_adequacy; [done| | ]. {
    apply: single_event_head_prim_step.
    move => ??????. by inversion 1.
  }
  iIntros (Hinv γm κsfull Hmod) "Hs Hm".
  (* set h := to_heap ∅. *)
  (* iMod (own_alloc (● h ⋅ ◯ h)) as (γh) "[Hh _]" => //. *)
  (* { apply auth_both_valid_discrete. split => //. } *)
  set f := to_fntbl fns.
  iMod (own_alloc (f)) as (γf) "Hf" => //.

  set (HheapG := HeapG _ _ γf Hmod).
  set (HreclangG := RecLangG _ _ HheapG).
  iAssert (fntbl fns) as "#Hfns". { by rewrite fntbl_eq. }
  iMod (Hwp HreclangG with "Hm Hfns") as "Hes".
  iModIntro. iExists _, _. iFrame "Hes Hs Hfns".
  iIntros (??) "[? Hσ]". iFrame.
  by iMod (fupd_intro_mask' _ ∅).
Qed.
