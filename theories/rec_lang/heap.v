Require Import Coq.Program.Equality.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From stdpp Require Import coPset.
From iris.algebra Require Import big_op gmap frac agree.
From iris.algebra Require Import csum excl auth cmra_big_op numbers.
From iris.bi Require Import fractional.
From iris.base_logic Require Export lib.own lib.ghost_var.
Require Import refframe.rec_lang.lang.

Definition fntblUR : cmra :=
  agreeR (gmapO fn_name fndefO).

Class moduleG EV Σ := ModuleG {
  module_spec : mod_state EV;
  module_ghostvarG :> ghost_varG Σ (mod_state EV);
  module_spec_name : gname;
  module_full_trace : list EV;
}.

Class modulePreG EV Σ := PreModuleG {
  module_pre_ghostvarG :> ghost_varG Σ (mod_state EV);
}.

Definition moduleΣ EV : gFunctors :=
  #[ghost_varΣ (mod_state EV)].

Instance subG_modulePreG {Σ} EV : subG (moduleΣ EV) Σ → modulePreG EV Σ.
Proof. solve_inG. Qed.

Definition own_module {Σ EV} `{!ghost_varG Σ (mod_state EV)} (γ : gname) (m : module EV) (σ : m.(m_state)) :=
  ghost_var γ (1/2) (MS m σ).
Definition NoUb {Σ EV} `{!ghost_varG Σ (mod_state EV)} `{!invG Σ} (γ : gname) (E : coPset) (Φ : iProp Σ) : iProp Σ :=
  |={E, ∅}=> ((|={∅, E}=> Φ) ∨ ∃ m σ, own_module γ m σ ∗
     (own_module γ m σ -∗ ⌜¬ σ ~{m, [] }~> (λ _, False)⌝ -∗ |={∅, E}=> Φ)).
Fixpoint WPspec {Σ EV} `{!ghost_varG Σ (mod_state EV)} `{!invG Σ} (γ : gname) (κs : list EV) (E : coPset) (Φ : iProp Σ) {struct κs} : iProp Σ :=
  match κs with
  | [] => NoUb γ E Φ
  | κ::κs' => NoUb γ E (|={E, ∅}=> ∃ m σ σ', ⌜σ ~{ m, [Vis κ] }~> (σ' =.)⌝ ∗ own_module γ m σ ∗  ( own_module γ m σ' -∗ |={∅, E}=> WPspec γ κs' E Φ))
  end.
Arguments WPspec : simpl never.

Class heapG Σ := HeapG {
  heap_fntbl_inG :> inG Σ (fntblUR);
  heap_fntbl_name : gname;
  heap_module :> moduleG rec_event Σ;
}.

Section WPspec.
  Context `{!ghost_varG Σ (mod_state EV)} `{!invG Σ}.

  Global Instance frommodal_noub γ E P : FromModal modality_id (NoUb γ E P) (NoUb γ E P) P.
  Proof.
    rewrite /FromModal. iIntros "HP /=".
    iMod (fupd_intro_mask' _ ∅) as "HE". set_solver.
    iModIntro. iLeft. iMod "HE". by iFrame.
  Qed.

  Global Instance elim_modal_noub_noub p γ E P Q :
    ElimModal True p false (NoUb γ E P) P (NoUb γ E Q) (NoUb γ E Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /=.
    iIntros (_) "[Hnub HP]".
    iMod "Hnub" as "[Hnub|Hnub]".
    (* TODO: for proving this, NoUb needs to be a fixpoint. *)
  Admitted.

  Lemma noub_use γ E m σ :
    own_module γ m σ -∗
    NoUb γ E (⌜¬ σ ~{m, [] }~> (λ _, False)⌝ ∗ own_module γ m σ).
  Proof.
    iIntros "Hm".
    iMod (fupd_intro_mask' _ ∅) as "HE". set_solver.
    iModIntro. iRight. iExists _, _. iFrame.
    iIntros "Hm" (?). iMod "HE". iModIntro. by iFrame.
  Qed.

  Lemma wpspec_noub γ E Φ κs:
    NoUb γ E (WPspec γ κs E Φ) -∗
    WPspec γ κs E Φ.
  Proof. iIntros "Hnub". by destruct κs; rewrite /WPspec/=-/WPspec; iMod "Hnub". Qed.

  Global Instance elim_modal_noub_wpspec p γ E P Q κs:
    ElimModal True p false (NoUb γ E P) P (WPspec γ κs E Q) (WPspec γ κs E Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /=.
    iIntros (_) "[Hnub HP]".
    iApply wpspec_noub. iMod "Hnub". iModIntro. by iApply "HP".
  Qed.

  Lemma wpspec_nil' γ E Φ:
    NoUb γ E Φ -∗ WPspec (EV:=EV) γ [] E Φ.
  Proof. done. Qed.

  Lemma wpspec_nil γ E Φ:
    Φ -∗ WPspec (EV:=EV) γ [] E Φ.
  Proof. iIntros "Φ". iApply wpspec_nil'. by iModIntro. Qed.

  Lemma wpspec_nil_inv γ E Φ:
    WPspec (EV:=EV) γ [] E Φ -∗ NoUb γ E Φ.
  Proof. done. Qed.

  Lemma wpspec_cons (κ : EV) m Pσ κs γ E Φ σ:
    σ ~{ m, [Vis κ] }~> Pσ →
    own_module γ m σ -∗
    (∀ σ', ⌜Pσ σ'⌝ -∗ own_module γ m σ' -∗ WPspec γ κs E Φ) -∗
    WPspec γ (κ::κs) E Φ.
  Proof.
    iIntros ([?[? Hor]]%has_trace_inv) "Hm HΦ". rewrite /WPspec/=-/WPspec.
    iModIntro. iMod (fupd_intro_mask' _ ∅) as "HE". set_solver. iModIntro.
    iExists _, _, _. iFrame. iSplit => //.
    iIntros "Hm". iMod "HE". iModIntro.
    destruct Hor.
    - iApply wpspec_noub. iMod (noub_use with "Hm") as (Hx) "?".
      contradict Hx. by apply: TraceUb.
    - by iApply "HΦ".
  Qed.

  Lemma wpspec_bind (κ : EV) κs γ E Φ:
    WPspec γ [κ] E (WPspec γ κs E Φ) -∗
    WPspec γ (κ::κs) E Φ.
  Proof. Admitted.
End WPspec.

Section definitions.
  Context `{!moduleG EV Σ} `{!invG Σ}.

  Definition spec_ctx (κsrest : list EV) : iProp Σ :=
    ∃ κsstart σscur,
      ⌜module_full_trace = κsstart ++ κsrest⌝ ∗
      ⌜module_spec.(ms_state) ~{ module_spec, Vis <$> κsstart }~> (σscur =.)⌝ ∗
      (* obtained by classical reasoning before switching to Iris *)
      ⌜¬ module_spec.(ms_state) ~{ module_spec, (Vis <$> module_full_trace) }~> (λ _, False)⌝ ∗
      own_module module_spec_name module_spec σscur.

  Lemma noub_elim κs P E:
    spec_ctx κs -∗
    NoUb module_spec_name E P ={E}=∗
    spec_ctx κs ∗ P.
  Proof.
    iIntros "Hsctx Hnub".
    iMod "Hnub" as "[>$|HP]" => //.
    iDestruct "HP" as (m σ) "[Hm HP]".
    iDestruct "Hsctx" as (κsstart σscur Hfull Hinit Hnub) "Hm2".
    iDestruct (ghost_var_agree with "Hm Hm2") as %Heq.
    dependent destruction Heq. (* THIS USES AXIOM K! *)
    iMod ("HP" with "Hm [%]"). {
      contradict Hnub.
      rewrite Hfull fmap_app.
      apply: has_trace_trans; [done|] => ? <-.
      by apply: (has_trace_trans []).
    }
    iModIntro. iFrame. iExists _, _. by iFrame.
  Qed.


  Lemma wpspec_cons_inv_ctx κ κs κs' Φ E:
    spec_ctx (κ::κs) -∗
    WPspec module_spec_name (κ :: κs') E Φ ={E}=∗
    spec_ctx κs ∗ WPspec module_spec_name κs' E Φ.
  Proof.
    rewrite /WPspec/=-/WPspec.
    iIntros "Hsctx Hspec".
    iMod (noub_elim with "Hsctx Hspec") as "[Hsctx Hspec]".
    iDestruct "Hsctx" as (κsstart σscur Hfull Hinit Hnub) "Hm".
    iMod "Hspec" as (m σ Pσ' Hstep) "[Hm2 HΦ]".
    iDestruct (ghost_var_agree with "Hm Hm2") as %Heq.
    dependent destruction Heq. (* THIS USES AXIOM K! *)
    iMod (ghost_var_update_halves with "Hm Hm2") as "[Hm Hm2]".
    iMod ("HΦ" with "Hm") as "$".
    iModIntro. iExists _, _. iFrame.
    iPureIntro. rewrite {1}Hfull. rewrite cons_middle app_assoc.
    split_and! => //. rewrite fmap_app.
    apply: has_trace_trans; [done|] => ? <-. done.
  Qed.
End definitions.

Definition to_fntbl : gmap fn_name fndef → fntblUR :=
  to_agree.

Section definitions.
  Context `{!heapG Σ}.

  Definition fntbl_def (fns : gmap fn_name fndef) : iProp Σ :=
    own heap_fntbl_name (to_fntbl fns).
  Definition fntbl_aux : seal (@fntbl_def). by eexists. Qed.
  Definition fntbl := unseal fntbl_aux.
  Definition fntbl_eq : @fntbl = @fntbl_def :=
    seal_eq fntbl_aux.

  Definition fntbl_entry_def (l : fn_name) (f: option fndef) : iProp Σ :=
    ∃ fns, ⌜fns !! l = f⌝ ∗ fntbl fns.
  Definition fntbl_entry_aux : seal (@fntbl_entry_def). by eexists. Qed.
  Definition fntbl_entry := unseal fntbl_entry_aux.
  Definition fntbl_entry_eq : @fntbl_entry = @fntbl_entry_def :=
    seal_eq fntbl_entry_aux.

  Definition state_ctx (σ: rec_state) (κs : list rec_event) : iProp Σ :=
    fntbl σ.(st_fns) ∗ spec_ctx κs.
End definitions.

Section fntbl.
  Context `{!heapG Σ}.

  Lemma to_fntbl_valid f : ✓ to_fntbl f.
  Proof. done. Qed.

  Global Instance fntbl_pers fns : Persistent (fntbl fns).
  Proof. rewrite fntbl_eq. by apply _. Qed.

  Global Instance fntbl_entry_pers f fn : Persistent (fntbl_entry f fn).
  Proof. rewrite fntbl_entry_eq. by apply _. Qed.

  Lemma fntbl_agree fns1 fns2 :
    fntbl fns1 -∗ fntbl fns2 -∗ ⌜fns1 = fns2⌝.
  Proof.
    rewrite fntbl_eq. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %?%to_agree_op_valid.
      by fold_leibniz.
  Qed.

  Lemma fntbl_entry_intro t f fn :
    t !! f = fn →
    fntbl t -∗ fntbl_entry f fn.
  Proof. rewrite fntbl_entry_eq. iIntros (?) "?". iExists _. by iFrame. Qed.

  Lemma fntbl_entry_lookup t f fn :
    fntbl t -∗ fntbl_entry f fn -∗ ⌜t !! f = fn⌝.
  Proof.
    rewrite fntbl_entry_eq. iIntros "Htbl Hf".
    iDestruct "Hf" as (fns2 ?) "Hf".
    by iDestruct (fntbl_agree with "Htbl Hf") as %->.
  Qed.

End fntbl.
