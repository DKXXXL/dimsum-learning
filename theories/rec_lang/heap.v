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

Record mod_state EV := ModState {
  ms_module : module EV;
  ms_state : ms_module.(m_state);
}.
Arguments ModState {_}.
Arguments ms_module {_}.
Arguments ms_state {_}.

Class moduleG EV Σ := ModuleG {
  module_spec : module EV;
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

Definition own_module {Σ} EV `{!ghost_varG Σ (mod_state EV)} (γ : gname) (m : module EV) (σ : m.(m_state)) :=
  ghost_var γ (1/2) (ModState m σ).
Definition WPspec {Σ} EV `{!ghost_varG Σ (mod_state EV)} `{!invG Σ} (γ : gname) (κs : list EV) (E : coPset) (Φ : iProp Σ) : iProp Σ :=
  |={E, ∅}=> ▷ ∃ m σ, own_module EV γ m σ ∗
   ∃ σ', ⌜has_trace m σ (Vis <$> κs) σ'⌝ ∗ (
         own_module EV γ m σ' -∗
        ⌜¬ ∃ σub, has_trace m σ ((Vis <$> κs) ++ [Ub]) σub⌝ -∗
        |={∅, E}=> Φ).


Class heapG Σ := HeapG {
  heap_fntbl_inG :> inG Σ (fntblUR);
  heap_fntbl_name : gname;
  heap_module :> moduleG rec_event Σ;
}.

Section definitions.
  Context `{!moduleG EV Σ}.

  Definition spec_ctx (κsrest : list EV) : iProp Σ :=
    ∃ κsstart σscur,
      ⌜module_full_trace = κsstart ++ κsrest⌝ ∗
      ⌜has_trace module_spec module_spec.(m_initial) (Vis <$> κsstart) σscur⌝ ∗
      (* obtained by classical reasoning before switching to Iris *)
      ⌜∀ κs, κs `prefix_of` module_full_trace → ¬ ∃ σub, has_trace module_spec module_spec.(m_initial) ((Vis <$>  κs) ++ [Ub]) σub⌝ ∗
      own_module EV module_spec_name module_spec σscur.

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
