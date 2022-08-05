From iris.program_logic Require Export language.
From iris.program_logic Require Import weakestpre.
From dimsum.core.iris Require Export sim.
Set Default Proof Using "Type".

Definition nb_step EV (_ : unit) (_ : option EV) (_ : unit → Prop) : Prop := False.
Definition nb_trans EV : mod_trans EV := ModTrans (nb_step EV).
Canonical Structure nb_mod_lang EV : mod_lang EV := {|
  mexpr := unit;
  mtrans := nb_trans EV;
  mexpr_rel _ _ := True;
|}.

Inductive lang_step (Λ : language) :
  (expr Λ * state Λ) → option (observation Λ) → ((expr Λ * state Λ) → Prop) → Prop :=
| LangStep e σ e' σ' efs κs :
  prim_step e σ κs e' σ' efs →
  lang_step Λ (e, σ) (head κs) (λ σ'', σ'' = (e', σ')).

Definition lang_trans (Λ : language) : mod_trans (observation Λ) :=
  ModTrans (lang_step Λ).

Canonical Structure lang_mod_lang (Λ : language) : mod_lang (observation Λ) := {|
  mexpr := expr Λ;
  mtrans := lang_trans Λ;
  mexpr_rel σ e := e = σ.1;
|}.

Section wp.
  Context {Λ : language}.
  Context `{!irisGS_gen HasNoLc Λ Σ}.

  Lemma sim_wp_adequacy e E Φ `{!ord_laterPreG Σ}:
    (∀ γ_ord,
      let _ : ord_laterGS Σ := OrdLaterGS _ _ γ_ord in
      ∃ (stateI : (lang_trans Λ).(m_state) → (nb_trans _).(m_state) → iProp Σ),
      (* TODO: Add a proof that the two state interpretations coincide. *)
      let _ : dimsumGS _ (lang_mod_lang Λ) (nb_mod_lang _) Σ := DimsumGS _ _ _ _ _ _ stateI in
     e ⪯{E} tt {{ λ e _, ∃ v, ⌜to_val e = Some v⌝ ∗ Φ v }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
  Abort.
End wp.
