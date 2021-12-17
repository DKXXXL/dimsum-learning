From iris.algebra Require Import auth.
From iris.bi Require Import fractional.
From iris.base_logic Require Export lib.own.
From iris.proofmode Require Export tactics.
From refframe.iris Require Export mono_ord.
Set Default Proof Using "Type".

Class ord_laterPreG Σ := OrdLaterPreG {
  ord_later_pre_inG :> inG Σ mono_ordR;
}.
Class ord_laterGS Σ := OrdLaterGS {
  ord_later_inG :> ord_laterPreG Σ;
  ord_later_name : gname;
}.
Definition ord_laterΣ : gFunctors :=
  #[ GFunctor (mono_ordR) ].

Global Instance subG_ord_laterΣ Σ :
  subG (ord_laterΣ) Σ → ord_laterPreG Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{!ord_laterGS Σ}.

  Definition ord_later_auth_def (n : trace_index) : iProp Σ :=
    own ord_later_name (mono_ord_auth 1 n).
  Definition ord_later_auth_aux : seal (@ord_later_auth_def). Proof. by eexists. Qed.
  Definition ord_later_auth := ord_later_auth_aux.(unseal).
  Definition ord_later_auth_eq : @ord_later_auth = @ord_later_auth_def := ord_later_auth_aux.(seal_eq).

  Definition ord_later_ub_def (n : trace_index) : iProp Σ :=
    own ord_later_name (mono_ord_ub n).
  Definition ord_later_ub_aux : seal (@ord_later_ub_def). Proof. by eexists. Qed.
  Definition ord_later_ub := ord_later_ub_aux.(unseal).
  Definition ord_later_ub_eq : @ord_later_ub = @ord_later_ub_def := ord_later_ub_aux.(seal_eq).

  Definition ord_later_ctx_def : iProp Σ :=
    ∃ n, ord_later_ub n.
  Definition ord_later_ctx_aux : seal (@ord_later_ctx_def). Proof. by eexists. Qed.
  Definition ord_later_ctx := ord_later_ctx_aux.(unseal).
  Definition ord_later_ctx_eq : @ord_later_ctx = @ord_later_ctx_def := ord_later_ctx_aux.(seal_eq).

  Definition ord_later_def (P : iProp Σ) : iProp Σ :=
    ∀ n, ord_later_auth n -∗ ord_later_auth n ∗ (∀ n', ⌜tiS n' ⊆ n⌝ -∗ ord_later_auth n' -∗ ord_later_auth n' ∗ P).
  Definition ord_later_aux : seal (@ord_later_def). Proof. by eexists. Qed.
  Definition ord_later := ord_later_aux.(unseal).
  Definition ord_later_eq : @ord_later = @ord_later_def := ord_later_aux.(seal_eq).

End definitions.

Notation "▷ₒ P" := (ord_later P) (at level 20, right associativity).

Local Ltac unseal := rewrite
  ?ord_later_eq /ord_later_def
  ?ord_later_ctx_eq /ord_later_ctx_def
  ?ord_later_auth_eq /ord_later_auth_def
  ?ord_later_ub_eq /ord_later_ub_def
.

Section lemmas.
  Context `{!ord_laterGS Σ}.
  Implicit Types (n : trace_index).

  Global Instance ord_later_auth_timeless n : Timeless (ord_later_auth n).
  Proof. unseal. apply _. Qed.
  Global Instance ord_later_ub_timeless n : Timeless (ord_later_ub n).
  Proof. unseal. apply _. Qed.
  Global Instance ord_later_ub_pers n : Persistent (ord_later_ub n).
  Proof. unseal. apply _. Qed.
  Global Instance ord_later_ctx_timeless : Timeless (ord_later_ctx).
  Proof. unseal. apply _. Qed.
  Global Instance ord_later_ctx_pers : Persistent (ord_later_ctx).
  Proof. unseal. apply _. Qed.

  Global Instance ord_later_ne (n : nat):
    Proper (dist n ==> dist n) ord_later.
  Proof. unseal. solve_proper. Qed.
  Global Instance ord_later_proper (n : nat):
    Proper ((≡) ==> (≡)) ord_later.
  Proof. unseal. solve_proper. Qed.

  Lemma ord_later_mono P1 P2:
    ▷ₒ P1 -∗
    (P1 -∗ P2) -∗
    ▷ₒ P2.
  Proof.
    unseal. iIntros "Hl HP" (n) "Ha". iDestruct ("Hl" with "Ha") as "[$ Hl]".
    iIntros (n' ?) "Ha". iDestruct ("Hl" with "[//] Ha") as "[$ Hl]". by iApply "HP".
  Qed.

  Global Instance elim_modal_ord_later p P Q :
    ElimModal True p false (▷ₒ P) P (▷ₒ Q) Q.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim.
    iIntros (?) "[??]". by iApply (ord_later_mono with "[$]").
  Qed.

  Lemma ord_later_alloc `{!ord_laterPreG Σ} n :
    ⊢ |==> ∃ _ : ord_laterGS Σ, ord_later_auth n.
  Proof using.
    iMod (own_alloc (mono_ord_auth 1 n)) as (γ) "Ha". { by apply mono_ord_auth_valid. }
    iModIntro. iExists (OrdLaterGS _ _ _). unseal. iFrame.
  Qed.

  Lemma ord_later_ctx_alloc n :
    ord_later_auth n -∗ ord_later_ctx.
  Proof. unseal. rewrite {1}mono_ord_auth_ub_op. iIntros "[??]". iExists _. iFrame. Qed.

  Lemma ord_later_update n n':
     n' ⊆ n →
    ord_later_auth n ==∗ ord_later_auth n'.
  Proof. unseal. iIntros (?) "Hown". iApply (own_update with "Hown"). by apply mono_ord_update. Qed.

  (* The other direction seems hard to prove. *)
  Lemma ord_later_sep P1 P2:
    (▷ₒ P1 ∗ ▷ₒ P2) -∗
    ▷ₒ (P1 ∗ P2).
  Proof.
    unseal. iIntros "[HP1 HP2]" (n) "Htok".
    iDestruct ("HP1" with "Htok") as "[Htok HP1]".
    iDestruct ("HP2" with "Htok") as "[Htok HP2]".
    iFrame. iIntros (n' ?) "Htok".
    iDestruct ("HP1" with "[//] Htok") as "[Htok $]".
    iDestruct ("HP2" with "[//] Htok") as "[Htok $]".
    done.
  Qed.

  Lemma ord_loeb P:
    ord_later_ctx -∗
    □ (▷ₒ P -∗ P) -∗
    P.
  Proof.
    unseal. iDestruct 1 as (n) "Hub". iIntros "#Hl".
    iInduction n as [] "IH" using ti_lt_ind.
    iApply "Hl".
    iIntros (n') "Hn'".
    iDestruct (own_valid_2 with "Hn' Hub") as %[_ ?]%mono_ord_both_frac_valid.
    iFrame. iIntros (n'' ?) "Ha".
    rewrite {1}mono_ord_auth_ub_op. iDestruct "Ha" as "[Ha Hn'']". iFrame.
    iApply ("IH" with "[] Hn''"). iPureIntro. by etrans.
  Qed.

  Lemma ord_later_elim P Q n:
    ▷ₒ P -∗
    ord_later_auth n -∗
    (ord_later_auth n ==∗ ∃ n', ⌜tiS n' ⊆ n⌝ ∗ ord_later_auth n' ∗ (ord_later_auth n' -∗ P ==∗ Q)) -∗
    |==> Q.
  Proof.
    unseal. iIntros "HP Ha Hwand".
    iDestruct ("HP" with "Ha") as "[Ha HP]".
    iMod ("Hwand" with "Ha") as (??) "[Ha Hwand]".
    iDestruct ("HP" with "[//] Ha") as "[Ha HP]".
    by iApply ("Hwand" with "Ha").
  Qed.
End lemmas.