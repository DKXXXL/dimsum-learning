From iris.algebra Require Import auth.
From iris.bi Require Import fractional.
From iris.base_logic Require Export lib.own.
From iris.proofmode Require Export tactics.
From dimsum.core.iris Require Export mono_ord.
Set Default Proof Using "Type".

(* Ideas for fixing mono_ord:

1. Only use natural numbers counting the number of steps already done
in the resource (potentially adding the original ordinal as a
parameter to ord_laterGS).

- Not sure how to make it work, in particular what to do the induction
  on. It seems like a problem if the authoratative side can switch
  which path it takes through the ordinal as it might not be
  well-founded for large ordinals (e.g. [oChoice nat (λ n, oS^n oO)])

2. Put the path through the ordinal into the resource.

-> Does not help since the universe of this path would be as large as
   the one of the ordinal.

3. Use explicit step indexing

-> Make the step index an explicit parameter of many definitions.
- Con: Would be annoying and require proving monotonicity often (?)
- Pro: Would probably work

4. Use monotone predicates over the step index

- Pro: Would be nicer than explicit step indexing
- Con: Would require reengineering Lithium to work on arbitrary BIs
- Con: Would maybe run into similar universe problems as it might push the
  universe of bi too high

5. Use coinduction instead of step indexing.

- Pro: Would avoid the use of ordinals entirely
- Con: It is unclear how to obtain such nice reasoning principles similar to Löb induction
  - Challenge: Can one support the use of Löb induction in RefinedC, i.e. for
    recursion between functions and for recursion between blocks?
  - Could maybe work if one extends each WP-like judgement with a iProp parameter
    that says that one can finish this kind of WP by showing that the iProp holds
    and then universally quantify over the iProp parameter and have wands in the
    context that show how to prove this iProp.
    - Does this work for mutual recursion?

6. Use transfinite Iris

- Would this work or would this run into the same universe problems?
- Would probably run into the same universe problems, as the type of ordinals in
  transfinite lives below the type of propositions.

7. Put the type of states into Set
-> Would solve the problem since now ordinals don't need to live in a very high universe

- Would require a first-order encoding of Iris propositions to handle prepost
- Would require changing itrees to a new definition that can only make choices
  over countable types and decidable propositions
- Pro: Would retain compatability with Transfinite Iris
- Pro: Might be good to avoid universe problems in the long term

CoInductive spec (EV : Set) : Set :=
| SNB | SUB
| SVis (e : EV) (s : spec EV) | STau (s : spec EV)
| SAll (f : positive → spec EV)
| SExist (f : positive → spec EV).

Or if one allows the states to be in Type@{Set+1} :
CoInductive spec (EV : Set) : Type@{Set+1} :=
| SVis (e : EV) (s : spec EV)
| SAll (T : Set) (f : T → spec EV)
| SExist (T : Set) (f : T → spec EV)
| STau (s : spec EV).

*)

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

  Definition ord_later_auth_def (n : ordinal) : iProp Σ :=
    own ord_later_name (mono_ord_auth 1 n).
  Definition ord_later_auth_aux : seal (@ord_later_auth_def). Proof. by eexists. Qed.
  Definition ord_later_auth := ord_later_auth_aux.(unseal).
  Definition ord_later_auth_eq : @ord_later_auth = @ord_later_auth_def := ord_later_auth_aux.(seal_eq).

  Definition ord_later_ub_def (n : ordinal) : iProp Σ :=
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
    ord_later_ctx -∗ ∃ n, ord_later_ub n ∗ ∀ n', ⌜oS n' ⊆ n⌝ -∗ ord_later_ub n' -∗ P.
    (* Old version: *)
    (* ∀ n, ord_later_auth n -∗ ord_later_auth n ∗ (∀ n', ⌜oS n' ⊆ n⌝ -∗ ord_later_auth n' -∗ ord_later_auth n' ∗ P). *)
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
  Implicit Types (n : ordinal).

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

  Lemma ord_later_intro P:
    P -∗ ▷ₒ P.
  Proof.
    unseal. iIntros "HP [% Hctx]".
    iExists _. iFrame. by iIntros.
  Qed.

  Lemma ord_later_mono P1 P2:
    ▷ₒ P1 -∗
    (P1 -∗ P2) -∗
    ▷ₒ P2.
  Proof.
    unseal. iIntros "Hl HP Hctx".
    iDestruct ("Hl" with "Hctx") as (?) "[Hn Hl]".
    iExists _. iFrame. iIntros (??) "?". iApply "HP".
    by iApply "Hl".
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
    unseal. iIntros "[HP1 HP2] #Hctx".
    iDestruct ("HP1" with "[$]") as (n1) "[Hn1 HP1]".
    iDestruct ("HP2" with "[$]") as (n2) "[Hn2 HP2]".
    iExists (o_min n1 n2).
    iCombine "Hn1 Hn2" as "Hn". rewrite mono_ord_ub_op. iFrame.
    iIntros (??) "#?".
    iDestruct ("HP1" with "[%] [$]") as "$". { etrans; [done|]. apply o_min_le_l. }
    iDestruct ("HP2" with "[%] [$]") as "$". { etrans; [done|]. apply o_min_le_r. }
  Qed.

  Lemma ord_later_pers P :
    □ ▷ₒ P -∗ ▷ₒ □ P.
  Proof.
    iIntros "#HP".
    unseal. iIntros "#Hctx".
    iDestruct ("HP" with "Hctx") as (?) "[? HP2]".
    iExists _. iFrame "#". iIntros (??) "#?".
    iModIntro. by iApply "HP2".
  Qed.

  Lemma ord_later_and P Q :
    ▷ₒ P ∧ ▷ₒ Q -∗ ▷ₒ (P ∧ Q).
  Proof.
    iIntros "HPQ".
    unseal. iIntros "#Hctx".
    iDestruct (bi.and_parallel with "HPQ []") as "HPQ".
    { iSplit; iIntros "HP"; iSpecialize ("HP" with "[$]"); iExact "HP". }
    rewrite bi.and_exist_l. iDestruct "HPQ" as (n2) "HPQ".
    rewrite bi.and_exist_r. iDestruct "HPQ" as (n1) "HPQ".
    iAssert (own ord_later_name (mono_ord_ub n1)) as "#Hn1". { iDestruct "HPQ" as "[[$ _] _]". }
    iAssert (own ord_later_name (mono_ord_ub n2)) as "#Hn2". { iDestruct "HPQ" as "[_ [$ _]]". }
    iExists (o_min n1 n2).
    iCombine "Hn1 Hn2" as "Hn". rewrite mono_ord_ub_op. iFrame "#".
    iIntros (??) "#Hn'".
    iSplit.
    - iDestruct "HPQ" as "[[_ HP] _]". iApply ("HP" with "[%] Hn'"). etrans; [done|]. apply o_min_le_l.
    - iDestruct "HPQ" as "[_ [_ HP]]". iApply ("HP" with "[%] Hn'"). etrans; [done|]. apply o_min_le_r.
  Qed.

  Lemma ord_loeb P:
    ord_later_ctx -∗
    □ (□ ▷ₒ P -∗ P) -∗
    P.
  Proof.
    unseal. iDestruct 1 as (n) "#Hub". iIntros "#Hl".
    iInduction n as [] "IH" using o_lt_ind.
    iApply "Hl". iModIntro. iIntros "_".
    iExists _. iFrame "#".
    iIntros (??) "#?". iApply "IH"; [done|]. by iModIntro.
  Qed.

  Lemma ord_later_sep_pers P1 P2:
    □ ▷ₒ (P1 ∗ P2) -∗
    (□ ▷ₒ P1 ∗ □ ▷ₒ P2).
  Proof.
    iIntros "#HP". iSplit; iModIntro; iApply (ord_later_mono with "[$]"); by iIntros "[??]".
  Qed.

  Lemma ord_later_elim P Q n:
    ▷ₒ P -∗
    ord_later_auth n -∗
    (ord_later_auth n ==∗ ∃ n', ⌜oS n' ⊆ n⌝ ∗ ord_later_auth n' ∗ (ord_later_auth n' -∗ P ==∗ Q)) -∗
    |==> Q.
  Proof.
    iIntros "HP Ha Hwand".
    iDestruct (ord_later_ctx_alloc with "[$]") as "#?".
    unseal.
    iDestruct ("HP" with "[$]") as (n1) "[Hn1 HP]".
    iDestruct (own_valid_2 with "Ha Hn1") as %?%mono_ord_both_valid.
    iMod ("Hwand" with "Ha") as (??) "[Ha Hwand]".
    rewrite {1}mono_ord_auth_ub_op. iDestruct "Ha" as "[Ha Hn']".
    iDestruct ("HP" with "[%] Hn'") as "HP". { by etrans. }
    by iApply ("Hwand" with "Ha").
  Qed.
End lemmas.

(** Proof mode instances *)
Global Instance elim_modal_ord_later `{!ord_laterGS Σ} p P Q :
  ElimModal True p false (▷ₒ P) P (▷ₒ Q) Q.
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim.
  iIntros (?) "[??]". by iApply (ord_later_mono with "[$]").
Qed.

Class MaybeIntoOrdLater `{!ord_laterGS Σ} (P : iProp Σ) (Q : iProp Σ) :=
  maybe_into_ord_later : P ⊢ ▷ₒ Q.
Global Arguments MaybeIntoOrdLater {_ _} _%I _%I.
Global Arguments maybe_into_ord_later {_ _} _%I _%I {_}.
Global Hint Mode MaybeIntoOrdLater + + ! -  : typeclass_instances.

Class IntoOrdLater `{!ord_laterGS Σ} (P : iProp Σ) (Q : iProp Σ) :=
  into_ord_later :> MaybeIntoOrdLater P Q.
Global Arguments IntoOrdLater {_ _} _%I _%I.
Global Arguments into_ord_later {_ _} _%I _%I {_}.
Global Hint Mode IntoOrdLater + + ! -  : typeclass_instances.

Global Instance maybe_into_ord_later_default `{!ord_laterGS Σ} (P : iProp Σ) :
  MaybeIntoOrdLater P P | 1000.
Proof. apply ord_later_intro. Qed.

Global Instance into_ord_later_ord_later `{!ord_laterGS Σ} (P : iProp Σ) :
  IntoOrdLater (▷ₒ P) P | 1000.
Proof. done. Qed.

Lemma modality_ord_later_mixin `{!ord_laterGS Σ} :
  modality_mixin ord_later (MIEnvTransform MaybeIntoOrdLater) (MIEnvTransform MaybeIntoOrdLater).
Proof.
  split; simpl.
  - split.
    + move => ?? ->. apply ord_later_pers.
    + move => ??. apply ord_later_and.
  - iIntros (???). done.
  - apply ord_later_intro.
  - iIntros (?? Himpl) "HP". iApply (ord_later_mono with "HP"). iApply Himpl.
  - iIntros (??) "[??]". iApply ord_later_sep. iFrame.
Qed.
Definition modality_ord_later `{!ord_laterGS Σ} :=
  Modality ord_later modality_ord_later_mixin.

Global Instance from_modal_ord_later `{!ord_laterGS Σ} P :
  FromModal True modality_ord_later (▷ₒ P) (▷ₒ P) P.
Proof. rewrite /FromModal/=. iIntros (?) "$".  Qed.
