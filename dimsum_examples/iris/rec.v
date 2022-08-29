From iris.base_logic.lib Require Import ghost_map.
From dimsum.core.iris Require Export iris.
From dimsum.examples Require Export rec.
From dimsum.core Require Import spec_mod.
From dimsum.examples Require Import memmove.
Set Default Proof Using "Type".

Local Open Scope Z_scope.

Class recPreGS (Σ : gFunctors) := RecPreGS {
  rec_heap_ghost_map_preG :> ghost_mapG Σ loc val;
  rec_alloc_ghost_map_preG :> ghost_mapG Σ prov nat;
  rec_fn_ghost_map_preG :> ghost_mapG Σ string fndef;
}.

Class recGS (Σ : gFunctors) := RecGS {
  rec_heap_ghost_mapG :> ghost_mapG Σ loc val;
  rec_alloc_ghost_mapG :> ghost_mapG Σ prov nat;
  rec_fn_ghost_mapG :> ghost_mapG Σ string fndef;
  rec_heap_name : gname;
  rec_alloc_name : gname;
  rec_fn_name : gname;
}.

Definition recΣ : gFunctors :=
  #[ ghost_mapΣ loc val; ghost_mapΣ prov nat; ghost_mapΣ string fndef ].

Global Instance subG_recΣ Σ :
  subG recΣ Σ → recPreGS Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{!recGS Σ}.

  Definition rec_mapsto_def (l : loc) (q : dfrac) (v : val) : iProp Σ :=
    ghost_map_elem rec_heap_name l q v.
  Local Definition rec_mapsto_aux : seal (@rec_mapsto_def).
  Proof. by eexists. Qed.
  Definition rec_mapsto := rec_mapsto_aux.(unseal).
  Local Definition rec_mapsto_unseal :
    @rec_mapsto = @rec_mapsto_def := rec_mapsto_aux.(seal_eq).

  Definition rec_mapsto_auth (h : gmap loc val) : iProp Σ :=
    ghost_map_auth rec_heap_name 1 h.

  Definition rec_fn_mapsto_def (f : string) (fn : fndef) : iProp Σ :=
    ghost_map_elem rec_fn_name f DfracDiscarded fn.
  Local Definition rec_fn_mapsto_aux : seal (@rec_fn_mapsto_def).
  Proof. by eexists. Qed.
  Definition rec_fn_mapsto := rec_fn_mapsto_aux.(unseal).
  Local Definition rec_fn_mapsto_unseal :
    @rec_fn_mapsto = @rec_fn_mapsto_def := rec_fn_mapsto_aux.(seal_eq).

  Definition rec_fn_auth (fns : gmap string fndef) : iProp Σ :=
    ghost_map_auth rec_fn_name 1 fns.

  Definition rec_state_interp (σ : rec_state) : iProp Σ :=
    rec_mapsto_auth (h_heap (st_heap σ)) ∗ rec_fn_auth (st_fns σ).
End definitions.

Notation "l ↦ v" := (rec_mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.
Notation "f ↪ fn" := (rec_fn_mapsto f fn)
  (at level 20, format "f  ↪  fn") : bi_scope.

Local Ltac unseal := rewrite
  ?rec_mapsto_unseal /rec_mapsto_def /rec_mapsto_auth
  ?rec_fn_mapsto_unseal /rec_fn_mapsto_def /rec_fn_auth.

Section lemmas.
  Context `{!recGS Σ}.

  Global Instance rec_fn_mapsto_pers f fn : Persistent (f ↪ fn).
  Proof. unseal. apply _. Qed.

  Lemma rec_fn_lookup f fn fns :
    rec_fn_auth fns -∗ f ↪ fn -∗ ⌜fns !! f = Some fn⌝.
  Proof. unseal. apply ghost_map_lookup. Qed.

End lemmas.

Program Canonical Structure rec_mod_lang {Σ} `{!recGS Σ} := {| (*  *)
  mexpr := expr;
  mectx := list expr_ectx;
  mfill := expr_fill;
  mcomp_ectx := flip app;
  mtrans := rec_trans;
  mexpr_rel σ e := e = st_expr σ;
  mstate_interp := rec_state_interp;
|}.
Next Obligation. move => *. by rewrite expr_fill_app. Qed.

Section lifting.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Lemma sim_rec_Call_internal f fn es Π Φ vs `{!AsVals es vs None} :
    length vs = length (fd_args fn) →
    f ↪ fn -∗
    ▷ₒ Φ (AllocA fn.(fd_vars) (subst_l fn.(fd_args) vs fn.(fd_body))) Π -∗
    TGT Call f es [{ Π }] {{ Φ }}.
  Proof.
    destruct AsVals0. iIntros (?) "Hfn HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e h fns] ??? Hp) "[Hh Hfns]". simplify_eq/=.
    iDestruct (rec_fn_lookup with "[$] [$]") as %?.
    rewrite right_id_L in Hp.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; try naive_solver.
      move => /= ??? e' [_ Heq]. by apply: list_expr_val_inv. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    do 2 iModIntro. iSplit!. iFrame.
    by iApply sim_tgt_expr_stop.
  Qed.
End lifting.

Section memmove.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Lemma sim_memcpy Π Φ d d' s' s n o hvs :
    n = Z.of_nat (length hvs) →
    o = 1 ∨ o = -1 →
    d' = (if bool_decide (o = 1) then d else d +ₗ (- n + 1)) →
    s' = (if bool_decide (o = 1) then s else s +ₗ (- n + 1)) →
    (if bool_decide (o = 1) then d.1 = s.1 → d.2 ≤ s.2 else d.1 = s.1 → s.2 ≤ d.2) →
    "memcpy" ↪ memcpy_rec -∗
    ([∗ list] i↦v∈hvs, (s' +ₗ i) ↦ v) -∗
    ([∗ list] i↦_∈hvs, ∃ v, (d' +ₗ i) ↦ v) -∗
    (([∗ list] i↦v∈hvs, (s' +ₗ i) ↦ v) -∗ ([∗ list] i↦v∈hvs, (d' +ₗ i) ↦ v) -∗ Φ (Val 0) Π) -∗
    TGT Call "memcpy" [Val (ValLoc d); Val $ ValLoc s; Val $ ValNum n; Val $ ValNum o] [{ Π }] {{ Φ }}.
  Proof.
    iIntros (Hn Ho Hd' Hs' Hle) "#Hf Hs Hd HΦ".
    iApply sim_tgt_expr_ctx. iIntros "#?".
    iRevert (d d' s s' n hvs Hn Hd' Hs' Hle) "Hs Hd HΦ".
    iApply ord_loeb; [done|].
    iIntros "!> #-#IH" (d d' s s' n hvs Hn Hd' Hs' Hle) "Hs Hd HΦ". simplify_eq.
    iApply (sim_tgt_expr_bind []).
    iApply (sim_rec_Call_internal with "Hf"); [done|]. iModIntro => /=.
  Abort.

  Lemma sim_memmove Π Φ d s n hvs :
    n = Z.of_nat (length hvs) →
    "memmove" ↪ memmove_rec -∗
    "memcpy" ↪ memcpy_rec -∗
    □ (∀ l1 l2 Φ,
        (∀ b, ⌜l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2)⌝ -∗ Φ (Val (ValBool b)) Π) -∗
          TGT Call "locle" [Val (ValLoc l1); Val $ ValLoc l2] [{ Π }] {{ Φ }}) -∗
    ([∗ list] i↦v∈hvs, (s +ₗ i) ↦ v) -∗
    ([∗ list] i↦_∈hvs, ∃ v, (d +ₗ i) ↦ v) -∗
    (([∗ list] i↦v∈hvs, (s +ₗ i) ↦ v) -∗ ([∗ list] i↦v∈hvs, (d +ₗ i) ↦ v) -∗ Φ (Val 0) Π) -∗
    TGT Call "memmove" [Val (ValLoc d); Val $ ValLoc s; Val $ ValNum n] [{ Π }] {{ Φ }}.
  Proof.
    iIntros (->) "#Hmemmove #Hmemcpy #Hlocle Hs Hd HΦ".
    iApply (sim_tgt_expr_bind []).
    iApply (sim_rec_Call_internal with "Hmemmove"); [done|]. iModIntro => /=.
  Abort.

  Lemma sim_locle Π Φ l1 l2 :
    (∀ b, ⌜l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2)⌝ -∗ Φ (Val (ValBool b)) Π) -∗
    TGT Call "locle" [Val (ValLoc l1); Val $ ValLoc l2] [{ Π }] {{ Φ }}.
  Proof. Admitted.


End memmove.

Section sim.
  Context {Σ : gFunctors} {EV : Type} `{!dimsumGS Σ}.

  Definition sim_tgt_handler (m_t m_s : mod_trans EV)
    (Π_s : (option EV → m_state m_s → iProp Σ) → iProp Σ) :
    option EV → ((m_state m_t → iProp Σ) → iProp Σ) → iProp Σ :=
    λ κ Pσ, (Π_s (λ κ' σ_s', ⌜κ = κ'⌝ ∗ Pσ (λ σ_t', σ_t' ⪯{m_t, m_s} σ_s')))%I.

  Lemma sim_tgt_handler_intro m_t m_s σ_t σ_s :
    σ_t ≈{m_t}≈>ₜ sim_tgt_handler m_t m_s (sim_src m_s σ_s) -∗ σ_t ⪯{m_t, m_s} σ_s.
  Proof. Admitted.
End sim.

From dimsum.core Require Import product.

Section map.
  Context {Σ : gFunctors} {EV1 EV2 : Type} {S : Type} `{!dimsumGS Σ}.
  Implicit Types (f : map_mod_fn EV1 EV2 S).

  Lemma sim_tgt_map m f σ σf Π :
    (σ ≈{m}≈>ₜ λ κ Pσ,
      ∀ κ' σf' ok, ⌜if κ is Some e then f σf e κ' σf' ok else κ' = None ∧ σf' = σf ∧ ok = true⌝ -∗
         Π κ' (λ P, Pσ (λ σ', P (σ', (σf', ok))))) -∗
    (σ, (σf, true)) ≈{map_trans m f}≈>ₜ Π.
  Proof.
    iIntros "Hsim".
    pose (F := (λ σ Π', (∀ κ Pσ, Π' κ Pσ -∗
         ∀ κ' σf' ok, ⌜if κ is Some e then f σf e κ' σf' ok else κ' = None ∧ σf' = σf ∧ ok = true⌝ -∗
          Π κ' (λ P, Pσ (λ σ', P (σ', (σf', ok))))) -∗ (σ, (σf, true)) ≈{map_trans m f}≈>ₜ Π)%I).
    iAssert (∀ Π, σ ≈{ m }≈>ₜ Π -∗ F σ Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"). iIntros (??) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_tgt_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros "Hc".
    iApply (sim_tgt_ctx with "[-]"). iIntros "?".
    iApply (sim_tgt_bi_mono1 with "[-]").
    iApply (fupd_sim_tgt with "[-]").
    iMod ("Hsim" with "[$]") as "[[% [? HP]]| Hs ]". {
      iModIntro. iDestruct ("Hc" with "[$] [//]") as "Hc".
      iApply (sim_tgt_stop with "[-]").
      iApply (bi_mono1_intro with "Hc"). iIntros (?) "?".
      iDestruct ("HP" with "[$]") as "$".
    }
    iModIntro. iApply (sim_tgt_step with "[-]"). iIntros (?? Hstep). inv_all/= @m_step.
    all: iMod ("Hs" with "[//]") as "Hs"; do 2 iModIntro.
    - do 2 case_match; simplify_eq. iDestruct "Hs" as "[[% [? HP]]|[%[%[% HF]]]]".
      + iDestruct ("Hc" with "[$] [//]") as "Hc".
        iLeft. iApply (bi_mono1_intro with "Hc"). iIntros (?) "?".
        iDestruct ("HP" with "[$]") as (??) "?".
        iExists (_, _). iFrame. iSplit!.
      + iRight. iExists (_, _). iSplit!; [done|].
        iApply (sim_tgt_wand with "[-] []"); [by iApply "HF"|].
        iIntros (??) "HΠ". by iApply bi_mono1_intro'.
    - iDestruct "Hs" as "[[% [? HP]]|[%[%[% HF]]]]"; simplify_eq.
      iDestruct ("Hc" with "[$] [//]") as "Hc".
      iLeft. iExists _. iFrame. iIntros (?) "?".
      iDestruct ("HP" with "[$]") as (??) "?".
      iExists (_, _). iFrame. iSplit!.
  Qed.

  Lemma sim_src_map m f σ σf Π `{!VisNoAng m} :
    (σ ≈{m}≈>ₛ λ κ σ',
      ∃ κ' σf' ok, ⌜if κ is Some e then f σf e κ' σf' ok else κ' = None ∧ σf' = σf ∧ ok = true⌝ ∗
         Π κ' (σ', (σf', ok))) -∗
    (σ, (σf, true)) ≈{map_trans m f}≈>ₛ Π.
  Proof.
    iIntros "Hsim".
    pose (F := (λ σ Π', (∀ κ σ', Π' κ σ' -∗
         ∃ κ' σf' ok, ⌜if κ is Some e then f σf e κ' σf' ok else κ' = None ∧ σf' = σf ∧ ok = true⌝ ∗
          Π κ' (σ', (σf', ok))) -∗ (σ, (σf, true)) ≈{map_trans m f}≈>ₛ Π)%I).
    iAssert (∀ Π, σ ≈{ m }≈>ₛ Π -∗ F σ Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"). iIntros (??) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_src_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros "Hc".
    iApply (sim_src_ctx with "[-]"). iIntros "?".
    iApply (fupd_sim_src with "[-]").
    iMod ("Hsim" with "[$]") as "[?| [%κ [% [% Hs]]] ]". {
      iModIntro. iApply (sim_src_stop with "[-]").
      iDestruct ("Hc" with "[$]") as (???[?[??]]) "Hc". by simplify_eq.
    }
    destruct κ.
    - exploit vis_no_all; [done|] => -[σ'' ?].
      iMod ("Hs" with "[%]") as "Hs"; [naive_solver|]. iModIntro.
      iDestruct ("Hc" with "[$]") as (????) "Hs".
      iApply (sim_src_step_end with "[-]"). { econs. { apply: ProductStepBoth; [done|]. by econs. } done. }
      iIntros ([σ' ?] [??]) "!>". have ? : σ' = σ'' by naive_solver. by simplify_eq.
    - iModIntro. iApply (sim_src_step with "[-]"). { econs; [by econs|done]. }
      iIntros ([??][??]). simplify_eq. iMod ("Hs" with "[//]") as "HF". iModIntro.
      by iApply "HF".
  Qed.
End map.

From dimsum.core Require Import state_transform.

Section state_transform.
  Context {Σ : gFunctors} {EV : Type} {S : Type} `{!dimsumGS Σ}.

  Lemma sim_tgt_state_transform (m : mod_trans EV) σ' (R : S → m.(m_state) → Prop) σ Π :
   (∀ σ σ1 σ2, R σ σ1 → R σ σ2 → σ1 = σ2) →
   (∀ σ1 σ σ' κ Pσ, m_step m σ κ Pσ → Pσ σ' → R σ1 σ → ∃ σ'', R σ'' σ') →
   R σ σ' →
   (σ' ≈{m}≈>ₜ λ κ Pσ, Π κ (λ P, Pσ (λ σ'', ∀ σ''', ⌜R σ''' σ''⌝ -∗ P σ'''))) -∗
    σ ≈{state_transform_trans m R}≈>ₜ Π.
  Proof.
    iIntros (Heq HRstep HR) "Hsim".
    pose (F := (λ σ' Π', ∀ σ,
                   ⌜R σ σ'⌝ -∗
                   (∀ κ Pσ, Π' κ Pσ -∗ Π κ (λ P, Pσ (λ σ'', ∀ σ''', ⌜R σ''' σ''⌝ -∗ P σ'''))) -∗
                   σ ≈{state_transform_trans m R}≈>ₜ Π)%I).
    iAssert (∀ Π, σ' ≈{ m }≈>ₜ Π -∗ F σ' Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"); [done|]. iIntros (??) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_tgt_ind with "[] Hsim"). { solve_proper. }
    clear σ' σ HR. iIntros "!>" (σ'?) "Hsim". iIntros (σ HR) "Hc".
    iApply (sim_tgt_ctx with "[-]"). iIntros "?".
    iApply (sim_tgt_bi_mono1 with "[-]").
    iApply (fupd_sim_tgt with "[-]").
    iMod ("Hsim" with "[$]") as "[[% [HΠ HP]]| Hs ]". {
      iModIntro. iApply (sim_tgt_stop with "[-]").
      iApply (bi_mono1_intro with "[Hc HΠ]"); [by iApply "Hc"|] => /=.
      iIntros (?) "?". iDestruct ("HP" with "[$]") as "HP". by iApply "HP".
    }
    iModIntro. iApply (sim_tgt_step with "[-]"). iIntros (?? Hstep). inv_all/= @m_step.
    have ?: σ' = σ'0 by naive_solver. subst.
    iMod ("Hs" with "[//]") as "Hs"; do 2 iModIntro.
    iDestruct "Hs" as "[[% [? HP]]|[%[%[% HF]]]]".
    - iDestruct ("Hc" with "[$]") as "Hc".
      iLeft. iApply (bi_mono1_intro with "Hc"). iIntros (?) "?".
      iDestruct ("HP" with "[$]") as (??) "HP".
      exploit HRstep; [done..|] => -[??].
      iSplit!; [done..|]. by iApply "HP".
    - iRight. simplify_eq. exploit HRstep; [done..|] => -[??].
      iSplit!; [done..|]. iApply (sim_tgt_wand with "[-] []"); [by iApply "HF"|].
      iIntros (??) "HΠ". by iApply bi_mono1_intro'.
  Qed.

  Lemma sim_src_state_transform (m : mod_trans EV) σ' (R : S → m.(m_state) → Prop) σ Π :
   R σ σ' →
   (σ' ≈{m}≈>ₛ λ κ σ'', ∀ σ''', ⌜R σ''' σ''⌝ -∗ Π κ σ''') -∗
    σ ≈{state_transform_trans m R}≈>ₛ Π.
  Proof.
    iIntros (HR) "Hsim".
    pose (F := (λ σ' Π', ∀ σ,
                   ⌜R σ σ'⌝ -∗
                   (∀ κ σ'', Π' κ σ'' -∗ ∀ σ''', ⌜R σ''' σ''⌝ -∗ Π κ σ''') -∗
                   σ ≈{state_transform_trans m R}≈>ₛ Π)%I).
    iAssert (∀ Π, σ' ≈{ m }≈>ₛ Π -∗ F σ' Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"); [done|]. iIntros (??) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_src_ind with "[] Hsim"). { solve_proper. }
    clear σ' σ HR. iIntros "!>" (σ'?) "Hsim". iIntros (σ HR) "Hc".
    iApply (sim_src_ctx with "[-]"). iIntros "?".
    iApply (fupd_sim_src with "[-]").
    iMod ("Hsim" with "[$]") as "[?| [%κ [% [% Hs]]] ]". {
      iModIntro. iApply (sim_src_stop with "[-]"). by iApply ("Hc" with "[$]").
    }
    iModIntro. iApply (sim_src_step with "[-]"); [by econs|].
    iIntros (? [?[??]]). iMod ("Hs" with "[//]") as "Hs". iModIntro.
    case_match.
    - by iApply ("Hc" with "Hs").
    - by iApply ("Hs" with "[//]").
  Qed.
End state_transform.

From dimsum.core Require Import seq_product.

Section seq_product.
  Context {Σ : gFunctors} {EV : Type} `{!dimsumGS Σ}.

  Lemma sim_tgt_seq_product_None (m1 m2 : mod_trans EV) σ1 σ2 Π :
    (∀ p, ▷ₒ Π (Some (SPENone p)) (λ P, P (p, σ1, σ2))) -∗
    (SPNone, σ1, σ2) ≈{seq_product_trans m1 m2}≈>ₜ Π.
  Proof.
    iIntros "HΠ". iApply (sim_tgt_bi_mono with "[-]").
    iApply (sim_tgt_step_end with "[-]"). iIntros (???). inv_all @m_step. iSpecialize ("HΠ" $! _).
    do 2 iModIntro. iApply (bi_mono1_intro with "HΠ"). iIntros (?) "?".
    iApply bi_mono1_intro'. iSplit!.
  Qed.

  Lemma sim_src_seq_product_None p (m1 m2 : mod_trans EV) σ1 σ2 Π :
    Π (Some (SPENone p)) (p, σ1, σ2) -∗
    (SPNone, σ1, σ2) ≈{seq_product_trans m1 m2}≈>ₛ Π.
  Proof.
    iIntros "HΠ". iApply (sim_src_step_end with "[-]"); [by econs|].
    iIntros (??). by simplify_eq.
  Qed.

  Lemma sim_tgt_seq_product_left (m1 m2 : mod_trans EV) σ1 σ2 Π :
    (σ1 ≈{m1}≈>ₜ λ κ Pσ,
      ∀ s', ⌜if κ is None then s' = SPLeft else True⌝ -∗
         Π ((λ e, SPELeft e s') <$> κ) (λ P, Pσ (λ σ', P (s', σ', σ2)))) -∗
    (SPLeft, σ1, σ2) ≈{seq_product_trans m1 m2}≈>ₜ Π.
  Proof.
    iIntros "Hsim".
    pose (F := (λ σ Π', (∀ κ Pσ, Π' κ Pσ -∗
         ∀ s', ⌜if κ is None then s' = SPLeft else True⌝ -∗
         Π ((λ e, SPELeft e s') <$> κ) (λ P, Pσ (λ σ', P (s', σ', σ2)))) -∗
         (SPLeft, σ, σ2) ≈{seq_product_trans m1 m2}≈>ₜ Π)%I).
    iAssert (∀ Π, σ1 ≈{ m1 }≈>ₜ Π -∗ F σ1 Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"). iIntros (??) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_tgt_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros "Hc".
    iApply (sim_tgt_ctx with "[-]"). iIntros "?".
    iApply (sim_tgt_bi_mono1 with "[-]").
    iApply (fupd_sim_tgt with "[-]").
    iMod ("Hsim" with "[$]") as "[[% [? HP]]| Hs ]". {
      iModIntro. iDestruct ("Hc" with "[$] [//]") as "Hc".
      iApply sim_tgt_stop.
      iApply (bi_mono1_intro with "[Hc] [-]"); [done|].
      iIntros (?) "?". by iDestruct ("HP" with "[$]") as "HP".
    }
    iModIntro. iApply (sim_tgt_step with "[-]"). iIntros (?? Hstep). inv_all/= @m_step.
    iMod ("Hs" with "[//]") as "Hs"; do 2 iModIntro.
    iDestruct "Hs" as "[[% [? HP]]|[%[%[% HF]]]]"; simplify_eq/=.
    - iDestruct ("Hc" with "[$] [//]") as "Hc".
      iLeft. iApply (bi_mono1_intro with "Hc").
      iIntros (?) "?".
      iDestruct ("HP" with "[$]") as (??) "?".
      iExists (_, _, _). iSplit!; [done|]. by iFrame.
    - iRight. iExists (_, _, _). iSplit!; [done|].
      iApply (sim_tgt_wand with "[-] []"); [by iApply "HF"|].
      iIntros (??) "HΠ". by iApply bi_mono1_intro'.
  Qed.

End seq_product.

Section link.
  Context {Σ : gFunctors} {EV : Type} {S : Type} `{!dimsumGS Σ}.
  Implicit Types (R : seq_product_case → S → EV → seq_product_case → S → EV → bool → Prop).

  Lemma sim_tgt_link_None R m1 m2 s σ1 σ2 Π :
    ▷ₒ (∀ e p' s' e' ok,
        ⌜R SPNone s e p' s' e' ok⌝ -∗
        Π (Some (Incoming, e')) (λ P, P (link_to_case ok p' e', s', σ1, σ2))) -∗
    (MLFNone, s, σ1, σ2) ≈{link_trans R m1 m2}≈>ₜ Π.
  Proof.
    iIntros "HΠ".
    iApply (sim_tgt_bi_mono1 with "[-]").
    iApply sim_tgt_state_transform; [naive_solver| admit |done|] => /=.
    iApply (sim_tgt_map with "[-]").
    iApply sim_tgt_seq_product_None. iIntros (p) "!>". iIntros (????).
    inv_all @link_filter.
    iApply (bi_mono1_intro with "[HΠ]"); [by iApply "HΠ"|] => /=.
    iIntros (?) "?". iIntros ([[[??]?]?] ?); simplify_eq/=. by repeat case_match; simplify_eq/=.
  Admitted.

  Definition link_tgt_left_handler R (m1 m2 : mod_trans (io_event EV))
    (Π : option (io_event EV) → ((link_case EV * S * m_state m1 * m_state m2 → iProp Σ) → iProp Σ) → iProp Σ)
    (s : S) (σ2 : m_state m2)
    : option (io_event EV) → ((m_state m1 → iProp Σ) → iProp Σ) → iProp Σ :=
    λ κ Pσ,
      match κ with
            | None => Π None (λ P, Pσ (λ σ1', P (MLFLeft, s, σ1', σ2)))
            | Some e => ∀ p' s' e' ok, ⌜R SPLeft s e.2 p' s' e' ok⌝ -∗ ⌜e.1 = Outgoing⌝ -∗
                 Π (if p' is SPNone then Some (Outgoing, e') else None)
                 (λ P, Pσ (λ σ1', P (link_to_case ok p' e', s', σ1', σ2)))
            end%I.

  Lemma sim_tgt_link_left R m1 m2 s σ1 σ2 Π :
    σ1 ≈{m1}≈>ₜ link_tgt_left_handler R m1 m2 Π s σ2 -∗
    (MLFLeft, s, σ1, σ2) ≈{link_trans R m1 m2}≈>ₜ Π.
  Proof.
    iIntros "Hsim".
    iApply (sim_tgt_bi_mono1 with "[-]").
    iApply sim_tgt_state_transform; [naive_solver| admit |done|] => /=.
    iApply (sim_tgt_map with "[-]").
    iApply sim_tgt_seq_product_left.
    iApply (sim_tgt_bi_mono2 with "[-]").
    iApply (sim_tgt_wand with "Hsim").
    iIntros (κ ?) "Hsim". iIntros (??????). destruct κ; destruct!/=.
    - inv_all @link_filter.
      iApply (bi_mono1_intro with "[Hsim]"); [by iApply "Hsim"|].
      iIntros (?) "HP". iApply (bi_mono1_intro with "HP").
      iIntros (?) "?". iIntros ([[[??]?]?]?). simplify_eq/=. by repeat case_match; simplify_eq/=.
    - iApply (bi_mono1_intro with "[Hsim]"); [by iApply "Hsim"|].
      iIntros (?) "HP". iApply (bi_mono1_intro with "HP").
      iIntros (?) "?". iIntros ([[[??]?]?]?). simplify_eq/=. done.
  Admitted.
End link.

Program Definition spec_mod_lang {Σ} (EV S : Type) (state_interp : S → iProp Σ)  : mod_lang EV Σ := {|
  mexpr := spec EV S void;
  mectx := unit;
  mfill _ := id;
  mcomp_ectx _ _:= tt;
  mtrans := spec_trans EV S;
  mexpr_rel σ t := σ.1 ≡ t;
  mstate_interp σ := state_interp σ.2;
|}.
Next Obligation. done. Qed.

Definition spec_mod_lang_unit {Σ} (EV : Type) : mod_lang EV Σ :=
  spec_mod_lang EV unit (λ _, True%I).

Section spec.
  Context `{!dimsumGS Σ} {EV S : Type} {state_interp : S → iProp Σ}.

  Global Instance sim_src_expr_spec_proper :
    Proper ((≡) ==> (=) ==> (=) ==> (⊣⊢)) (sim_src_expr (Λ:=spec_mod_lang EV S state_interp)).
  Proof.
    move => ?? ? ?? -> ?? ->.
    Local Transparent sim_src_expr.
    Local Typeclasses Transparent sim_src_expr.
    iSplit; iIntros "HP" (?) "?"; iIntros (??); simplify_eq/=; iApply ("HP" with "[$]"); iPureIntro => /=.
    all: by etrans; [done|].
    Unshelve. all: exact tt.
  Qed.

  Let X := (spec_mod_lang EV _ state_interp).
  Local Canonical Structure X.

  Lemma sim_src_TAll {T} k Π Φ :
    (∀ x, SRC (k x) [{ Π }] {{ Φ }}) -∗
    SRC (Spec.bind (TAll T) k) [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_src_expr_step_None. iIntros (?[??]?) "?". simplify_eq/=. iModIntro.
    iExists _. iSplit. { iPureIntro. by econs. }
    iIntros ([??] [??]) "!>". simplify_eq. iSplit!. iFrame. iApply "Hsim".
  Qed.

  Lemma sim_src_TExist {T} x k Π Φ :
    SRC (k x) [{ Π }] {{ Φ }} -∗
    SRC (Spec.bind (TExist T) k) [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_src_expr_step_None. iIntros (?[??]?) "?". simplify_eq/=. iModIntro.
    iExists _. iSplit. { iPureIntro. by econs. }
    iIntros ([??] ?) "!>". simplify_eq. iSplit!. iFrame.
  Qed.

  Lemma sim_src_TAssume k Π Φ P :
    (⌜P⌝ -∗ SRC (k tt) [{ Π }] {{ Φ }}) -∗
    SRC (Spec.bind (TAssume P) k) [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_src_expr_step_None. iIntros (?[??]?) "?". simplify_eq/=. iModIntro.
    iExists _. iSplit. { iPureIntro. by econs. }
    iIntros ([??] [??]) "!>". simplify_eq. iSplit!. iFrame. by iApply "Hsim".
  Qed.

  Lemma sim_src_TAssert k Π Φ (P : Prop) :
    P →
    SRC (k tt) [{ Π }] {{ Φ }} -∗
    SRC (Spec.bind (TAssert P) k) [{ Π }] {{ Φ }}.
  Proof.
    iIntros (?) "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_src_expr_step_None. iIntros (?[??]?) "?". simplify_eq/=. iModIntro.
    iExists _. iSplit. { iPureIntro. by econs. }
    iIntros ([??] ?) "!>". simplify_eq. iSplit!. iFrame.
    Unshelve. done.
  Qed.

  Lemma sim_src_TVis k Π Φ e :
    (∀ σ,
        (∀ Π',
            SRC k tt [{ Π' }] {{ Φ }} -∗
            σ ≈{spec_trans EV S}≈>ₛ Π') -∗
     Π (Some e) σ) -∗
    SRC (Spec.bind (TVis e) k) [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_src_expr_step. iIntros (?[??]?) "?". simplify_eq/=. iModIntro.
    iExists _, _. iSplit. { iPureIntro. by econs. }
    iIntros ([??] ?) "!> HΦ". simplify_eq.
    iApply "Hsim". iIntros (?) "?". by iApply ("HΦ" with "[//] [$]").
  Qed.
End spec.


Section memmove.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Local Canonical Structure spec_mod_lang_unit.

  Context `{!dimsumGS Σ} `{!recGS Σ}.
  Lemma memmove_sim  :
    rec_fn_auth (main_prog ∪ memmove_prog ∪ memcpy_prog) -∗
      (MLFNone, [], rec_init (main_prog ∪ memmove_prog ∪ memcpy_prog), (locle_spec, ())) ⪯{
        rec_link_trans {["main"; "memmove"; "memcpy"]} {["locle"]} rec_trans (spec_trans rec_event ()),
        spec_trans rec_event ()} (main_spec, ()).
  Proof.
    iIntros "?". iApply (sim_tgt_handler_intro with "[-]").
    iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????). destruct!/=.
    case_match; destruct!/=.
    unfold sim_tgt_handler.
    iApply (sim_src_expr_elim with "[] [-]"); [simpl; done..|].
    rewrite /main_spec/TReceive bind_bind.
    iApply (sim_src_TExist (_, _, _)).
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply sim_src_TVis. iIntros (?) "Hsrc". iSplit!.
    iApply (sim_tgt_handler_intro with "[-]"). iApply sim_tgt_stop.
    iApply "Hsrc".
    iApply sim_src_TAssume. iIntros (?).
    iApply sim_src_TAssume. iIntros (?). simplify_eq.
    rewrite bool_decide_true; [|done].
    (* iApply sim_src_expr_stop. *)
  Admitted.
End memmove.

Lemma memmove_refines_spec :
  trefines (rec_link {["main"; "memmove"; "memcpy"]} {["locle"]}
              (rec_mod (main_prog ∪ memmove_prog ∪ memcpy_prog))
              (spec_mod locle_spec tt))
    (spec_mod main_spec tt).
Proof.
  apply (sim_adequacy #[dimsumΣ; recΣ]); [apply _..|].
  iIntros (??) "!>". simpl.
  iApply memmove_sim.
Abort.

(* Idea: construct PI for source level proof from pre and
postconditions of all the external functions instead of constructing
it directly from the used combinators. Maybe one can do the texan
triple trick to force monotonicity of the Π. *)
