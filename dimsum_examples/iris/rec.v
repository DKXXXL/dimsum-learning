From iris.algebra Require Import big_op gmap frac agree dfrac_agree.
From iris.base_logic.lib Require Import ghost_map.
From dimsum.core.iris Require Export iris.
From dimsum.examples Require Export rec.
From dimsum.core Require Import spec_mod.
From dimsum.examples Require Import memmove.
Set Default Proof Using "Type".

Local Open Scope Z_scope.

Definition fnsUR : cmra :=
  agreeR (gmapO string (leibnizO fndef)).

Definition to_fns : gmap string fndef → fnsUR :=
  to_agree.


Class recPreGS (Σ : gFunctors) := RecPreGS {
  rec_mapsto_ghost_map_preG :> ghost_mapG Σ loc val;
  rec_alloc_ghost_map_preG :> ghost_mapG Σ loc Z;
  rec_fn_preG :> inG Σ fnsUR;
}.

Class recGS (Σ : gFunctors) := RecGS {
  rec_mapsto_ghost_mapG :> ghost_mapG Σ loc val;
  rec_alloc_ghost_mapG :> ghost_mapG Σ loc Z;
  rec_fnG :> inG Σ fnsUR;
  rec_mapsto_name : gname;
  rec_alloc_name : gname;
  rec_fn_name : gname;
}.

Definition recΣ : gFunctors :=
  #[ ghost_mapΣ loc val; ghost_mapΣ loc Z; GFunctor fnsUR ].

Global Instance subG_recΣ Σ :
  subG recΣ Σ → recPreGS Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{!recGS Σ}.

  Definition rec_mapsto_def (l : loc) (q : dfrac) (v : val) : iProp Σ :=
    ghost_map_elem rec_mapsto_name l q v.
  Local Definition rec_mapsto_aux : seal (@rec_mapsto_def).
  Proof. by eexists. Qed.
  Definition rec_mapsto := rec_mapsto_aux.(unseal).
  Local Definition rec_mapsto_unseal :
    @rec_mapsto = @rec_mapsto_def := rec_mapsto_aux.(seal_eq).

  Definition rec_mapsto_auth (h : gmap loc val) : iProp Σ :=
    ghost_map_auth rec_mapsto_name 1 h.

  Definition rec_alloc_def (l : loc) (sz : Z) : iProp Σ :=
    ghost_map_elem rec_alloc_name l (DfracOwn 1) sz.
  Local Definition rec_alloc_aux : seal (@rec_alloc_def).
  Proof. by eexists. Qed.
  Definition rec_alloc := rec_alloc_aux.(unseal).
  Local Definition rec_alloc_unseal :
    @rec_alloc = @rec_alloc_def := rec_alloc_aux.(seal_eq).

  Definition rec_alloc_auth (h : gset loc) : iProp Σ :=
    ∃ p,
    ⌜∀ l sz, p !! l = Some sz → sz > 0⌝ ∗
    ⌜∀ l sz, p !! l = Some sz → ∀ l', l'.1 = l.1 → l' ∈ h ↔ l.2 ≤ l'.2 < l.2 + sz⌝ ∗
    ghost_map_auth rec_alloc_name 1 p.

  Definition rec_fn_auth (fns : gmap string fndef) : iProp Σ :=
    own rec_fn_name (to_fns fns).
  Definition rec_fn_mapsto_def (f : string) (fn : option fndef) : iProp Σ :=
    ∃ fns, ⌜fns !! f = fn⌝ ∗ rec_fn_auth fns.
  Local Definition rec_fn_mapsto_aux : seal (@rec_fn_mapsto_def).
  Proof. by eexists. Qed.
  Definition rec_fn_mapsto := rec_fn_mapsto_aux.(unseal).
  Local Definition rec_fn_mapsto_unseal :
    @rec_fn_mapsto = @rec_fn_mapsto_def := rec_fn_mapsto_aux.(seal_eq).

  Definition rec_state_interp (σ : rec_state) : iProp Σ :=
    rec_mapsto_auth (h_heap (st_heap σ)) ∗ rec_alloc_auth (dom (h_heap (st_heap σ))) ∗ rec_fn_auth (st_fns σ).
End definitions.

Notation "l ↦ v" := (rec_mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.
Notation "f ↪ fn" := (rec_fn_mapsto f fn)
  (at level 20, format "f  ↪  fn") : bi_scope.

Local Ltac unseal := rewrite
  ?rec_mapsto_unseal /rec_mapsto_def /rec_mapsto_auth
  ?rec_alloc_unseal /rec_alloc_def /rec_alloc_auth
  ?rec_fn_mapsto_unseal /rec_fn_mapsto_def /rec_fn_auth.

Section lemmas.
  Context `{!recGS Σ}.

  Global Instance rec_fn_auth_pers fns : Persistent (rec_fn_auth fns).
  Proof. unseal. apply _. Qed.

  Global Instance rec_fn_mapsto_pers f fn : Persistent (f ↪ fn).
  Proof. unseal. apply _. Qed.

  Lemma rec_fn_auth_agree fns1 fns2 :
    rec_fn_auth fns1 -∗ rec_fn_auth fns2 -∗ ⌜fns1 = fns2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    move: Hvalid => /to_agree_op_valid.
    by fold_leibniz.
  Qed.

  Lemma rec_fn_intro f fn fns :
    fns !! f = fn → rec_fn_auth fns -∗ f ↪ fn.
  Proof. unseal. iIntros (?) "Htbl". iExists _. by iFrame. Qed.

  Lemma rec_fn_lookup f fn fns :
    rec_fn_auth fns -∗ f ↪ fn -∗ ⌜fns !! f = fn⌝.
  Proof.
    unseal. iIntros "Htbl Hf".
    iDestruct "Hf" as (fns2 ?) "Hf".
    by iDestruct (rec_fn_auth_agree with "Htbl Hf") as %->.
  Qed.

End lemmas.

Lemma recgs_alloc `{!recPreGS Σ} fns :
  ⊢ |==> ∃ H : recGS Σ, rec_mapsto_auth ∅ ∗ rec_alloc_auth ∅ ∗ rec_fn_auth fns.
Proof.
  iMod (own_alloc (to_fns fns)) as (γf) "#Hfns" => //.
  iMod (ghost_map_alloc (V:=val)) as (γh) "[??]".
  iMod (ghost_map_alloc (V:=Z)) as (γa) "[??]".

  iModIntro. iExists (RecGS _ _ _ _ γh γa γf). iFrame "#∗".
  iExists ∅. iFrame. iPureIntro; split!.
Qed.

Record expr_heap := ExprHeap {
 eh_expr : expr;
 eh_heap : option heap_state;
}.
Add Printing Constructor expr_heap.

Definition expr_heap_fill (K : list expr_ectx) (e : expr_heap) : expr_heap :=
  ExprHeap (expr_fill K (eh_expr e)) (eh_heap e).

Arguments expr_heap_fill !_ _ /.

Notation "e @ h" := (ExprHeap e (Some h)) (at level 14) : stdpp_scope.
Notation "e @ -" := (ExprHeap e None) (at level 14, only parsing) : stdpp_scope.
Notation "e" := (ExprHeap e None) (at level 14, only printing) : stdpp_scope.

Program Canonical Structure rec_mod_lang {Σ} `{!recGS Σ} := {|
  mexpr := expr_heap;
  mectx := list expr_ectx;
  mfill := expr_heap_fill;
  mcomp_ectx := flip app;
  mtrans := rec_trans;
  mexpr_rel σ e := st_expr σ = eh_expr e ∧ if eh_heap e is Some h then st_heap σ = h else True;
  mstate_interp := rec_state_interp;
|}.
Next Obligation. move => ???? [??]/=. by rewrite /expr_heap_fill/= expr_fill_app. Qed.

Section lifting.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Lemma sim_tgt_rec_Call_internal f fn es Π Φ vs `{!AsVals es vs None} :
    length vs = length (fd_args fn) →
    f ↪ Some fn -∗
    ▷ₒ Φ (AllocA fn.(fd_vars) (subst_l fn.(fd_args) vs fn.(fd_body)) @ -) Π -∗
    TGT Call f es @ - [{ Π }] {{ Φ }}.
  Proof.
    destruct AsVals0. iIntros (?) "Hfn HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e h fns] ?? [??] Hp) "[Hh [Ha Hfns]]". simplify_eq/=.
    iDestruct (rec_fn_lookup with "[$] [$]") as %?.
    rewrite right_id_L in Hp.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; try naive_solver.
      move => /= ??? e' [_ Heq]. by apply: list_expr_val_inv. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    do 2 iModIntro. iExists _, (_ @ -). iSplit!. iFrame.
    by iApply sim_tgt_expr_stop2.
  Qed.

  Lemma sim_tgt_rec_Waiting fns h Π Φ (b : bool) :
    rec_fn_auth fns -∗
    (rec_mapsto_auth (h_heap h) -∗
     rec_alloc_auth (dom (h_heap h)) -∗
     (∀ f fn vs h', ⌜fns !! f = Some fn⌝ -∗
       ▷ₒ Π (Some (Incoming, ERCall f vs h')) (λ P,
         ∀ σ,
           (rec_mapsto_auth (h_heap h') -∗
            rec_alloc_auth (dom (h_heap h')) -∗
            σ ⤇ₜ λ Π', TGT Call f (Val <$> vs) @ - [{ Π' }] {{ Φ }}) -∗
           P σ)) ∧
      ∀ v h', ⌜b⌝ -∗
       ▷ₒ Π (Some (Incoming, ERReturn v h')) (λ P, True)) -∗
    TGT Waiting b @ h [{ Π }] {{ Φ }}.
  Proof.
    iIntros "#Hfns HΦ".
    iApply sim_tgt_expr_step => /=. iIntros (? [e h0 fns0] ?? [??] Hp) "[Hh [Ha Hfns']]". simplify_eq/=.
    iDestruct (rec_fn_auth_agree with "Hfns' Hfns") as %?. subst.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    - iDestruct ("HΦ" with "[$] [$]") as "[HΦ _]". iDestruct ("HΦ" with "[//]") as "?".
      do 2 iModIntro. admit.
    - iDestruct ("HΦ" with "[$] [$]") as "[_ HΦ]". iDestruct ("HΦ" with "[//]") as "?".
      do 2 iModIntro. admit.
  Admitted.
End lifting.

Section memmove.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Lemma sim_memcpy Π Φ d d' s' s n o hvs :
    n = Z.of_nat (length hvs) →
    o = 1 ∨ o = -1 →
    d' = (if bool_decide (o = 1) then d else d +ₗ (- n + 1)) →
    s' = (if bool_decide (o = 1) then s else s +ₗ (- n + 1)) →
    (if bool_decide (o = 1) then d.1 = s.1 → d.2 ≤ s.2 else d.1 = s.1 → s.2 ≤ d.2) →
    "memcpy" ↪ Some memcpy_rec -∗
    ([∗ list] i↦v∈hvs, (s' +ₗ i) ↦ v) -∗
    ([∗ list] i↦_∈hvs, ∃ v, (d' +ₗ i) ↦ v) -∗
    (([∗ list] i↦v∈hvs, (s' +ₗ i) ↦ v) -∗ ([∗ list] i↦v∈hvs, (d' +ₗ i) ↦ v) -∗ Φ (Val 0 @ -) Π) -∗
    TGT Call "memcpy" [Val (ValLoc d); Val $ ValLoc s; Val $ ValNum n; Val $ ValNum o] @ - [{ Π }] {{ Φ }}.
  Proof.
    iIntros (Hn Ho Hd' Hs' Hle) "#Hf Hs Hd HΦ".
    iApply sim_tgt_expr_ctx. iIntros "#?".
    iRevert (d d' s s' n hvs Hn Hd' Hs' Hle) "Hs Hd HΦ".
    iApply ord_loeb; [done|].
    iIntros "!> #-#IH" (d d' s s' n hvs Hn Hd' Hs' Hle) "Hs Hd HΦ". simplify_eq.
    iApply (sim_tgt_expr_bind [] (_ @ -) with "[-]").
    iApply (sim_tgt_rec_Call_internal with "Hf"); [done|]. iModIntro => /=.
  Abort.

  Lemma sim_memmove Π Φ d s n hvs :
    n = Z.of_nat (length hvs) →
    "memmove" ↪ Some memmove_rec -∗
    "memcpy" ↪ Some memcpy_rec -∗
    □ (∀ l1 l2 Φ,
        (∀ b, ⌜l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2)⌝ -∗ Φ (Val (ValBool b) @ -) Π) -∗
          TGT Call "locle" [Val (ValLoc l1); Val $ ValLoc l2] @ - [{ Π }] {{ Φ }}) -∗
    ([∗ list] i↦v∈hvs, (s +ₗ i) ↦ v) -∗
    ([∗ list] i↦_∈hvs, ∃ v, (d +ₗ i) ↦ v) -∗
    (([∗ list] i↦v∈hvs, (s +ₗ i) ↦ v) -∗ ([∗ list] i↦v∈hvs, (d +ₗ i) ↦ v) -∗ Φ (Val 0 @ -) Π) -∗
    TGT Call "memmove" [Val (ValLoc d); Val $ ValLoc s; Val $ ValNum n] @ - [{ Π }] {{ Φ }}.
  Proof.
    iIntros (->) "#Hmemmove #Hmemcpy #Hlocle Hs Hd HΦ".
    iApply (sim_tgt_expr_bind [] (_ @ -)).
    iApply (sim_tgt_rec_Call_internal with "Hmemmove"); [done|]. iModIntro => /=.
    simpl.
  Abort.

  Lemma sim_locle Π Φ l1 l2 :
    (∀ b, ⌜l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2)⌝ -∗ Φ (Val (ValBool b) @ -) Π) -∗
    TGT Call "locle" [Val (ValLoc l1); Val $ ValLoc l2] @ - [{ Π }] {{ Φ }}.
  Proof. Admitted.


End memmove.

Section sim.
  Context {Σ : gFunctors} {EV : Type} `{!dimsumGS Σ}.

  Definition sim_tgt_handler {m_t m_s : mod_trans EV}
    (σ : m_state m_s) :
    option EV → ((m_state m_t → iProp Σ) → iProp Σ) → iProp Σ :=
    λ κ Pσ, (σ ≈{m_s}≈>ₛ (λ κ' σ_s', ⌜κ = κ'⌝ ∗ Pσ (λ σ_t', σ_t' ⪯{m_t, m_s} σ_s')))%I.

  Lemma sim_tgt_handler_intro m_t m_s σ_t σ_s :
    σ_t ≈{m_t}≈>ₜ sim_tgt_handler σ_s -∗ σ_t ⪯{m_t, m_s} σ_s.
  Proof.
    iIntros "?". rewrite sim_unfold.
    iApply (sim_tgt_wand with "[$]"). iIntros (??) "?".
    iApply (sim_src_wand with "[$]"). iIntros (??) "[% ?]".
    iSplit; [done|]. by iApply bi_mono1_intro0.
  Qed.

End sim.

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
    iApply sim_tgt_state_transform; [done|] => /=.
    iApply (sim_tgt_map with "[-]").
    iApply sim_tgt_seq_product_None. iIntros (p) "!>". iIntros (????).
    inv_all @link_filter.
    iApply (bi_mono1_intro with "[HΠ]"); [by iApply "HΠ"|] => /=.
    iIntros (?) "?". iIntros ([[[??]?]?] ?); simplify_eq/=. by repeat case_match; simplify_eq/=.
  Qed.

  Definition link_tgt_left_handler R {m1 m2 : mod_trans (io_event EV)}
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
    σ1 ≈{m1}≈>ₜ link_tgt_left_handler R Π s σ2 -∗
    (MLFLeft, s, σ1, σ2) ≈{link_trans R m1 m2}≈>ₜ Π.
  Proof.
    iIntros "Hsim".
    iApply (sim_tgt_bi_mono1 with "[-]").
    iApply sim_tgt_state_transform; [done|] => /=.
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
  Qed.

  Lemma sim_tgt_link_left_recv R m1 m2 s σ1 σ2 Π e :
    (σ1 ≈{m1}≈>ₜ λ κ Pσ,
      match κ with
      | None => Π None (λ P, Pσ (λ σ1', P (MLFRecvL e, s, σ1', σ2)))
      | Some e' => ⌜e' = (Incoming, e)⌝ -∗ Π None (λ P, Pσ (λ σ1', P (MLFLeft, s, σ1', σ2)))
      end%I) -∗
    (MLFRecvL e, s, σ1, σ2) ≈{link_trans R m1 m2}≈>ₜ Π.
  Proof.
    iIntros "Hsim".
    iApply (sim_tgt_bi_mono1 with "[-]").
    iApply sim_tgt_state_transform; [done|] => /=.
    iApply (sim_tgt_map with "[-]").
    iApply sim_tgt_seq_product_left.
    iApply (sim_tgt_bi_mono2 with "[-]").
    iApply (sim_tgt_wand with "Hsim").
    iIntros (κ ?) "Hsim". iIntros (??????). destruct κ; destruct!/=.
    - inv_all @link_filter.
      iApply (bi_mono1_intro with "[Hsim]"); [by iApply "Hsim"|].
      iIntros (?) "HP". iApply (bi_mono1_intro with "HP").
      iIntros (?) "?". iIntros ([[[??]?]?]?). by simplify_eq/=.
    - iApply (bi_mono1_intro with "[Hsim]"); [by iApply "Hsim"|].
      iIntros (?) "HP". iApply (bi_mono1_intro with "HP").
      iIntros (?) "?". iIntros ([[[??]?]?]?). simplify_eq/=. done.
  Qed.
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
    (∀ σ, σ ⤇ₛ (λ Π, SRC k tt [{ Π }] {{ Φ }}) -∗ Π (Some e) σ) -∗
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
    rec_state_interp (rec_init (main_prog ∪ memmove_prog ∪ memcpy_prog)) -∗
    (MLFNone, [], rec_init (main_prog ∪ memmove_prog ∪ memcpy_prog), (locle_spec, ())) ⪯{
      rec_link_trans {["main"; "memmove"; "memcpy"]} {["locle"]} rec_trans (spec_trans rec_event ()),
      spec_trans rec_event ()} (main_spec, ()).
  Proof.
    iIntros "[Hh [Ha #Hfns]]". iApply (sim_tgt_handler_intro with "[-]").
    iApply (sim_tgt_link_None with "[-]").
    iIntros "!>" (??????). destruct!/=. case_match; destruct!/=.
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
    iApply sim_src_expr_stop1. iIntros (?) "Hsrc". iSplit!.
    iApply (sim_tgt_handler_intro with "[-]").
    iApply (sim_tgt_link_left_recv with "[-]").
    iApply (sim_tgt_expr_elim [] (_ @ _) with "[Ha Hh] [-]"); [done| by iFrame |] => /=.
    iApply (sim_tgt_rec_Waiting with "[$]"). iIntros "Hh Ha".
    iSplit; [|by iIntros].
    iIntros (???? Hin) "!>". iIntros (?). simplify_map_eq.
    iApply sim_src_stop. iSplit!. iIntros (?) "Htgt".
    iApply (sim_tgt_handler_intro with "[-]").
    iApply (sim_tgt_link_left with "[-]").
    iApply ("Htgt" with "[Hh] [Ha]"). admit. admit.
    iApply (sim_tgt_expr_bind [] (_ @ -)).
    iApply sim_tgt_rec_Call_internal. 2: { by iApply (rec_fn_intro with "[$]"). } { done. }
    iModIntro => /=.
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
  iApply (fupd_sim with "[-]").
  iMod recgs_alloc as (?) "[?[??]]". iModIntro.
  iApply memmove_sim. iFrame.
Qed.

(* Idea: construct PI for source level proof from pre and
postconditions of all the external functions instead of constructing
it directly from the used combinators. Maybe one can do the texan
triple trick to force monotonicity of the Π. *)
