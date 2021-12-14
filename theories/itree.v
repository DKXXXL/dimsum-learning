From ITree Require Export ITree ITreeFacts.
From ITree Require Export ITree.
Require Export refframe.module.
Require Import refframe.trefines.

Notation "' x ← y ;;; z" := (ITree.bind y (λ x : _, z))
  (at level 20, x pattern, y at level 100, z at level 200) : stdpp_scope.
Notation "x ← y ;;; z" := (ITree.bind y (λ x : _, z))
  (at level 20, y at level 100, z at level 200) : stdpp_scope.
Notation "y ;;;; z" := (ITree.bind y (λ _, z))
  (at level 100, z at level 200, right associativity) : stdpp_scope.


Inductive moduleE (EV S : Type) : Type → Type :=
| IVis (e : EV) : moduleE EV S unit
| IAll (T : Type) : moduleE EV S T
| IExist (T : Type) : moduleE EV S T
| IGet : moduleE EV S S
| IPut (s : S) : moduleE EV S unit
.
Arguments IVis {_ _}.
Arguments IAll {_ _}.
Arguments IExist {_ _}.
Arguments IGet {_ _}.
Arguments IPut {_ _}.

Inductive mod_itree_step EV S : (itree (moduleE EV S) unit * S) → option EV → ((itree (moduleE EV S) unit * S) → Prop) → Prop :=
| ITauS t t' s:
  observe t = TauF t' →
  mod_itree_step EV S (t, s) None (λ σ', σ' = (t', s))
| IVisS t t' s e:
  observe t = VisF (IVis e) t' →
  mod_itree_step EV S (t, s) (Some e) (λ σ', σ' = (t' tt, s))
.

Definition mod_itree EV S := Mod (mod_itree_step EV S).
Inductive under_tall {EV} : trace EV → (trace EV → Prop) → Prop :=
| UTEnd κs (P : _ → Prop):
  P κs →
  under_tall κs P
| UTAll T f κs (P : _ → Prop):
  (∀ x, under_tall (f x) P) →
  tall T f ⊆ κs →
  under_tall κs P.

Lemma under_tall_mono {EV} (κs1 κs2 : trace EV) (P1 P2 : _ → Prop):
  under_tall κs1 P1 →
  κs1 ⊆ κs2 →
  (∀ κs1' κs2', κs1' ⊆ κs2' → P1 κs1' → P2 κs2') →
  under_tall κs2 P2.
Proof.
  move => Hall. elim: Hall κs2.
  - move => ????? HP. econs. apply: HP; [..|done] => //.
  - move => ????? IH ??? HP. apply: UTAll; [|by etrans]. move => ?. apply: IH; [done|].
    done.
Qed.

Global Instance under_tall_proper {EV} :
  Proper ((⊆) ==> ((⊆) ==> impl) ==> impl) (@under_tall EV).
Proof. move => κs1 κs2 Hsub ?? HP Hall. by apply: under_tall_mono. Qed.

Lemma thas_trace_under_tall {EV} m (κs1 κs2 : trace EV) (P1 Pσ : _ → Prop) σ:
  under_tall κs1 P1 →
  κs1 ⊆ κs2 →
  (∀ κs', P1 κs' → σ ~{ m, κs' }~>ₜ Pσ) →
  σ ~{ m, κs2 }~>ₜ Pσ.
Proof.
  move => Hall. elim: Hall κs2.
  - move => ???? <- HP. by apply: HP.
  - move => ????? IH Hκ ?? HP. apply: TTraceAll; [|by etrans]. naive_solver.
Qed.

Lemma tnhas_trace_under_tall {EV} m (κs1 κs2 : trace EV) (P1 Pσ : _ → Prop) σ n:
  under_tall κs1 P1 →
  κs1 ⊆ κs2 →
  (∀ κs', P1 κs' → σ ~{ m, κs', n }~>ₜ Pσ) →
  σ ~{ m, κs2, n }~>ₜ Pσ.
Proof.
  move => Hall. elim: Hall κs2.
  - move => ???? <- HP. by apply: HP.
  - move => ????? IH Hκ ?? HP. apply: TNTraceAll; [|by etrans |]. naive_solver. done.
Qed.

Lemma thas_trace_inv' {EV} (m : module EV) κs (Pσ : _ → Prop) σ:
  σ ~{ m, κs }~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ σ) ∨
    ∃ κ κs' Pσ2, m_step m σ κ Pσ2 ∧ (∀ σ2, Pσ2 σ2 → σ2 ~{ m, κs' }~>ₜ Pσ) ∧ tapp (option_trace κ) κs' ⊆ κs).
Proof.
  elim.
  - move => ?????. econs. naive_solver.
  - move => *. econs. naive_solver.
  - move => ?????? IH ?. apply: UTAll; [|done]. done.
Qed.

Lemma tnhas_trace_inv' {EV} (m : module EV) κs (Pσ : _ → Prop) σ n:
  σ ~{ m, κs, n }~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ σ) ∨
    ∃ κ κs' Pσ2 fn, m_step m σ κ Pσ2 ∧ (∀ σ2 (H : Pσ2 σ2), σ2 ~{ m, κs', fn (σ2 ↾ H) }~>ₜ Pσ)
      ∧ tapp (option_trace κ) κs' ⊆ κs ∧ (∀ x, fn x ⊂ n)).
Proof.
  elim.
  - move => ??????. econs. naive_solver.
  - move => *. econs. right. naive_solver.
  - move => ???????? IH ??. apply: UTAll; [|done].
    move => ?. apply: under_tall_mono; [done..|].
    move => ?? Hκ [[??]|?]; [left|right].
    + split; [|done]. by rewrite -Hκ.
    + destruct_all?. eexists _, _, _, _. split_and! => //. { by etrans. } move => ?.
      by apply: ti_lt_le.
Qed.

Lemma tnhas_trace_Tau' {EV S} t t' n n' Pσ s κs:
  observe t = TauF t' →
  (t', s) ~{mod_itree EV S, κs, n}~>ₜ Pσ →
  n ⊂ n' →
  (t, s) ~{mod_itree EV S, κs, n'}~>ₜ Pσ.
Proof.
  move => Htau Ht Hsub. apply: (TNTraceStep _ _ (λ _, n)); [by econs| |done|simpl; done] => /= ? ->. done.
Qed.

Lemma thas_trace_Tau' {EV S} t t' Pσ s κs:
  observe t = TauF t' →
  (t', s) ~{mod_itree EV S, κs}~>ₜ Pσ →
  (t, s) ~{mod_itree EV S, κs}~>ₜ Pσ.
Proof. move => Htau Ht. tstep_None; [by econs|]. naive_solver. Qed.

Lemma tnhas_trace_Tau_inv' {EV S} t t' n Pσ s κs:
  observe t' = TauF t →
  (t', s) ~{mod_itree EV S, κs, n}~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ (t', s)) ∨
    ∃ n', n' ⊂ n ∧ (t, s) ~{ mod_itree _ _,  κs, n' }~>ₜ Pσ).
Proof.
  move => Htau /tnhas_trace_inv' Ht. apply: under_tall_mono; [done..|] => {Ht} κs1 κs2 /= Hκs1 [[??]|?].
  { left. split; [by etrans|done]. }
  right. destruct_all!. invert_all @mod_itree_step; rewrite ->Htau in *; simplify_eq.
  eexists _. split; [done|]. rewrite -Hκs1 -H0. naive_solver.
  Unshelve. done.
Qed.

(*
Lemma tnhas_trace_Tau_inv' {EV S} t t' n Pσ s κs:
  observe t' = TauF t →
  (t', s) ~{mod_itree EV S, κs, n}~>ₜ Pσ →
  (* (tnil ⊆ κs ∧ Pσ (t', s)) ∨ ∃ n', n' ⊂ n ∧ (t, s) ~{mod_itree EV S, κs, n'}~>ₜ Pσ *)
  ∃ n', n' ⊂ n ∧ (t, s) ~{mod_itree EV S, κs, n'}~>ₜ Pσ.
  (* (t, s) ~{mod_itree EV S, tnil, tiO}~>ₜ (λ σ, σ = (t, s) ∧ *)
      (* ((tnil ⊆ κs ∧ Pσ (t', s)) ∨ ). *)
Proof.
  move => Htau. move Hσ: (t, s) => σ. move Hσ': (t', s) => σ' Ht.
  elim: Ht t t' Hσ Hσ' Htau; clear.
  - admit.
    (* tend. naive_solver. *)
  - move => ?????????? IH ? Hκs ???? Htau. simplify_eq. invert_all @m_step; rewrite ->Htau in *; simplify_eq.
  (* tend. split; [done|]. right. eexists _. split. 2: { rewrite -Hκs. done. } done. *)
    admit.
  - move => ???????? IH Hκs??????. subst.
    (* apply: TNTraceAll; [|done|done] => ?. by apply: IH. *)
Abort.

Lemma tnhas_trace_Tau_inv' {EV S} t t' n Pσ Pσ' s κs:
  (prod_relation (eutt eq) (=) ==> iff)%signature Pσ Pσ' →
  observe t' = TauF t →
  (t', s) ~{mod_itree EV S, κs, n}~>ₜ Pσ →
  (t, s) ~{mod_itree EV S, κs, n}~>ₜ Pσ'.
Proof.
  move => Hproper Htau. move Hσ: (t, s) => σ. move Hσ': (t', s) => σ' Ht.
  elim: Ht t t' Hσ Hσ' Hproper Htau; clear.
  - move => ?????? t t' ?? Hproper Htau. tend. subst. eapply Hproper; [|done]. split => //=.
    by rewrite (itree_eta t') Htau tau_eutt.
  - move => ?????????? IH ? Hκs ???? Hproper Htau. simplify_eq.
    invert_all @m_step; rewrite ->Htau in *; simplify_eq.
    apply: tnhas_trace_mono; [done|done| | ].
    + by apply ti_lt_impl_le.
    + move => ??. eapply Hproper; [|done]. done.
  - move => ???????? IH Hκs???????. subst.
    apply: TNTraceAll; [|done|done] => ?. by apply: IH.
  Unshelve. done.
Qed.
 *)

Lemma thas_trace_Tau_inv' {EV S} t t' Pσ Pσ' s κs:
  (prod_relation (eutt eq) (=) ==> iff)%signature Pσ Pσ' →
  observe t' = TauF t →
  (t', s) ~{mod_itree EV S, κs}~>ₜ Pσ →
  (t, s) ~{mod_itree EV S, κs}~>ₜ Pσ'.
Proof.
  move => Hproper Htau /thas_trace_n[??].
  apply thas_trace_n. eexists _.
  (* by apply: tnhas_trace_Tau_inv'. *)
(* Qed. *)
Admitted.

Lemma tnhas_trace_inv {EV} (m : module EV) σ (Pσ : _ → Prop) (P : _ → _ → Prop):
  (∀ n, Pσ σ → P n tnil) →
  (∀ κ κs' Pσ2 n f,
      m.(m_step) σ κ Pσ2 →
      (∀ σ2 (H:Pσ2 σ2), σ2 ~{ m, κs', f (σ2 ↾ H) }~>ₜ Pσ) →
      (∀ x, f x ⊂ n) →
      P n (tapp (option_trace κ) κs')) →
  (∀ T f fn n, (∀ x, P (fn x) (f x)) → (∀ x, fn x ⊆ n) → P n (tall T f)) →
  (∀ n κs κs', P n κs' → κs' ⊆ κs → P n κs) →
  ∀ n κs, σ ~{ m, κs, n }~>ₜ Pσ → P n κs.
Proof.
  move => HEnd HStep Hall Hsub κs n Ht.
  elim: Ht HEnd HStep Hall Hsub; clear.
  - naive_solver.
  - naive_solver.
  - move => T f fn n σ κs Pσ ? IH ?? HEnd HStep Hall Hsub.
    apply: (Hsub); [|done].
    apply: (Hall) => ? //.
    apply: IH; naive_solver.
Qed.
Ltac tnhas_trace_inv H :=
  lazymatch type of H with
  | _ ~{ _, ?κs, ?n }~>ₜ _ => pattern n; pattern κs
  end;
  lazymatch goal with
  | |- (λ κs', (λ n', @?P n' κs') ?n) ?κs => change (P n κs)
  end;
  apply: (tnhas_trace_inv _ _ _ _ _ _ _ _ _ _ H); try clear H; [ | |
     try by [move => *; apply subtrace_all_r; eauto];
     try by [move => *; apply thas_trace_all; eauto] |
     try by [move => ???? <-]
 ].


Lemma tnhas_trace_Ret_inv' {EV S} t x n Pσ s κs:
  observe t = RetF x →
  (t, s) ~{mod_itree EV S, κs, n}~>ₜ Pσ →
  under_tall κs (λ κs, tnil ⊆ κs ∧ Pσ (t, s)).
Proof.
  move => Hret /tnhas_trace_inv' Ht.
  apply: under_tall_mono; [done..|] => {Ht} κs1 κs2 /= Hκs [[??]|]. { split => //. by rewrite -Hκs. }
  move => ?. destruct_all!. invert_all @mod_itree_step; rewrite ->Hret in *; simplify_eq.
Qed.
(*
Lemma thas_trace_Tau' {EV S} t t' Pσ s κs:
  observe t = TauF t' →
  (t', s) ~{mod_itree EV S, κs}~>ₜ Pσ →
  (t, s) ~{mod_itree EV S, κs}~>ₜ Pσ.
Proof. move => Htau Ht. tstep_None; [by econs|]. naive_solver. Qed.
*)
From Paco Require Import paco.

Lemma thas_trace_eutt_mono {EV S} t t' s κs Pσ Pσ':
  (prod_relation (eutt eq) (=) ==> iff)%signature Pσ Pσ' →
  (t, s) ~{ mod_itree EV S, κs }~>ₜ Pσ →
  t ≈ t' →
  (t', s) ~{ mod_itree EV S, κs }~>ₜ Pσ'.
Proof.
  move => HP /thas_trace_n[n Ht] Heq.
  elim/(well_founded_ind ti_lt_wf): n κs t t' s Ht Heq HP.
  move => n IHn κs t t' s Ht Heq HP.
  punfold Heq. unfold eqit_ in Heq at 1.
  move: Heq. move Hot: (observe t) => ot. move Hot': (observe t') => ot' Heq.
  elim: Heq t t' n IHn Ht Hot Hot'.
  - move => ?? -> t t' n IHn Ht Hot Hot'.
    move: Ht => /(tnhas_trace_Ret_inv' _ _ _ _ _)Ht. specialize (Ht _ ltac:(done)).
    apply: thas_trace_under_tall; [done..|] => ? [??]. tend.
    eapply HP; [|done]. split; [|done] => /=. rewrite (itree_eta t) Hot (itree_eta t') Hot'. done.
  - move => m1 m2 [REL|//] t t' n IHn Ht Hot Hot'. rewrite -/(eqit _ _ _) in REL.
    apply: thas_trace_Tau'; [done|]. revert IHn.
    tnhas_trace_inv Ht. { tend. eapply HP; [|done]. split => //=. by rewrite (itree_eta t) Hot tau_eutt REL. }
    2: { move => ???? IH ? IHn. apply thas_trace_all => ?. apply: IH => *. apply: IHn => //. by apply: ti_lt_le. }
    move => ?????? Ht Hlt IHn. invert_all @m_step; rewrite -> Hot in *; simplify_eq.
    specialize (Ht _ ltac:(done)).
    apply: IHn; [done|done| |done]. by rewrite REL.
  - admit.
  - move => t1 ot2 ? REL IH t t' n IHn Ht Hot Hot'.
    move: Ht => /(tnhas_trace_Tau_inv' _ _ _ _ _ _)Ht. specialize (Ht _ _ ltac:(done) ltac:(done)).
    apply: IH => //. apply: tnhas_trace_mono; [done..|] => ??. eapply HP; [|done]. done.
  - move => ot1 t2 ? REL IH t t' n IHn Ht Hot Hot'.
    tstep_None; [by econs|] => ? ->. by apply: IH.
    Unshelve.
Admitted.

Global Instance mod_itree_proper EV S b1 b2:
  Proper ((prod_relation (eqit eq b1 b2) (=)) ==> (=) ==> (prod_relation (eutt eq) (=) ==> iff) ==> iff) (thas_trace (mod_itree EV S)).
Proof.
  move => [??] [??] [/= Heq ->] ?? -> ?? Hf.
  split => ?.
  all: apply: thas_trace_eutt_mono; [try done| done |].
  - by apply: eqit_mon; [| | |done].
  - move => ?? [??]. symmetry. by apply Hf.
  - symmetry. by apply: eqit_mon; [| | |done].
Qed.

(*
(* TODO: add step index to thas_trace and make sure that this step
index only goes down in calls to sim *)
Lemma thas_trace_eqitF' {EV S} t t' s κs Pσ b1 b2 sim :
  (go t, s) ~{ mod_itree EV S, κs }~>ₜ Pσ →
  eqitF eq b1 b2 id sim t t' →
  (∀ m1 m2 κs, (m1, s) ~{ mod_itree EV S, κs }~>ₜ Pσ → sim m1 m2 → (m2, s) ~{ mod_itree EV S, κs }~>ₜ Pσ) →
  (∀ t1 t2 s, Pσ (t1, s) → t1 ≈ t2 → Pσ (t2, s)) →
  (go t', s)  ~{ mod_itree EV S, κs }~>ₜ Pσ.
Proof.
  move => Ht Heq Hsim HRR.
  induction Heq.
  - thas_trace_inv Ht. subst. 2: intros; invert_all @m_step. tend.
  - tstep_None; [by constructor|] => ? ->. apply: Hsim; [|done].
    thas_trace_inv Ht. { tend. apply: HRR; [done|]. by rewrite tau_eutt. }
    move => ?????. invert_all @m_step. done.
  - thas_trace_inv Ht. { tend. apply: HRR; [done|]. admit. }
    move => ???? IH. invert_all' @m_step; simplify_eq.
    + simpl in H3; simplify_eq; simplify_K.
      apply: Hsim.
      * tstep; [ | |done].
        admit.
      * tstep; [ | |done].
        admit.
        (* => /= ??. apply: IH. *)
      apply UIPM.inj_pair2 in H2.
  - apply IHHeq. admit.
  - admit.
Admitted.

Lemma thas_trace_eutt_mono'' {EV S} t t' s κs Pσ :
  (go t, s) ~{ mod_itree EV S, κs }~>ₜ Pσ →
  go t ≈ go t' →
  (∀ t1 t2 s, Pσ (t1, s) → t1 ≈ t2 → Pσ (t2, s)) →
  (go t', s) ~{ mod_itree EV S, κs }~>ₜ Pσ.
Proof.
  move => Ht Heq Hproper. punfold Heq.
  apply: thas_trace_eqitF'; [done|done| |].
  - move => ??? [Heq2 | //].

  Lemma thas_trace_eutt_mono' {EV S} σ1 σ2 κs Pσ :
  σ1 ~{ mod_itree EV S, κs }~>ₜ Pσ →
  σ1.1 ≈ σ2.1 →
  σ1.2 = σ2.2 →
  (∀ t1 t2 s, Pσ (t1, s) → t1 ≈ t2 → Pσ (t2, s)) →
  σ2 ~{ mod_itree EV S, κs }~>ₜ Pσ.
Proof.
  move => Ht Heq1 Heq2 Hproper.
  destruct σ1 as [t s], σ2 as [t' s']. simplify_eq/=. punfold Heq1.

  apply thas_trace_eqitF'.
  induction Heq1; simplify_eq.
  elim: Heq1.

  elim: Ht σ2 Heq1 Heq2 Hproper.
  - move => [??] ???? [??] /= ??. subst. tend. naive_solver.
  - move => [t1 ?] ??????? IH Hκs [??]/= Heq ??. subst. rewrite -Hκs. invert_all @m_step.
    + apply IH => /=; [|done..]. rewrite -Heq (itree_eta t1) H3. rewrite tau_eutt. done.
    + tstep_Some.
      * apply IVisS.
  - move => ?????? IH Hκs ????. rewrite -Hκs. apply thas_trace_all => ?. by apply IH.
Qed.

Lemma thas_trace_eutt_mono {EV S} t t' s κs Pσ :
  (t, s) ~{ mod_itree EV S, κs }~>ₜ Pσ →
  t ≈ t' →
  (∀ t1 t2 s, Pσ (t1, s) → t1 ≈ t2 → Pσ (t2, s)) →
  (t', s) ~{ mod_itree EV S, κs }~>ₜ Pσ.
Proof. move => ???. by apply: thas_trace_eutt_mono'. Qed.
*)

Require refframe.example_modules.
Module itree_examples.
Import refframe.example_modules.

Lemma itree_trefines_tau_l :
  trefines (MS (mod_itree nat unit) (Tau (Ret tt), tt)) (MS (mod_itree nat unit) (Ret tt, tt)).
Proof. constructor => /= ?. rewrite tau_eutt. done. Qed.

Lemma mod1_trefines_itree :
  trefines (MS mod1 0) (MS (mod_itree nat unit) ((_ ← trigger (IVis 1) ;;; Ret tt), tt)).
Proof.
  constructor => /= ? Ht.
  thas_trace_inv Ht; [tend|] => ???? Ht. invert_all @m_step.
  rewrite bind_trigger.
  tstep_Some; [by econs|] => ? ->.
  thas_trace_inv Ht; [tend|] => ???? Ht. invert_all @m_step.
Qed.

Lemma itree_trefines_mod1 :
  trefines (MS (mod_itree nat unit) ((trigger (IVis 1);;;; Ret tt), tt)) (MS mod1 0).
Proof.
  constructor => /= ?. rewrite bind_trigger.
Abort.

End itree_examples.
