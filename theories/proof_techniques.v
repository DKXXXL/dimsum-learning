Require Export refframe.module.
Require Import refframe.trefines.

(*** Proving refinement *)

(** ** [mod_to_trace] *)
Fixpoint mod_to_trace {EV} (m : module EV) (n : trace_index) (σ : m.(m_state)) : trace EV :=
  match n with
  | tiO => tnb
  | tiS n' => tall { x : option EV * (m.(m_state) → Prop) | m.(m_step) σ x.1 x.2} (λ x,
         tapp (option_trace (`x).1) (tex {σ' : m.(m_state) | (`x).2 σ'} (λ σ', mod_to_trace m n' (`σ'))))
  | tiChoice T fn => tall T (λ x, mod_to_trace m (fn x) σ)
  end.

Lemma thas_trace_mod_to_trace {EV} (m : module EV) n σ :
  σ ~{m, mod_to_trace m n σ}~>ₜ -.
Proof.
  elim: n σ => /=.
  - move => ?. tend. apply tnb_sub.
  - move => n IH σ. apply thas_trace_all => -[[/=??]?].
    tstep; [done| |done] => ??. apply: (thas_trace_ex (exist _ _ _)); [done|]. naive_solver.
  - move => ?? IH σ. apply thas_trace_all. naive_solver.
Qed.

Lemma mod_to_trace_mono {EV} (m : module EV) n n' σ :
  n' ⊆ n →
  mod_to_trace m n σ ⊆ mod_to_trace m n' σ.
Proof.
  move => Hsub. elim: Hsub σ => /=.
  - move => ??. apply tnb_sub.
  - move => ??? IH σ.
    apply tall_mono => -[[/=??]?].
    apply tapp_mono; [done|].
    apply tex_mono => ?.
    naive_solver.
  - move => T f {}n ? IH σ. econs. naive_solver.
  - move => T f {}n x Hle IH σ. econs. naive_solver.
Qed.

(** ** [inv] *)
Lemma inv_implies_trefines {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → m2.(m_state) → Prop):
  inv m1.(ms_state) m2.(ms_state) →
  (∀ σi1 σs1 Pσi2 e,
      inv σi1 σs1 → m_step m1 σi1 e Pσi2 →
      σs1 ~{ m2, option_trace e }~>ₜ (λ σs2, ∃ σi2, Pσi2 σi2 ∧ inv σi2 σs2)) →
  trefines m1 m2.
Proof.
  move => Hinvinit Hinvstep.
  constructor => // κs. move: m1.(ms_state) m2.(ms_state) Hinvinit => σi1 σs1 Hinv Hsteps.
  elim: Hsteps σs1 Hinv => {σi1 κs}.
  - move => ???????. by constructor.
  - move => σi1 Pσi2 Pσi3 κ κs κs' Hstep Hsteps IH Hcons σs1 Hinv.
    have ?:= (Hinvstep _ _ _ _ Hinv Hstep).
    apply: thas_trace_mono; [|done|done].
    apply: thas_trace_trans; [done|] => ? /=[?[??]].
    by apply: IH.
  - move => ??????????.
    apply: thas_trace_mono; [|done|done].
    apply: thas_trace_all => ?. naive_solver.
Qed.

Lemma inv'_implies_trefines {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → m2.(m_state) → trace EV → Prop):
  (∀ κs, ms_state m1 ~{ m1, κs }~>ₜ (λ _, True) → inv m1.(ms_state) m2.(ms_state) κs) →
  (∀ σi1 σs1 Pσi2 e κs κs',
      inv σi1 σs1 κs → m_step m1 σi1 e Pσi2 → tapp (option_trace e) κs' ⊆ κs →
      σs1 ~{ m2, option_trace e }~>ₜ (λ σs2, ∃ σi2, Pσi2 σi2 ∧ inv σi2 σs2 κs')) →
  (∀ σi1 σs1 κs T f,
      inv σi1 σs1 κs → tall T f ⊆ κs → ∀ x, inv σi1 σs1 (f x)) →
  trefines m1 m2.
Proof.
  move => Hinvinit Hinvstep Hinvall.
  constructor => // κs. move: m1.(ms_state) m2.(ms_state) (Hinvinit κs) => σi1 σs1 Hinv Hsteps.
  move: (Hinv Hsteps) => {}Hinv.
  elim: Hsteps σs1 Hinv => {σi1 κs}.
  - move => ???????. by constructor.
  - move => σi1 Pσi2 Pσi3 κ κs κs' Hstep Hsteps IH Hcons σs1 Hinv.
    have ?:= (Hinvstep _ _ _ _ _ _ Hinv Hstep Hcons).
    apply: thas_trace_mono; [|done|done].
    apply: thas_trace_trans; [done|] => ? /=[?[??]].
    by apply: IH.
  - move => ?????? IH ???.
    apply: thas_trace_mono; [|done|done].
    apply: thas_trace_all => ?. naive_solver.
Qed.

Lemma trefines_implies_inv' {EV} (m1 m2 : mod_state EV):
  trefines m1 m2 →
  ∃ (inv : m1.(m_state) → m2.(m_state) → trace EV → Prop),
  (∀ κs, ms_state m1 ~{ m1, κs }~>ₜ (λ _, True) → inv m1.(ms_state) m2.(ms_state) κs) ∧
  (∀ σi1 σs1 Pσi2 e κs κs',
      inv σi1 σs1 κs → m_step m1 σi1 e Pσi2 → tapp (option_trace e) κs' ⊆ κs →
      σs1 ~{ m2, option_trace e }~>ₜ (λ σs2, ∃ σi2, Pσi2 σi2 ∧ inv σi2 σs2 κs')) ∧
  (∀ σi1 σs1 κs T f,
      inv σi1 σs1 κs → tall T f ⊆ κs → ∀ x, inv σi1 σs1 (f x)).
Proof.
  move => [Hr].
  eexists (λ σi σs κs, σs ~{ m2, κs }~>ₜ (λ _, True)).
  split_and!.
  - done.
  - move => {Hr} ?????????.  admit.
  - admit.
Abort.

Lemma inv''_implies_trefines {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → m2.(m_state) → trace EV → Prop):
  (∀ κs, inv m1.(ms_state) m2.(ms_state) κs) →
  (∀ σi1 σs1 Pσi2 e κs κs',
      inv σi1 σs1 κs → m_step m1 σi1 e Pσi2 → tapp (option_trace e) κs' ⊆ κs →
      σs1 ~{ m2, option_trace e }~>ₜ (λ σs2, ∃ σi2, Pσi2 σi2 ∧ inv σi2 σs2 κs')) →
  (∀ σi1 σs1 κs T f,
      inv σi1 σs1 κs → tall T f ⊆ κs → ∀ x, inv σi1 σs1 (f x)) →
  trefines m1 m2.
Proof. Abort.
(*
  move => Hinvinit Hinvstep Hinvall.
  constructor => // κs. move: m1.(ms_state) m2.(ms_state) (Hinvinit κs) => σi1 σs1 Hinv Hsteps.
  move: (Hinv Hsteps) => {}Hinv.
  elim: Hsteps σs1 Hinv => {σi1 κs}.
  - move => ???????. by constructor.
  - move => σi1 Pσi2 Pσi3 κ κs κs' Hstep Hsteps IH Hcons σs1 Hinv.
    have ?:= (Hinvstep _ _ _ _ _ _ Hinv Hstep Hcons).
    apply: thas_trace_mono; [|done|done].
    apply: thas_trace_trans; [done|] => ? /=[?[??]].
    by apply: IH.
  - move => ?????? IH ???.
    apply: thas_trace_mono; [|done|done].
    apply: thas_trace_all => ?. naive_solver.
Qed.
 *)
(*
Lemma trefines_implies_inv'' {EV} (m1 m2 : mod_state EV):
  trefines m1 m2 →
  ∃ (inv : m1.(m_state) → m2.(m_state) → trace EV → Prop),
  (∀ κs, inv m1.(ms_state) m2.(ms_state) κs) ∧
  (∀ σi1 σs1 Pσi2 e κs κs',
      inv σi1 σs1 κs → m_step m1 σi1 e Pσi2 → tapp (option_trace e) κs' ⊆ κs →
      σs1 ~{ m2, option_trace e }~>ₜ (λ σs2, ∃ σi2, Pσi2 σi2 ∧ inv σi2 σs2 κs')) ∧
  (∀ σi1 σs1 κs T f,
      inv σi1 σs1 κs → tall T f ⊆ κs → ∀ x, inv σi1 σs1 (f x)).
Proof.
  move => [Hr].
  eexists (λ σi σs κs, σs ~{ m2, κs }~>ₜ (λ _, True)).
  split_and!.
  - done.
  - move => {Hr} ?????????.  admit.
  - admit.
Abort.
*)

(** * [wp] *)
Inductive wp {EV} (m1 m2 : module EV) : trace_index → m1.(m_state) -> m2.(m_state) -> Prop :=
| Wp_step' σi1 σs1 n:
    (∀ Pσi2 κ n', tiS n' ⊆ n → m_step m1 σi1 κ Pσi2 -> ∃ Pσ2,
      σs1 ~{ m2, option_trace κ }~>ₜ Pσ2 ∧
      ∀ σs2, Pσ2 σs2 → ∃ σi2, Pσi2 σi2 ∧ wp m1 m2 n' σi2 σs2) ->
    wp m1 m2 n σi1 σs1
.

Lemma Wp_step {EV} (m1 m2 : module EV) σi1 σs1 n:
  (∀ Pσi2 n' κ, tiS n' ⊆ n → m_step m1 σi1 κ Pσi2 ->
      σs1 ~{ m2, option_trace κ }~>ₜ (λ σs2, ∃ σi2, Pσi2 σi2 ∧ wp m1 m2 n' σi2 σs2)) ->
    wp m1 m2 n σi1 σs1
.
Proof. move => ?. constructor. naive_solver. Qed.

Lemma wp_mono {EV} (m1 m2 : module EV) n1 n2 σi σs:
  wp m1 m2 n1 σi σs →
  n2 ⊆ n1 →
  wp m1 m2 n2 σi σs.
Proof.
  move => Hwp Hle.
  constructor => ?????.
  inversion_clear Hwp as [??? Hwp2]; subst.
  have {Hwp2}[?[? Hwp]]:= Hwp2 _ _ _ ltac:(by etrans) ltac:(done).
  eexists _. split; [done|] => ??.
  have {Hwp}[?[? Hwp]]:= Hwp _ ltac:(done).
  by eexists _.
Qed.

Lemma wp_implies_refines {EV} (m1 m2 : mod_state EV):
  (∀ n, wp m1 m2 n m1.(ms_state) m2.(ms_state)) →
  trefines m1 m2.
Proof.
  destruct m1 as [m1 σi1]. destruct m2 as [m2 σs1]. move => /= Hwp.
  constructor => κs /= /thas_trace_n [n Hsteps].
  elim: Hsteps σs1 {Hwp}(Hwp n); clear.
  - move => ????????. tend.
  - move => Pσ2 fn σ1 Pσ3 κ κs κs' n Hstep ? IH Hlt Hκs σs1 Hwp. rewrite -Hκs.
    inversion_clear Hwp as [??? Hwp2]; subst.
    have {Hwp2}[?[? Hwp]]:= Hwp2 _ _ _ ltac:(done) ltac:(done).
    apply: thas_trace_trans; [done|] => ??.
    have {Hwp}[?[? Hwp]]:= Hwp _ ltac:(done).
    apply: IH; [done|] => ?.
    apply: wp_mono; [done|]. by econs.
  - move => T fn f σ κs Pσ n ? IH Hκs Hle σs1 Hwp. rewrite -Hκs.
    apply thas_trace_all => ?. apply: IH.
    apply: wp_mono; [done|]. etrans; [|done]. by econs.
Qed.

Lemma wp_complete {EV} (m1 m2 : mod_state EV):
  trefines m1 m2 →
  ∀ n, wp m1 m2 n m1.(ms_state) m2.(ms_state).
Proof.
  destruct m1 as [m1 σi1]. destruct m2 as [m2 σs1]. move => /= [Href] n.
  have {Href} := Href (mod_to_trace _ n σi1) ltac:(apply thas_trace_mod_to_trace) => /=.
  elim/ti_lt_ind: n σi1 σs1 => /= n IH σi σs Ht.
  apply Wp_step => Pσi n' κ Hsub Hstep.
  move: Ht => /thas_trace_mono Ht.
  have {Ht} := Ht _ (λ _, True) ltac:(by apply mod_to_trace_mono) ltac:(done) => /=.
  move => /thas_trace_all_inv Ht.
  have /=/thas_trace_app_inv {}Ht := (Ht (exist _ (κ, Pσi) Hstep)).
  rewrite -(tapp_tnil_r (option_trace κ)). apply: thas_trace_trans; [done|].
  move => ? /= /thas_trace_ex_inv {}Ht.
  apply: thas_trace_mono; [done..|] => ? /= [[??]?].
  naive_solver.
Qed.

(** * tsim *)

Definition tsim {EV} (n : trace_index) (b : bool) (mi ms : module EV) (σi : mi.(m_state)) (κss : trace EV) (σs : ms.(m_state))  :=
  ∀ κs n',
    tiS?b n' ⊆ n →
    σi ~{ mi, κs, n' }~>ₜ - →
    σs ~{ ms, tapp κss κs }~>ₜ -.

Notation "σi ⪯{ mi , ms , n , b , κss } σs" := (tsim n b mi ms σi κss σs) (at level 70,
    format "σi  ⪯{ mi ,  ms ,  n ,  b ,  κss }  σs") : type_scope.
Notation "σi ⪯{ mi , ms , n , b } σs" := (tsim n b mi ms σi tnil σs) (at level 70,
    format "σi  ⪯{ mi ,  ms ,  n ,  b }  σs") : type_scope.

Lemma tsim_implies_trefines {EV} (mi ms : mod_state EV) :
  (∀ n, mi.(ms_state) ⪯{mi, ms, n, false} ms.(ms_state)) →
  trefines mi ms.
Proof. move => Hsim. constructor => ? /thas_trace_n [??]. by apply: Hsim => /=. Qed.

Lemma tsim_mono {EV} {mi ms : module EV} σi σs b n n' κs:
  σi ⪯{mi, ms, n', b, κs} σs →
  n ⊆ n' →
  σi ⪯{mi, ms, n, b, κs} σs.
Proof. move => Hsim Hn ???. apply: Hsim. by destruct b; (etrans; [done|]). Qed.

Lemma tsim_mono_b {EV} {mi ms : module EV} σi σs n κs b:
  σi ⪯{mi, ms, n, b, κs} σs →
  σi ⪯{mi, ms, n, true, κs} σs.
Proof. move => Hsim Hn ??. apply: Hsim. destruct b => //. by apply ti_lt_impl_le. Qed.

Definition Plater (P : bool → Prop) : Prop :=
  P true → P false.
Arguments Plater _ /.

Lemma tsim_remember {EV} {mi ms : module EV} (Pσ : _ → _ → _ → Prop) σi σs b n :
  Pσ n σi σs →
  (∀ n n' σi σs, tiS?b n' ⊆ n → Pσ n σi σs → Pσ n' σi σs) →
  (* (∀ n', tiS?b n' ⊆ n → Plater (λ b', ∀ σi σs, Pσ n' σi σs → σi ⪯{mi, ms, n', b'} σs)) → *)
  (∀ n', tiS?b n' ⊆ n →
         (∀ n'' σi σs, n'' ⊆ n' → Pσ n'' σi σs → σi ⪯{mi, ms, n'', true} σs) →
         (∀ σi σs, Pσ n' σi σs → σi ⪯{mi, ms, n', false} σs)) →
  σi ⪯{mi, ms, n, b} σs.
Proof.
  move => HP HPmono Hsim κs' n' Hn Ht /=.
  move: HP => /HPmono HP. move: (HP _ ltac:(done)) => {}HP.
  elim/ti_lt_ind: n' κs' σi σs Hn HP Ht.
  move => n' IHn κs' σi σs Hn HP Ht.
  apply: Hsim; [done| |done| |done]. 2: done.
  move => ????????? /=. eapply IHn; [by etrans | | |done].
  - etrans; [|done]. apply tiS_maybe_mono; [done|]. etrans; [|done]. etrans; [|done]. apply ti_le_S.
  - apply: HPmono; [|done]. etrans; [|done]. by apply tiS_maybe_mono.
Qed.

Lemma tsim_remember_all {EV A} {mi ms : module EV} σi σs b n:
  (∀ n', tiS?b n' ⊆ n → Plater (λ b', ∀ x, σi x ⪯{mi, ms, n', b'} σs x)) →
  ∀ x : A, σi x ⪯{mi, ms, n, b} σs x.
Proof.
  move => Hsim x. apply: (tsim_remember (λ _ σi' σs', ∃ x, σi' = σi x ∧ σs' = σs x)).
  all: naive_solver.
Qed.

Lemma tsim_step_l {EV} {mi ms : module EV} σi σs n b :
  (∀ κ Pσi,
      mi.(m_step) σi κ Pσi →
      ∃ σi', Pσi σi' ∧ σi' ⪯{mi, ms, n, true, option_trace κ} σs) →
  σi ⪯{mi, ms, n, b} σs.
Proof.
  move => Hsim κs' n' Hn /tnhas_trace_inv Ht.
  apply: thas_trace_under_tall; [done..|] => {Ht} κs [[??]|[?[?[?[?[?[?[<- ?]]]]]]]]. { tend. }
  have [?[? {}Hsim]]:= Hsim _ _ ltac:(done).
  apply: Hsim. 2: { naive_solver. }
  destruct b; (etrans; [|done]).
  - econs. apply ti_lt_impl_le. etrans; [|done]. econs. by econs.
  - etrans; [|done]. econs. by econs.
    Unshelve. done.
Qed.

Lemma tsim_step_r {EV} {mi ms : module EV} σi σs n b κs κs' κs'' :
  κs = tapp κs' κs'' →
  σs ~{ ms, κs' }~>ₜ (λ σs', σi ⪯{mi, ms, n, b, κs''} σs') →
  σi ⪯{mi, ms, n, b, κs} σs.
Proof.
  move => -> Hsim κss n' HIs Ht. rewrite -assoc_L. apply: thas_trace_trans; [done|] => ? {}Hsim.
  by apply: Hsim.
Qed.

(** * tstep *)
Create HintDb tstep discriminated.
(* The following sadly causes more problems than it solves since
module is a dependent pair and [m.(m_state)] cannot be reduced if [m] is
opaque. *)
(* Global Hint Constants Opaque : tstep. *)
(* Global Hint Variables Opaque : tstep. *)

Class TStepI {EV} (mi : module EV) (σi : mi.(m_state)) (P : (bool → option EV → ((mi.(m_state) → Prop) → Prop) → Prop) → Prop) : Prop := {
  tstepi_proof G:
    P G →
    σi -{ mi }-> (λ b κ Pσ, ∃ b' P', G b' κ P' ∧ (b' → b) ∧ ∀ G', P' G' → ∃ σ', Pσ σ' ∧ G' σ')
}.
Global Hint Mode TStepI + + ! - : tstep.

Lemma tsim_tstep_i {EV} (mi : module EV) σi P `{!TStepI mi σi P} ms σs n b:
  P (λ b' κ Pσ, Pσ (λ σi', σi' ⪯{mi, ms, n, b || b', option_trace κ} σs)) →
  σi ⪯{mi, ms, n, b} σs.
Proof.
  move => HP κs n' Hn /= Hi.
  efeed pose proof @steps_impl_elim_n as Hd. 2: done. { by apply: tstepi_proof. }
  apply: thas_trace_under_tall; [done..|] => {Hi HP Hd} {}κs /= [?|]. { tend. }
  move => [?[?[?[?[?[[b'[? [HP [? HG']]]][<-[??]]]]]]]]. move: HP => /HG'[?[? Hs]].
  apply: Hs. 2: naive_solver.
  etrans; [|done]. etrans; [ apply tiS_maybe_orb|]. apply tiS_maybe_mono; [done|].
  etrans; [|done]. by apply tiS_maybe_mono.
Qed.

Lemma tsim_tstep_both {EV} (mi : module EV) σi P `{!TStepI mi σi P} ms σs n b:
  P (λ b' κ Pσ, σs ~{ms, option_trace κ}~>ₜ (λ σs', Pσ (λ σi', σi' ⪯{mi, ms, n, b || b', tnil} σs'))) →
  σi ⪯{mi, ms, n, b} σs.
Proof.
  move => HP κs n' Hn Hi /=.
  efeed pose proof @steps_impl_elim_n as Hd. 2: done. { by apply: tstepi_proof. }
  apply: thas_trace_under_tall; [done..|] => {Hi HP Hd} {}κs /= [?|]. { tend. }
  move => [?[?[?[?[?[[?[?[?[? HG']]]][<-[??]]]]]]]].
  apply: thas_trace_trans; [done|] => ? /HG' [σi' [? {}Ht]].
  apply: Ht; [|naive_solver].
  etrans; [|done]. etrans; [ apply tiS_maybe_orb|]. apply tiS_maybe_mono; [done|].
  etrans; [|done]. by apply tiS_maybe_mono.
Qed.

Class TStepS {EV} (ms : module EV) (σs : ms.(m_state)) (P : (option EV → ((ms.(m_state) → Prop) → Prop) → Prop) → Prop) : Prop := {
  tsteps_proof G:
    P G →
    ∃ κ P',
      G κ P' ∧
      ∀ G', P' G' → σs -{ ms, κ }->ₛ G'
}.
Global Hint Mode TStepS + + ! - : tstep.

Lemma tsim_tstep_s {EV} (ms : module EV) σs κs P `{!TStepS ms σs P} mi σi n b :
  P (λ κ P',
      if κ is Some e then
        if κs is tcons e' κs' then e = e' ∧ P' (λ σs', σi ⪯{mi, ms, n, b, κs'} σs') else False
      else
        P' (λ σs', σi ⪯{mi, ms, n, b, κs} σs')) →
  σi ⪯{mi, ms, n, b, κs} σs.
Proof.
  move => /tsteps_proof[κ [?[? HG']]] ????.
  repeat case_match => //; destruct_all?; simplify_eq/= => //.
  - apply: (thas_trace_trans (tcons _ tnil)); simplify_eq/=.
    { apply (steps_spec_has_trace' _ (Some _)); naive_solver. }
    naive_solver.
  - apply: (thas_trace_trans tnil); simplify_eq/=.
    { apply (steps_spec_has_trace' _ None); naive_solver. }
    naive_solver.
Qed.

Lemma thas_trace_tstep_s {EV} (m : module EV) σ κs Pσ `{!TStepS m σ P} :
  P (λ κ P',
      if κ is Some e then
        ∃ κs', tcons e κs' ⊆ κs ∧ P' (λ σ', σ' ~{m, κs'}~>ₜ Pσ)
      else
        P' (λ σ', σ' ~{m, κs}~>ₜ Pσ)
  ) →
  σ ~{m, κs}~>ₜ Pσ.
Proof.
 move => /tsteps_proof[?[?[??]]].
 case_match; destruct_all?; simplify_eq/=.
 - revert select (_ ⊆ _) => <-.
   apply: (thas_trace_trans (tcons _ tnil)); simplify_eq/=.
    { apply (steps_spec_has_trace' _ (Some _)); naive_solver. }
   naive_solver.
  - apply: (thas_trace_trans tnil); simplify_eq/=.
    { apply (steps_spec_has_trace' _ None); naive_solver. }
    naive_solver.
Qed.

Lemma steps_spec_tstep_s {EV} (m : module EV) σ κ Pσ `{!TStepS m σ P} :
  P (λ κ' P', κ = κ' ∧ P' Pσ) →
  σ -{m, κ}->ₛ Pσ.
Proof. move => /tsteps_proof[?[?[[? HP] HG']]]. subst. move: HP => /HG'. done. Qed.

Lemma steps_impl_tstep_i {EV} (m : module EV) σ (Pσ : _ → _ → _ → Prop) `{!TStepI m σ P} :
  P (λ b κ' P', ∀ (b' : bool) (Pσ' : _ → Prop), (b → b') → P' (λ σ', Pσ' σ' → Pσ b' κ' Pσ')) →
  σ -{m}-> Pσ.
Proof.
  move => /tstepi_proof?. apply: steps_impl_mono; [done|] => ??? [?[?[HP[? HG']]]].
  naive_solver.
Qed.

Ltac tstep_s :=
  first [
      once (notypeclasses refine (tsim_tstep_s _ _ _ _ _ _ _ _ _); [solve [typeclasses eauto with tstep]|]); simpl
    | once (notypeclasses refine (thas_trace_tstep_s _ _ _ _ _); [solve [typeclasses eauto with tstep]|]); simpl
    | once (notypeclasses refine (steps_spec_tstep_s _ _ _ _ _)); [solve [typeclasses eauto with tstep]|]; simpl
    ].
Ltac tstep_i :=
  first [
      once (notypeclasses refine (tsim_tstep_i _ _ _ _ _ _ _ _); [solve [typeclasses eauto with tstep]|]); simpl
    | once (notypeclasses refine (steps_impl_tstep_i _ _ _ _); [solve [typeclasses eauto with tstep]|]); simpl
    ].
Ltac tstep_both :=
  once (notypeclasses refine (tsim_tstep_both _ _ _ _ _ _ _ _); [solve [typeclasses eauto with tstep]|]); simpl.

Lemma tstep_i_generic EV (m : module EV) σ:
  TStepI m σ (λ G, σ -{ m }-> (λ b κ Pσ, G b κ (λ G', ∃ σ', Pσ σ' ∧ G' σ'))).
Proof. constructor => ? HG. apply: steps_impl_mono; [done|]. naive_solver. Qed.
Global Hint Resolve tstep_i_generic | 1000 : tstep.

Lemma tstep_s_generic EV (m : module EV) σ:
  TStepS m σ (λ G, ∃ κ, G κ (λ G', σ -{m, κ}->ₛ G')).
Proof. constructor => ? [??]. eexists _, _. split; [done|]. done. Qed.
Global Hint Resolve tstep_s_generic | 1000 : tstep.

(** * proving a refinement based on another refinement *)

Lemma forall_to_ex1 A B (P1 : A → Prop)  P2 (Q : B → Prop):
 (∃ n : A, P1 n ∧ (∀ y, P2 n y → Q y)) -> (∀ y, (∀ n : A, P1 n → P2 n y) → Q y).
Proof. naive_solver. Qed.

(** Exploration of a proof technique that is more complete than other ones: *)
Lemma trefines_implies_trefines {EV} (m1 m2 : mod_state EV):
  trefines m1 m2 → trefines m1 m2.
Proof.
  move => [/=Hr]. constructor => κs Ht.
  move: Hr. move: (ms_state m1) (ms_state m2) Ht => σ1 σ2 Ht.
  move: σ2. apply: forall_to_ex1.
  elim: Ht.
  - move => ?????. eexists tnil. split; [ by apply: TTraceEnd|]. move => ??. by apply: TTraceEnd.
  - move => ??? κ ?? Hstep ? IH ?.
    have [f Hf]:= CHOICE IH.
    eexists (tapp (option_trace κ) (tex _ f)). split.
    + apply: TTraceStep; [done| |done]. move => ??. apply: thas_trace_ex. naive_solver.
    + move => σ2. destruct κ; simplify_eq/=.
      * move => /(thas_trace_cons_inv _ _) Ht.
        apply: (thas_trace_trans tnil); [done|] => ? [?[? {}Ht]].
        apply: thas_trace_mono; [|done|done].
        apply: TTraceStep; [done | |simpl; done]. move => ??.
        have /thas_trace_ex_inv{}Ht := Ht _ ltac:(done).
        apply: (thas_trace_trans tnil); [done|] => ? [[??]?].
        apply: thas_trace_mono; [|done| ]. naive_solver. done.
      * move => /thas_trace_ex_inv Ht.
        apply: (thas_trace_trans tnil); [done|] => ? [[??]?].
        apply: thas_trace_mono; [|done|done]. naive_solver.
  - move => ?????? IH ?.
    have [fx Hfx]:= AxCHOICE _ _ _ IH.
    eexists (tall _ (λ x, fx x)). split.
    + apply: thas_trace_all. naive_solver.
    + move => ? /thas_trace_all_inv ?. apply: thas_trace_mono; [|done|done].
      apply: thas_trace_all. naive_solver.
      Unshelve. done.
Qed.

Lemma forall_to_ex2 A B1 B2 (P1 : A → Prop)  P2 (Q : B1 → B2 → Prop) R:
 (∃ n : A, P1 n ∧ (∀ y1 y2, R y1 y2 → P2 n y1 y2 → Q y1 y2)) -> (∀ y1 y2, R y1 y2 → (∀ n : A, P1 n → P2 n y1 y2) → Q y1 y2).
Proof. naive_solver. Qed.

Lemma trefines1_implies_trefines2 {EV1 EV2} (mi1 ms1 : mod_state EV1) (mi2 ms2 : mod_state EV2)
      (iinv : mi1.(m_state) → mi2.(m_state) → Prop)
      (sinv : ms1.(m_state) → ms2.(m_state) → Prop):
  trefines mi1 ms1 →
  iinv mi1.(ms_state) mi2.(ms_state) →
  sinv ms1.(ms_state) ms2.(ms_state) →
  (∀ σ1 σ2 κ Pσ2, iinv σ1 σ2 → m_step mi2 σ2 κ Pσ2 → ∃ κ',
    (if κ' is Some e then
       ∀ σs1 σs2 Pσs1, sinv σs1 σs2 → m_step ms1 σs1 κ' Pσs1 →
          σs2 ~{ ms2, option_trace κ }~>ₜ (λ σs2', ∃ σs1', Pσs1 σs1' ∧ sinv σs1' σs2')
     else κ = None) ∧
       σ1 ~{ mi1, option_trace κ' }~>ₜ (λ σ1', ∃ σ2', Pσ2 σ2' ∧ iinv σ1' σ2')) →
  (∀ σ1 σ2 Pσ1, sinv σ1 σ2 → m_step ms1 σ1 None Pσ1 →
                σ2 ~{ ms2, tnil }~>ₜ (λ σ2', ∃ σ1', Pσ1 σ1' ∧ sinv σ1' σ2')) →
  trefines mi2 ms2.
Proof.
  move => [/=Hr] Hiinvinit Hsinvinit Histep Hsnil.
  have {}Hsnil: (∀ σ1 σ2 Pσ1, sinv σ1 σ2 → σ1 ~{ ms1, tnil }~>ₜ Pσ1 →
                σ2 ~{ ms2, tnil }~>ₜ (λ σ2', ∃ σ1', Pσ1 σ1' ∧ sinv σ1' σ2')). {
    clear -Hsnil.
    move => σ1 σ2 Pσ1 Hsinv /thas_trace_nil_inv.
    have : @tnil EV1 ⊆ tnil by done. move: {1 3}(@tnil EV1) => κs Hκs Ht.
    elim: Ht σ2 Hsinv Hκs.
    - move => ????????. apply: TTraceEnd; naive_solver.
    - move => ??? κ ?? Hstep ? IH Hs1 ?? Hs2.
      pose proof (transitivity Hs1 Hs2) as Hs. destruct κ; simplify_eq/=; [easy| ].
      move: Hstep => /Hsnil {}Hstep.
      apply: (thas_trace_trans tnil); naive_solver.
  }
  constructor => κs Ht. move: Hiinvinit Hsinvinit Hr.
  move: (ms_state mi1) (ms_state mi2) (ms_state ms1) (ms_state ms2) Ht => σi1 σi2 σs1 σs2 Ht Hiinit Hsinit.
  move: σs1 σs2 Hsinit. apply: forall_to_ex2.
  elim: Ht σi1 Hiinit.
  - move => ???????. eexists tnil. split; [ by apply: TTraceEnd|]. move => ????. by apply: TTraceEnd.
  - move => ? Pσ2 ? κ ? κs' Hstep ? IH ? ? Hiinv.
    have [κ' [Hsend Hsteps]]:= Histep _ _ _ _ Hiinv Hstep.
    have {}IH : ∀ σi1, (∃ σ2', Pσ2 σ2' ∧ iinv σi1 σ2') → ∃ n, σi1 ~{ mi1, n }~>ₜ (λ _, True) ∧
       (∀ y1 y2, sinv y1 y2 → y1 ~{ ms1, n }~>ₜ (λ _, True) → y2 ~{ ms2, κs' }~>ₜ (λ _, True)).
    { move => ?. naive_solver. }
    have [f Hf]:= CHOICE IH.
    eexists (tapp (option_trace κ') (tex _ f)). split.
    + apply: thas_trace_trans; [done| ] => ?[?[??]].
      apply: thas_trace_ex. naive_solver.
    + move => σs1 σs2 ? /thas_trace_app_inv Happ.
      apply: (thas_trace_mono _ _ (λ _, True)); [|done|done].
      move: Happ. destruct κ'; simplify_eq/=.
      * move => /(thas_trace_cons_inv _ _)/Hsnil Ht.
        apply: (thas_trace_trans tnil); [naive_solver|].
        move => {Ht} ? [? [[?[? HP]]?]].
        apply: thas_trace_trans; [naive_solver|].
        move => ?[?[??]].
        have /Hsnil ?:= HP _ ltac:(done).
        apply: (thas_trace_trans tnil); [naive_solver|].
        move => ? [?[/thas_trace_ex_inv/Hsnil??]].
        apply: (thas_trace_trans tnil); [naive_solver|].
        move => ?[?[[[?[?[??]]]?]?]].
        naive_solver.
      * move => /Hsnil Hs.
        apply: (thas_trace_trans tnil); [naive_solver|].
        move => ? [? [/thas_trace_ex_inv/Hsnil? ?]].
        apply: (thas_trace_trans tnil); [naive_solver|].
        move => ? [?[[[?[?[??]]]?]?]]. naive_solver.
  - move => ?????? IH ???.
    have {}IH := (IH _ _ ltac:(done)).
    have [fx Hfx]:= AxCHOICE _ _ _ IH.
    eexists (tall _ (λ x, fx x)). split.
    + apply: thas_trace_all. naive_solver.
    + move => ??? /thas_trace_all_inv ?. apply: thas_trace_mono; [|done|done].
      apply: thas_trace_all. naive_solver.
      Unshelve. all: naive_solver.
Qed.
