Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.filter.

(*** Proving refinement *)

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

(** * tsim *)

Definition tsim {EV} (n : trace_index) (b : bool) (mi ms : module EV) (σi : mi.(m_state)) (κss : trace EV) (σs : ms.(m_state))  :=
  ∀ κs n',
    (if b then tiS n' ⊆ n else n' ⊆ n) →
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
  (∀ n n' σi σs, tiS n' ⊆ n → Pσ n σi σs → Pσ n' σi σs) →
  (* TODO: can one somehow link this n' to the n? *)
  (∀ n', Plater (λ b', ∀ σi σs, Pσ n' σi σs → σi ⪯{mi, ms, n', b'} σs)) →
  σi ⪯{mi, ms, n, b} σs.
Proof.
  move => HP HPmono Hsim κs' n' Hn Ht /=.
  have {}Hn: n' ⊆ n. { destruct b; (etrans; [|done]) => //. apply ti_le_S. }
  elim/ti_lt_ind: n n' κs' σi σs Hn HP Ht.
  move => n IHn n' κs' σi σs Hn HP Ht.
  apply: Hsim ; [|done|done|done].
  move => ????? Hn'/=. eapply IHn; [done..|].
  by apply: HPmono.
Qed.

Lemma tsim_remember_all {EV A} {mi ms : module EV} σi σs b n:
  (∀ n, Plater (λ b', ∀ x, σi x ⪯{mi, ms, n, b'} σs x)) →
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
Global Hint Constants Opaque : tstep.
Global Hint Variables Opaque : tstep.
Class TStepI {EV} (mi : module EV) (σi : mi.(m_state)) (P : (trace EV → ((bool → mi.(m_state) → Prop) → Prop) → Prop) → Prop) : Prop := {
  tstepi_proof n Pσi G κs:
    σi ~{mi, κs, n}~>ₜ Pσi →
    P G →
    under_tall κs (λ κs,
      (tnil ⊆ κs ∧ Pσi σi) ∨
      ∃ κs1 κs2 (Pσ : _ → Prop),
        tapp κs1 κs2 ⊆ κs ∧
        (∀ G', Pσ G' → ∃ σi' b n', σi' ~{mi, κs2, n'}~>ₜ Pσi ∧ (if b then tiS n' ⊆ n else n' ⊆ n) ∧ G' b σi') ∧
        G κs1 Pσ
      )
}.
Global Hint Mode TStepI + + ! - : tstep.

Lemma tsim_tstep_i {EV} (mi : module EV) σi P `{!TStepI mi σi P} ms σs n b:
  P (λ κs1 Pσ, Pσ (λ b' σi', σi' ⪯{mi, ms, n, b || b', κs1} σs)) →
  σi ⪯{mi, ms, n, b} σs.
Proof.
  move => HP κs n' Hn /tstepi_proof Hi. move: HP => /Hi /= {}HP.
  apply: thas_trace_under_tall; [done..|] => {Hi HP} {}κs /= [[??]|[κs1[κs2[Pσ [Hκs [HPσ /HPσ[σi' [b' [n'' [?[? Ht]]]]]]]]]]].
  { tend. }
  rewrite -Hκs. apply: Ht; [|done]. destruct b, b' => /=; (etrans; [|done]); try econs; (etrans; [|done]) => //.
  apply ti_le_S.
Qed.

Lemma tsim_tstep_both {EV} (mi : module EV) σi P `{!TStepI mi σi P} ms σs n b:
  P (λ κs1 Pσ, σs ~{ms, κs1}~>ₜ (λ σs', Pσ (λ b' σi', σi' ⪯{mi, ms, n, b || b', tnil} σs'))) →
  σi ⪯{mi, ms, n, b} σs.
Proof.
  move => HP κs n' Hn /tstepi_proof Hi. move: HP => /Hi /= {}HP.
  apply: thas_trace_under_tall; [done..|] => {Hi HP} {}κs /= [[??]|[κs1[κs2[Pσ [Hκs [HPσ Ht]]]]]].
  { tend. }
  rewrite -Hκs. apply: thas_trace_trans; [done|] => ? /HPσ[σi' [b' [n'' [?[? {}Ht]]]]].
  apply: Ht; [|done]. destruct b, b' => /=; (etrans; [|done]); try econs; (etrans; [|done]) => //.
  apply ti_le_S.
Qed.

Lemma TStepI_single {EV} (mi : module EV) σi (P : _ → Prop) :
  (∀ G κ Pσi,
    mi.(m_step) σi κ Pσi →
    P G →
    ∃ (Pσ : _ → Prop),
    (∀ G', Pσ G' → ∃ σi', Pσi σi' ∧ G' true σi') ∧
    G (option_trace κ) Pσ
  ) →
  TStepI mi σi P.
Proof.
  move => Hstep. constructor => ???? Ht HP.
  thas_trace_inv Ht.
  - left. naive_solver.
  - right. have [?[HG ?]]:= Hstep _ _ _ ltac:(done) ltac:(done).
    eexists _, _, _. split_and!; [done| |done]. move => ? /HG[?[??]]. eexists _, _, _.
    split_and!; [naive_solver| |done] => /=. etrans; [|done]. econs. by econs.
    Unshelve. done.
Qed.

Class TStepS {EV} (ms : module EV) (σs : ms.(m_state)) (κs : trace EV)
      (P : (trace EV → ms.(m_state) → Prop) → Prop) : Prop := {
  tsteps_proof G:
    P G →
    ∃ κs' κs'', tapp κs' κs'' ⊆ κs ∧ σs ~{ ms, κs' }~>ₜ (λ σs', G κs'' σs')
}.
Global Hint Mode TStepS + + ! + - : tstep.

Lemma tsim_tstep_s {EV} (ms : module EV) σs κs P `{!TStepS ms σs κs P} mi σi n b :
  P (λ κs' σs', σi ⪯{mi, ms, n, b, κs'} σs') →
  σi ⪯{mi, ms, n, b, κs} σs.
Proof.
  move => /tsteps_proof [?[?[Hκs ?]]] => ????. rewrite -Hκs -tapp_assoc.
  apply: thas_trace_trans; [done|] => ? Ht. by apply: Ht.
Qed.

Lemma thas_trace_tstep_s {EV} (m : module EV) σ κs Pσ `{!TStepS m σ κs P} :
  P (λ κs' σ', σ' ~{m, κs'}~>ₜ Pσ) →
  σ ~{m, κs}~>ₜ Pσ.
Proof. move => /tsteps_proof [?[?[<- ?]]]. by apply: thas_trace_trans. Qed.

Ltac tstep_s :=
  (* TODO: also use thas_trace_tstep_s here *)
  notypeclasses refine (tsim_tstep_s _ _ _ _ _ _ _ _ _); [solve [typeclasses eauto with tstep]|]; simpl.
Ltac tstep_i :=
  notypeclasses refine (tsim_tstep_i _ _ _ _ _ _ _ _); [solve [typeclasses eauto with tstep]|]; simpl.


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

(** showing that [trefines1_implies_trefines2] is useful by proving
[tmod_filter_refines] with a siginificantly simpler proof. *)
Lemma tmod_filter_refines' {EV1 EV2} (R : EV1 → option EV2 → Prop) mi ms σi σs:
  trefines (MS mi σi) (MS ms σs) →
  trefines (MS (mod_filter mi R) σi) (MS (mod_filter ms R) σs).
Proof.
  move => Hr. eapply (trefines1_implies_trefines2 (MS mi _) (MS ms _) (MS (mod_filter mi R) _) (MS (mod_filter ms R) _) (λ σ1 σ2, σ1 = σ2) (λ σ1 σ2, σ1 = σ2)); [done.. | |] => /=.
  - move => ???? -> Hstep. inversion Hstep; simplify_eq. eexists e.
    split.
    + case_match; simplify_eq => //.
      move => ??? -> ?. apply: TTraceStep; [| |by erewrite tapp_tnil_r].
      { econstructor; [done| simpl; done]. }
      move => ??. apply: TTraceEnd; naive_solver.
    + apply: TTraceStep; [done| |by erewrite tapp_tnil_r].
      move => ??. apply: TTraceEnd; [|done]. naive_solver.
  - move => ??? -> ?.
    apply: TTraceStep; [by econstructor| |simpl; done].
    move => ??. apply: TTraceEnd; [|done]. naive_solver.
Qed.
