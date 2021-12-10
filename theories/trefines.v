Require Export refframe.module.
Require Import refframe.srefines.
Require Import refframe.filter.
Require Import refframe.product.
Require Import refframe.example_modules.

(** [trefines] is a weaker notion of refinement that does not allow commuting choices and externally visible events*)

Inductive trace (EV : Type) : Type :=
| tnil
| tcons (κ : EV) (κs : trace EV)
| tex (T : Type) (f : T → trace EV)
| tall (T : Type) (f : T → trace EV).
Arguments tnil {_}.
Arguments tcons {_}.
Arguments tex {_}.
Arguments tall {_}.

Fixpoint tapp {EV} (κs1 κs2 : trace EV) :=
  match κs1 with
  | tnil => κs2
  | tcons κ κs' => tcons κ (tapp κs' κs2)
  | tex T f => tex T (λ x, tapp (f x) κs2)
  | tall T f => tall T (λ x, tapp (f x) κs2)
  end.

Definition option_trace {EV} (κ : option EV) : trace EV :=
  match κ with
  | Some κ => tcons κ tnil
  | None => tnil
  end.

Inductive subtrace {EV} : trace EV → trace EV → Prop :=
| subtrace_nil :
    subtrace tnil tnil
| subtrace_cons κ κs κs':
    subtrace κs κs' →
    subtrace (tcons κ κs) (tcons κ κs')
| subtrace_ex_l T f κs':
    (∀ x, subtrace (f x) κs') →
    subtrace (tex T f) κs'
| subtrace_all_r T f κs:
    (∀ x, subtrace κs (f x)) →
    subtrace κs (tall T f)
| subtrace_ex_r {T f} x κs:
    subtrace κs (f x) →
    subtrace κs (tex T f)
| subtrace_all_l {T f} x κs':
    subtrace (f x) κs' →
    subtrace (tall T f) κs'
.
Global Instance trace_subseteq EV : SubsetEq (trace EV) := @subtrace EV.
Global Instance trace_equiv EV : Equiv (trace EV) := λ x y, x ⊆ y ∧ y ⊆ x.

Global Instance subtrace_preorder EV : PreOrder (@subtrace EV).
Proof.
  constructor.
  - move => κs. elim: κs.
    + constructor.
    + move => ???. by constructor.
    + move => ???. constructor => ?. econstructor. naive_solver.
    + move => ???. constructor => ?. econstructor. naive_solver.
  - move => x y z Hs. elim: Hs z.
    + done.
    + move => ???? IH z Hs.
      elim: z Hs.
      * inversion 1.
      * move => ??? Hs. inversion Hs; simplify_eq. constructor. naive_solver.
      * move => ??? Hs. inversion Hs; simplify_K.
        econstructor. naive_solver.
      * move => ??? Hs. inversion Hs; simplify_K.
        econstructor. naive_solver.
    + move => ???? IH ??. constructor. naive_solver.
    + move => ???? IH z Hs.
      elim: z Hs.
      * inversion 1; simplify_K. naive_solver.
      * move => ??? Hs. inversion Hs; simplify_K. naive_solver.
      * move => ??? Hs. inversion Hs; simplify_K.
        -- econstructor. naive_solver.
        -- naive_solver.
      * move => ??? Hs. inversion Hs; simplify_K.
        -- econstructor. naive_solver.
        -- naive_solver.
    + move => ?? v ?? IH z Hs.
      elim: z Hs.
      * inversion 1; simplify_K. naive_solver.
      * move => ??? Hs. inversion Hs; simplify_K. naive_solver.
      * move => ??? Hs. inversion Hs; simplify_K; [ naive_solver |].
        econstructor. naive_solver.
      * move => ??? Hs. inversion Hs; simplify_K; [ naive_solver |].
        econstructor. naive_solver.
    + move => ?? v ?? IH z Hs. econstructor. naive_solver.
Qed.
Global Instance equiv_trace_equiv EV : Equivalence (≡@{trace EV}).
Proof.
  constructor.
  - done.
  - move => ?? [??]. done.
  - move => ??? [??] [??]. by split; etrans.
Qed.

Lemma subtrace_nil_ex_inv EV T f:
  @tnil EV ⊆ tex T f →
  ∃ x, tnil ⊆ f x.
Proof. inversion 1; simplify_K. naive_solver. Qed.

Lemma subtrace_cons_ex_inv {EV} (κ : EV) κs T f:
  tcons κ κs ⊆ tex T f →
  ∃ x, tcons κ κs ⊆ f x.
Proof. inversion 1; simplify_K. naive_solver. Qed.

Lemma subtrace_all_nil_inv EV T f:
  tall T f ⊆ @tnil EV →
  ∃ x, f x ⊆ tnil.
Proof. inversion 1; simplify_K. naive_solver. Qed.

Lemma subtrace_all_cons_inv {EV} (κ : EV) κs T f:
  tall T f ⊆ tcons κ κs →
  ∃ x, f x ⊆ tcons κ κs.
Proof. inversion 1; simplify_K. naive_solver. Qed.

Global Instance tapp_assoc {EV} : Assoc (=) (@tapp EV).
Proof.
  move => x. elim: x => //=.
  - move => ?????. f_equal. naive_solver.
  - move => ?? IH ??. f_equal. apply functional_extensionality. naive_solver.
  - move => ?? IH ??. f_equal. apply functional_extensionality. naive_solver.
Qed.

Lemma tapp_mono {EV} (κs1 κs1' κs2 κs2' : trace EV) :
  κs1 ⊆ κs1' →
  κs2 ⊆ κs2' →
  tapp κs1 κs2 ⊆ tapp κs1' κs2'.
Proof.
  move => Hs.
  elim: Hs κs2 κs2' => /=.
  - naive_solver.
  - move => ????????. constructor. naive_solver.
  - move => ????????. constructor => ?. naive_solver.
  - move => ????????. econstructor. naive_solver.
  - move => ?????????. econstructor. naive_solver.
  - move => ?????????. econstructor. naive_solver.
Qed.

Lemma tapp_tnil_r {EV} (κs : trace EV) :
  tapp κs tnil = κs.
Proof.
  elim: κs.
  - done.
  - move => ?? Htapp /=. by f_equal.
  - move => ?? IH /=. f_equal. apply functional_extensionality. naive_solver.
  - move => ?? IH /=. f_equal. apply functional_extensionality. naive_solver.
Qed.

Definition tub {EV} :=
  @tex EV Empty_set (λ x, match x with end).

Definition tnb {EV} :=
  @tall EV Empty_set (λ x, match x with end).

Lemma tub_sub {EV} (κs : trace EV):
  tub ⊆ κs.
Proof. by constructor. Qed.

Lemma tnb_sub {EV} (κs : trace EV):
  κs ⊆ tnb.
Proof. by constructor. Qed.

Lemma tex_unit EV (f : _ → trace EV):
  tex () f ≡ f tt.
Proof. split; econstructor; [case|]; done. Qed.


(* Definition VisNoUb {EV} (m : module EV) (κ : option EV) (Pσ : (m.(m_state) → Prop)) := *)
  (* is_Some κ → ∃ σ, Pσ σ. *)

Inductive thas_trace {EV} (m : module EV) : m.(m_state) → trace EV → (m.(m_state) → Prop) → Prop :=
| TTraceEnd σ (Pσ : _ → Prop) κs:
    Pσ σ →
    tnil ⊆ κs →
    thas_trace m σ κs Pσ
| TTraceStep σ1 Pσ2 Pσ3 κ κs κs':
    m.(m_step) σ1 κ Pσ2 →
    (∀ σ2, Pσ2 σ2 → thas_trace m σ2 κs' Pσ3) →
    tapp (option_trace κ) κs' ⊆ κs →
    (* VisNoUb m κ Pσ2 → *)
    thas_trace m σ1 κs Pσ3
| TTraceAll T f σ κs Pσ:
    (∀ x, thas_trace m σ (f x) Pσ) →
    tall T f ⊆ κs →
    thas_trace m σ κs Pσ
.
Notation " σ '~{' m , Pκs '}~>ₜ' P " := (thas_trace m σ Pκs P) (at level 40).

Inductive thas_trace_simple {EV} (m : module EV) : m.(m_state) → trace EV → (m.(m_state) → Prop) → Prop :=
| TSTraceEnd σ (Pσ : _ → Prop) κs:
    Pσ σ →
    tnil ⊆ κs →
    thas_trace_simple m σ κs Pσ
| TSTraceStep σ1 Pσ2 Pσ3 κ κs κs':
    m.(m_step) σ1 κ Pσ2 →
    (∀ σ2, Pσ2 σ2 → thas_trace_simple m σ2 κs' Pσ3) →
    tapp (option_trace κ) κs' ⊆ κs →
    (* VisNoUb m κ Pσ2 → *)
    thas_trace_simple m σ1 κs Pσ3
.
Notation " σ '~{' m , Pκs '}~>ₜₛ' P " := (thas_trace_simple m σ Pκs P) (at level 40).

Global Instance thas_trace_proper {EV} (m : module EV) :
  Proper ((=) ==> (⊆) ==> (pointwise_relation m.(m_state) impl) ==> impl) (thas_trace m).
Proof.
  move => ?? -> κs1 κs2 Hκs Pσ1 Pσ2 HP Ht.
  elim: Ht κs2 Pσ2 Hκs HP.
  - move => ???????? HP. apply: TTraceEnd. by apply: HP. by etrans.
  - move => ??????? IH Hnext ??? Hκs HP.
    apply: TTraceStep; [done| |].
    + move => ??. naive_solver.
    + by etrans.
  - move => *. eapply TTraceAll. naive_solver. by etrans.
Qed.

Lemma thas_trace_mono {EV} {m : module EV} κs' κs (Pσ2' Pσ2 : _ → Prop)  σ1 :
  σ1 ~{ m, κs' }~>ₜ Pσ2' →
  κs' ⊆ κs →
  (∀ σ, Pσ2' σ → Pσ2 σ) →
  σ1 ~{ m, κs }~>ₜ Pσ2.
Proof. move => ???. by apply: thas_trace_proper. Qed.

Lemma thas_trace_trans {EV} κs1 κs2 (m : module EV) σ1 Pσ2 Pσ3 :
  σ1 ~{ m, κs1 }~>ₜ Pσ2 →
  (∀ σ2, Pσ2 σ2 → σ2 ~{ m, κs2 }~>ₜ Pσ3) →
  σ1 ~{ m, tapp κs1 κs2 }~>ₜ Pσ3.
Proof.
  elim.
  - move => ??????.
    apply: thas_trace_mono; [ naive_solver | |done].
    etrans; [| by apply: tapp_mono]. done.
  - move => ???????????.
    apply: TTraceStep; [done| |].
    + naive_solver.
    + etrans; [| by apply: tapp_mono]. by rewrite assoc.
  - move => *.
    eapply TTraceAll. 2: {
      etrans; [| by apply: tapp_mono].
      simpl. done.
    }
    naive_solver.
Qed.

Lemma thas_trace_ex {EV T} x f (m : module EV) σ Pσ:
  σ ~{ m, f x }~>ₜ Pσ →
  σ ~{ m, tex T f }~>ₜ Pσ.
Proof. move => ?. apply: thas_trace_mono; [done| |done]. by econstructor. Qed.

Lemma thas_trace_all {EV T} f (m : module EV) σ Pσ:
  (∀ x, σ ~{ m, f x }~>ₜ Pσ) →
  σ ~{ m, tall T f }~>ₜ Pσ.
Proof. move => ?. by eapply TTraceAll. Qed.

Lemma thas_trace_nil_inv' {EV} κs (m : module EV) σ1 Pσ3:
  σ1 ~{ m, κs }~>ₜ Pσ3 → κs ⊆ tnil →
  σ1 ~{ m, tnil }~>ₜₛ Pσ3.
Proof.
  elim.
  - move => *. by apply: TSTraceEnd.
  - move => ??? κ ???? IH Hs1 Hs2.
    pose proof (transitivity Hs1 Hs2) as Ht.
    destruct κ; simplify_eq/=. 1: by inversion Ht.
    apply: TSTraceStep; [done| move => ??; by apply: IH | done].
  - move => ?????? IH Hs1 Hs2.
    pose proof (transitivity Hs1 Hs2) as Ht.
    inversion Ht; simplify_K. by apply: IH.
Qed.

Lemma thas_trace_nil_inv {EV} (m : module EV) σ1 Pσ3:
  σ1 ~{ m, tnil }~>ₜ Pσ3 →
  σ1 ~{ m, tnil }~>ₜₛ Pσ3.
Proof. move => ?. by apply: thas_trace_nil_inv'. Qed.

Lemma thas_trace_cons_inv' {EV} κs κs' κ (m : module EV) σ1 Pσ3:
  σ1 ~{ m, κs }~>ₜ Pσ3 → κs ⊆ tcons κ κs' →
  σ1 ~{ m, tnil }~>ₜ (λ σ2, ∃ Pσ2', m.(m_step) σ2 (Some κ) Pσ2' ∧ ∀ σ2', Pσ2' σ2' → σ2' ~{ m, κs' }~>ₜ Pσ3).
Proof.
  move => Hs.
  elim: Hs κ κs'.
  - move => ?????  κ κs' ?.
    have : tnil ⊆ tcons κ κs' by etrans.
    easy.
  - move => ??? κ' ???? IH Hs ?? Hsub.
    destruct κ'; simplify_eq/=.
    + pose proof (transitivity Hs Hsub) as Ht.
      inversion Ht; simplify_eq.
      constructor; [|done].
      eexists _. split; [ done |]. move => ??.
      apply: thas_trace_mono; [ naive_solver | | naive_solver].
      done.
    + apply: TTraceStep; [ done | | by constructor].
      move => ??. apply: IH; [done|].
      etrans. done. done.
  - move => ?????? IH Hsub ?? Hsub2.
    pose proof (transitivity Hsub Hsub2) as [??]%subtrace_all_cons_inv.
    naive_solver.
Qed.

Lemma thas_trace_cons_inv {EV} κs' κ (m : module EV) σ1 Pσ3:
  σ1 ~{ m, tcons κ κs' }~>ₜ Pσ3 →
  σ1 ~{ m, tnil }~>ₜ (λ σ2, ∃ Pσ2', m.(m_step) σ2 (Some κ) Pσ2' ∧ ∀ σ2', Pσ2' σ2' → σ2' ~{ m, κs' }~>ₜ Pσ3).
Proof. move => ?. by apply: thas_trace_cons_inv'. Qed.

Lemma thas_trace_ex_inv' {EV} κs T f (m : module EV) σ1 Pσ3:
  σ1 ~{ m, κs }~>ₜ Pσ3 → κs ⊆ tex T f →
  σ1 ~{ m, tnil }~>ₜ (λ σ2, ∃ x, σ2 ~{ m, f x }~>ₜ Pσ3).
Proof.
  move => Hs.
  elim: Hs T f.
  - move => ????? T f ?.
    have : tnil ⊆ tex T f by etrans.
    move => /subtrace_nil_ex_inv[??].
    constructor; [|done]. eexists _. by constructor.
  - move => ??? κ ???? IH Hs ?? Hsub.
    destruct κ; simplify_eq/=.
    + pose proof (transitivity Hs Hsub) as Ht.
      move: Ht => /(subtrace_cons_ex_inv _ _)[??].
      constructor; [|done]. eexists _.
      apply: TTraceStep; [done|done|done].
    + apply: TTraceStep; [ done | | by constructor].
      move => ??. apply: IH; [done|].
      by etrans.
  - move => T1 f1 ???? IH Hsub1 T2 f2 Hsub2.
    pose proof (transitivity Hsub1 Hsub2) as Ht.
    inversion Ht; simplify_K. 2: naive_solver.
    constructor; [|done]. eexists _. apply: thas_trace_mono; [|done|done].
    by apply: thas_trace_all.
Qed.

Lemma thas_trace_ex_inv {EV} T f (m : module EV) σ1 Pσ3:
  σ1 ~{ m, tex T f }~>ₜ Pσ3 →
  σ1 ~{ m, tnil }~>ₜ (λ σ2, ∃ x, σ2 ~{ m, f x }~>ₜ Pσ3).
Proof. move => ?. by apply: thas_trace_ex_inv'. Qed.

Lemma thas_trace_all_inv' {EV T} κs f (m : module EV) σ1 Pσ3:
  σ1 ~{ m, κs }~>ₜ Pσ3 → κs ⊆ tall T f →
  ∀ x, σ1 ~{ m, f x }~>ₜ Pσ3.
Proof.
  move => ???. apply: thas_trace_mono; [done| |done].
  etrans; [done|]. by econstructor.
Qed.

Lemma thas_trace_all_inv {EV} T f (m : module EV) σ1 Pσ3:
  σ1 ~{ m, tall T f }~>ₜ Pσ3 →
  ∀ x, σ1 ~{ m, f x }~>ₜ Pσ3.
Proof. move => ??. by apply: thas_trace_all_inv'. Qed.

Lemma thas_trace_app_inv {EV} κs1 κs2 (m : module EV) σ1 Pσ3 :
  σ1 ~{ m, tapp κs1 κs2 }~>ₜ Pσ3 →
  σ1 ~{ m, κs1 }~>ₜ (λ σ2, σ2 ~{ m, κs2 }~>ₜ Pσ3).
Proof.
  elim: κs1 σ1 => /=.
  - move => ??. by apply: TTraceEnd.
  - move => ???? /(thas_trace_cons_inv _ _)?.
    apply: (thas_trace_trans tnil); [done| ].
    move => ?[?[??]]. apply: TTraceStep; [done| |simpl; done].
    naive_solver.
  - move => ???? /thas_trace_ex_inv?.
    apply: (thas_trace_trans tnil); [done| ].
    move => ?[??]. apply: thas_trace_ex. naive_solver.
  - move => ???? /thas_trace_all_inv?.
    apply: thas_trace_all. naive_solver.
Qed.

Lemma has_trace_inv {EV} κs (m : module EV) σ1 Pσ2:
  σ1 ~{ m, κs }~>ₜ Pσ2 →
  σ1 ~{ m, κs }~>ₜ (λ _, False) ∨ ∃ σ, Pσ2 σ.
Proof.
  elim; clear.
  - naive_solver.
  - move => σ1 Pσ2 Pσ3 κ κs κs' ? ? IH ?.
    have [?|HF]:= EM (∀ σ2 : m_state m, Pσ2 σ2 → σ2 ~{ m, κs' }~>ₜ (λ _ : m_state m, False)).
    + left. apply: TTraceStep; [done|done |done].
    + have [?|?]:= EM (∃ σ2, Pσ2 σ2 ∧ ¬ σ2 ~{ m, κs' }~>ₜ (λ _ : m_state m, False)).
      naive_solver.
      exfalso. apply: HF => σ3?.
      have [//|?]:= EM (σ3 ~{ m, κs' }~>ₜ (λ _ : m_state m, False)). naive_solver.
  - move => T f σ κs Pσ _ IH Hsub.
    have [[x ?]|?]:= EM (∃ x : T, ¬ σ ~{ m, f x }~>ₜ (λ _, False)). naive_solver.
    left. eapply TTraceAll; [|done] => x.
    have [|]:= EM (σ ~{ m, f x }~>ₜ (λ _ : m_state m, False)); naive_solver.
Qed.


Record trefines {EV} (mimpl mspec : mod_state EV) : Prop := {
  tref_subset:
    ∀ κs, mimpl.(ms_state) ~{ mimpl, κs }~>ₜ (λ _, True) →
          mspec.(ms_state) ~{ mspec, κs }~>ₜ (λ _, True)
}.

Global Instance trefines_preorder EV : PreOrder (@trefines EV).
Proof.
  constructor.
  - constructor => // κ Hi; naive_solver.
  - move => ??? [Hr1] [Hr2]. constructor => /=. naive_solver.
Qed.

Module ttest.

Lemma mod_ang_comm_not_refines:
  ¬ trefines (MS mod_ang_comm2 0) (MS mod_ang_comm1 0).
Proof.
  move => [/=Hr]. feed pose proof (Hr (tex bool (λ b, if b then tcons 1 $ tcons 2 tnil else tcons 1 $ tcons 3 tnil))) as Hr2.
  - apply: TTraceStep; [constructor| | simpl; done]. move => ?[->|->].
    + apply: (thas_trace_ex true).
      apply: TTraceStep; [constructor| | simpl; done]. move => ?->.
      apply: TTraceStep; [constructor| | simpl; done]. move => ?->.
      by apply: TTraceEnd.
    + apply: (thas_trace_ex false).
      apply: TTraceStep; [constructor| | simpl; done]. move => ?->.
      apply: TTraceStep; [constructor| | simpl; done]. move => ?->.
      by apply: TTraceEnd.
  - move: Hr2 => /thas_trace_ex_inv/thas_trace_nil_inv{}Hr2.
    inversion Hr2; simplify_eq => //. 2: invert_all @m_step => //; easy.
    move: H => [[] {}Hr].
    all: move: Hr => /(thas_trace_cons_inv _ _ _)/thas_trace_nil_inv{}Hr.
    all: inversion Hr; simplify_K; [| invert_all @m_step => //; easy].
    all: move: H => [? [? {}Hr]].
    all: invert_all @m_step.
    all: move: (Hr _ ltac:(done)) => {}Hr.

    all: move: Hr => /(thas_trace_cons_inv _ _ _)/thas_trace_nil_inv{}Hr.
    all: inversion Hr; simplify_K; [ move: H => [?[??]]; by invert_all @m_step|].
    all: invert_all @m_step.
    1: move: (H2 5 ltac:(naive_solver)) => {}Hr.
    2: move: (H2 3 ltac:(naive_solver)) => {}Hr.
    all: inversion Hr; simplify_K; [ move: H => [?[??]]; invert_all mod_ang_comm1_step|].
    all: invert_all @m_step.
    all: pose proof (transitivity H5 H3); easy.
Qed.

End ttest.

(*** Proof that trefines implies srefines *)
Inductive thas_trace_rel {EV} : (list (event EV) → Prop) → (trace EV) → Prop :=
| TRel_nil (Pκs : _ → Prop) κs:
   κs ⊆ tnil →
   Pκs [] →
   Pκs [Nb] →
   thas_trace_rel Pκs κs
| TRel_cons (Pκs : _ → Prop) κ κs κs':
   κs' ⊆ tcons κ κs →
   Pκs [] →
   Pκs [Vis κ] →
   thas_trace_rel (λ κs, Pκs (Vis κ::κs)) κs →
   thas_trace_rel Pκs κs'
| TRel_ex (Pκs : _ → Prop) T f κs:
   κs ⊆ tex T f →
   Pκs [] →
   (∀ x, thas_trace_rel Pκs (f x)) →
   thas_trace_rel Pκs κs
.

Lemma thas_trace_rel_mono_l {EV} (Pκs1 Pκs2 : _ → Prop) (κs : trace EV) :
  thas_trace_rel Pκs1 κs →
  (∀ x, Pκs1 x → Pκs2 x) →
  thas_trace_rel Pκs2 κs.
Proof.
  move => Ht. elim: Ht Pκs2.
  - move => ?????? Hsub. apply: TRel_nil => //; by apply: Hsub.
  - move => *. apply: TRel_cons; naive_solver.
  - move => *. apply: TRel_ex; naive_solver.
Qed.

Lemma thas_trace_rel_mono_r {EV} Pκs (κs1 κs2 : trace EV) :
  thas_trace_rel Pκs κs1 →
  κs2 ⊆ κs1 →
  thas_trace_rel Pκs κs2.
Proof.
  move => Ht. elim: Ht κs2.
  - move => ???????. apply: TRel_nil => //. by etrans.
  - move => *. apply: TRel_cons; [|done..]. by etrans.
  - move => *. apply: TRel_ex; [|done..]. by etrans.
Qed.

Lemma thas_trace_rel_tnil {EV} Pκs (κs : trace EV) :
  thas_trace_rel Pκs κs →
  tnil ⊆ κs →
  Pκs [] ∧ Pκs [Nb].
Proof.
  elim.
  - done.
  - move => ???? Hsub1 ???? Hsub2.
    pose proof (transitivity Hsub2 Hsub1) as Ht. inversion Ht; simplify_K.
  - move => ???? Hsub1 ??? Hsub2.
    pose proof (transitivity Hsub2 Hsub1) as Ht. inversion Ht; simplify_K. naive_solver.
Qed.

Lemma thas_trace_rel_tcons {EV} Pκs (κs : trace EV) κs' κ :
  thas_trace_rel Pκs κs →
  tcons κ κs' ⊆ κs →
  Pκs [Vis κ] ∧ thas_trace_rel (λ κs, Pκs (Vis κ :: κs)) κs'.
Proof.
  elim.
  - move => ?? Hsub1 ?? Hsub2.
    pose proof (transitivity Hsub2 Hsub1) as Ht. inversion Ht; simplify_K.
  - move => ???? Hsub1 ???? Hsub2.
    pose proof (transitivity Hsub2 Hsub1) as Ht. inversion Ht; simplify_K.
    split; [done|]. by apply: thas_trace_rel_mono_r.
  - move => ???? Hsub1 ??? Hsub2.
    pose proof (transitivity Hsub2 Hsub1) as Ht. inversion Ht; simplify_K. naive_solver.
Qed.

Lemma thas_trace_rel_tall {EV} Pκs (κs : trace EV) T f :
  thas_trace_rel Pκs κs →
  tall T f ⊆ κs →
  ∃ x, thas_trace_rel Pκs (f x).
Proof.
  elim.
  - move => ?? Hsub1 ?? Hsub2.
    pose proof (transitivity Hsub2 Hsub1) as Ht. inversion Ht; simplify_K. eexists _.
    by apply: TRel_nil.
  - move => ???? Hsub1???? Hsub2.
    pose proof (transitivity Hsub2 Hsub1) as Ht. inversion Ht; simplify_K. eexists _.
    by apply: TRel_cons.
  - move => ???? Hsub1 ??? Hsub2.
    pose proof (transitivity Hsub2 Hsub1) as Ht.
    inversion Ht; simplify_K.
    + naive_solver.
    + eexists _. by apply: TRel_ex.
Qed.

Lemma thas_trace_rel_nil {EV} Pκs (κs : trace EV) :
  thas_trace_rel Pκs κs →
  Pκs [].
Proof. inversion 1; by simplify_eq. Qed.

Lemma shas_trace_thas_trace {EV} (m : module EV) σ Pσ (Pκs : _ → Prop):
  σ ~{ m, Pκs }~>ₛ Pσ ↔ ∃ κs, thas_trace_rel Pκs κs ∧ σ ~{ m, κs }~>ₜ Pσ.
Proof.
  split.
  - elim.
    + move => ???? [??]. eexists tnil. split; [by constructor|]. by apply: TTraceEnd.
    + move => ?? Pσ2 ? κ Hstep ? IH [??].
      have [f Hf] := CHOICE IH.
      eexists (tapp (option_trace κ) (tex _ f)).
      split.
      * destruct κ => /=.
        -- apply: TRel_cons; [done..|]. apply: TRel_ex; [done..|] => -[??]. naive_solver.
        -- apply: TRel_ex; [done..|] => -[??]. naive_solver.
      * apply: TTraceStep; [done..| |done].
        move => ??. apply: thas_trace_ex. naive_solver.
  - move => [κs [Hκs Ht]].
    elim: Ht Pκs Hκs.
    + move => ???????. apply: STraceEnd; [done|].
      by apply: thas_trace_rel_tnil.
    + move => ??? κ ???? IH ?? Hrel.
      move: (Hrel) => /thas_trace_rel_nil?.
      apply: STraceStep; [done| |].
      * move => ??. apply: IH; [done| ].
        destruct κ => //; simplify_eq/=. 2: by apply: thas_trace_rel_mono_r.
        efeed pose proof @thas_trace_rel_tcons as H; [done..|]. naive_solver.
      * split; [done|]. destruct κ => //; simplify_eq/=.
        efeed pose proof @thas_trace_rel_tcons as H; [done..|]. naive_solver.
    + move => ?????? IH Hall ??.
      have := thas_trace_rel_tall _ _ _ _ ltac:(done) ltac:(done).
      naive_solver.
      Unshelve. done.
Qed.

Lemma trefines_srefines {EV} (m1 m2 : mod_state EV):
  trefines m1 m2 → srefines m1 m2.
Proof.
  move => [?]. constructor => ? /shas_trace_thas_trace[?[??]].
  apply/shas_trace_thas_trace. naive_solver.
Qed.
(* Print Assumptions trefines_refines. *)

Fixpoint trace_to_set {EV} (κs : trace EV) : list (event EV) → Prop :=
  match κs with
  | tnil => λ κs, κs = [] ∨ κs = [Nb]
  | tcons κ κs => λ κs', κs' = [] ∨ ∃ κs'', κs' = Vis κ::κs'' ∧ trace_to_set κs κs''
  | tex T f => λ κs, ∃ x, trace_to_set (f x) κs
  | tall T f => λ κs, ∀ x, trace_to_set (f x) κs
  end.

(* The following cannot be provable since [refines m1 m2 → trefines m1 m2] does not hold. *)
Lemma thas_trace_has_trace {EV} (m : module EV) σ Pσ κs:
  σ ~{ m, κs }~>ₜ Pσ ↔ σ ~{ m, trace_to_set κs }~>ₛ Pσ.
Proof.
  rewrite shas_trace_thas_trace. split.
  - move => ?. eexists _. split; [|done].
    clear. elim: κs => /=.
    + apply: TRel_nil; naive_solver.
    + move => ???. apply: TRel_cons; [done|naive_solver| |].
      * right. eexists _. split; [done|]. by apply: thas_trace_rel_nil.
      * apply: thas_trace_rel_mono_l; [done|]. naive_solver.
    + move => ?? IH.
      apply: TRel_ex; [done| |]. admit.
      move => ?. apply: thas_trace_rel_mono_l. done. naive_solver.
    + move => ?? IH.
      admit.
  - move => [κs' [Hrel Ht]]. apply: thas_trace_mono; [done| |done]. clear Ht.
    move: Hrel. move HPκs: (trace_to_set _) => Pκs Ht.
    have : ∀ x, Pκs x → trace_to_set κs x by rewrite HPκs => ?.
    elim: Ht κs {HPκs}.
    + move => ???? Hnb κs Hsub. etrans; [done|].
      move: Hnb => /Hsub /=. elim: κs {Hsub} => //=.
      * naive_solver.
      * move => ??? [??]. econstructor. naive_solver.
      * move => ????. econstructor. naive_solver.
    + move => ???????????. etrans; [done|].
      admit.
    + move => ??????????. etrans; [done|].
      constructor. naive_solver.
Abort.

Lemma refines_not_trefines:
  ¬ (∀ EV (m1 m2 : mod_state EV), srefines m1 m2 → trefines m1 m2).
Proof.
  move => Hr. apply: ttest.mod_ang_comm_not_refines. apply: Hr.
  apply mod_ang_comm_equiv.
Qed.


(* [trefines m1 m2 ↔ dem_refines m1 m2] cannot hold anymore since we made the
environment more powerful and it can now react to the choices of the module.

Consider the following (demonic) module:
         B
   A     /- 3
1 --- 2 -
         \- 4
         C

It currently refines:
   A      B
   /- 2' --- 3
1 -
   \- 2  --- 4
   A      C

But when cast to an angelic module, the original module
accepts the trace
[tcons A (tall bool (λ b, if b then tcons B nil else tcons C nil))]
But the second does not!

So it seems like one needs to loose a commuting rule of non-det choice. With
angelic choice in the environment, one can now observe the difference between these
two modules. Not sure if this is bad or good.


The problem of adding tall to dem module is that when instantiating Iris, one
cannot use nat as the step index as has_trace might contain infinite branching.
Two solutions:
1. Use Transfinite Iris
2. Restrict all angelic choices everywhere to be finite.
  - This might be the way to go for a first try as most of the examples
    that I can think of so far only rely on finite angelic non-det (e.g.
    choosing a provenance should only need to choose an existing provenance
    I hope). But I am still afraid that this will blow up in our face somewhen.
 *)

(*** trefines for [mod_filter] *)

Fixpoint trace_bind {EV1 EV2} (f : EV1 → trace EV2) (κs : trace EV1) : trace EV2 :=
  match κs with
  | tnil => tnil
  | tcons κ κs => tapp (f κ) (trace_bind f κs)
  | tex T f' => tex T (λ x, trace_bind f (f' x))
  | tall T f' => tall T (λ x, trace_bind f (f' x))
  end.

Lemma trace_bind_mono {EV1 EV2} (f : EV1 → trace EV2) κs1 κs2 :
  κs1 ⊆ κs2 →
  trace_bind f κs1 ⊆ trace_bind f κs2.
Proof.
  elim => //=.
  - move => ?????. by apply: tapp_mono.
  - move => ?????. constructor. naive_solver.
  - move => ?????. econstructor. naive_solver.
  - move => ??????. econstructor. naive_solver.
  - move => ??????. econstructor. naive_solver.
Qed.


Definition filtered_trace {EV1 EV2} (R : EV1 → option EV2 → Prop)
  : trace EV1 → trace EV2 :=
  trace_bind (λ κ, tall ({ κ' | R κ κ'}) (λ x, option_trace (`x))).

Lemma filtered_trace_mono {EV1 EV2} (R : EV1 → option EV2 → Prop) κs1 κs2 :
  κs1 ⊆ κs2 →
  filtered_trace R κs1 ⊆ filtered_trace R κs2.
Proof. apply trace_bind_mono. Qed.

Lemma tmod_filter_to_mod {EV1 EV2} (m : module EV1) (R : EV1 → option EV2 → Prop) σi Pσ κs:
  σi ~{ mod_filter m R, κs }~>ₜ Pσ →
  ∃ κs', filtered_trace R κs' ⊆ κs ∧ σi ~{ m, κs' }~>ₜ Pσ.
Proof.
  elim.
  - move => ?????. eexists tnil => /=. split; [done|]. by constructor.
  - move => ??? κ ?? Hstep ? IH Hs.
    inversion Hstep; simplify_eq.
    have [f Hf]:= CHOICE IH.
    eexists (tapp (option_trace e) (tex _ f)). split.
    + etrans; [|done].
      destruct e => /=; simplify_option_eq.
      * rewrite /filtered_trace/=-/(filtered_trace _).
        apply: (subtrace_all_l (exist _ _ _)); [done|] => ?.
        apply: tapp_mono; [done|].
        constructor => -[??]. naive_solver.
      * rewrite /filtered_trace/=-/(filtered_trace _).
        constructor => -[??]. naive_solver.
    + apply: TTraceStep; [done | |done].
      move => ??/=. eapply thas_trace_ex. naive_solver.
      Unshelve. done.
  - move => T f ???? IH ?.
    have [fx Hfx]:= AxCHOICE _ _ _ IH.
    eexists (tall T (λ x, fx x)) => /=.
    rewrite /filtered_trace/=-/(filtered_trace _).
    split.
    + etrans; [|done]. constructor => ?. econstructor. naive_solver.
    + apply: thas_trace_all. naive_solver.
Qed.

Lemma tmod_to_mod_filter {EV1 EV2} (m : module EV1) (R : EV1 → option EV2 → Prop) σi Pσ κs:
  σi ~{ m, κs }~>ₜ Pσ →
  σi ~{ mod_filter m R, filtered_trace R κs }~>ₜ Pσ.
Proof.
  elim.
  - move => ?????. constructor. done. by apply: (filtered_trace_mono _ tnil).
  - move => ??? κ ?? Hstep ? IH Hs.
    apply: thas_trace_mono; [| by apply: filtered_trace_mono |done].
    destruct κ => /=.
    + rewrite /filtered_trace/=-/(filtered_trace _).
      apply thas_trace_all => -[??].
      apply: TTraceStep; [econstructor;[done| simpl;done] |done |done].
    + apply: TTraceStep; [by econstructor | done | simpl;done].
  - move => ????????.
    apply: thas_trace_mono; [| by apply: filtered_trace_mono |done].
    rewrite /filtered_trace/=-/(filtered_trace _).
    apply: thas_trace_all. naive_solver.
Qed.

Lemma tmod_filter_refines {EV1 EV2} (R : EV1 → option EV2 → Prop) mi ms σi σs:
  trefines (MS mi σi) (MS ms σs) →
  trefines (MS (mod_filter mi R) σi) (MS (mod_filter ms R) σs).
Proof.
  move => [/=Hr]. constructor => /=? /tmod_filter_to_mod[?[? /Hr/tmod_to_mod_filter?]].
  by apply: thas_trace_mono.
Qed.

(*** trefines for [product] *)
Inductive mod_product_rel {EV1 EV2} : trace (option EV1 * option EV2) → trace EV1 → trace EV2 → Prop :=
| MPR_nil κs :
    tnil ⊆ κs →
    mod_product_rel κs tnil tnil
| MPR_ex1 T f κs κs2 :
    (∀ x, mod_product_rel κs (f x) κs2) →
    mod_product_rel κs (tex T f) κs2
| MPR_ex2 T f κs κs2 :
    (∀ x, mod_product_rel κs κs2 (f x)) →
    mod_product_rel κs κs2 (tex T f)
| MPR_all1 {T} x f κs κs2 :
    mod_product_rel κs (f x) κs2 →
    mod_product_rel κs (tall T f) κs2
| MPR_all2 {T} x f κs κs2 :
    mod_product_rel κs κs2 (f x) →
    mod_product_rel κs κs2 (tall T f)
| MPR_all T f κs κs1 κs2:
    (∀ x, mod_product_rel (f x) κs1 κs2) →
    (tall T f) ⊆ κs →
    mod_product_rel κs κs1 κs2
| MPR_cons_l κ κs κs' κs1' κs2 :
    mod_product_rel κs' κs1' κs2 →
    tcons (Some κ, None) κs' ⊆ κs →
    mod_product_rel κs (tcons κ κs1') κs2
| MPR_cons_r κ κs κs' κs1 κs2' :
    mod_product_rel κs' κs1 κs2' →
    tcons (None, Some κ) κs' ⊆ κs →
    mod_product_rel κs κs1 (tcons κ κs2')
| MPR_cons_both κ1 κ2 κs κs' κs1' κs2' :
    mod_product_rel κs' κs1' κs2' →
    tcons (Some κ1, Some κ2) κs' ⊆ κs →
    mod_product_rel κs (tcons κ1 κs1') (tcons κ2 κs2')
.


Lemma mod_product_rel_mono {EV1 EV2} κs κs' (κs1 : trace EV1) (κs2 : trace EV2) :
  mod_product_rel κs κs1 κs2 →
  κs ⊆ κs' →
  mod_product_rel κs' κs1 κs2.
Proof.
  move => Ht.
  elim: Ht κs'.
  - move => ????. constructor. by etrans.
  - move => *. constructor. naive_solver.
  - move => *. constructor. naive_solver.
  - move => *. econstructor. naive_solver.
  - move => *. econstructor; naive_solver.
  - move => *. eapply MPR_all. 2: by etrans. naive_solver.
  - move => ????? ?? IH ??.
    apply: MPR_cons_l; [| by etrans]. naive_solver.
  - move => ????? ?? IH ??.
    apply: MPR_cons_r; [| by etrans]. naive_solver.
  - move => *.
    apply: MPR_cons_both; [| by etrans]. naive_solver.
Qed.


Lemma tmod_product_to_mods {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ Pσ κs:
  σ ~{ mod_product m1 m2, κs }~>ₜ Pσ → ∃ κs', mod_product_rel κs κs'.1 κs'.2 ∧
    σ.1 ~{ m1, κs'.1 }~>ₜ (λ _, True) ∧ σ.2 ~{ m2, κs'.2 }~>ₜ (λ _, True).
Proof.
  elim.
  - move => [σ1 σ2] ????. eexists (tnil, tnil) => /=.
    split_and!.
    + apply: mod_product_rel_mono; [|done]. by constructor.
    + by constructor.
    + by constructor.
  - move => [σ1 σ2] ????? Hstep _ IH ?.
    inversion Hstep; simplify_eq.
    + have {}IH := IH (_, σ2) (conj _ ltac:(exact (eq_refl σ2))).
      have [f Hf]:= CHOICE IH.
      unshelve eexists (tapp (option_trace e) (tex _ (λ x, (f x).1)), (tall _ (λ x, (f x).2))) => /=.
      split_and!.
      -- apply: mod_product_rel_mono; [|done].
         destruct e => //=.
         ++ apply: MPR_cons_l; [|done].
            constructor => -[??]. econstructor.
            naive_solver.
         ++ constructor => -[??]. econstructor. naive_solver.
      -- apply: TTraceStep; [ done | | done].
         move => σ' Hσ'. apply: (thas_trace_ex (exist _ σ' Hσ')).
         apply: thas_trace_mono. naive_solver. done. naive_solver.
      -- apply: thas_trace_all => -[??].
         apply: thas_trace_mono. naive_solver. done. naive_solver.
    + have {}IH := IH (σ1, _) (conj ltac:(exact (eq_refl σ1)) _).
      have [f Hf]:= CHOICE IH.
      unshelve eexists ((tall _ (λ x, (f x).1)), tapp (option_trace e) (tex _ (λ x, (f x).2))) => /=.
      split_and!.
      -- apply: mod_product_rel_mono; [|done].
         destruct e => //=.
         ++ apply: MPR_cons_r; [|done].
            constructor => -[??]. econstructor.
            naive_solver.
         ++ constructor => -[??]. econstructor. naive_solver.
      -- apply: thas_trace_all => -[??].
         apply: thas_trace_mono. naive_solver. done. naive_solver.
      -- apply: TTraceStep; [ done | | done].
         move => σ' Hσ'. apply: (thas_trace_ex (exist _ σ' Hσ')).
         apply: thas_trace_mono. naive_solver. done. naive_solver.
    + have {}IH := IH (_, _) (conj _ _).
      have [f Hf]:= CHOICE2 IH.
      unshelve eexists (tcons e1 (tex _ (λ x1, (tall _ (λ x2, (f x1 x2).1)))),
                        tcons e2 (tex _ (λ x2, (tall _ (λ x1, (f x1 x2).2))))) => /=.
      split_and!.
      -- apply: mod_product_rel_mono; [|done]. simpl.
         econstructor; [|done..].
         constructor => -[??].
         constructor => -[??].
         econstructor.
         econstructor. naive_solver.
      -- apply: TTraceStep; [ done | | simpl; done].
         move => ??.
         apply: thas_trace_ex. apply: thas_trace_all => -[??]. naive_solver.
      -- apply: TTraceStep; [ done | | simpl; done].
         move => ??.
         apply: thas_trace_ex. apply: thas_trace_all => -[??]. naive_solver.
  - move => T f ???? IH ?.
    have [fx Hfx]:= AxCHOICE _ _ _ IH.
    eexists (tall T (λ x, (fx x).1), tall T (λ x, (fx x).2)) => /=.
    split_and! => //.
    -- apply: mod_product_rel_mono; [|done].
       eapply MPR_all; [|done] => ?.
       econstructor. econstructor. naive_solver.
    -- apply: thas_trace_all. naive_solver.
    -- apply: thas_trace_all. naive_solver.
       Unshelve. done. done.
Qed.

Lemma mod_product_nil_l {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ1 σ2 Pσ κs:
  σ1 ~{ m1, κs }~>ₜ Pσ → κs ⊆ tnil →
  (σ1, σ2) ~{ mod_product m1 m2, tnil }~>ₜ (λ σ', Pσ σ'.1 ∧ σ2 = σ'.2).
Proof.
  elim.
  - move => ??????. constructor; [|done]. naive_solver.
  - move => ??? κ ????? Hs1 Hs2.
    pose proof (transitivity Hs1 Hs2) as Hs.
    destruct κ; [inversion Hs|]; simplify_eq/=.
    apply: TTraceStep; [ by apply: ProductStepL | | simpl;done].
    move => [??] /=. naive_solver.
  - move => ??????? Hs1 Hs2.
    pose proof (transitivity Hs1 Hs2) as [??]%subtrace_all_nil_inv. naive_solver.
Qed.

Lemma mod_product_nil_r {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ1 σ2 Pσ κs:
  σ2 ~{ m2, κs }~>ₜ Pσ → κs ⊆ tnil →
  (σ1, σ2) ~{ mod_product m1 m2, tnil }~>ₜ (λ σ', Pσ σ'.2 ∧ σ1 = σ'.1).
Proof.
  elim.
  - move => ??????. constructor; [|done]. naive_solver.
  - move => ??? κ ????? Hs1 Hs2.
    pose proof (transitivity Hs1 Hs2) as Hs.
    destruct κ; [inversion Hs|]; simplify_eq/=.
    apply: TTraceStep; [ by apply: ProductStepR | | simpl;done].
    move => [??] /=. naive_solver.
  - move => ??????? Hs1 Hs2.
    pose proof (transitivity Hs1 Hs2) as [??]%subtrace_all_nil_inv. naive_solver.
Qed.

Lemma tmods_to_mod_product {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ κs κs1 κs2:
  mod_product_rel κs κs1 κs2 →
  σ.1 ~{ m1, κs1 }~>ₜ (λ _, True) → σ.2 ~{ m2, κs2 }~>ₜ (λ _, True) →
  σ ~{ mod_product m1 m2, κs }~>ₜ (λ _, True).
Proof.
  move => Hrel.
  elim: Hrel σ.
  - move => ?????. by constructor.
  - move => ????? /= IH [??] /thas_trace_ex_inv ??.
    apply: (thas_trace_trans tnil). { by apply: mod_product_nil_l. }
    move => [??] /= [[??]?]. naive_solver.
  - move => ????? IH [??] ? /thas_trace_ex_inv ?.
    apply: (thas_trace_trans tnil). { by apply: mod_product_nil_r. }
    move => [??] /= [[??]?]. naive_solver.
  - move => ?????? IH ? /thas_trace_all_inv ??. apply: IH; [|done]. naive_solver.
  - move => ?????? IH ?? /thas_trace_all_inv ?. apply: IH; [done|]. naive_solver.
  - move => ?????? IH ????.
    apply: thas_trace_mono; [|done| done].
    apply: thas_trace_all => ?. naive_solver.
  - move => ?????? IH ? [??]/= /(thas_trace_cons_inv _ _) ??.
    apply: thas_trace_mono; [|done| done].
    apply: (thas_trace_trans tnil). { by apply: mod_product_nil_l. }
    move => /= [??] /= [[?[??]]?]. subst.
    apply: TTraceStep; [ by apply: ProductStepL |  | simpl;done].
    move => [??] /= [??]. subst. naive_solver.
  - move => ?????? IH ? [??]/=? /(thas_trace_cons_inv _ _)?.
    apply: thas_trace_mono; [|done| done].
    apply: (thas_trace_trans tnil). { by apply: mod_product_nil_r. }
    move => /= [??] /= [[?[??]]?]. subst.
    apply: TTraceStep; [ by apply: ProductStepR |  | simpl;done].
    move => [??] /= [??]. subst. naive_solver.
  - move => ??????? IH ? [??]/= /(thas_trace_cons_inv _ _)? /(thas_trace_cons_inv _ _)?.
    apply: thas_trace_mono; [|done| done].
    apply: (thas_trace_trans tnil). { by apply: mod_product_nil_l. }
    move => /= [??] /= [[?[??]]?]. subst.
    apply: (thas_trace_trans tnil). { by apply: mod_product_nil_r. }
    move => /= [??] /= [[?[??]]?]. subst.
    apply: TTraceStep; [ by apply: ProductStepBoth |  | simpl;done].
    move => [??] /= [??]. subst. naive_solver.
Qed.

Lemma mod_product_trefines {EV1 EV2} (m1 m1' : module EV1) (m2 m2' : module EV2) σ1 σ1' σ2 σ2':
  trefines (MS m1 σ1) (MS m1' σ1') →
  trefines (MS m2 σ2) (MS m2' σ2') →
  trefines (MS (mod_product m1 m2) (σ1, σ2)) (MS (mod_product m1' m2') (σ1', σ2')).
Proof.
  move => [/=Hr1] [/=Hr2]. constructor => κs /= /tmod_product_to_mods[κs1 [κs2 [/Hr1 ? /Hr2 ?]]].
  by apply: tmods_to_mod_product.
Qed.


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

Lemma forall_to_ex1 A B (P1 : A → Prop)  P2 (Q : B → Prop):
 (∃ n : A, P1 n ∧ (∀ y, P2 n y → Q y)) -> (∀ y, (∀ n : A, P1 n → P2 n y) → Q y).
Proof. naive_solver. Qed.

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

(*
TODO: next steps:
- Add sequential product
- Add stateful filter
- Add product that only executes one side and non-determinisitically switches between the two (with an explicit event)
  - This might be more general than the current product as one might be able to get the current one by hiding the switching events?!
    - For (Some _, Some _) events one might need the stateful filter
*)
