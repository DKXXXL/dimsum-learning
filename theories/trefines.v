Require Export refframe.module.

(** [trefines] is a weaker notion of refinement that does not allow commuting choices and externally visible events*)

(** * tree traces *)
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
Global Instance subtrace_rewrite {EV} : RewriteRelation (@subtrace EV) := {}.

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

Global Instance tapp_proper {EV} :
  Proper ((⊆) ==> (⊆) ==> (⊆)) (@tapp EV).
Proof. move => ??????. by apply tapp_mono. Qed.
Global Instance tapp_proper_flip {EV} :
  Proper (flip (⊆) ==> flip (⊆) ==> (flip (⊆))) (@tapp EV).
Proof. move => ??????. by apply tapp_mono. Qed.

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


(** * trefines *)

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

Global Instance thas_trace_proper_flip {EV} (m : module EV) :
  Proper ((=) ==> (flip (⊆)) ==> (=) ==> flip impl) (thas_trace m).
Proof. move => ?? -> ?? Hsub ?? -> /=. by rewrite Hsub. Qed.

Lemma thas_trace_mono {EV} {m : module EV} κs' κs (Pσ2' Pσ2 : _ → Prop)  σ1 :
  σ1 ~{ m, κs' }~>ₜ Pσ2' →
  κs' ⊆ κs →
  (∀ σ, Pσ2' σ → Pσ2 σ) →
  σ1 ~{ m, κs }~>ₜ Pσ2.
Proof. move => ???. by apply: thas_trace_proper. Qed.

Lemma thas_trace_mono' {EV} {m : module EV} κs' κs (Pσ2 : _ → Prop)  σ1 :
  σ1 ~{ m, κs' }~>ₜ Pσ2 →
  κs' ⊆ κs →
  σ1 ~{ m, κs }~>ₜ Pσ2.
Proof. by move => ? <-. Qed.

(* thas_trace_inv gives an induction hypothesis for tall. *)
(* TODO: How useful is this? It cannot be used to replace the
inductions in this file as it does not allow changing the state. *)
Lemma thas_trace_inv {EV} (m : module EV) σ (Pσ : _ → Prop) (P : _ → Prop):
  (Pσ σ → P tnil) →
  (∀ κ κs' Pσ2 Pσ3,
      m.(m_step) σ κ Pσ2 →
      (∀ σ2, Pσ2 σ2 → σ2 ~{ m, κs' }~>ₜ Pσ3) →
      P (tapp (option_trace κ) κs')) →
  (∀ T f, (∀ x, P (f x)) → P (tall T f)) →
  (∀ κs κs', P κs' → κs' ⊆ κs → P κs) →
  ∀ κs, σ ~{ m, κs }~>ₜ Pσ → P κs.
Proof.
  move => HEnd HStep Hall Hsub κs Ht.
  elim: Ht HEnd HStep Hall Hsub; clear.
  - naive_solver.
  - naive_solver.
  - move => T f σ κs Pσ ? IH ? HEnd HStep Hall Hsub.
    apply: (Hsub); [|done]. apply: (Hall) => ?.
    apply: IH; naive_solver.
Qed.
Ltac thas_trace_inv H :=
  lazymatch type of H with
  | _ ~{ _, ?κs }~>ₜ _ => pattern κs
  end;
  apply: (thas_trace_inv _ _ _ _ _ _ _ _ _ H); [ | |
   try by [move => *; apply subtrace_all_r; naive_solver] |
   try by [move => ??? <-]
 ].

Lemma thas_trace_trans {EV} κs1 κs2 (m : module EV) σ1 Pσ2 Pσ3 :
  σ1 ~{ m, κs1 }~>ₜ Pσ2 →
  (∀ σ2, Pσ2 σ2 → σ2 ~{ m, κs2 }~>ₜ Pσ3) →
  σ1 ~{ m, tapp κs1 κs2 }~>ₜ Pσ3.
Proof.
  elim.
  - move => ???? <- /= ?. naive_solver.
  - move => ????????? <- ?. rewrite -assoc_L.
    apply: TTraceStep; [done| |done].
    naive_solver.
  - move => ??????? <- ?.
    eapply TTraceAll; [|simpl; done].
    naive_solver.
Qed.

Lemma thas_trace_ex {EV T} x f (m : module EV) σ Pσ:
  σ ~{ m, f x }~>ₜ Pσ →
  σ ~{ m, tex T f }~>ₜ Pσ.
Proof. move => ?. apply: thas_trace_mono'; [done|]. by econstructor. Qed.

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
  - move => ??? κ ???? IH <- Ht.
    destruct κ; simplify_eq/=. 1: by inversion Ht.
    apply: TSTraceStep; [done| move => ??; by apply: IH | done].
  - move => ?????? IH <- Ht. inversion Ht; simplify_K. by apply: IH.
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
  - move => ???? Hnil κ κs'. rewrite -Hnil => ?. easy.
  - move => ??? κ' ???? IH Hs ??. rewrite -Hs => Ht.
    destruct κ'; simplify_eq/=.
    + inversion Ht; simplify_eq.
      constructor; [|done].
      eexists _. split; [ done |]. move => ??.
      apply: thas_trace_mono; [ naive_solver | | naive_solver].
      done.
    + apply: TTraceStep; [ done | | by constructor].
      move => ??. by apply: IH.
  - move => ?????? IH Hsub ??. rewrite -Hsub => /(subtrace_all_cons_inv _ _)[??].
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
