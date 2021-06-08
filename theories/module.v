Require Import refframe.base.
Require Import refframe.axioms.
Require Import stdpp.namespaces.
Require Import stdpp.strings.
Require Import stdpp.gmap.
Require Import stdpp.binders.
Require Import stdpp.propset.
Require Import stdpp.telescopes.

Definition FiniteP (A : Type) : Prop :=
  ∃ l : list A, ∀ x : A, x ∈ l.
Definition FinitePred {A} (P : A → Prop) : Prop :=
  FiniteP { x | P x }.

Lemma Finite_FiniteP (A : Type) `{!EqDecision A} `{!Finite A} :
  FiniteP A.
Proof. eexists (enum A) => ?. apply elem_of_enum. Qed.

Lemma FinitePred_eq {A} (x : A):
  FinitePred (eq x).
Proof. eexists [_] => -[??]. subst. by apply elem_of_list_singleton. Qed.

Lemma FinitePred_False A:
  FinitePred (λ _ : A, False).
Proof. eexists [] => -[??]. done. Qed.

Lemma FinitePred_prod {A B} (Pa : A → Prop) (Pb : B → Prop) :
  FinitePred Pa → FinitePred Pb →
  FinitePred (λ '(a, b), Pa a ∧ Pb b).
Proof.
  move => [la Hla] [lb Hlb].
  unshelve eexists (a ← la; b ← lb; mret (exist _ (`a, `b) _) ).
  { simpl. split; apply proj2_sig. }
  move => [[a b][Ha Hb]]/=.
  apply elem_of_list_bind. eexists (exist _ a Ha). split; [|done].
  apply elem_of_list_bind. eexists (exist _ b Hb). split; [|done].
  by apply elem_of_list_ret.
Qed.

Lemma max_finitep {A} (f : A → nat) :
  FiniteP A →
  ∃ n, ∀ a, f a ≤ n.
Proof.
  move => [l Hl]. eexists (max_list (f <$> l)) => a.
  apply max_list_elem_of_le. apply elem_of_list_fmap. naive_solver.
Qed.

Inductive trace (EV : Type) : Type :=
| tnil
| tcons (κ : EV) (κs : trace EV)
| tex (T : Type) (f : T → trace EV)
| tall (T : Type) (F : FiniteP T) (f : T → trace EV).
Arguments tnil {_}.
Arguments tcons {_}.
Arguments tex {_}.
Arguments tall {_}.

Fixpoint tapp {EV} (κs1 κs2 : trace EV) :=
  match κs1 with
  | tnil => κs2
  | tcons κ κs' => tcons κ (tapp κs' κs2)
  | tex T f => tex T (λ x, tapp (f x) κs2)
  | tall T F f => tall T F (λ x, tapp (f x) κs2)
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
| subtrace_all_r T f κs F:
    (∀ x, subtrace κs (f x)) →
    subtrace κs (tall T F f)
| subtrace_ex_r {T f} x κs:
    subtrace κs (f x) →
    subtrace κs (tex T f)
| subtrace_all_l {T f} x κs' F:
    subtrace (f x) κs' →
    subtrace (tall T F f) κs'
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
      * move => ???? Hs. inversion Hs; simplify_K.
        econstructor. naive_solver.
    + move => ???? IH ??. constructor. naive_solver.
    + move => ????? IH z Hs.
      elim: z Hs.
      * inversion 1; simplify_K. naive_solver.
      * move => ??? Hs. inversion Hs; simplify_K. naive_solver.
      * move => ??? Hs. inversion Hs; simplify_K.
        -- econstructor. naive_solver.
        -- naive_solver.
      * move => ???? Hs. inversion Hs; simplify_K.
        -- econstructor. naive_solver.
        -- naive_solver.
    + move => ?? v ?? IH z Hs.
      elim: z Hs.
      * inversion 1; simplify_K. naive_solver.
      * move => ??? Hs. inversion Hs; simplify_K. naive_solver.
      * move => ??? Hs. inversion Hs; simplify_K; [ naive_solver |].
        econstructor. naive_solver.
      * move => ???? Hs. inversion Hs; simplify_K; [ naive_solver |].
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

Lemma subtrace_all_nil_inv EV T f F:
  tall T F f ⊆ @tnil EV →
  ∃ x, f x ⊆ tnil.
Proof. inversion 1; simplify_K. naive_solver. Qed.

Lemma subtrace_all_cons_inv {EV} (κ : EV) κs T f F:
  tall T F f ⊆ tcons κ κs →
  ∃ x, f x ⊆ tcons κ κs.
Proof. inversion 1; simplify_K. naive_solver. Qed.

Global Instance tapp_assoc {EV} : Assoc (=) (@tapp EV).
Proof.
  move => x. elim: x => //=.
  - move => ?????. f_equal. naive_solver.
  - move => ?? IH ??. f_equal. apply functional_extensionality. naive_solver.
  - move => ??? IH ??. f_equal. apply functional_extensionality. naive_solver.
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
  - move => ??? IH /=. f_equal. apply functional_extensionality. naive_solver.
Qed.

Definition tub {EV} :=
  @tex EV Empty_set (λ x, match x with end).

Definition tnb {EV} :=
  @tall EV Empty_set (Finite_FiniteP _) (λ x, match x with end).

Lemma tub_sub {EV} (κs : trace EV):
  tub ⊆ κs.
Proof. by constructor. Qed.

Lemma tnb_sub {EV} (κs : trace EV):
  κs ⊆ tnb.
Proof. by constructor. Qed.

Lemma tex_unit EV (f : _ → trace EV):
  tex () f ≡ f tt.
Proof. split; econstructor; [case|]; done. Qed.

Record module (EV : Type) : Type := {
  m_state : Type;
  m_step : m_state → option EV → (m_state → Prop) → Prop;
  (* TODO: Do we really want this? This is necessary to use nat as step index in Iris. *)
  m_ang_finite σ κ Pσ: m_step σ κ Pσ → FinitePred Pσ
}.
Arguments m_state {_}.
Arguments m_step {_}.

(* TODO: for angelic version, list EV must become propset (list EV).
It must also be precise, i.e. TraceEnd must enforce T ≡ {[ [] ]}. For
TraceStep, one can probably use T ≡ (option_list κ ++.) <$> T' and add T' ≡ ({[ κs |
(∃ σ, Pσ σ ∧ κs ∈ fT σ)]}) inside the ∀ σ. Otherwise one could also
explicitly handle the UB on the outside (T' should be unconstrained if there is UB)
 The next steps use [fT σ] as
their set. This also requires the set of next states to be precise.
One can try if the version is sensible by proving for

  A
  /- 1 -- UB
 /
0
 \
  \- 2
  B

That
0 ~{ m, T }~> _, True
→ (∃ κs, B::κs ∈ T) → T ≡ {[ [B] ]}

But one also needs to require that the trace of the spec is a subset of the trace of the source. Not sure how to best handle UB. Maybe the subset must not be empty? One must be careful that one cannot commute UB with external events, i.e. representing UB as the empty set of traces does not seem to work (but it would be very elegant otherwise). Or do something like the following?

Set Printing Universes.
(* Set Universe Polymorphism. *)
Inductive trace (EV : Type) : Type :=
| TEnd : trace EV
| TCons (κ : EV) (κs : trace EV) : trace EV
| TChoice (T : Type): (T → Prop) → (T → trace EV) → trace EV
.

Fixpoint trace_sub {EV} (κs1 κs2 : trace EV) : Prop :=
  match κs1, κs2 with
  | _, TChoice _ T P κs2' => ∀ x : T, P x → trace_sub κs1 (κs2' x)
  | TChoice _ T P κs1', _ => ∃ x : T, P x ∧ trace_sub (κs1' x) κs2
  | TCons _ κ1 κs1', TCons _ κ2 κs2' => κ1 = κ2 ∧ trace_sub κs1' κs2'
  | TEnd _, TEnd _ => True
  | TEnd _, TCons _ _ _ => False
  | TCons _ _ _, TEnd _ => False
  end.

The above seems tricky to work with and may not allow commuting angelic non-det in both directions.

Other idea: Do what was said in the first version above, but ensure that
the arbitrary trace from UB is non-empty. This ensures that the trace set never becomes empty
and that hopefully solves the UB commuting problem.

    m.(m_step) σ1 κ Pσ2 →
    (∀ σ2, Pσ2 σ2 → has_trace m σ2 Pκs2 Pσ3) →
    Pκs ≡ (option_list (Vis <$> κ) ++.) <$> Pκs1 →
    ((∃ σ, Pσ2 σ ∧ Pκs1 ≡ (∃ σ, Pσ2 σ ∧ κs ∈ Pκs2 σ))
     ∨ (¬ (∃ σ, Pσ2 σ) ∧ ∃ κs, κs ∈ Pκs1)
    has_trace m σ1 Pκs Pσ3

Refinement would be defined as:
∀ κs, mimpl.(ms_state) ~{ mimpl, Pκi }~> (λ _, True) → ∃ Pκs, Pκs ⊆ Pκi ∧ mspec.(ms_state) ~{ mspec, Pκs }~> (λ _, True)

Safety would be defined as follows and should be transferred by refinement:
Definition safe {EV} (m : mod_state EV) (P : list (event EV) → Prop) :=
  ∀ Pκs, m.(ms_state) ~{ m, Pκs }~> (λ _, True) → ∃ κs, κs ∈ Pκs ∧ P κs.

Or even Pκs should not be precise, i.e.

    m.(m_step) σ1 κ Pσ2 →
    (∀ σ2, Pσ2 σ2 → has_trace m σ2 (λ κs, Pκs (option_list (Vis <$> κ) ++ κs)) Pσ3) →
    Pκs κs →
    has_trace m σ1 Pκs Pσ3

This means that Refinement can be defined as
∀ Pκs, mimpl.(ms_state) ~{ mimpl, Pκs }~> (λ _, True) → mspec.(ms_state) ~{ mspec, Pκs }~> (λ _, True)

And safety as:
Definition safe {EV} (m : mod_state EV) (P : (list (event EV) → Prop) → Prop) :=
  ∀ Pκs, m.(ms_state) ~{ m, Pκs }~> (λ _, True) → P Pκs.

The key observation is that this definition of has_trace already builds in that a target
can have more angelic behavior as the spec and one can only prove safe for properties that
are closed under expansion to bigger sets. E.g. properties of the form P Pκs := ∃ κ, Pκs ∧ (...) work,
but something with P Pκs := (∀ κs, Pκs κs → ...) does not work. This is feature, not a bug
since such properties are not preserved by refinement anyway.
*)

(* Defining traces using (list (event EV) → Prop) has one big problem:
With this definition angelic choice commutes with visible events and
this causes a few problems. One problem for [mod_filter] is explained
below, but there is a worse problem: horizontal compositionality does
not hold! In short, the problem is that when linking two modules, one
can depend on the angelic choices of the other (this is an important
feature), but refinement can move the angelic choices such that the
spec cannot emulate the same dependency that the implementation had.

Consider the following programs:

MI1:
                S           A
    /- 2 true  --- 3 true  ---
1 -a
    \- 2 false --- 3 false ---
                S           B

MS1:                        A
         S      /- 4 true  ---
1 --- 2 --- 3 -a
                \- 4 false ---
                            B

M2:
                S           A
    /- 2 true  --- 3 true  ---
1 -d
    \- 2 false --- 3 false ---
                S           B

We have MI1 ⊑ MS1, but link MI1 M2 ⊑ link MS1 M2 does not hold!
In particular, link MI1 M2 has the trace
 [(S, S); (A, A)] ∨ [(S, S); (B, B)]
(because the demonic choice in M2 can use the value of the angelic choice of MI1)
but link MS1 M2 does not have this trace since there one has to pick the
value of the demonic choice in M2 before one sees the angelic choice.

 *)

Inductive trace_steps : Type :=
| ts0 | tsS (n : trace_steps) | tschoice T (f : T → trace_steps).

Inductive ts_resolve : trace_steps → trace_steps → Prop :=
| ts_resolve_0 :
    ts_resolve ts0 ts0
| ts_resolve_S n1 n2:
    ts_resolve n1 n2 →
    ts_resolve (tsS n1) (tsS n2)
| ts_resolve_choice_l T f n2 :
    (∀ x, ts_resolve (f x) n2) →
    ts_resolve (tschoice T f) n2
| ts_resolve_choice_r {T} x f n2 :
    ts_resolve n2 (f x) →
    ts_resolve n2 (tschoice T f).

Global Instance ts_equiv : Equiv (trace_steps) := λ x y, ts_resolve x y ∧ ts_resolve y x.

Global Instance ts_resolve_preorder : PreOrder ts_resolve.
Proof.
  constructor.
  - move => n. elim: n.
    + constructor.
    + move => *. by constructor.
    + move => *. constructor => ?. econstructor. naive_solver.
  - move => x y z Hs. elim: Hs z.
    + done.
    + move => ??? IH z Hs.
      elim: z Hs.
      * inversion 1.
      * move => ?? Hs. inversion Hs; simplify_eq. constructor. naive_solver.
      * move => ??? Hs. inversion Hs; simplify_K.
        econstructor. naive_solver.
    + move => ???? IH ??. constructor. naive_solver.
    + move => ?? v ?? IH z Hs.
      elim: z Hs.
      * inversion 1; simplify_K. naive_solver.
      * move => ?? Hs. inversion Hs; simplify_K. naive_solver.
      * move => ??? Hs. inversion Hs; simplify_K; [ naive_solver |].
        econstructor. naive_solver.
Qed.
Global Instance equiv_ts_equiv : Equivalence (≡@{trace_steps}).
Proof.
  constructor.
  - done.
  - move => ?? [??]. done.
  - move => ??? [??] [??]. by split; etrans.
Qed.


Definition VisNoUb {EV} (m : module EV) (κ : option EV) (Pσ : (m.(m_state) → Prop)) :=
  is_Some κ → ∃ σ, Pσ σ.

Inductive has_trace {EV} (m : module EV) : m.(m_state) → trace EV → (m.(m_state) → Prop) → Prop :=
| TraceEnd σ (Pσ : _ → Prop) κs:
    Pσ σ →
    tnil ⊆ κs →
    has_trace m σ κs Pσ
| TraceStep σ1 Pσ2 Pσ3 κ κs κs':
    m.(m_step) σ1 κ Pσ2 →
    (∀ σ2, Pσ2 σ2 → has_trace m σ2 κs' Pσ3) →
    tapp (option_trace κ) κs' ⊆ κs →
    VisNoUb m κ Pσ2 →
    (* The following is not useful. One needs to know if any of the traces can lead to UB.
    LEM (∃ σ, Pσ2 σ) →
     *)
    has_trace m σ1 κs Pσ3
| TraceAll T f σ κs Pσ F:
    (∀ x, has_trace m σ (f x) Pσ) →
    tall T F f ⊆ κs →
    has_trace m σ κs Pσ
.
Notation " σ '~{' m , Pκs '}~>' P " := (has_trace m σ Pκs P) (at level 40).

Inductive nhas_trace {EV} (m : module EV) : nat → m.(m_state) → trace EV → (m.(m_state) → Prop) → Prop :=
| NTraceEnd σ (Pσ : _ → Prop) κs n:
    Pσ σ →
    tnil ⊆ κs →
    nhas_trace m n σ κs Pσ
| NTraceStep σ1 Pσ2 Pσ3 κ κs κs' n:
    m.(m_step) σ1 κ Pσ2 →
    (∀ σ2, Pσ2 σ2 → nhas_trace m n σ2 κs' Pσ3) →
    tapp (option_trace κ) κs' ⊆ κs →
    VisNoUb m κ Pσ2 →
    (* The following is not useful. One needs to know if any of the traces can lead to UB.
    LEM (∃ σ, Pσ2 σ) →
     *)
    nhas_trace m (S n) σ1 κs Pσ3
| NTraceAll T f σ κs Pσ n fn F:
    (∀ x, nhas_trace m (fn x) σ (f x) Pσ) →
    tall T F f ⊆ κs →
    (∀ x, fn x ≤ n) →
    nhas_trace m n σ κs Pσ
.
Notation " σ '~{' m , n , Pκs '}~>' P " := (nhas_trace m n σ Pκs P) (at level 40).


Global Instance has_trace_proper {EV} (m : module EV) :
  Proper ((=) ==> (⊆) ==> (pointwise_relation m.(m_state) impl) ==> impl) (has_trace m).
Proof.
  move => ?? -> κs1 κs2 Hκs Pσ1 Pσ2 HP Ht.
  elim: Ht κs2 Pσ2 Hκs HP.
  - move => ???????? HP. apply: TraceEnd. by apply: HP. by etrans.
  - move => ???????? IH Hnext ??? Hκs HP.
    apply: TraceStep => //.
    + move => ??. by apply: IH.
    + by etrans.
  - move => *. eapply TraceAll. naive_solver. by etrans.
Qed.

Global Instance nhas_trace_proper {EV} (m : module EV) :
  Proper ((le) ==> (=) ==> (⊆) ==> (pointwise_relation m.(m_state) impl) ==> impl) (nhas_trace m).
Proof.
  move => n1 n2 Hn ?? -> κs1 κs2 Hκs Pσ1 Pσ2 HP Ht.
  elim: Ht n2 κs2 Pσ2 Hn Hκs HP.
  - move => ??????????? HP. apply: NTraceEnd. by apply: HP. by etrans.
  - move => ????????? IH ?? n2 ??? Hκs HP. destruct n2; [lia|].
    apply: NTraceStep => //.
    + move => ??. apply: IH => //. lia.
    + by etrans.
  - move => *.
    eapply NTraceAll.
    + naive_solver.
    + by etrans.
    + move => ?. etrans; [|done]. naive_solver.
Qed.

Lemma has_trace_mono {EV} {m : module EV} κs' κs (Pσ2' Pσ2 : _ → Prop)  σ1 :
  σ1 ~{ m, κs' }~> Pσ2' →
  κs' ⊆ κs →
  (∀ σ, Pσ2' σ → Pσ2 σ) →
  σ1 ~{ m, κs }~> Pσ2.
Proof. move => ???. by apply: has_trace_proper. Qed.

Lemma nhas_trace_mono {EV} n1 n2 {m : module EV} κs' κs (Pσ2' Pσ2 : _ → Prop)  σ1 :
  σ1 ~{ m, n1, κs' }~> Pσ2' →
  n1 ≤ n2 →
  κs' ⊆ κs →
  (∀ σ, Pσ2' σ → Pσ2 σ) →
  σ1 ~{ m, n2, κs }~> Pσ2.
Proof. move => ????. by apply: nhas_trace_proper. Qed.

Lemma has_trace_to_n {EV} (m : module EV) σ Pσ κs:
  σ ~{ m, κs }~> Pσ ↔ ∃ n, σ ~{ m, n, κs }~> Pσ.
Proof.
  split.
  - elim.
    + move => *. eexists 0. by constructor.
    + move => ???????? IH ??.
      have [f Hf]:= CHOICE IH.
      have [|n Hn]:= max_finitep f. { by apply: m_ang_finite. }
      eexists (S n).
      apply: NTraceStep => // ? HP.
      apply: nhas_trace_mono; naive_solver.
    + move => ??????? IH ?.
      have [f Hf]:= AxCHOICE _ _ _ IH.
      have [//|n Hn]:= max_finitep f.
      eexists n. by eapply NTraceAll.
  - move => [n Hn].
    elim: Hn.
    + move => *. by constructor.
    + move => *. apply: TraceStep => //.
    + move => *. eapply TraceAll => //.
      Unshelve. done.
Qed.

Lemma has_trace_trans {EV} κs1 κs2 (m : module EV) σ1 Pσ2 Pσ3 :
  σ1 ~{ m, κs1 }~> Pσ2 →
  (∀ σ2, Pσ2 σ2 → σ2 ~{ m, κs2 }~> Pσ3) →
  σ1 ~{ m, tapp κs1 κs2 }~> Pσ3.
Proof.
  elim.
  - move => ??????.
    apply: has_trace_mono; [ naive_solver | |done].
    etrans; [| by apply: tapp_mono]. done.
  - move => ????????????.
    apply: TraceStep; [done| | |done].
    + naive_solver.
    + etrans; [| by apply: tapp_mono]. by rewrite assoc.
  - move => *.
    eapply TraceAll. 2: {
      etrans; [| by apply: tapp_mono].
      simpl. done.
    }
    naive_solver.
Qed.

Lemma has_trace_ex {EV T} x f (m : module EV) σ Pσ:
  σ ~{ m, f x }~> Pσ →
  σ ~{ m, tex T f }~> Pσ.
Proof. move => ?. apply: has_trace_mono; [done| |done]. by econstructor. Qed.

Lemma has_trace_all {EV T} f (m : module EV) σ Pσ F:
  (∀ x, σ ~{ m, f x }~> Pσ) →
  σ ~{ m, tall T F f }~> Pσ.
Proof. move => ?. by eapply TraceAll. Qed.

Lemma has_trace_cons_inv' {EV} κs κs' κ (m : module EV) σ1 Pσ3:
  σ1 ~{ m, κs }~> Pσ3 → κs ⊆ tcons κ κs' →
  σ1 ~{ m, tnil }~> (λ σ2, ∃ Pσ2', m.(m_step) σ2 (Some κ) Pσ2' ∧ VisNoUb m (Some κ) Pσ2' ∧ ∀ σ2', Pσ2' σ2' → σ2' ~{ m, κs' }~> Pσ3).
Proof.
  move => Hs.
  elim: Hs κ κs'.
  - move => ?????  κ κs' ?.
    have : tnil ⊆ tcons κ κs' by etrans.
    easy.
  - move => ??? κ' ???? IH Hs ??? Hsub.
    destruct κ'; simplify_eq/=.
    + pose proof (transitivity Hs Hsub) as Ht.
      inversion Ht; simplify_eq.
      constructor; [|done].
      eexists _. split; [ done |]. split; [ done |]. move => ??.
      apply: has_trace_mono; [ naive_solver | | naive_solver].
      done.
    + apply: TraceStep; [ done | | by constructor| done].
      move => ??. apply: IH; [done|].
      etrans. done. done.
  - move => ??????? IH Hsub ?? Hsub2.
    pose proof (transitivity Hsub Hsub2) as [??]%subtrace_all_cons_inv.
    naive_solver.
Qed.

Lemma has_trace_cons_inv {EV} κs' κ (m : module EV) σ1 Pσ3:
  σ1 ~{ m, tcons κ κs' }~> Pσ3 →
  σ1 ~{ m, tnil }~> (λ σ2, ∃ Pσ2', m.(m_step) σ2 (Some κ) Pσ2' ∧ VisNoUb m (Some κ) Pσ2' ∧ ∀ σ2', Pσ2' σ2' → σ2' ~{ m, κs' }~> Pσ3).
Proof. move => ?. by apply: has_trace_cons_inv'. Qed.

Lemma has_trace_ex_inv' {EV} κs T f (m : module EV) σ1 Pσ3:
  σ1 ~{ m, κs }~> Pσ3 → κs ⊆ tex T f →
  σ1 ~{ m, tnil }~> (λ σ2, ∃ x, σ2 ~{ m, f x }~> Pσ3).
Proof.
  move => Hs.
  elim: Hs T f.
  - move => ????? T f ?.
    have : tnil ⊆ tex T f by etrans.
    move => /subtrace_nil_ex_inv[??].
    constructor; [|done]. eexists _. by constructor.
  - move => ??? κ ???? IH Hs ??? Hsub.
    destruct κ; simplify_eq/=.
    + pose proof (transitivity Hs Hsub) as Ht.
      move: Ht => /(subtrace_cons_ex_inv _ _)[??].
      constructor; [|done]. eexists _.
      apply: TraceStep; [done|done|done|done].
    + apply: TraceStep; [ done | | by constructor| done].
      move => ??. apply: IH; [done|].
      by etrans.
  - move => T1 f1 ????? IH Hsub1 T2 f2 Hsub2.
    pose proof (transitivity Hsub1 Hsub2) as Ht.
    inversion Ht; simplify_K. 2: naive_solver.
    constructor; [|done]. eexists _. apply: has_trace_mono; [|done|done].
    by apply: has_trace_all.
Qed.

Lemma has_trace_ex_inv {EV} T f (m : module EV) σ1 Pσ3:
  σ1 ~{ m, tex T f }~> Pσ3 →
  σ1 ~{ m, tnil }~> (λ σ2, ∃ x, σ2 ~{ m, f x }~> Pσ3).
Proof. move => ?. by apply: has_trace_ex_inv'. Qed.

Lemma has_trace_all_inv' {EV T} κs f (m : module EV) σ1 Pσ3 F:
  σ1 ~{ m, κs }~> Pσ3 → κs ⊆ tall T F f →
  ∀ x, σ1 ~{ m, f x }~> Pσ3.
Proof.
  move => ???. apply: has_trace_mono; [done| |done].
  etrans; [done|]. by econstructor.
Qed.

Lemma has_trace_all_inv {EV} T f (m : module EV) σ1 Pσ3 F:
  σ1 ~{ m, tall T F f }~> Pσ3 →
  ∀ x, σ1 ~{ m, f x }~> Pσ3.
Proof. move => ??. by apply: has_trace_all_inv'. Qed.

Lemma has_trace_inv {EV} κs (m : module EV) σ1 Pσ2:
  σ1 ~{ m, κs }~> Pσ2 →
  σ1 ~{ m, κs }~> (λ _, False) ∨ ∃ σ, Pσ2 σ.
Proof.
  elim; clear.
  - naive_solver.
  - move => σ1 Pσ2 Pσ3 κ κs κs' ? ? IH ??.
    have [?|HF]:= EM (∀ σ2 : m_state m, Pσ2 σ2 → σ2 ~{ m, κs' }~> (λ _ : m_state m, False)).
    + left. apply: TraceStep; [done|done |done|done].
    + have [?|?]:= EM (∃ σ2, Pσ2 σ2 ∧ ¬ σ2 ~{ m, κs' }~> (λ _ : m_state m, False)).
      naive_solver.
      exfalso. apply: HF => σ3?.
      have [//|?]:= EM (σ3 ~{ m, κs' }~> (λ _ : m_state m, False)). naive_solver.
  - move => T f σ κs Pσ F _ IH Hsub.
    have [[x ?]|?]:= EM (∃ x : T, ¬ σ ~{ m, f x }~> (λ _, False)). naive_solver.
    left. eapply TraceAll; [|done] => x.
    have [|]:= EM (σ ~{ m, f x }~> (λ _ : m_state m, False)); naive_solver.
Qed.


(*
Lemma has_trace_trans {EV} κs1 κs2 (m : module EV) σ1 Pσ2 Pσ3 :
  σ1 ~{ m, κs1 }~> Pσ2 →
  (∀ σ2, Pσ2 σ2 → σ2 ~{ m, κs2 }~> Pσ3) →
  σ1 ~{ m, κs1 ++ κs2 }~> Pσ3.
Proof.
  elim.
  - naive_solver.
  - move => ?????????. rewrite -app_assoc. econstructor; eauto.
  - move => ?????. by apply: TraceUb.
Qed.

Lemma has_trace_trans' {EV} κs1 κs2 (m : module EV) σ1 Pσ3 :
  σ1 ~{ m, κs1 }~> (λ σ2, σ2 ~{ m, κs2 }~> Pσ3) →
  σ1 ~{ m, κs1 ++ κs2 }~> Pσ3.
Proof. move => ?. by apply: has_trace_trans. Qed.

Lemma has_trace_add_empty {EV} κs1 (m : module EV) σ1 σ2 :
  σ1 ~{ m, κs1 ++ [] }~> σ2 →
  σ1 ~{ m, κs1 }~> σ2.
Proof. by rewrite -{2}[κs1](right_id_L [] (++)). Qed.

Lemma has_trace_inv {EV} κs (m : module EV) σ1 Pσ2:
  σ1 ~{ m, κs }~> Pσ2 →
  ∃ σ2, σ1 ~{ m, κs }~> (σ2 =.) ∧ (m.(m_is_ub) σ2 ∨ Pσ2 σ2).
Proof.
  elim.
  - move => ???. eexists _. split; [by apply: TraceEnd| by right].
  - move => ??????? [?[? Hor]].
    eexists _. split; [ by apply: TraceStep | done].
  - move => ????. eexists _. split; [by apply: TraceUb| by left].
Qed.

Lemma has_trace_ub_inv {EV} κs (m : module EV) σ1 Pσ2:
  σ1 ~{m, Ub :: κs }~> Pσ2 →
  σ1 ~{m, [] }~> (λ _, False).
Proof.
  move Hκ: (Ub :: κs) => κ Hκs.
  elim: Hκs Hκ => //.
  - move => ??? [] //= ??? IH ?. apply: TraceStepNone; [done|].
    naive_solver.
  - move => ?????. by apply: TraceUb.
Qed.

Lemma has_trace_cons_inv {EV} κs κ (m : module EV) σ1 Pσ3:
  σ1 ~{ m, Vis κ :: κs }~> Pσ3 →
  σ1 ~{ m, [] }~> (λ σ2, ∃ σ2', m.(m_step) σ2 (Some κ) σ2' ∧ σ2' ~{ m, κs }~> Pσ3).
Proof.
  move Hs: (Vis κ :: κs) => s Hκs.
  elim: Hκs Hs => //.
  - move => ??? [] //=.
    + move => ???? IH [] ??. subst. apply: TraceEnd. eexists _. split; [done|]. naive_solver.
    + move => ??? IH ?. apply: TraceStepNone; [done|]. naive_solver.
  - move => ?????. by apply: TraceUb.
Qed.

Lemma has_trace_app_inv {EV} κs1 κs2 (m : module EV) σ1 Pσ3:
  σ1 ~{ m, κs1 ++ κs2 }~> Pσ3 →
  σ1 ~{ m, κs1 }~> (λ σ2, σ2 ~{ m, κs2 }~> Pσ3).
Proof.
  elim: κs1 σ1 => /=. { move => ??. by apply: TraceEnd. }
  move => [|?] ? IH ?.
  - move => /has_trace_ub_inv?. by apply: (has_trace_trans []).
  - move => /(has_trace_cons_inv _ _)?.
    apply: (has_trace_trans []); [done|] => ? [?[??]].
    apply: TraceStepSome; [done|]. naive_solver.
Qed.

Lemma has_trace_ub_app_inv {EV} κs (m : module EV) σ1 Pσ2:
  σ1 ~{ m, κs ++ [Ub] }~> Pσ2 →
  σ1 ~{ m, κs }~> (λ _, False).
Proof.
  move => /has_trace_app_inv ?.
  apply: has_trace_add_empty.
  apply: has_trace_trans; [done|] => ?.
  apply: has_trace_ub_inv.
Qed.
*)

Record mod_state EV := MS {
  ms_module : module EV;
  ms_state : ms_module.(m_state);
}.
Arguments MS {_}.
Arguments ms_module {_}.
Arguments ms_state {_}.
Coercion ms_module : mod_state >-> module.

Record refines {EV} (mimpl mspec : mod_state EV) : Prop := {
  ref_subset:
    ∀ κs, mimpl.(ms_state) ~{ mimpl, κs }~> (λ _, True) →
          mspec.(ms_state) ~{ mspec, κs }~> (λ _, True)
}.

Global Instance sqsubseteq_refines EV : SqSubsetEq (mod_state EV) := refines.

Definition refines_equiv {EV} (m1 m2 : mod_state EV) : Prop := m1 ⊑ m2 ∧ m2 ⊑ m1.

Definition safe {EV} (m : mod_state EV) (P : trace EV → Prop) :=
  ∀ κs, m.(ms_state) ~{ m, κs }~> (λ _, True) → P κs.

Lemma refines_preserves_safe EV (mspec mimpl : mod_state EV) P:
  safe mspec P →
  mimpl ⊑ mspec →
  safe mimpl P.
Proof. move => Hs [Hr] κs Hκs. apply: Hs. by apply: Hr. Qed.

Global Instance refines_preorder EV : PreOrder (@refines EV).
Proof.
  constructor.
  - constructor => // κ Hi; naive_solver.
  - move => ??? [Hr1] [Hr2]. constructor => /=. naive_solver.
Qed.

(*** Demonic module **)
Inductive event (EV : Type) : Type :=
| Ub | Vis (e : EV).
Arguments Ub {_}.
Arguments Vis {_}.

Record dem_module (EV : Type) : Type := {
  dem_state : Type;
  dem_step : dem_state → option EV → dem_state → Prop;
  dem_is_ub : dem_state → Prop;
}.
Arguments dem_state {_}.
Arguments dem_step {_}.
Arguments dem_is_ub {_}.

Inductive dem_has_trace {EV} (m : dem_module EV) : m.(dem_state) → list (event EV) → (m.(dem_state) → Prop) → Prop :=
| DTraceEnd σ (Pσ : _ → Prop):
    Pσ σ →
    dem_has_trace m σ [] Pσ
| DTraceStep σ1 σ2 Pσ3 κ κs:
    m.(dem_step) σ1 κ σ2 →
    dem_has_trace m σ2 κs Pσ3 →
    dem_has_trace m σ1 (option_list (Vis <$> κ) ++ κs) Pσ3
| DTraceUb σ1 κs Pσ2:
    m.(dem_is_ub) σ1 →
    dem_has_trace m σ1 κs Pσ2
.
Notation " σ '~{' m , κ '}~>ₘ' P " := (dem_has_trace m σ κ P) (at level 40).

Global Instance dem_has_trace_proper {EV} (m : dem_module EV) :
  Proper ((=) ==> (=) ==> (pointwise_relation m.(dem_state) impl) ==> impl) (dem_has_trace m).
Proof.
  move => ?? -> ?? -> Pσ1 Pσ2 HP Ht.
  elim: Ht Pσ2 HP.
  - move => ???? HP. apply: DTraceEnd. by apply: HP.
  - move => ??????????. apply: DTraceStep; naive_solver.
  - move => ??????. by apply: DTraceUb.
Qed.

Lemma dem_has_trace_mono {EV} (m : dem_module EV) σ1 (Pσ2 Pσ2' : _ → Prop) κs:
  σ1 ~{ m, κs }~>ₘ Pσ2' →
  (∀ σ, Pσ2' σ → Pσ2 σ) →
  σ1 ~{ m, κs }~>ₘ Pσ2.
Proof. move => ??. by apply: dem_has_trace_proper. Qed.

Lemma DTraceEnd' {EV} (m : dem_module EV) σ :
  σ ~{ m, [] }~>ₘ (σ =.).
Proof. by apply: DTraceEnd. Qed.

Lemma DTraceStepNone {EV} κs (m : dem_module EV) σ2 σ1 Pσ3 :
  m.(dem_step) σ1 None σ2 →
  σ2 ~{ m, κs }~>ₘ Pσ3 →
  σ1 ~{ m, κs }~>ₘ Pσ3.
Proof. move => ??. by apply: (DTraceStep _ _ _ _ None). Qed.

Lemma DTraceStepSome {EV} κs (m : dem_module EV) σ2 σ1 Pσ3 κ :
  m.(dem_step) σ1 (Some κ) σ2 →
  σ2 ~{ m, κs }~>ₘ Pσ3 →
  σ1 ~{ m, Vis κ :: κs }~>ₘ Pσ3.
Proof. move => ??. by apply: (DTraceStep _ _ _ _ (Some _)). Qed.

Lemma DTraceStep' {EV} κs κs' (m : dem_module EV) σ2 σ1 Pσ3 κ :
  m.(dem_step) σ1 κ σ2 →
  κs = option_list (Vis <$> κ) ++ κs' →
  σ2 ~{ m, κs' }~>ₘ Pσ3 →
  σ1 ~{ m, κs }~>ₘ Pσ3.
Proof. move => ? -> ?. by apply: DTraceStep. Qed.

Lemma dem_has_trace_trans {EV} κs1 κs2 (m : dem_module EV) σ1 Pσ2 Pσ3 :
  σ1 ~{ m, κs1 }~>ₘ Pσ2 →
  (∀ σ2, Pσ2 σ2 → σ2 ~{ m, κs2 }~>ₘ Pσ3) →
  σ1 ~{ m, κs1 ++ κs2 }~>ₘ Pσ3.
Proof.
  elim.
  - naive_solver.
  - move => ?????????. rewrite -app_assoc. econstructor; eauto.
  - move => ?????. by apply: DTraceUb.
Qed.

Lemma dem_has_trace_trans' {EV} κs1 κs2 (m : dem_module EV) σ1 Pσ3 :
  σ1 ~{ m, κs1 }~>ₘ (λ σ2, σ2 ~{ m, κs2 }~>ₘ Pσ3) →
  σ1 ~{ m, κs1 ++ κs2 }~>ₘ Pσ3.
Proof. move => ?. by apply: dem_has_trace_trans. Qed.

Lemma dem_has_trace_add_empty {EV} κs1 (m : dem_module EV) σ1 σ2 :
  σ1 ~{ m, κs1 ++ [] }~>ₘ σ2 →
  σ1 ~{ m, κs1 }~>ₘ σ2.
Proof. by rewrite -{2}[κs1](right_id_L [] (++)). Qed.

Lemma dem_has_trace_inv {EV} κs (m : dem_module EV) σ1 Pσ2:
  σ1 ~{ m, κs }~>ₘ Pσ2 →
  ∃ σ2, σ1 ~{ m, κs }~>ₘ (σ2 =.) ∧ (m.(dem_is_ub) σ2 ∨ Pσ2 σ2).
Proof.
  elim.
  - move => ???. eexists _. split; [by apply: DTraceEnd| by right].
  - move => ??????? [?[? Hor]].
    eexists _. split; [ by apply: DTraceStep | done].
  - move => ????. eexists _. split; [by apply: DTraceUb| by left].
Qed.

Lemma dem_has_trace_ub_inv {EV} κs (m : dem_module EV) σ1 Pσ2:
  σ1 ~{m, Ub :: κs }~>ₘ Pσ2 →
  σ1 ~{m, [] }~>ₘ (λ _, False).
Proof.
  move Hκ: (Ub :: κs) => κ Hκs.
  elim: Hκs Hκ => //.
  - move => ??? [] //= ??? IH ?. apply: DTraceStepNone; [done|].
    naive_solver.
  - move => ?????. by apply: DTraceUb.
Qed.

Lemma dem_has_trace_cons_inv {EV} κs κ (m : dem_module EV) σ1 Pσ3:
  σ1 ~{ m, Vis κ :: κs }~>ₘ Pσ3 →
  σ1 ~{ m, [] }~>ₘ (λ σ2, ∃ σ2', m.(dem_step) σ2 (Some κ) σ2' ∧ σ2' ~{ m, κs }~>ₘ Pσ3).
Proof.
  move Hs: (Vis κ :: κs) => s Hκs.
  elim: Hκs Hs => //.
  - move => ??? [] //=.
    + move => ???? IH [] ??. subst. apply: DTraceEnd. eexists _. split; [done|]. naive_solver.
    + move => ??? IH ?. apply: DTraceStepNone; [done|]. naive_solver.
  - move => ?????. by apply: DTraceUb.
Qed.

Lemma dem_has_trace_app_inv {EV} κs1 κs2 (m : dem_module EV) σ1 Pσ3:
  σ1 ~{ m, κs1 ++ κs2 }~>ₘ Pσ3 →
  σ1 ~{ m, κs1 }~>ₘ (λ σ2, σ2 ~{ m, κs2 }~>ₘ Pσ3).
Proof.
  elim: κs1 σ1 => /=. { move => ??. by apply: DTraceEnd. }
  move => [|?] ? IH ?.
  - move => /dem_has_trace_ub_inv?. by apply: (dem_has_trace_trans []).
  - move => /(dem_has_trace_cons_inv _ _)?.
    apply: (dem_has_trace_trans []); [done|] => ? [?[??]].
    apply: DTraceStepSome; [done|]. naive_solver.
Qed.

Lemma dem_has_trace_ub_app_inv {EV} κs (m : dem_module EV) σ1 Pσ2:
  σ1 ~{ m, κs ++ [Ub] }~>ₘ Pσ2 →
  σ1 ~{ m, κs }~>ₘ (λ _, False).
Proof.
  move => /dem_has_trace_app_inv ?.
  apply: dem_has_trace_add_empty.
  apply: dem_has_trace_trans; [done|] => ?.
  apply: dem_has_trace_ub_inv.
Qed.

Inductive dem_ub_step {EV} (m : dem_module EV) : m.(dem_state) → option EV → (m.(dem_state) → Prop) → Prop :=
| MStepStep σ1 κ σ2:
    m.(dem_step) σ1 κ σ2 →
    dem_ub_step m σ1 κ (σ2 =.)
| MStepUb σ1:
    m.(dem_is_ub) σ1 →
    dem_ub_step m σ1 None (λ _, False).

Program Definition dem_module_to_module {EV} (m : dem_module EV) : module EV := {|
  m_step := dem_ub_step m
|}.
Next Obligation.
  move => ????? Hstep. inversion Hstep; simplify_eq/=.
  - apply FinitePred_eq.
  - apply FinitePred_False.
Qed.
Coercion dem_module_to_module : dem_module >-> module.

Record dem_mod_state EV := DMS {
  dms_module : dem_module EV;
  dms_state : dms_module.(dem_state);
}.
Arguments DMS {_}.
Arguments dms_module {_}.
Arguments dms_state {_}.
Coercion dms_module : dem_mod_state >-> dem_module.

Definition dms_to_ms {EV} (m : dem_mod_state EV) : mod_state EV := {|
  ms_module := m;
  ms_state := m.(dms_state)
|}.
Coercion dms_to_ms : dem_mod_state >-> mod_state.

Record dem_refines {EV} (mimpl mspec : dem_mod_state EV) : Prop := {
  dem_ref_subset:
    ∀ κs, mimpl.(dms_state) ~{ mimpl, κs }~>ₘ (λ _, True) →
          mspec.(dms_state) ~{ mspec, κs }~>ₘ (λ _, True)
}.

Global Instance sqsubseteq_dem_refines EV : SqSubsetEq (dem_mod_state EV) := dem_refines.

Definition dem_refines_equiv {EV} (m1 m2 : dem_mod_state EV) : Prop := m1 ⊑ m2 ∧ m2 ⊑ m1.

Definition dem_safe {EV} (m : dem_mod_state EV) (P : list (event EV) → Prop) :=
  ∀ κs, m.(dms_state) ~{ m, κs }~>ₘ (λ _, True) → P κs.

Lemma dem_refines_preserves_safe EV (mspec mimpl : dem_mod_state EV) P:
  dem_safe mspec P →
  mimpl ⊑ mspec →
  dem_safe mimpl P.
Proof. move => Hs [Hr] κs Hκs. apply: Hs. by apply: Hr. Qed.

Global Instance dem_refines_preorder EV : PreOrder (@dem_refines EV).
Proof.
  constructor.
  - constructor => // κ Hi; naive_solver.
  - move => ??? [Hr1] [Hr2]. constructor => /=. naive_solver.
Qed.

Inductive extend_ub {EV} : list (event EV) → list (event EV) → Prop :=
| EU_nil :
    extend_ub [] []
| EU_cons κ κs1 κs2 :
    extend_ub κs1 κs2 →
    extend_ub (Vis κ :: κs1) (Vis κ :: κs2)
| EU_ub κs1 κs2 :
    extend_ub (Ub :: κs1) κs2
.

Lemma dem_extend_ub {EV} (m : dem_module EV) σ Pσ κs κs' :
 extend_ub κs κs' →
 σ ~{ m, κs }~>ₘ Pσ →
 σ ~{ m, κs' }~>ₘ Pσ.
Proof.
  move => Hub Ht. elim: Ht κs' Hub.
  - move => ???? Hub. inversion Hub; simplify_eq. by constructor.
  - move => ??? [κ|]/= ????? Hub.
    + inversion Hub; simplify_eq.
      apply: DTraceStepSome; naive_solver.
    + apply: DTraceStepNone; naive_solver.
  - move => ??????. by constructor.
Qed.

(*** Relating [module] and [dem_module] *)

Fixpoint list_to_trace {EV} (κs : list (event EV)) : trace EV :=
  match κs with
  | [] => tnil
  | Vis κ::κs' => tcons κ (list_to_trace κs')
  | Ub::κs' => tub
  end.

Lemma list_to_trace_app {EV} (κs1 κs2 : list (event EV)):
  list_to_trace (κs1 ++ κs2) = tapp (list_to_trace κs1) (list_to_trace κs2).
Proof.
  elim: κs1 => //= -[|?] /= ??.
  - rewrite /tub. f_equal. by apply functional_extensionality.
  - by f_equal.
Qed.

Lemma list_to_trace_option_list {EV} (κ : option EV):
  list_to_trace (Vis <$> option_list κ) = option_trace κ.
Proof. destruct κ => //. Qed.

Lemma list_to_trace_sub_inv {EV} (κs1 κs2 : list (event EV)) :
  list_to_trace κs1 ⊆ list_to_trace κs2 →
  extend_ub κs1 κs2.
Proof.
  elim: κs1 κs2 => /=.
  - move => [|[|?]?] //=.
    + move => ?. constructor.
    + inversion 1; simplify_eq. done.
    + inversion 1.
  - move => [|?]? IH [/=|[|?]?] Hs; inversion Hs; simplify_eq; try constructor; try done.
    naive_solver.
Qed.

(* TODO: This cannot hold anymore since we made the environment more
powerful and it can now react to the choices of the module. Maybe we
can commute the choices to the beginning of the traces, but I am not
sure if this will work. Otherwise we have to add enviroment choices to
trace of dem_module as well.

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
Lemma has_trace_dem_has_trace {EV} (m : dem_module EV) σ Pσ κs:
  σ ~{ m, κs }~> Pσ ↔ ∃ κs', list_to_trace κs' ⊆ κs ∧ σ ~{ m, κs' }~>ₘ Pσ.
Proof.
  split.
  - elim; clear.
    + move => ???. eexists []. split; [done|]. by constructor.
    + move => ??? κ κs' κs'' Hstep ? IH ??.
      inversion Hstep; simplify_eq.
      * have [?[??]]:= IH _ ltac:(done).
        eexists _. split; [ | by apply: DTraceStep].
        rewrite option_list_fmap. etrans; [|done].
        rewrite list_to_trace_app list_to_trace_option_list.
        by apply: tapp_mono.
      * simplify_eq/=. eexists [Ub]. split; [ | by apply: DTraceUb].
        by constructor.
    + move => T f σ κs ? F _ IH Hs.
      have [[x ?]| Hx]:= EM (∃ x, f x ⊆ κs).
      * have [?[??]]:= IH x. eexists _. split; [|done]. etrans; [|done]. done.
      *

        have ? : κs ≡ tnb. {
          split. by constructor.
          etrans; [|done]. constructor => x.
          contradict Hx. eexists x.
          admit.
        }

        eexists []. split. 2: constructor. simpl.
        etrans; [|done]. constructor => x.
        have := Hx (ex_intro _ x _).
        admit. admit.
        (*
        contradict Hx.
        elim: κs T {IH} f Hs; clear.
        -- inversion 1; simplify_K. naive_solver.
        -- move => ?? IH ??. inversion 1; simplify_K. naive_solver.
        -- move => ?? IH ??. inversion 1; simplify_K. 2: naive_solver.
           have [??]:= IH _ _ _ ltac:(done). eexists _. econstructor. done.
        -- move => ?????. inversion 1; simplify_K. 2: naive_solver.
           admit.
*)
  - move => [κs' [HP Ht]].
    apply: (has_trace_mono (list_to_trace κs')); [| naive_solver |done]. clear HP.
    elim: Ht => /=.
    + move => ???. by constructor.
    + move => ??? κ ????.
      apply: TraceStep; [ by constructor | naive_solver | | unfold VisNoUb; naive_solver ].
      by rewrite option_list_fmap list_to_trace_app list_to_trace_option_list.
    + move => ????. apply: TraceStep; [by constructor | done | | unfold VisNoUb => -[??] // ].
      simpl. done.
Admitted.

Lemma dem_has_trace_has_trace {EV} (m : dem_module EV) σ Pσ κs:
  σ ~{ m, κs }~>ₘ Pσ ↔ σ ~{ m, list_to_trace κs }~> Pσ.
Proof.
  rewrite has_trace_dem_has_trace. split; first naive_solver.
  move => [? [/list_to_trace_sub_inv ? ?]].
  by apply: dem_extend_ub.
Qed.

Lemma safe_dem_safe {EV} (m : dem_mod_state EV) P:
  dem_safe m P ↔ safe m (λ κs, ∃ κs', list_to_trace κs' ⊆ κs ∧
    ∀ κs'', extend_ub κs' κs'' → P κs'').
Proof.
  split.
  - move => Hsafe ?. move => /has_trace_dem_has_trace[?[??]].
    eexists _. split; [done|]. move => ??. apply: Hsafe.
    by apply: dem_extend_ub.
  - move => Hsafe ? /dem_has_trace_has_trace Ht.
    have [?[/list_to_trace_sub_inv? ?]]:= Hsafe _ Ht. naive_solver.
Qed.

Lemma refines_dem_refines {EV} (m1 m2 : dem_mod_state EV):
  dem_refines m1 m2 ↔ refines m1 m2.
Proof.
  split.
  - move => [?]. constructor => ? /has_trace_dem_has_trace?.
    apply/has_trace_dem_has_trace. naive_solver.
  - move => [?]. constructor => ? /dem_has_trace_has_trace?.
    apply/dem_has_trace_has_trace. naive_solver.
Qed.

(*** [mod_filter] *)
Inductive filter_step {EV1 EV2} (m : module EV1) (R : EV1 → option EV2 → Prop) :
  m.(m_state) → option EV2 → (m.(m_state) → Prop) → Prop :=
| FilterStep σ e e' Pσ:
    m.(m_step) σ e Pσ →
    (* TODO: is there a better way to formulate this? E.g. assume
    that there is no R None None Some in the theorem? *)
    (if e is Some κ then R κ e' else e' = None) →
    VisNoUb m e Pσ →
    filter_step m R σ e' Pσ
.

Program Definition mod_filter {EV1 EV2} (m : module EV1) (R : EV1 → option EV2 → Prop) (F : ∀ x, FinitePred (R x)) : module EV2 := {|
  m_step := filter_step m R;
|}.
Next Obligation. move => ???????? Hstep. inversion Hstep; simplify_eq. by apply: m_ang_finite. Qed.

Fixpoint trace_bind {EV1 EV2} (f : EV1 → trace EV2) (κs : trace EV1) : trace EV2 :=
  match κs with
  | tnil => tnil
  | tcons κ κs => tapp (f κ) (trace_bind f κs)
  | tex T f' => tex T (λ x, trace_bind f (f' x))
  | tall T F f' => tall T F (λ x, trace_bind f (f' x))
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


Definition filtered_trace {EV1 EV2} (R : EV1 → option EV2 → Prop) (F : ∀ x, FinitePred (R x))
  : trace EV1 → trace EV2 :=
  trace_bind (λ κ, tall ({ κ' | R κ κ'}) (F κ) (λ x, option_trace (`x))).

Lemma filtered_trace_mono {EV1 EV2} (R : EV1 → option EV2 → Prop) κs1 κs2 F :
  κs1 ⊆ κs2 →
  filtered_trace R F κs1 ⊆ filtered_trace R F κs2.
Proof. apply trace_bind_mono. Qed.

Lemma mod_filter_to_mod {EV1 EV2} (m : module EV1) (R : EV1 → option EV2 → Prop) F σi Pσ κs:
  σi ~{ mod_filter m R F, κs }~> Pσ →
  ∃ κs', filtered_trace R F κs' ⊆ κs ∧ σi ~{ m, κs' }~> Pσ.
Proof.
  elim.
  - move => ?????. eexists tnil => /=. split; [done|]. by constructor.
  - move => ??? κ ?? Hstep ? IH Hs ?.
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
    + apply: TraceStep; [done | |done |done].
      move => ??/=. eapply has_trace_ex. naive_solver.
      Unshelve. done.
  - move => T f ????? IH ?.
    have [fx Hfx]:= AxCHOICE _ _ _ IH.
    eexists (tall T ltac:(done) (λ x, fx x)) => /=.
    rewrite /filtered_trace/=-/(filtered_trace _).
    split.
    + etrans; [|done]. constructor => ?. econstructor. naive_solver.
    + apply: has_trace_all. naive_solver.
Qed.

Lemma mod_to_mod_filter {EV1 EV2} (m : module EV1) (R : EV1 → option EV2 → Prop) σi Pσ κs F:
  σi ~{ m, κs }~> Pσ →
  σi ~{ mod_filter m R F, filtered_trace R F κs }~> Pσ.
Proof.
  elim.
  - move => ?????. constructor. done. by apply: (filtered_trace_mono _ tnil).
  - move => ??? κ ?? Hstep ? IH Hs ?.
    apply: has_trace_mono; [| by apply: filtered_trace_mono |done].
    destruct κ => /=.
    + rewrite /filtered_trace/=-/(filtered_trace _).
      apply has_trace_all => -[??].
      apply: TraceStep; [econstructor;[done| simpl;done |done] |done |done |unfold VisNoUb in *; naive_solver].
    + apply: TraceStep; [by econstructor | done | simpl;done | move => [??]; done].
  - move => ?????????.
    apply: has_trace_mono; [| by apply: filtered_trace_mono |done].
    rewrite /filtered_trace/=-/(filtered_trace _).
    apply: has_trace_all. naive_solver.
Qed.

Lemma mod_filter_refines {EV1 EV2} (R : EV1 → option EV2 → Prop) mi ms σi σs F:
  MS mi σi ⊑ MS ms σs →
  MS (mod_filter mi R F) σi ⊑ MS (mod_filter ms R F) σs.
Proof.
  move => [/=Hr]. constructor => /=? /mod_filter_to_mod[?[? /Hr/mod_to_mod_filter?]].
  by apply: has_trace_mono.
Qed.

(*** [mod_product] *)
Inductive product_step {EV1 EV2} (m1 : module EV1) (m2 : module EV2) :
  (m1.(m_state) * m2.(m_state)) → option (option EV1 * option EV2) → ((m1.(m_state) * m2.(m_state)) → Prop) → Prop :=
| ProductStepL σ1 σ2 e Pσ:
    m1.(m_step) σ1 e Pσ →
    product_step m1 m2 (σ1, σ2)
                 (if e is Some e' then Some (Some e', None) else None)
                 (λ '(σ1', σ2'), Pσ σ1' ∧ σ2 = σ2')
| ProductStepR σ1 σ2 e Pσ:
    m2.(m_step) σ2 e Pσ →
    product_step m1 m2 (σ1, σ2)
                 (if e is Some e' then Some (None, Some e') else None)
                 (λ '(σ1', σ2'), σ1 = σ1' ∧ Pσ σ2')
| ProductStepBoth σ1 σ2 e1 e2 Pσ1 Pσ2:
    m1.(m_step) σ1 (Some e1) Pσ1 →
    m2.(m_step) σ2 (Some e2) Pσ2 →
    product_step m1 m2 (σ1, σ2)
                 (Some (Some e1, Some e2))
                 (λ '(σ1', σ2'), Pσ1 σ1' ∧ Pσ2 σ2')
.

Program Definition mod_product {EV1 EV2} (m1 : module EV1) (m2 : module EV2) : module (option EV1 * option EV2) := {|
  m_step := product_step m1 m2;
|}.
Next Obligation.
  move => ??????? Hstep. inversion Hstep; simplify_eq/=; apply: FinitePred_prod.
  all: try by apply FinitePred_eq.
  all: by eapply m_ang_finite.
Qed.

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
| MPR_all1 {T} x f κs κs2 F :
    mod_product_rel κs (f x) κs2 →
    mod_product_rel κs (tall T F f) κs2
| MPR_all2 {T} x f κs κs2 F :
    mod_product_rel κs κs2 (f x) →
    mod_product_rel κs κs2 (tall T F f)
| MPR_all T f κs κs1 κs2 F:
    (∀ x, mod_product_rel (f x) κs1 κs2) →
    (tall T F f) ⊆ κs →
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


Lemma mod_product_to_mods {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ Pσ κs:
  σ ~{ mod_product m1 m2, κs }~> Pσ → ∃ κs', mod_product_rel κs κs'.1 κs'.2 ∧
    σ.1 ~{ m1, κs'.1 }~> (λ _, True) ∧ σ.2 ~{ m2, κs'.2 }~> (λ _, True).
Proof.
  elim.
  - move => [σ1 σ2] ????. eexists (tnil, tnil) => /=.
    split_and!.
    + apply: mod_product_rel_mono; [|done]. by constructor.
    + by constructor.
    + by constructor.
  - move => [σ1 σ2] ????? Hstep _ IH ? Hnub.
    inversion Hstep; simplify_eq.
    + have {}IH := IH (_, σ2) (conj _ ltac:(exact (eq_refl σ2))).
      have [f Hf]:= CHOICE IH.
      unshelve eexists (tapp (option_trace e) (tex _ (λ x, (f x).1)), (tall _ _ (λ x, (f x).2))) => /=.
      { by apply: m_ang_finite. }
      split_and!.
      -- apply: mod_product_rel_mono; [|done].
         destruct e => //=.
         ++ apply: MPR_cons_l; [|done].
            constructor => -[??]. econstructor.
            naive_solver.
         ++ constructor => -[??]. econstructor. naive_solver.
      -- apply: TraceStep; [ done | | done |]. 2: {
           unfold VisNoUb, is_Some in *. destruct e => //. 2: naive_solver.
           have [|[??]?]:= Hnub. naive_solver. naive_solver.
         }
         move => σ' Hσ'. apply: (has_trace_ex (exist _ σ' Hσ')).
         apply: has_trace_mono. naive_solver. done. naive_solver.
      -- apply: has_trace_all => -[??].
         apply: has_trace_mono. naive_solver. done. naive_solver.
    + have {}IH := IH (σ1, _) (conj ltac:(exact (eq_refl σ1)) _).
      have [f Hf]:= CHOICE IH.
      unshelve eexists ((tall _ _ (λ x, (f x).1)), tapp (option_trace e) (tex _ (λ x, (f x).2))) => /=.
      { by apply: m_ang_finite. }
      split_and!.
      -- apply: mod_product_rel_mono; [|done].
         destruct e => //=.
         ++ apply: MPR_cons_r; [|done].
            constructor => -[??]. econstructor.
            naive_solver.
         ++ constructor => -[??]. econstructor. naive_solver.
      -- apply: has_trace_all => -[??].
         apply: has_trace_mono. naive_solver. done. naive_solver.
      -- apply: TraceStep; [ done | | done |]. 2: {
           unfold VisNoUb, is_Some in *. destruct e => //. 2: naive_solver.
           have [|[??]?]:= Hnub. naive_solver. naive_solver.
         }
         move => σ' Hσ'. apply: (has_trace_ex (exist _ σ' Hσ')).
         apply: has_trace_mono. naive_solver. done. naive_solver.
    + have {}IH := IH (_, _) (conj _ _).
      have [f Hf]:= CHOICE2 IH.
      unshelve eexists (tcons e1 (tex _ (λ x1, (tall _ _ (λ x2, (f x1 x2).1)))),
                        tcons e2 (tex _ (λ x2, (tall _ _ (λ x1, (f x1 x2).2))))) => /=.
      { by apply: m_ang_finite. }
      { by apply: m_ang_finite. }
      split_and!.
      -- apply: mod_product_rel_mono; [|done]. simpl.
         econstructor; [|done..].
         constructor => -[??].
         constructor => -[??].
         econstructor.
         econstructor. naive_solver.
      -- apply: TraceStep; [ done | | simpl; done |]. 2: {
           unfold VisNoUb, is_Some in *. have [|[??]?]:= Hnub. naive_solver. naive_solver.
         }
         move => ??.
         apply: has_trace_ex. apply: has_trace_all => -[??]. naive_solver.
      -- apply: TraceStep; [ done | | simpl; done |]. 2: {
           unfold VisNoUb, is_Some in *. have [|[??]?]:= Hnub. naive_solver. naive_solver.
         }
         move => ??.
         apply: has_trace_ex. apply: has_trace_all => -[??]. naive_solver.
  - move => T f ????? IH ?.
    have [fx Hfx]:= AxCHOICE _ _ _ IH.
    eexists (tall T ltac:(done) (λ x, (fx x).1), tall T ltac:(done) (λ x, (fx x).2)) => /=.
    split_and! => //.
    -- apply: mod_product_rel_mono; [|done].
       eapply MPR_all; [|done] => ?.
       econstructor. econstructor. naive_solver.
    -- apply: has_trace_all. naive_solver.
    -- apply: has_trace_all. naive_solver.
       Unshelve. done. done.
Qed.

Lemma mod_product_nil_l {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ1 σ2 Pσ κs:
  σ1 ~{ m1, κs }~> Pσ → κs ⊆ tnil →
  (σ1, σ2) ~{ mod_product m1 m2, tnil }~> (λ σ', Pσ σ'.1 ∧ σ2 = σ'.2).
Proof.
  elim.
  - move => ??????. constructor; [|done]. naive_solver.
  - move => ??? κ ????? Hs1 ? Hs2.
    pose proof (transitivity Hs1 Hs2) as Hs.
    destruct κ; [inversion Hs|]; simplify_eq/=.
    apply: TraceStep; [ by apply: ProductStepL | | simpl;done | by move => -[??]].
    move => [??] /=. naive_solver.
  - move => ???????? Hs1 Hs2.
    pose proof (transitivity Hs1 Hs2) as [??]%subtrace_all_nil_inv. naive_solver.
Qed.

Lemma mod_product_nil_r {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ1 σ2 Pσ κs:
  σ2 ~{ m2, κs }~> Pσ → κs ⊆ tnil →
  (σ1, σ2) ~{ mod_product m1 m2, tnil }~> (λ σ', Pσ σ'.2 ∧ σ1 = σ'.1).
Proof.
  elim.
  - move => ??????. constructor; [|done]. naive_solver.
  - move => ??? κ ????? Hs1 ? Hs2.
    pose proof (transitivity Hs1 Hs2) as Hs.
    destruct κ; [inversion Hs|]; simplify_eq/=.
    apply: TraceStep; [ by apply: ProductStepR | | simpl;done | by move => -[??]].
    move => [??] /=. naive_solver.
  - move => ???????? Hs1 Hs2.
    pose proof (transitivity Hs1 Hs2) as [??]%subtrace_all_nil_inv. naive_solver.
Qed.

Lemma mods_to_mod_product {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ κs κs1 κs2:
  mod_product_rel κs κs1 κs2 →
  σ.1 ~{ m1, κs1 }~> (λ _, True) → σ.2 ~{ m2, κs2 }~> (λ _, True) →
  σ ~{ mod_product m1 m2, κs }~> (λ _, True).
Proof.
  move => Hrel.
  elim: Hrel σ.
  - move => ?????. by constructor.
  - move => ????? /= IH [??] /has_trace_ex_inv ??.
    apply: (has_trace_trans tnil). { by apply: mod_product_nil_l. }
    move => [??] /= [[??]?]. naive_solver.
  - move => ????? IH [??] ? /has_trace_ex_inv ?.
    apply: (has_trace_trans tnil). { by apply: mod_product_nil_r. }
    move => [??] /= [[??]?]. naive_solver.
  - move => ?????? ? IH ? /has_trace_all_inv ??. apply: IH; [|done]. naive_solver.
  - move => ?????? ? IH ?? /has_trace_all_inv ?. apply: IH; [done|]. naive_solver.
  - move => ??????? IH ????.
    apply: has_trace_mono; [|done| done].
    apply: has_trace_all => ?. naive_solver.
  - move => ?????? IH ? [??]/= /(has_trace_cons_inv _ _) ??.
    apply: has_trace_mono; [|done| done].
    apply: (has_trace_trans tnil). { by apply: mod_product_nil_l. }
    move => /= [??] /= [[?[?[Hvis ?]]]?]. subst.
    apply: TraceStep; [ by apply: ProductStepL |  | simpl;done |]. 2: {
      have [|??]:= Hvis. naive_solver. unfold VisNoUb in *. eexists (_,_). naive_solver.
    }
    move => [??] /= [??]. subst. naive_solver.
  - move => ?????? IH ? [??]/=? /(has_trace_cons_inv _ _)?.
    apply: has_trace_mono; [|done| done].
    apply: (has_trace_trans tnil). { by apply: mod_product_nil_r. }
    move => /= [??] /= [[?[?[Hvis ?]]]?]. subst.
    apply: TraceStep; [ by apply: ProductStepR |  | simpl;done |]. 2: {
      have [|??]:= Hvis. naive_solver. unfold VisNoUb in *. eexists (_,_). naive_solver.
    }
    move => [??] /= [??]. subst. naive_solver.
  - move => ??????? IH ? [??]/= /(has_trace_cons_inv _ _)? /(has_trace_cons_inv _ _)?.
    apply: has_trace_mono; [|done| done].
    apply: (has_trace_trans tnil). { by apply: mod_product_nil_l. }
    move => /= [??] /= [[?[?[Hvis ?]]]?]. subst.
    apply: (has_trace_trans tnil). { by apply: mod_product_nil_r. }
    move => /= [??] /= [[?[?[Hvis2 ?]]]?]. subst.
    apply: TraceStep; [ by apply: ProductStepBoth |  | simpl;done |]. 2: {
      have [|??]:= Hvis. naive_solver.
      have [|??]:= Hvis2. naive_solver.
      unfold VisNoUb in *. eexists (_,_). naive_solver.
    }
    move => [??] /= [??]. subst. naive_solver.
Qed.

Lemma mod_product_refines {EV1 EV2} (m1 m1' : module EV1) (m2 m2' : module EV2) σ1 σ1' σ2 σ2':
  MS m1 σ1 ⊑ MS m1' σ1' →
  MS m2 σ2 ⊑ MS m2' σ2' →
  MS (mod_product m1 m2) (σ1, σ2) ⊑ MS (mod_product m1' m2') (σ1', σ2').
Proof.
  move => [/=Hr1] [/=Hr2]. constructor => κs /= /mod_product_to_mods[κs1 [κs2 [/Hr1 ? /Hr2 ?]]].
  by apply: mods_to_mod_product.
Qed.

(*** Proving refinement *)

(** ** [inv] *)
Lemma inv_implies_refines {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → m2.(m_state) → Prop):
  inv m1.(ms_state) m2.(ms_state) →
  (∀ σi1 σs1 Pσi2 e,
      inv σi1 σs1 → m_step m1 σi1 e Pσi2 →
      σs1 ~{ m2, option_trace e }~> (λ σs2, ∃ σi2, Pσi2 σi2 ∧ inv σi2 σs2)) →
  m1 ⊑ m2.
Proof.
  move => Hinvinit Hinvstep.
  constructor => // κs. move: m1.(ms_state) m2.(ms_state) Hinvinit => σi1 σs1 Hinv Hsteps.
  elim: Hsteps σs1 Hinv => {σi1 κs}.
  - move => ???????. by constructor.
  - move => σi1 Pσi2 Pσi3 κ κs κs' Hstep Hsteps IH Hcons Hnoub σs1 Hinv.
    have ?:= (Hinvstep _ _ _ _ Hinv Hstep).
    apply: has_trace_mono; [|done|done].
    apply: has_trace_trans; [done|] => ? /=[?[??]].
    by apply: IH.
  - move => ???????????.
    apply: has_trace_mono; [|done|done].
    apply: has_trace_all => ?. naive_solver.
Qed.

(** ** [wp] *)
Inductive wp {EV} (m1 m2 : module EV) : nat → m1.(m_state) -> m2.(m_state) -> Prop :=
| wp_step' σi1 σs1 n:
    (∀ Pσi2 κ n', n = S n' → m_step m1 σi1 κ Pσi2 -> ∃ Pσ2,
      σs1 ~{ m2, option_trace κ }~> Pσ2 ∧
      ∀ σs2, Pσ2 σs2 → ∃ σi2, Pσi2 σi2 ∧ wp m1 m2 n' σi2 σs2) ->
    wp m1 m2 n σi1 σs1
.
Lemma wp_mono {EV} (m1 : module EV) m2 κs σ n n':
  wp m1 m2 n σ κs →
  n' ≤ n →
  wp m1 m2 n' σ κs.
Proof.
  elim: n' n σ κs.
  - move => ???? Hwp. constructor. done.
  - move => n' IH [|n] σ κs Hwp ?. lia.
    inversion Hwp as [??? Hwp']; simplify_eq.
    constructor => Pσi2 κ ?[?]?. subst.
    efeed revert Hwp';[done..|] => -[?[? Hwp'']].
    naive_solver lia.
Qed.

Lemma wp_step {EV} (m1 m2 : module EV) σi1 σs1 n:
    (∀ Pσi2 κ n', n = S n' → m_step m1 σi1 κ Pσi2 ->
      σs1 ~{ m2, option_trace κ }~> (λ σs2, ∃ σi2, Pσi2 σi2 ∧ wp m1 m2 n' σi2 σs2)) ->
    wp m1 m2 n σi1 σs1
.
Proof. move => ?. constructor. naive_solver. Qed.

Lemma wp_implies_refines {EV} (m1 m2 : mod_state EV):
  (∀ n, wp m1 m2 n m1.(ms_state) m2.(ms_state)) →
  m1 ⊑ m2.
Proof.
  move => Hwp.
  constructor => κs /has_trace_to_n [n Hi].
  move: Hi {Hwp}(Hwp n).
  move: m1.(ms_state) => σi1.
  move: m2.(ms_state) => σs1 Hi.
  elim: Hi σs1.
  - move => ????????. by apply: TraceEnd.
  - move => ????????? IH ??? Hwp.
    inversion_clear Hwp as [??? Hwp2]; subst.
    efeed revert Hwp2; [done..|] => -[?[? Hwp]].
    apply: has_trace_mono; [|done..].
    apply: has_trace_trans; [done|] => ??.
    efeed revert Hwp; [done|] => -[?[??]]. by apply: IH.
  - move => ????????? IH ????.
    apply: has_trace_mono; [|done..].
    apply: has_trace_all => ?. apply: IH.
    by apply: wp_mono.
Qed.

Lemma wp_step_impl {EV} (m1 m2 : module EV) σi1 σs n:
  (∀ Pσi2 κ n', n = S n' → m_step m1 σi1 κ Pσi2 ->
    ∃ σi2, Pσi2 σi2 ∧ κ = None ∧ wp m1 m2 n' σi2 σs) ->
  wp m1 m2 n σi1 σs
.
Proof.
  move => Hstep.
  apply wp_step => ?????.
  efeed revert Hstep; [done..|] => -[?[?[??]]]. subst.
  constructor; [|done]. naive_solver.
Qed.

Lemma wp_step_spec {EV} (m1 m2 : module EV) σi σs1 Pσs2 n:
  m_step m2 σs1 None Pσs2 ->
  (∀ σs2, Pσs2 σs2 → wp m1 m2 n σi σs2) ->
  wp m1 m2 n σi σs1
.
Proof.
  move => Hstep Hwp.
  apply wp_step => ?????.
  apply: TraceStep; [done| | simpl;done | by move => -[??]] => ??.
  efeed revert Hwp; [done|] => {}Hwp.
  inversion_clear Hwp as [??? Hwp2].
  efeed revert Hwp2; [done..|] => -[?[??]].
  by apply: has_trace_mono.
Qed.

Lemma wp_step_both {EV} (m1 m2 : module EV) σi1 σs1 n :
  (∀ Pσi2 κ n', n = S n' → m_step m1 σi1 κ Pσi2 -> ∃ Pσ2,
   m_step m2 σs1 κ Pσ2 ∧ VisNoUb m2 κ Pσ2 ∧
   ∀ σs2, Pσ2 σs2 → ∃ σi2, Pσi2 σi2 ∧ wp m1 m2 n' σi2 σs2) ->
  wp m1 m2 n σi1 σs1.
Proof.
  move => Hstep.
  constructor => ?????.
  efeed revert Hstep; [done..|] => -[?[?[??]]].
  eexists _. split; [|done].
  apply: TraceStep; [done| by constructor | |done].
  by rewrite tapp_tnil_r.
Qed.

(* TODO:

 mod_seq : (m1 : module EV1) (m2 : module EV2) (f1 : EV1 -> (EV2 + EV3)) (f2 : EV2 -> (EV1 + EV3)) : module EV3

mod_wrap : (m1 : module EV2) : (w : EV1 → trace EV2) :
- allows silent steps of m1
- at each step demonically chooses if it tries to emit an event e in EV1
  - if it does so, it follows the demonic and angelic choices of the trace [w e]
  - when that reaches a cons k ks, m1 takes a step emitting k
    - only then the event for the wrapped module is emitted
  - the demonic and angelic choices make up the richer structure of EV2 from EV1
- this formulation should work for events that contain mixed angelic and demonic choice
  - e.g. translating an atomic read from an assembly memory module to a C memory module

Proof rule for merging mod_wrap:
∀ w : EV1 → trace EV2,
(∀ e1 e2, f1 e1 = inl e2 →
   trace_bind (λ k, if f2 k is inl k' then tcons k' tnil else tub) (w e1) ⊆ w e2) →
mod_seq (mod_wrap m1 w) (mod_wrap m2 w) f1 f1 ⊑ mod_wrap (mod_seq m1 m2 f2) w

The proof should follow the subtrace relationship when constructing the new evaluation.

Example of w:
λ e,
 match e with
| AsmInCall  v => tall T (λ x, tcons (CInCall (asm_val_to_C x v)) tnil)
| AsmInRet   v => tall T (λ x, tcons (CInRet (asm_val_to_C x v)) tnil)
| AsmOutCall v => tex T (λ x, tcons (COutCall (asm_val_to_C x v)) tnil)
| AsmOutRet  v => tex T (λ x, tcons (COutRet (asm_val_to_C x v)) tnil)
 *)

Ltac invert_all_tac f :=
  let do_invert H := inversion H; clear H in
  repeat lazymatch goal with
         | H : f |- _ => do_invert H
         | H : f _ |- _ => do_invert H
         | H : f _ _|- _ => do_invert H
         | H : f _ _ _|- _ => do_invert H
         | H : f _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _ _ _ _ _|- _ => do_invert H
         end.

Tactic Notation "invert_all" constr(f) := invert_all_tac f; simplify_eq/=.
Tactic Notation "invert_all'" constr(f) := invert_all_tac f.


(* Ltac inv_step := invert_all' @m_ub_step; invert_all @m_step. *)
Ltac inv_step := invert_all @m_step.

(*** Tests *)

(*
  TODO: prove the following refinement for which wp is probably not enough

            A     B
           /- 2  --- 3
  spec: 1 -
           \- 2' --- 4
            A     C

                  B
           A     /- 3
  impl: 1 --- 2 -
                 \- 4
                 C

*)
Module test.

(*   2
  1 --- 2 (done)
 *)
Inductive mod1_step : bool → option nat → (bool → Prop) → Prop :=
| T1False: mod1_step false (Some 2) (true =.).


Program Definition mod1 : module nat := {|
  m_state := bool;
  m_step := mod1_step;
|}.
Next Obligation.
  move => ???. inversion 1. apply: FinitePred_eq.
Qed.

(*         2
  1 --- 2 --- 3 (done)
 *)
Inductive mod2_state := | S1 | S2 | S3.
Inductive mod2_step : mod2_state → option nat → (mod2_state → Prop) → Prop :=
| T2S1: mod2_step S1 None (S2 =.)
| T2S2: mod2_step S2 (Some 2) (S3 =.).
Program Definition mod2 : module nat := {|
  m_state := mod2_state;
  m_step := mod2_step;
|}.
Next Obligation.
  move => ???. inversion 1; apply: FinitePred_eq.
Qed.

Definition t2_to_t1_inv (σ1 : mod2_state) (σ2 : bool) : Prop :=
  σ2 = match σ1 with
  | S1 | S2 => false
  | _ => true
  end.
Lemma test_refines1 :
  MS mod2 S1 ⊑ MS mod1 false.
Proof.
  apply (inv_implies_refines (MS mod2 S1) (MS mod1 false) t2_to_t1_inv).
  - done.
  - move => σi1 σs1 σi2 e -> ?. inv_step => //.
    + apply: TraceEnd; [|done]. naive_solver.
    + apply: TraceStep; [constructor | | simpl;done | by econstructor].
      move => ? <-.
      apply: TraceEnd; [|done]. naive_solver.
Qed.

Lemma test_refines1_wp :
  MS mod2 S1 ⊑ MS mod1 false.
Proof.
  apply wp_implies_refines => n /=.

  apply: wp_step_impl => ?????. inv_step.
  eexists _. split_and!; [done..|].

  apply: wp_step_both => ?????. inv_step.
  eexists _. split_and!; [constructor| by econstructor |] => ? <-.
  eexists _. split_and!; [done..|].

  apply: wp_step_impl => ?????. inv_step.
Qed.


(*** old stuff *)

(* Definition set_refines {EV} (mi ms : module EV) (Pσi : mi.(m_state) → Prop) (Pσs : ms.(m_state) → Prop) : Prop := *)
  (* ∀ κs, (∀ σi, Pσi σi → σi ~{ mi, κs }~> (λ _, True)) → ∀ σs, Pσs σs → σs ~{ ms, κs }~> (λ _, True). *)
Definition set_refines {EV} (mi ms : module EV) (Pσi : mi.(m_state) → Prop) (Pσs : ms.(m_state) → Prop) : Prop :=
  ∀ κs, (∀ σi, Pσi σi → σi ~{ mi, κs }~> (λ _, True)) → ∃ σs, Pσs σs ∧ σs ~{ ms, κs }~> (λ _, True).

(* Definition set_refines {EV} (mi ms : module EV) (Pσi : mi.(m_state) → Prop) (Pσs : ms.(m_state) → Prop) : Prop := *)
  (* ∀ κs, ∀ σi, Pσi σi → σi ~{ mi, κs }~> (λ _, True) → ∃ σs, Pσs σs ∧ σs ~{ ms, κs }~> (λ _, True). *)

Lemma set_refines_intro EV (mi ms : mod_state EV):
  mi ⊑ ms →
  set_refines mi ms (mi.(ms_state) =.) (ms.(ms_state) =.).
Proof. move => [?] ?. naive_solver. Qed.

Lemma set_refines_mono EV (mi ms : module EV) (Pσi Pσs Pσi' Pσs' : _ → Prop):
  set_refines mi ms Pσi' Pσs' →
  (∀ x, Pσi' x → Pσi x) →
  (∀ x, Pσs' x → Pσs x) →
  set_refines mi ms Pσi Pσs.
Proof.
  move => Hr Hi Hs κs H.
  have [|?[??]]:= Hr κs; naive_solver.
Qed.

Lemma set_refines_step_Some {EV} (m1 m2 : module EV) Pσi1 Pσs1 Pσi2 e:
  set_refines m1 m2 Pσi1 Pσs1 →
  (∀ σi1, Pσi1 σi1 → m1.(m_step) σi1 (Some e) (Pσi2 σi1) ∧ VisNoUb m1 (Some e) (Pσi2 σi1)) →
  set_refines m1 m2 (λ σi, ∃ σi1, Pσi2 σi1 σi)
              (λ σs, ∃ Pσ σss, Pσs1 σss ∧ σss ~{m2, tcons e tnil}~> Pσ ∧ Pσ σs).
Proof.
  move => Hr Hstep κs Hi.
  have [|σs [? Hs]]:= Hr (tcons e κs). {
    move => σi Pσi.
    apply: TraceStep; [naive_solver | naive_solver | by constructor; constructor | naive_solver].
  }
  move: Hs => /(has_trace_cons_inv _ _)Hs.
  move: (Hs) => /has_trace_inv [?|[σ' [Pσ'[? [Hvis ?]]]]].
  + eexists σs. split.
    * eexists (_ =.), σs. split; [done|]. split; [|done].
      apply: (has_trace_trans tnil). done. done.
    * apply: (has_trace_trans tnil). done. done.
  + destruct Hvis as [σ'' ?]. naive_solver.
    eexists σ''. split; [|naive_solver].
    eexists (λ σ, σ ~{ m2, κs }~> (λ _, True)), σs. split; [done|]. split.
    * apply: (has_trace_trans tnil). done.
      move => ? [?[?[??]]].
      apply: TraceStep; [ done | | by constructor; constructor |done].
      move => ??. constructor. naive_solver. done.
    * naive_solver.
Qed.

Lemma set_refines_step_None {EV} (m1 m2 : module EV) Pσi1 Pσs1 Pσi2:
  set_refines m1 m2 Pσi1 Pσs1 →
  (∀ σi1, Pσi1 σi1 → σi1 ~{ m1, tnil }~> (Pσi2 σi1)) →
  set_refines m1 m2 (λ σi, ∃ σi1, Pσi2 σi1 σi) Pσs1.
Proof.
  move => Hr Hstep κs Hi.
  have [|σs [? Hs]]:= Hr κs. {
    move => ??. apply: (has_trace_trans tnil). naive_solver. naive_solver.
  }
  naive_solver.
Qed.

Lemma set_refines_step_None' {EV} (m1 m2 : module EV) Pσi1 Pσs1 Pσi2:
  set_refines m1 m2 Pσi1 Pσs1 →
  (∀ σi1, Pσi1 σi1 → Pσi2 σi1 σi1 ∨ ∃ P, m1.(m_step) σi1 None P ∧ (∀ σ, P σ → Pσi2 σi1 σ)) →
  set_refines m1 m2 (λ σi, ∃ σi1, Pσi2 σi1 σi) Pσs1.
Proof.
  move => Hr Hstep κs Hi.
  have [|σs [? Hs]]:= Hr κs. {
    move => σi ?.
    have [?|[?[??]]]:= Hstep σi ltac:(done).
    - naive_solver.
    - apply: TraceStep. done. naive_solver. by constructor. by unfold VisNoUb => -[??].
  }
  naive_solver.
Qed.

(* TODO: This does not make any sense yet! But there should be a rule for choice for set_refines. *)
Lemma set_refines_choice {EV} T (m1 m2 : module EV) Pσi1 (f : {σ | Pσi1 σ} → T) x Pσs1:
  set_refines m1 m2 Pσi1 Pσs1 →
  set_refines m1 m2 (λ σ, ∃ HP : Pσi1 σ, f (σ ↾ HP) = x) Pσs1.
Proof.
  move => Hr κs Hs.
  have {}Hs : ∀ σi (HP : Pσi1 σi), f (σi ↾ HP) = x → σi ~{ m1, κs }~> (λ _ : m_state m1, True) by naive_solver.

  (* TODO: This is not the right thing. *)
  have []:= Hr (tchoice T (λ x, κs)). {
    move => ??.
    apply: has_trace_choice. done.
    apply: Hs.
    admit.
    (* admit. *)
    (* apply: (has_trace_trans tnil). naive_solver. naive_solver. *)
  }
  move => ? [? /has_trace_choice_inv].
  eexists _. split; [done|].
  apply: (has_trace_trans tnil). done. naive_solver.
  (* naive_solver. *)
Abort.

Lemma mod_filter_refines' {EV1 EV2} (R : EV1 → option (option EV2)) mi ms σi σs:
  MS mi σi ⊑ MS ms σs →
  MS (mod_filter mi R) σi ⊑ MS (mod_filter ms R) σs.
Proof.
  move => /set_refines_intro /= Hr. constructor => κs /=.
  have Hs : (
              ∀ Pσi Pσs, set_refines mi ms Pσi Pσs →
                (∀ σi, Pσi σi → σi ~{ mod_filter mi R, κs }~> (λ _, True)) →
                ∃ κs' σs, κs' ⊆ κs ∧ Pσs σs ∧ σs ~{ mod_filter ms R, κs' }~> (λ _, True)
            ); last first. {
    move => ?.
    have [//| |?[?[?[??]]]]:= Hs (σi =.) (σs =.); [naive_solver|]. subst.
    by apply: has_trace_mono.
  }
  elim: κs; clear.
  - move => Pσi Pσs Hr Hi.
    have [ |?[??]]:= Hr tnil _. by constructor.
    eexists tnil, _. split;[done|]. split;[done|]. by constructor.
  - move => κ κs IH Pσi Pσs Hr Hi.

    (* TODO: Define nhas_trace, i.e. has_trace indexed by a trace ()
    where each cons of the trace corresponds to one step (silent or
    not silent). We can then do induction on the trace (). Either at
    the toplevel of this proof or internally when we deal with tnil
    steps. We also need a relation trace_le that is like subtrace, but
    tnil ≤ tcons. We can construct a global trace_step_index that is
    bigger than the step_indices of all traces in Pσi by using choice.
    It might be that some of the traces in Pσi finish earlier than others, but
    set_refines_step_None' can handle that.  *)

    have := set_refines_step_None _ _ _ _ _ ltac:(done).

    (*

    move HP: (λ σ2, ∃ P, _) => P.
    move Hκn: tnil => κn Ht.
    have {}Hκn : (κn ⊆ tnil) by naive_solver.
    elim: Ht HP Hκn. 2: {
      move => ??? κ' ?? Hstep ? IH2 Hnext ? Hsub. subst.
      have {}IH2:= IH2 _ _ ltac:(done).
      destruct κ'; simplify_eq/=. {
        move: Hnext => /trace_next_cons[? [Hsub2 ?]].
        pose proof (transitivity Hsub2 Hsub). easy.
      }
      move: Hnext => /trace_next_nil Hnext.
      inversion Hstep; simplify_eq.
      apply: IH2. admit. admit.
    }
    move => ??? HP ???. subst.
    have {HP} [?[Hstep ?]]:= HP.
    inversion Hstep; simplify_eq. destruct e => //.

    admit.
    +
*)
    admit.
  - move => T f IH Pσi Pσs Hr Hi.


    have {}Hi : ∀ σi, Pσi σi → σi ~{ mod_filter mi R, tnil }~> (λ σ2, ∃ x, σ2 ~{ mod_filter mi R, f x }~> (λ _, True)). {
      move => ??. apply has_trace_choice_inv. naive_solver.
    }
    have {}Hi : ∀ σi, Pσi σi → ∃ x, σi ~{ mod_filter mi R, f x }~> (λ _, True). {
      (* not provable, but we should be able to eliminate the nil trace like in the cons case *)
      admit.
    }

    (* have [ft ?]: ∃ ft : trace EV2 → trace EV1, True. admit. *)

    (* have := Hr (tchoice T (λ x, ft (f x))). *)


    have [[σx ?]|?]:= EM (∃ σ, Pσi σ). 2: {
      have [ |x [?/has_trace_choice_inv ?]]:= Hr tub _. naive_solver.
      eexists _, _. split;[done|]. split;[done|].
      (* should be provable *)
      admit.
    }

    (* TODO: not sure if adding the ∃ (κs' : trace EV2) in the goal was a good idea. *)

    suff : ∃ x σs, Pσs σs ∧ σs ~{ mod_filter ms R, f x }~> (λ _, True). {
      move => [?[?[??]]]. eexists _. split; [done|]. by apply: has_trace_choice.
    }
    have [fc Hfc]:= CHOICE_trace Hi.
    have [//|x ?]:= Hi σx.

    eexists x. apply: (IH x (λ σ, ∃ HP : Pσi σ, fc (exist _ σ HP) = x)).
    { apply: set_refines_mono; [done| |done].
      (* THIS IS NOT PROVABLE! *)
      admit. }
    naive_solver.
Abort.


Definition set_refines {EV} (mi ms : module EV) (Pσi : mi.(m_state) → Prop) (Pσs : ms.(m_state) → Prop) : Prop :=
  ∀ κs, ∃ σi, Pσi σi ∧ (σi ~{ mi, κs }~> (λ _, True) → ∃ σs, Pσs σs ∧ σs ~{ ms, κs }~> (λ _, True)).

(* Definition set_refines {EV} (mi ms : module EV) (Pσi : mi.(m_state) → Prop) (Pσs : ms.(m_state) → Prop) : Prop := *)
  (* ∀ κs, ∀ σi, Pσi σi → σi ~{ mi, κs }~> (λ _, True) → ∃ σs, Pσs σs ∧ σs ~{ ms, κs }~> (λ _, True). *)

Lemma set_refines_intro EV (mi ms : mod_state EV):
  mi ⊑ ms →
  set_refines mi ms (mi.(ms_state) =.) (ms.(ms_state) =.).
Proof. move => [?] ?. naive_solver. Qed.

Lemma set_refines_step_Some {EV} (m1 m2 : module EV) Pσi1 Pσs1 Pσi2 e:
  set_refines m1 m2 Pσi1 Pσs1 →
  (∀ σi1, Pσi1 σi1 → m1.(m_step) σi1 (Some e) Pσi2) →
  set_refines m1 m2 (λ σi, ∃ σis, Pσi1 σis ∧ σis ~{m1, tcons e tnil}~> (λ σie, σi = σie))
              (λ σs, ∃ σss, Pσs1 σss ∧ σss ~{m2, tcons e tnil}~> (λ σse, σs = σse)).
Proof.

  move => Hr Hstep κs.
  have [σi2 [? Hs]]:= Hr (tcons e κs).

  have [|?[??]]:= Hs. {
    apply: TraceStep. naive_solver. 2: by constructor; constructor. ; [done | | ].

  have [//| |σsx[? /(has_trace_cons_inv _ _)?]]:= Hr (tcons e κs) σi1. {
    apply: TraceStep; [done | | ].
    admit.
  }
  eexists σsx.
  split.
  - admit.
  -

  (*
  move => Hr ? Hstep κs.
  have [σi2 [??]]:= Hr (tcons e κs).
  eexists σi1. split. {
    eexists _. split; [done|].
    apply: TraceStep. ; [done | | ].
   *)

  move => Hr ? Hstep κs ? ? ?.
  have [//| |σsx[? /(has_trace_cons_inv _ _)?]]:= Hr (tcons e κs) σi1. {
    apply: TraceStep; [done | | ]. 2: { constructor. by constructor. }
    admit.
  }
  eexists σsx.
  split.
  - admit.
  -

Lemma set_refines_step_Some {EV} (m1 m2 : module EV) Pσi1 Pσs1 σi1 Pσi2 e:
  set_refines m1 m2 Pσi1 Pσs1 →
  Pσi1 σi1 →
  m1.(m_step) σi1 (Some e) Pσi2 →
  set_refines m1 m2 (λ σi, ∃ σis, Pσi1 σis ∧ σis ~{m1, tcons e tnil}~> (λ σie, σi = σie))
              (λ σs, ∃ σss, Pσs1 σss ∧ σss ~{m2, tcons e tnil}~> (λ σse, σs = σse)).
Proof.
  (*
  move => Hr ? Hstep κs.
  have [σi2 [??]]:= Hr (tcons e κs).
  eexists σi1. split. {
    eexists _. split; [done|].
    apply: TraceStep. ; [done | | ].
   *)
  move => Hr ? Hstep κs ? [σx [??]] ?.
  have [//| |σsx[? /(has_trace_cons_inv _ _)?]]:= Hr (tcons e κs) σx. {
    admit.
  }
  eexists σsx.
  split.
  - admit.
  -
    (* apply: TraceStep; [done | | ]. *)

set_refines mi ms Pσi Pσs

Lemma mod_filter_nil_refines {EV1 EV2} (mi ms : module EV1) (R : EV1 → option (option EV2)) σi Pσi Pσs Pσ:
  set_refines mi ms Pσi Pσs →
  Pσi σi →
  σi ~{ mod_filter mi R, tnil }~> Pσ →
  ∃ σs, Pσs σs ∧ σs ~{ mod_filter ms R, tnil }~> (λ _, True).
Proof. Admitted.

Lemma mod_filter_refines {EV1 EV2} (R : EV1 → option (option EV2)) mi ms σi σs:
  MS mi σi ⊑ MS ms σs →
  MS (mod_filter mi R) σi ⊑ MS (mod_filter ms R) σs.
Proof.
  move => /set_refines_intro /= Hr. constructor => κs /=.
  suff Hs : (
              ∀ Pσi Pσs, set_refines mi ms Pσi Pσs →
             ∀ σi, Pσi σi →
                 σi ~{ mod_filter mi R, κs }~> (λ _, True) → ∃ σs, Pσs σs ∧ σs ~{ mod_filter ms R, κs }~> (λ _, True)

            ). {
    have := Hs (σi =.) (σs =.). naive_solver.
  }
  elim: κs; clear.
  - move => Pσi Pσs Hr σi ??.
    have [//| |?[??]]:= Hr tnil σi. by constructor.
    eexists _. split;[done|]. by constructor.
  - move => κ κs IH Pσi Pσs Hr σi ? /(has_trace_cons_inv _ _ _).
    move HP: (λ σ2, ∃ P, _) => P.
    move Hκn: tnil => κn Ht.
    have {}Hκn : (κn ⊆ tnil) by naive_solver.
    elim: Ht HP Hκn. 2: {
      move => ??? κ' ?? Hstep ? IH2 Hnext ? Hsub. subst.
      have {}IH2:= IH2 _ _ ltac:(done).
      destruct κ'; simplify_eq/=. {
        move: Hnext => /trace_next_cons[? [Hsub2 ?]].
        pose proof (transitivity Hsub2 Hsub). easy.
      }
      move: Hnext => /trace_next_nil Hnext.
      inversion Hstep; simplify_eq.
      apply: IH2. admit. admit.
    }
    move => ??? HP ???. subst.
    have {HP} [?[Hstep ?]]:= HP.
    inversion Hstep; simplify_eq. destruct e => //.

    admit.
    +
    admit.
  - move => T Hdec f IH Pσi Pσs Hr σi ? /(has_trace_choice_inv _ _ _) Ht.



  →
  σ ~{ mod_filter m R, κs }~> Pσ →
  σ ~{ m, filter_trace_to_mod R κs }~> Pσ.
Proof.


Fixpoint filter_trace_choose {EV1 EV2} (n : nat) (R : EV1 → option (option EV2)) (κs : trace EV1)
         `{!EqDecision EV1} : trace (EV1) :=
  match n with
  | 0 => κs
  | S n => tchoice EV1 _ (λ e, if R e is Some None then tcons e (filter_trace_choose n R κs) else tub)
  end.

Lemma filter_trace_choose_mono {EV1 EV2} (R : EV1 → option (option EV2)) n κs1 κs2 `{!EqDecision EV1}:
  κs1 ⊆ κs2 →
  filter_trace_choose n R κs1 ⊆ filter_trace_choose n R κs2.
Proof.
  elim: n => //= ???.
  constructor => x. eapply (subtrace_choice_r x). case_match => //. case_match => //.
  constructor. naive_solver.
Qed.

Fixpoint filter_trace_to_mod {EV1 EV2} (R : EV1 → option (option EV2))
  (κs : trace EV2) `{!EqDecision EV1} `{!EqDecision EV2} : trace (EV1) :=
  match κs with
  | tnil => tchoice nat _ (λ n, filter_trace_choose n R tnil)
  | tcons κ κs => tchoice nat _ (λ n, filter_trace_choose n R (
      tchoice EV1 _ (λ e, if R e is Some e' then if e' is Some e'' then if bool_decide (e'' = κ) then
          tcons e (filter_trace_to_mod R κs) else tub else tub else tub)))
  | tchoice T Hdec f => tchoice T Hdec (λ x, filter_trace_to_mod R (f x))
  end .

Lemma filter_trace_to_mod_mono {EV1 EV2} (R : EV1 → option (option EV2)) κs1 κs2 `{!EqDecision EV1} `{!EqDecision EV2}:
  κs1 ⊆ κs2 →
  filter_trace_to_mod R κs1 ⊆ filter_trace_to_mod R κs2.
Proof.
  elim => /=.
  - done.
  - move => ?????.
    constructor => n. eapply (subtrace_choice_r n).
    apply: filter_trace_choose_mono.
    constructor => x. eapply (subtrace_choice_r x).
    case_match; [case_match|] => //. case_bool_decide => //. by econstructor.
  - move => ??????. constructor. naive_solver.
  - move => ???????. econstructor. naive_solver.
Qed.

Lemma mod_filter_to_mod {EV1 EV2} (m : module EV1) (R : EV1 → option (option EV2)) σ κs Pσ `{!EqDecision EV1} `{!EqDecision EV2}:
  σ ~{ mod_filter m R, κs }~> Pσ →
  σ ~{ m, filter_trace_to_mod R κs }~> Pσ.
Proof.
  elim; clear.
  - move => ?? κs ?.
    elim: κs => /=.
    + move => ?. constructor; [done|]. by eapply (subtrace_choice_r 0).
    + move => ??? Hs. inversion Hs.
    + move => ???? /subtrace_nil_choice_inv[x ?].
      apply: has_trace_mono; [ naive_solver | | done]. by econstructor.
  - move => ??? κ κs κs' Hs _ IH Hnext. inversion Hs; simplify_eq.
    apply: TraceStep; [done| apply: IH |]. clear IH.
    destruct e; simplify_eq/=. 2: {
      apply trace_next_nil. apply filter_trace_to_mod_mono. by apply trace_next_nil.
    }
    destruct κ. 2: {
      move: Hnext => /trace_next_nil Hnext.
      elim: Hnext => //=.
      - apply: TNchoiceR => n.
        apply: (TNchoice (S n)) => /=.
        apply: (TNchoice e) => /=. case_match; simplify_eq.
        constructor.
        constructor. done.
      - move => ?????.
        apply: TNchoiceR => n.
        apply: (TNchoice (S n)) => /=.
        apply: (TNchoice e) => /=. case_match; simplify_eq.
        constructor.
        constructor. apply: filter_trace_choose_mono.
        constructor => x. eapply (subtrace_choice_r x).
        case_match; [case_match|] => //. case_bool_decide => //.  econstructor.
        by apply: filter_trace_to_mod_mono.
      - move => ??????. constructor. done.
      - move => ???????. econstructor. done.
    }
      elim: κs Hnext => /=.
      - move => ?. econstructor.
      move: Hnext.
    }
    move: Hnext. move Hlk: (option_list _) => lκ Hnext.
    elim: Hnext Hlk.
    + destruct κ => //. admit.
    elim: κs κs' Hnext => /=.
    + admit.
      (* inversion 1; simplify_eq. destruct e; simplify_eq/=. *)
      (* admit. constructor. *)
      (* constructor. *)
    + move => ?? IH ??.
      econstructor. erewrite H0. case_match.

     mo
    elim: Hs.
    eexists _. by constructor.
  - move => ?????? Hstep ? IH ?.
    inversion Hstep; simplify_eq.
    eexists (tchoice _ _ (λ σ, ex_proj1 (IH σ _))).


Inductive filter_trace_rel {EV1 EV2} (R : EV1 → option EV2 → Prop) : list (event EV1) → list (event EV2) → Prop :=
| FTREnd :
    filter_trace_rel R [] []
| FTRStep κ κ' κs κs':
    R κ κ' →
    filter_trace_rel R κs κs' →
    filter_trace_rel R (Vis κ :: κs) (option_list (Vis <$> κ') ++ κs')
| FTRUb κs':
    filter_trace_rel R [Ub] κs'
.

Lemma mod_filter_to_mod {EV1 EV2} (m : module EV1) (R : EV1 → option EV2 → Prop) σ Pκs Pσ:
  σ ~{ mod_filter m R, Pκs }~> Pσ →
  σ ~{ m, λ κs, ∃ κs', filter_trace_rel R κs κs' ∧ Pκs κs' }~> Pσ.
Proof.
  elim.
  - move => ?????. apply: TraceEnd; [done|]. eexists []. split; [|done]. constructor.
  - move => ?????? Hstep ? IH ?. inversion Hstep; simplify_eq.
    apply: TraceStep; [done| |].
    + move => σ2 ?. apply: has_trace_mono; [by apply: IH | |done] => /=.
      move => κs [κs' [? ?]].
      eexists _. split; [|done].
      destruct e; simplify_eq/=; [|done]. by apply: FTRStep.
    + eexists _. split; [|done].
      destruct e; simplify_eq/=.
      * constructor; [done|]. apply: FTRUb.
      * apply: FTRUb.
Qed.

Lemma mod_to_mod_filter {EV1 EV2} (m : module EV1) (R : EV1 → option EV2 → Prop) σ Pκs Pκs' Pσ:
(* The first condition states that [mod_filter] does not add more
non-determinism. This condition (or maybe something slightly weaker)
sadly is necessary, because this definition of refinement allows to
commute angelic choice and visible events. Consider the modules I and S

I :       A     B
    /- 2 --- 4 --- 6
1 -a
    \- 3 --- 5 --- 7
          A     C

S :              B
         A      /- 6
1 --- 2 --- 4 -a
                \- 7
                C

and a relation R with [R A (Some A1)], [R A (Some A2)], [R B (Some B)], [R C (Some C)].
Then we have I ⊑ S but not mod_filter R I ⊑ mod_filter R S since the trace
 [A1; B] ∨ [A2; C] can be produced by mod_filter R I, but not by mod_filter R S.
The cruicial difference is that I can pick two different elements of R for A, while S
can only pick one and whatever it picks, the angelic choice could resolve in the wrong way.
 *)
  (∀ κ1 κ2 κ2', R κ1 κ2 → R κ1 κ2' → κ2 = κ2') →
  σ ~{ m, Pκs }~> Pσ → (∀ κs, Pκs κs → ∃ κs', filter_trace_rel R κs κs' ∧ Pκs' κs') →
  σ ~{ mod_filter m R, Pκs' }~> Pσ.
Proof.
  move => HR Ht. elim: Ht Pκs'.
  - move => ?????? HP. have [//|? [Hf ?]]:= HP [] _. inversion Hf; simplify_eq. by apply: TraceEnd.
  - move => σ1?? Pσ3 κ ??? IH ? Pκs' HP.
    destruct κ; simplify_eq/=.
    + have [?[Hf ?]]:= HP _ ltac:(done).
      inversion Hf; simplify_eq.
      apply: TraceStep; [ econstructor; [done | simpl;done] | | done].
      move => σ2 ?.
      apply: (has_trace_mono (λ κs, Pκs' (option_list (Vis <$> κ') ++ κs))); [apply: IH;[done|] | done | done].
      move => ? HP'.
      have [?[ Hf' ?]]:= HP _ HP'. inversion Hf'; simplify_eq.
      eexists _. split; [done|]. have := HR _ _ _ H1 H2. naive_solver.
    + have [?[??]]:= HP _ ltac:(done).
      apply: TraceStep; [ by econstructor | | simplify_eq/=; done]; simplify_eq/=.
      move => σ2 ?. by apply: IH.
Qed.

Lemma mod_filter_refines {EV1 EV2} (m1 m2 : module EV1) (R : EV1 → option EV2 → Prop) σ1 σ2 :
  (∀ κ1 κ2 κ2', R κ1 κ2 → R κ1 κ2' → κ2 = κ2') →
  MS m1 σ1 ⊑ MS m2 σ2 →
  MS (mod_filter m1 R) σ1 ⊑ MS (mod_filter m2 R) σ2.
Proof.
  move => ? [/= Hr]. constructor => /= ? /mod_filter_to_mod/Hr Hm. apply: mod_to_mod_filter; [done|done|].
  naive_solver.
Qed.


(*** link *)
Record link_mediator EV1 EV2 EV3 := {
  lm_state : Type;
  lm_initial : lm_state;
  lm_step : lm_state → option EV1 → option EV2 → option EV3 → lm_state → Prop;
}.
Arguments lm_state {_ _ _}.
Arguments lm_initial {_ _ _}.
Arguments lm_step {_ _ _}.

Definition stateless_mediator {EV1 EV2 EV3} (R : option EV1 → option EV2 → option EV3 → Prop) : link_mediator EV1 EV2 EV3 := {|
  lm_state := unit;
  lm_initial := tt;
  lm_step _ e1 e2 e3 _:= R e1 e2 e3;
|}.

Inductive link_step {EV1 EV2 EV3} (m1 : module EV1) (m2 : module EV2) (M : link_mediator EV1 EV2 EV3) :
  m1.(m_state) * m2.(m_state) * M.(lm_state) → option EV3 → m1.(m_state) * m2.(m_state) * M.(lm_state) → Prop :=
| LinkStepL σ1 σ2 e1 e' σ1' σm σm':
    m1.(m_step) σ1 e1 σ1' →
    (* TODO: is there a better way to formulate this? E.g. assume
    that there is no R None None Some in the theorem? *)
    (if e1 is Some es1 then M.(lm_step) σm e1 None e' σm' else e' = None ∧ σm' = σm) →
    link_step m1 m2 M (σ1, σ2, σm) e' (σ1', σ2, σm')
| LinkStepR σ1 σ2 e2 e' σ2' σm σm':
    m2.(m_step) σ2 e2 σ2' →
    (if e2 is Some es2 then M.(lm_step) σm None e2 e' σm' else e' = None ∧ σm' = σm) →
    link_step m1 m2 M (σ1, σ2, σm) e' (σ1, σ2', σm')
| LinkStepBoth σ1 σ2 e1 e2 e' σ1' σ2' σm σm':
    m1.(m_step) σ1 (Some e1) σ1' →
    m2.(m_step) σ2 (Some e2) σ2' →
    M.(lm_step) σm (Some e1) (Some e2) e' σm' →
    link_step m1 m2 M (σ1, σ2, σm) e' (σ1', σ2', σm').

Definition link {EV1 EV2 EV3} (m1 : module EV1) (m2 : module EV2) (M : link_mediator EV1 EV2 EV3) : module EV3 := {|
  m_state := m1.(m_state) * m2.(m_state) * M.(lm_state);
  m_step := (link_step m1 m2 M);
  m_is_ub σ := m1.(m_is_ub) σ.1.1 ∨ m2.(m_is_ub) σ.1.2;
|}.


Lemma link_empty_steps_l {EV1 EV2 EV3} m1 m2 (M : link_mediator EV1 EV2 EV3) σ1 Pσ1' σ2 σm  :
  σ1 ~{ m1, [] }~> Pσ1' →
  (σ1, σ2, σm) ~{ link m1 m2 M, [] }~> (λ '(σ1', σ2', σm'), Pσ1' σ1' ∧ σ2' = σ2 ∧ σm = σm').
Proof.
  move Hκ: ([]) => κ Hsteps.
  elim: Hsteps Hκ.
  - move => ????. by apply: TraceEnd.
  - move => ??? [] //= ?????. apply: (TraceStepNone); [ | naive_solver]. by econstructor.
  - move => ?????. apply: TraceUb. naive_solver.
Qed.

Lemma link_empty_steps_r {EV1 EV2 EV3} m1 m2 (M : link_mediator EV1 EV2 EV3) σ1 Pσ2' σ2 σm :
  σ2 ~{ m2, [] }~> Pσ2' →
  (σ1, σ2, σm) ~{ link m1 m2 M, [] }~> (λ '(σ1', σ2', σm'), σ1' = σ1 ∧ Pσ2' σ2' ∧ σm = σm').
Proof.
  move Hκ: ([]) => κ Hsteps.
  elim: Hsteps Hκ.
  - move => ????. by apply: TraceEnd.
  - move => ??? [] //= ?????. apply: (TraceStepNone); [ | naive_solver]. by econstructor.
  - move => ?????. apply: TraceUb. naive_solver.
Qed.

Inductive link_trace_related {EV1 EV2 EV3} (M : link_mediator EV1 EV2 EV3) : M.(lm_state) → list (event EV1) → list (event EV2) → list (event EV3) → M.(lm_state) → Prop :=
| LinkTraceRelNil σm:
    link_trace_related M σm [] [] [] σm
| LinkTraceRelUbL κs2 κs3 σm σm2:
    link_trace_related M σm [Ub] κs2 κs3 σm2
| LinkTraceRelUbR κs1 κs3 σm σm2:
    link_trace_related M σm κs1 [Ub] κs3 σm2
| LinkTraceRelL κ1 κ1' κs1 κs2 κs3 σm σm' σm2:
    link_trace_related M σm' κs1 κs2 κs3 σm2 →
    M.(lm_step) σm (Some κ1) None κ1' σm' →
    link_trace_related M σm ([Vis κ1] ++ κs1) κs2 (option_list (Vis <$> κ1') ++ κs3) σm2
| LinkTraceRelR κ2 κ2' κs1 κs2 κs3 σm σm' σm2:
    link_trace_related M σm' κs1 κs2 κs3 σm2 →
    M.(lm_step) σm None (Some κ2) κ2' σm' →
    link_trace_related M σm κs1 ([Vis κ2] ++ κs2) (option_list (Vis <$> κ2') ++ κs3) σm2
| LinkTraceRelBoth κ1 κ2 κ3 κs1 κs2 κs3 σm σm' σm2:
    link_trace_related M σm' κs1 κs2 κs3 σm2 →
    M.(lm_step) σm (Some κ1) (Some κ2) κ3 σm' →
    link_trace_related M σm ([Vis κ1] ++ κs1) ([Vis κ2] ++ κs2) (option_list (Vis <$> κ3) ++ κs3) σm2
.

Lemma link_trace_related_create {EV1 EV2 EV3} (M : link_mediator EV1 EV2 EV3) m1 m2 κs3 σ1 :
  σ1 ~{ link m1 m2 M, κs3 }~> (λ _, True) →
  ∃ κs1 κs2 σm', link_trace_related M σ1.2 κs1 κs2 κs3 σm' ∧
  σ1.1.1 ~{ m1, κs1 }~> (λ _, True) ∧
  σ1.1.2 ~{ m2, κs2 }~> (λ _, True).
Proof.
  elim; clear.
  - move => σ ? ?. eexists [], [], _. split_and!; by constructor.
  - move => σ1 σ2 Pσ3 κ κs Hstep Hsteps [κs1 [κs2 [σm' [Hlink [Hκ1 Hκ2]]]]].
    inversion Hstep; clear Hstep; simplify_eq.
    + eexists (option_list (Vis <$> e1) ++ κs1), κs2, _.
      split_and! => //; destruct e1; destruct_and?; simplify_eq/= => //; rewrite ?right_id //. by econstructor.
      * by apply: TraceStepSome.
      * by apply: TraceStepNone.
    + eexists κs1, (option_list (Vis <$> e2) ++ κs2), _.
      split_and! => //; destruct e2; destruct_and?; simplify_eq/= => //; rewrite ?right_id //. by econstructor.
      * by apply: TraceStepSome.
      * by apply: TraceStepNone.
    + eexists ([Vis e1] ++ κs1), ([Vis e2] ++ κs2), _.
      split_and!.
      * by apply: LinkTraceRelBoth.
      * by apply: TraceStepSome.
      * by apply: TraceStepSome.
  - move => [σ1 σm] κs σ2 /= [] Hub.
    + eexists [Ub], [], σm => /=. split_and!. by econstructor.
      * by apply: TraceUb.
      * by apply: TraceEnd.
    + eexists [], [Ub], σm. split_and!. by econstructor.
      * by apply: TraceEnd.
      * by apply: TraceUb.
Qed.

Lemma link_trace_related_step {EV1 EV2 EV3} (M : link_mediator EV1 EV2 EV3) m1 m2 κs1 κs2 κs3 σ1 σ2 σm σm':
  link_trace_related M σm κs1 κs2 κs3 σm' →
  σ1 ~{ m1, κs1 }~> (λ _, True) →
  σ2 ~{ m2, κs2 }~> (λ _, True) →
  (σ1, σ2, σm) ~{ link m1 m2 M, κs3 }~> (λ _, True).
Proof.
  move => Hrel.
  elim: Hrel σ1 σ2; clear.
  - move => σm σ1 σ2 Hstep1 Hstep2.
    apply: (has_trace_trans [] []). { by apply: link_empty_steps_l. }
    move => [[??]?] [?[??]]. subst.
    apply: has_trace_mono; [|done]. by apply: link_empty_steps_r.
  - move => ?????? /has_trace_ub_inv??.
    apply: (has_trace_trans []). { by apply: link_empty_steps_l. }
    move => [[??]?] [?[??]]. done.
  - move => ??????? /has_trace_ub_inv?.
    apply: (has_trace_trans []). { by apply: link_empty_steps_r. }
    move => [[??]?] [?[??]]. done.
  - move => κ1 κ1' κs1 κs2 κs3 ??? ? IH HR σ1 σ2 /= /(has_trace_cons_inv _ _)??.
    apply: (has_trace_trans []). { by apply: link_empty_steps_l. }
    move => [[??]?] [[?[??]][??]] /=. subst.
    apply: TraceStep; [ | by apply: IH].
    by apply: LinkStepL.
  - move => κ1 κ1' κs1 κs2 κs3 ??? ? IH HR σ1 σ2 /= ?/(has_trace_cons_inv _ _)?.
    apply: (has_trace_trans []). { by apply: link_empty_steps_r. }
    move => [[??]?] [?[[?[??]]?]] /=. subst.
    apply: TraceStep; [ | by apply: IH].
    by apply: LinkStepR.
  - move => κ1 κ2 κ3 κs1 κs2 κs3 ??? ? IH HR σ1 σ2 /= /(has_trace_cons_inv _ _)? /(has_trace_cons_inv _ _)?.
    apply: (has_trace_trans []). { by apply: link_empty_steps_l. }
    move => [[??]?] [[?[??]][??]] /=. subst.
    apply: (has_trace_trans []). { by apply: link_empty_steps_r. }
    move => [[??]?] [?[[?[??]]?]] /=. subst.
    apply: TraceStep; [ | by apply: IH].
    by apply: LinkStepBoth.
Qed.

Lemma refines_horizontal {EV1 EV2 EV3} (m1 m2 m1' m2' : module _) σ1 σ2 σ1' σ2' (M : link_mediator EV1 EV2 EV3) :
  MS m1 σ1 ⊑ MS m1' σ1' →
  MS m2 σ2 ⊑ MS m2' σ2' →
  MS (link m1 m2 M) (σ1, σ2, M.(lm_initial)) ⊑
  MS (link m1' m2' M) (σ1', σ2', M.(lm_initial)).
Proof.
  move => [Hr1] [Hr2].
  constructor => κs /= /link_trace_related_create [?[?[?[?[??]]]]].
  apply: link_trace_related_step; [done|..].
  - by apply: Hr1.
  - by apply: Hr2.
Qed.

(*** has_non_ub_trace *)
Inductive has_non_ub_trace {EV} (m : module EV) : m.(m_state) → list EV → m.(m_state) → Prop :=
| NUBTraceEnd σ:
    has_non_ub_trace m σ [] σ
| NUBTraceStep σ1 σ2 σ3 κ κs:
    m.(m_step) σ1 κ σ2 →
    has_non_ub_trace m σ2 κs σ3 →
    has_non_ub_trace m σ1 (option_list κ ++ κs) σ3
.
Notation " σ '~{' m , κ '}~>ₙ' σ' " := (has_non_ub_trace m σ κ σ') (at level 40).
Notation " σ '~{' m , κ '}~>ₙ' - " := (∃ σ', has_non_ub_trace m σ κ σ') (at level 40).

Lemma NUBTraceStepNone {EV} κs (m : module EV) σ2 σ1 σ3 :
  m.(m_step) σ1 None σ2 →
  σ2 ~{ m, κs }~>ₙ σ3 →
  σ1 ~{ m, κs }~>ₙ σ3.
Proof. move => ??. by apply: (NUBTraceStep _ _ _ _ None). Qed.

Lemma NUBTraceStepSome {EV} κs (m : module EV) σ2 σ1 σ3 κ :
  m.(m_step) σ1 (Some κ) σ2 →
  σ2 ~{ m, κs }~>ₙ σ3 →
  σ1 ~{ m, κ :: κs }~>ₙ σ3.
Proof. move => ??. by apply: (NUBTraceStep _ _ _ _ (Some _)). Qed.

Lemma has_non_ub_trace_trans {EV} κs1 κs2 (m : module EV) σ1 σ2 σ3 :
  σ1 ~{ m, κs1 }~>ₙ σ2 →
  σ2 ~{ m, κs2 }~>ₙ σ3 →
  σ1 ~{ m, κs1 ++ κs2 }~>ₙ σ3.
Proof.
  elim => //.
  move => ?????????. rewrite -app_assoc. econstructor; eauto.
Qed.

Lemma has_non_ub_trace_add_empty {EV} κs1 (m : module EV) σ1 σ2 :
  σ1 ~{ m, κs1 ++ [] }~>ₙ σ2 →
  σ1 ~{ m, κs1 }~>ₙ σ2.
Proof. by rewrite -{2}[κs1](right_id_L [] (++)). Qed.

Lemma has_trace_to_non_ub_trace EV (m : module EV) σ1 κs Pσ2:
  σ1 ~{ m, κs }~> Pσ2 →
  ∃ κs' σ2', Vis <$> κs' `prefix_of` κs ∧ σ1 ~{ m, κs' }~>ₙ σ2' ∧
             ((Vis <$> κs' = κs ∧ Pσ2 σ2') ∨ m.(m_is_ub) σ2').
Proof.
  elim.
  - move => ?. eexists [], _. naive_solver constructor.
  - move => ??? κ ??? [κs' [σ2' [?[??]]]]. eexists (option_list κ ++ κs'), σ2'.
    split_and! => //.
    + destruct κ => //. by apply: prefix_cons.
    + by econstructor.
    + destruct κ; naive_solver.
  - move => ????. eexists [], _. split_and! => //=.
    + by apply prefix_nil.
    + by constructor.
    + by right.
Qed.

(*** has_no_behavior *)
Definition has_no_behavior {EV} (m : module EV) (σ : m.(m_state)) :=
  ∀ σ' κs, σ ~{ m, κs }~> σ' → κs = [].

Lemma no_behavior_step {EV} (m : module EV) σ:
  (∀ e σ', m.(m_step) σ e σ' → e = None ∧ has_no_behavior m σ') → ¬(m_is_ub m σ) → has_no_behavior m σ.
Proof. move => Hstep ??? Htrace. inversion Htrace; simplify_eq/= => //. efeed pose proof Hstep => //. naive_solver. Qed.

(*** state_set *)
Definition power_reach {EV} (m : module EV) (σs : propset m.(m_state)) (κs : list (event EV)) : propset m.(m_state) :=
  {[ σ2 | ∃ σ1, σ1 ∈ σs ∧ σ1 ~{ m, κs }~> (σ2 =.) ]}.

Global Instance power_reach_proper {EV} (m : module EV) :
  Proper ((≡) ==> (=) ==> (≡)) (power_reach m).
Proof. move => ?? ? ?? ?. set_solver. Qed.

Global Instance power_reach_subseteq_proper {EV} (m : module EV) :
  Proper ((⊆) ==> (=) ==> (⊆)) (power_reach m).
Proof. move => ?? ? ?? ?. set_solver. Qed.

Lemma power_reach_refl {EV} (m : module EV) σs:
  σs ⊆ power_reach m σs [].
Proof. set_unfold. move => ??. eexists _. split; [done|]. by apply: TraceEnd. Qed.

Lemma power_reach_trans {EV} κs1 κs2 (m : module EV) σs:
  (* TODO: one can prove an equivalence using has_trace_inv *)
  power_reach m (power_reach m σs κs1) κs2 ⊆ power_reach m σs (κs1 ++ κs2).
Proof.
  set_unfold => ?.
  move => [? [[?[??]]?]]. eexists _. split; [done|]. apply: has_trace_trans; [done|naive_solver].
Qed.

Lemma elem_of_power_reach {EV} (m : module EV) σ σ' σs κs:
  σ' ∈ σs →
  σ' ~{ m, κs }~> (σ =.) →
  σ ∈ power_reach m σs κs.
Proof. move => ?. eexists _. naive_solver. Qed.

Definition power_module {EV} (m : module EV) : module EV := {|
  m_state := propset m.(m_state);
  m_step σs1 κ σs2 :=
    (σs2 ≡ power_reach m σs1 (option_list (Vis <$> κ))) ∧ ∃ σ, σ ∈ σs2;
  m_is_ub σs := ∃ σ, σ ∈ σs ∧ m.(m_is_ub) σ;
|}.

Lemma power_step_mono {EV} (m : module EV) σ1 σ2 σ κ:
  m_step (power_module m) σ1 κ σ →
  σ1 ⊆ σ2 →
  ∃ σ', σ ⊆ σ' ∧ m_step (power_module m) σ2 κ σ'.
Proof. move => [Heq ?] ?. eexists _. split; [|split;[done|]]; set_solver. Qed.

Lemma power_mono {EV} (m : module EV) σ1 σ2 κs:
  σ1 ~{ power_module m, κs }~> (λ _, True) →
  σ1 ⊆ σ2 →
  σ2 ~{ power_module m, κs }~> (λ _, True).
Proof.
  move HPσ: (λ _, True) => Pσ.
  move => HT. elim: HT σ2 HPσ.
  - move => ???? <- ?. by apply: TraceEnd.
  - move => ??????? IH ???. subst.
    have [?[??]]:= power_step_mono _ _ _ _ _ ltac:(done) ltac:(done).
    apply: TraceStep; [done|]. by apply: IH.
  - move => ???????. apply: TraceUb. simplify_eq/=. set_solver.
Qed.

Lemma power_elim {EV} (m : module EV) Pσ κs:
  Pσ ~{ power_module m, κs }~> (λ _, True) →
  (∃ σ, σ ∈ Pσ) →
  ∃ σ, σ ∈ Pσ ∧ σ ~{ m, κs }~> (λ _, True).
Proof.
  elim.
  - move => ??? [??]. eexists _. split. 2: by apply: TraceEnd. done.
  - move => ????? [Heq [? Hin]] ? IH [??].
    move: Hin. rewrite Heq => -[?[??]].
    case: IH. { set_unfold. naive_solver. }
    move => ?. rewrite Heq. move => [[?[??]]?].
    eexists _. split. 2: apply: has_trace_trans; [done|]. done. naive_solver.
  - move => ??? [?[??]] [??]. eexists _.
    split. 2: by apply: TraceUb. done.
Qed.

Lemma power_elim_singleton {EV} (m : module EV) σ κs:
  {[σ]} ~{ power_module m, κs }~> (λ _, True) →
  σ ~{ m, κs }~> (λ _, True).
Proof. move => /power_elim -[|??]; set_solver. Qed.

Lemma power_intro {EV} (m : module EV) Pσ σ κs:
  σ ~{ m, κs }~> (λ _, True) →
  σ ∈ Pσ → Pσ ~{ power_module m, κs }~> (λ _, True).
Proof.
  move => Htrace.
  elim: Htrace Pσ.
  - move => ? Pσ ?. move => ??. by apply: TraceEnd.
  - move => ??? κ ??? IH ??.
    apply: TraceStep.
    + split; [ done|]. set_unfold.
      eexists _, _. split; [done|].
      apply: TraceStep'; [done| | by apply: TraceEnd].
        by rewrite right_id.
    + apply: IH. set_unfold.
      eexists _. split => //.
      apply: TraceStep'; [done| | by apply: TraceEnd].
        by rewrite right_id.
  - move => ??????.
    apply: TraceUb => /=. naive_solver.
Qed.
Lemma power_intro_singleton {EV} (m : module EV) σ κs:
  σ ~{ m, κs }~> (λ _, True) →
  {[σ]} ~{ power_module m, κs }~> (λ _, True).
Proof. move => ?. apply: power_intro; set_solver. Qed.

Lemma power_nil {EV} (m : module EV) σs Pσ:
  σs ~{ power_module m, [] }~> Pσ →
  ∃ σs', σs' ⊆ (power_reach m σs []) ∧ (m_is_ub (power_module m) σs' ∨ Pσ σs').
Proof.
  move Hκ: [] => κ Htrace.
  elim: Htrace Hκ; clear.
  - move => σs ???. eexists σs. split; [|naive_solver]. by apply: power_reach_refl.
  - move => ??? [//|] ? [Heq [? Hin]] ? IH /= ?.
    have [//|σs'[? Hor]]:= IH.
    eexists σs'. split; [|done].
    etrans; [done|]. rewrite Heq /=. by apply: power_reach_trans.
  - move => ??? ??. subst. eexists _. split; [| by left].
    by apply: power_reach_refl.
Qed.

Definition state_set_refines {EV} (mimpl mspec : module EV) (σi : mimpl.(m_state)) (σs : propset mspec.(m_state)) : Prop :=
  (∃ σ, σ ∈ σs) ∧ ∀ κs, σi ~{ mimpl, κs }~> (λ _, True) → σs ~{ power_module mspec, κs }~> (λ _, True).


Lemma inv_set_implies_refines {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → propset m2.(m_state) → Prop):
  inv m1.(ms_state) {[ m2.(ms_state) ]} →
  (∀ σi1 σs1 σi2 e, inv σi1 σs1 → m_ub_step m1 σi1 e σi2 →
      σs1 ~{ power_module m2, option_list e }~> (λ σs2, inv σi2 σs2)) →
  m1 ⊑ m2.
Proof.
  move => Hinvinit Hinvstep.
  constructor => // κs.
  move: m1.(ms_state) Hinvinit => σi1 Hinv Hsteps.
  have : ({[ms_state m2]} ~{ power_module m2, κs }~> (λ _, True)). 2: {
    apply: power_elim_singleton.
  }
  move: {[ m2.(ms_state) ]} Hinv => σs1 Hinv.
  elim: Hsteps σs1 Hinv => {σi1 κs}.
  - move => ?????. by apply: TraceEnd.
  - move => σi1 σi2 σi3 κ κs Hstep Hsteps IH σs1 Hinv.
    have {}Hs := Hinvstep _ _ _ _ Hinv ltac:(by constructor).
    apply: has_trace_trans;[done|] => ? /=?.
    by apply: IH.
  - move => ??? Hs σs Hinv.
    have /has_trace_ub_inv? := Hinvstep _ _ _ _ Hinv ltac:(by constructor).
    by apply: (has_trace_trans []).
Qed.

Lemma state_set_refines_inhabited {EV} (m1 m2 : module EV) σi σs:
  state_set_refines m1 m2 σi σs → ∃ σ, σ ∈ σs.
Proof. by move => []. Qed.

Lemma state_set_refines_initial {EV} (m1 m2 : mod_state EV):
  m1 ⊑ m2 →
  state_set_refines m1 m2 (ms_state m1) {[ms_state m2]}.
Proof. move => [Hr]. split; [set_solver|]. move => ? /Hr/power_intro_singleton?. done. Qed.

Lemma state_set_refines_step_Some {EV} (m1 m2 : module EV) σi1 σs1 σi2 e:
  state_set_refines m1 m2 σi1 σs1 →
  m1.(m_step) σi1 (Some e) σi2 →
  state_set_refines m1 m2 σi2 (power_reach m2 σs1 [Vis e]).
Proof.
  move => [[??] Hstate] Hstep. split. {
    have := Hstate [Vis e] ltac:(by apply: TraceStepSome; [|apply: TraceEnd]).
    move => /(has_trace_cons_inv _ _)/power_nil[?[?[[σ[??]]|[?[[Heq[??]]?]]]]].
    -- eexists σ.
       apply: elem_of_subseteq_1; [apply: (power_reach_trans [])|].
       apply: elem_of_power_reach; [ by apply: elem_of_subseteq_1|].
         by apply: TraceUb.
    -- eexists _.
       apply: elem_of_subseteq_1; [|done]. rewrite Heq.
       etrans; [| apply: (power_reach_trans [])].
         by apply: power_reach_subseteq_proper.
  }
  move => κs ?.
  have /(has_trace_cons_inv _ _):= Hstate (Vis e :: κs) ltac:(by apply: TraceStepSome).
  move => /power_nil [? [? Hor]].
  apply: power_mono; [| apply: (power_reach_trans [])].
  apply: power_mono; [|by apply: power_reach_subseteq_proper].
  case: Hor.
  - move => [?[??]]. apply: TraceUb. eexists _. split; [|done].
    eexists _. split; [done|]. by apply: TraceUb.
  - move => [?[[??]?]]. apply: power_mono; [done|]. set_solver.
Qed.

Lemma state_set_refines_step_None {EV} (m1 m2 : module EV) σi1 σs1 σi2:
  state_set_refines m1 m2 σi1 σs1 →
  m1.(m_step) σi1 None σi2 →
  state_set_refines m1 m2 σi2 σs1.
Proof. move => [? Hstate] Hstep. split; [done|] => κs ?. apply: Hstate. by apply: TraceStepNone. Qed.

Lemma state_set_refines_step {EV} (m1 m2 : module EV) σi1 σs1 σi2 κ:
  state_set_refines m1 m2 σi1 σs1 →
  m1.(m_step) σi1 κ σi2 →
  state_set_refines m1 m2 σi2 (power_reach m2 σs1 (option_list (Vis <$> κ))).
Proof.
  move => Hstate ?. destruct κ.
  - by apply: state_set_refines_step_Some.
  - move: Hstate => [[??] Hstate].
    split. { eexists _. apply: elem_of_power_reach; [done|]. by apply: TraceEnd. }
    move => κs ?.
    have ?:= Hstate (κs) ltac:(by apply: TraceStepNone).
    apply: power_mono; [done|]. apply: power_reach_refl.
Qed.

Lemma state_set_refines_ub {EV} (m1 m2 : module EV) σi1 σs1:
  state_set_refines m1 m2 σi1 σs1 →
  m1.(m_is_ub) σi1 →
  σs1 ~{ power_module m2, [] }~> (λ _, False).
Proof.
  move => [? Hstate] ?.
  have /has_trace_ub_inv ?:= Hstate [Ub] ltac:(by apply: TraceUb).
  by apply: (has_trace_trans []).
Qed.

Lemma state_set_refines_ub_step {EV} (m1 m2 : module EV) σi1 σs1 σi2 e:
  state_set_refines m1 m2 σi1 σs1 →
  m_ub_step m1 σi1 e σi2 →
  σs1 ~{ power_module m2, option_list e }~> (λ σs2 : m_state (power_module m2), state_set_refines m1 m2 σi2 σs2).
Proof.
  move => Hstate. inversion 1; simplify_eq.
  - have Hstate' := state_set_refines_step _ _ _ _ _ _ ltac:(done) ltac:(done).
    move: (Hstate') => /state_set_refines_inhabited?.
    apply: (TraceStep' _ []); [done| by rewrite right_id |].
    apply: TraceEnd. by apply: state_set_refines_step.
  - apply: (has_trace_trans []); [ by apply: state_set_refines_ub | done].
Qed.

Lemma refines_implies_inv_set {EV} (m1 m2 : mod_state EV):
  m1 ⊑ m2 →
  ∃ (inv : m1.(m_state) → propset m2.(m_state) → Prop),
  inv m1.(ms_state) {[ m2.(ms_state) ]} ∧
  (∀ σi1 σs1 σi2 e, inv σi1 σs1 → m_ub_step m1 σi1 e σi2 →
      σs1 ~{ power_module m2, option_list e }~> (λ σs2, inv σi2 σs2)).
Proof.
  move => Href.
  eexists (state_set_refines m1 m2).
  split_and!.
  - by apply: state_set_refines_initial.
  - move => ????. apply: state_set_refines_ub_step.
Qed.


(*
Definition state_set_refines {EV} (mimpl mspec : module EV) (σi : mimpl.(m_state)) (σs : propset mspec.(m_state)) : Prop :=
  ∀ κs, σi ~{ mimpl, κs }~> (λ _, True) → ∃ σs1, σs1 ∈ σs ∧ σs1 ~{ mspec, κs }~> (λ _, True).

Lemma inv_set_implies_refines {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → propset m2.(m_state) → Prop):
  inv m1.(ms_state) {[ m2.(ms_state) ]} →
  (∀ σi σs, inv σi σs → ∃ σ, σ ∈ σs) →
  (∀ σi σs, inv σi σs → m1.(m_is_ub) σi → ∃ σs1, σs1 ∈ σs ∧ σs1 ~{ m2, [] }~> (λ _, False)) →
  (∀ σi1 σs1 σi2 e, inv σi1 σs1 → m1.(m_step) σi1 e σi2 →
      ∃ σs2, inv σi2 σs2 ∧ σs2 ⊆ {[ σ2 | ∃ σ1, σ1 ∈ σs1 ∧ σ1 ~{ m2, option_list (Vis <$> e) }~> (σ2 =.) ]}) →
  m1 ⊑ m2.
Proof.
  move => Hinvinit Hinvnonempty Hinvsafe Hinvstep.
  constructor => // κs.
  move: m1.(ms_state) Hinvinit => σi1 Hinv Hsteps.
  have : (∃ σs1, σs1 ∈ ({[ms_state m2]} : propset _) ∧ σs1 ~{ m2, κs }~> (λ _, True)); last set_solver.
  move: {[ m2.(ms_state) ]} Hinv => σs1 Hinv.
  elim: Hsteps σs1 Hinv => {σi1 κs}.
  - move => ???? /Hinvnonempty [??]. eexists _. split => //. by apply: TraceEnd.
  - move => σi1 σi2 σi3 κ κs Hstep Hsteps IH σs1 Hinv.
    have [σs2 [Hinv2 Hsub]]:= Hinvstep _ _ _ _ Hinv Hstep.
    have [σs3 [Hin ?]]:= IH _ Hinv2.
    have [σ1 [??]]:= Hsub _ Hin.
    eexists _. split => //. apply: has_trace_trans; [done|] => ??.
    by subst.
  - move => ??? /Hinvsafe Hs σs Hinv.
    have [? [? ?]]:= Hs _ Hinv.
    eexists _. split => //.
    by apply: (has_trace_trans []).
Qed.

Lemma state_set_refines_initial {EV} (m1 m2 : mod_state EV):
  m1 ⊑ m2 →
  state_set_refines m1 m2 (ms_state m1) {[ms_state m2]}.
Proof. move => [Hr] ??. naive_solver. Qed.

Lemma state_set_refines_step {EV} (m1 m2 : module EV) σi1 σs1 σi2 e:
  state_set_refines m1 m2 σi1 σs1 →
  m1.(m_step) σi1 e σi2 →
  state_set_refines m1 m2 σi2 {[ σ2 | ∃ σ1, σ1 ∈ σs1 ∧ σ1 ~{ m2, option_list (Vis <$> e) }~> (σ2 =.) ]}.
Proof.
  move => Hinv Hstep κs Hκs.
  have [|? [? /has_trace_app_inv?]]:= Hinv (option_list (Vis <$> e) ++ κs).
  (* have [|? [? ?]]:= Hinv (option_list (Vis <$> e) ++ κs). *)
  { by apply: TraceStep. }
  set_unfold.
  eexists _.
  split.
  eexists _. split => //. apply: has_trace_mono.
  done.
  move => ?/=.
Admitted.

Lemma state_set_refines_step_None {EV} (m1 m2 : module EV) σi1 σs1 σi2:
  state_set_refines m1 m2 σi1 σs1 →
  m1.(m_step) σi1 None σi2 →
  state_set_refines m1 m2 σi2 σs1.
Proof.
  move => Hinv Hstep κs Hκs.
  have [|? [? ?]]:= Hinv κs.
  { by apply: TraceStepNone. }
  set_solver.
Qed.

Lemma state_set_refines_non_empty {EV} (m1 m2 : module EV) σi σs:
  state_set_refines m1 m2 σi σs → ∃ σ, σ ∈ σs.
Proof.
  move => Hs.
  have [|?[??]]:= Hs []. by apply: TraceEnd.
  naive_solver.
Qed.

Lemma state_set_refines_ub {EV} (m1 m2 : module EV) σi σs:
  state_set_refines m1 m2 σi σs →
  m1.(m_is_ub) σi →
  ∃ σ, σ ∈ σs ∧ σ ~{ m2, [] }~> (λ _, False).
Proof.
  move => Hs Hub.
  have [|?[?/has_trace_ub_inv?]]:= Hs [Ub]. by apply: TraceUb.
  set_solver.
Qed.

Lemma refines_implies_inv_set {EV} (m1 m2 : mod_state EV):
  m1 ⊑ m2 →
  ∃ (inv : m1.(m_state) → propset m2.(m_state) → Prop),
  inv m1.(ms_state) {[ m2.(ms_state) ]} ∧
  (∀ σi σs, inv σi σs → ∃ σ, σ ∈ σs) ∧
  (∀ σi σs, inv σi σs → m1.(m_is_ub) σi → ∃ σs1, σs1 ∈ σs ∧ σs1 ~{ m2, [] }~> (λ _, False)) ∧
  (∀ σi1 σs1 σi2 e, inv σi1 σs1 → m1.(m_step) σi1 e σi2 →
      ∃ σs2, inv σi2 σs2 ∧ σs2 ⊆ {[ σ2 | ∃ σ1, σ1 ∈ σs1 ∧ σ1 ~{ m2, option_list (Vis <$> e) }~> (σ2 =.) ]}).
Proof.
  move => Href.
  eexists (state_set_refines m1 m2).
  split_and!.
  - by apply: state_set_refines_initial.
  - by apply: state_set_refines_non_empty.
  - move => σi σs Hinv Hub. by apply: state_set_refines_ub.
  - move => σi1 σs1 σi2 e Hinv Hstep.
    eexists _. split_and!; last reflexivity.
    by apply: state_set_refines_step.
Qed.
*)
(*** wp': equivalent definition of refines *)
Inductive wp' {EV} (m1 : module EV) (m2 : mod_state EV) : nat → m1.(m_state) -> list (event EV) -> Prop :=
| Wp_step' σi1 κs n:
       (∀ σi2 κ n', n = S n' → m_ub_step m1 σi1 κ σi2 ->
         m2.(ms_state) ~{ m2, κs ++ option_list κ }~> (λ _, True) ∧
         wp' m1 m2 n' σi2 (κs ++ option_list κ)) ->
    wp' m1 m2 n σi1 κs
.

Lemma wp'_weaken {EV} (m1 : module EV) m2 κs σ n n':
  n' ≤ n →
  wp' m1 m2 n σ κs →
  wp' m1 m2 n' σ κs.
Proof.
  elim: n' n σ κs.
  - move => ???? Hwp. constructor. done.
  - move => n' IH [|n] σ κs ? Hwp. lia.
    inversion Hwp as [??? Hwp']; simplify_eq.
    constructor => σi2 κ ?[?]?. subst.
    have [//|? ?]:= Hwp' σi2 κ _ ltac:(done).
    split; [done|]. apply: IH; [|done]. lia.
Qed.

Lemma forall_to_ex A B (P : A → B → Prop) (Q : B → Prop):
 (∃ n : A, ∀ y : B, P n y → Q y) -> ∀ y : B, ((∀ n : A, P n y) → Q y).
Proof. naive_solver. Qed.

Lemma wp'_implies_refines {EV} (m1 m2 : mod_state EV):
  (∀ n, wp' m1 m2 n m1.(ms_state) []) →
  m1 ⊑ m2.
Proof.
  move => Hwp.
  constructor => κs.
  move: m1.(ms_state) Hwp => σi1.
  have : (has_trace m2 m2.(ms_state) [] (λ _, True)). { by apply: TraceEnd. }
  (* move: {2}m2.(ms_state) => σs1. *)
  have : κs = [] ++ κs by [].
  move: ([]) => κstart. move: {2 3}(κs) => κend.
  move => Hκ Hs Hwp Hsteps.
  move: κstart Hwp Hκ Hs. apply: forall_to_ex.
  elim: Hsteps => {σi1 κend}.
  - move => σi1 ??. exists 0 => κstart Hwp Hκ Hs.
    by rewrite right_id in Hκ; subst.
  - move => σi1 σi2 σi3 κ κend Hstep Hsteps [n IH]. exists (S n) => κstart Hwp Hs Hκs.
    inversion_clear Hwp as [??? Hwp2]; subst.
    have [//|??]:= (Hwp2 _ _ n _ ltac:(by constructor)) => //.
    apply: IH; [done| |done].
    by rewrite assoc.
  - move => σ1 ???. exists 1 => ? Hwp ??.
    inversion_clear Hwp as [??? Hwp2]; subst.
    have [//|/has_trace_ub_app_inv? ?]:= (Hwp2 _ _ 0 _ ltac:(by constructor)) => //.
    by apply: has_trace_trans.
Qed.

Lemma refines_implies_wp' {EV} (m1 m2 : mod_state EV):
  m1 ⊑ m2 →
  (∀ n, wp' m1 m2 n m1.(ms_state) []).
Proof.
  move => [Hr] n.
  have : (has_trace m1 m1.(ms_state) [] (m1.(ms_state) =.)). { by apply: TraceEnd. }
  move: {2 3}(m1.(ms_state)) => σi.
  move: ([]) => κstart.
  elim/lt_wf_ind: n κstart σi.
  move => n IH κstart σi Hstepi.
  constructor => σi2 κ n' ? Hstep; subst.
  inversion Hstep; simplify_eq.
  - have : ms_state m1 ~{ m1, κstart ++ option_list (Vis <$> κ0) }~> eq σi2. {
      apply: has_trace_trans; [done|] => ? <-.
      rewrite -(right_id_L [] (++) (option_list _)).
      apply: TraceStep => //.
        by apply: TraceEnd.
    }
    split. { apply: Hr. by apply: has_trace_mono. }
      by apply: IH; [ lia|].
  - split.
    + apply: Hr.
      apply: has_trace_trans; [done|] => ? <-. by apply: TraceUb.
    + apply: IH; [lia|].
      apply: has_trace_trans; [done|] => ? <-. by apply: TraceUb.
Qed.

(*** Proving refinement *)
Lemma inv_implies_refines {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → m2.(m_state) → Prop):
  inv m1.(ms_state) m2.(ms_state) →
  (∀ σi1 σs1 σi2 e,
      inv σi1 σs1 → m_ub_step m1 σi1 e σi2 →
      σs1 ~{ m2, option_list e }~> (λ σs2, inv σi2 σs2)) →
  m1 ⊑ m2.
Proof.
  move => Hinvinit Hinvstep.
  constructor => // κs. move: m1.(ms_state) m2.(ms_state) Hinvinit => σi1 σs1 Hinv Hsteps.
  elim: Hsteps σs1 Hinv => {σi1 κs}.
  - by eauto using TraceEnd.
  - move => σi1 σi2 σi3 κ κs Hstep Hsteps IH σs1 Hinv.
    have ?:= (Hinvstep _ _ _ _ Hinv ltac:(by constructor)).
    apply: has_trace_trans; [done|] => ? /=?.
    by apply: IH.
  - move => ????? Hinv.
    have /has_trace_ub_inv ?:= (Hinvstep _ _ _ _ Hinv ltac:(by constructor)).
    by apply: (has_trace_trans []).
Qed.
(* This does not seem nice to work work. *)
Lemma inv_implies_refines_equiv {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → m2.(m_state) → Prop):
  inv m1.(ms_state) m2.(ms_state) →
  (∀ σi1 σs1 σi2 e, inv σi1 σs1 → m_ub_step m1 σi1 e σi2 →
      σs1 ~{ m2, option_list e }~> (λ σs2, inv σi2 σs2)) →
  (∀ σi1 σs1 σs2 e, inv σi1 σs1 → m_ub_step m2 σs1 e σs2 →
      σi1 ~{ m1, option_list e }~> (λ σi2, inv σi2 σs2)) →
  refines_equiv m1 m2.
Proof.
  move => Hinvinit Hinvstep1 Hinvstep2.
  split; [ apply: inv_implies_refines => //; naive_solver |].
  apply: (inv_implies_refines _ _ (flip inv)) => //=; naive_solver.
Qed.

(*
Lemma inv_implies_refines' {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → m2.(m_state) → Prop):
  inv m1.(ms_state) m2.(ms_state) →
  (∀ σi σs, inv σi σs → m1.(m_is_ub) σi → σs ~{ m2, [] }~> (λ _, False)) →
  (∀ σi1 σs1 σi2 e, inv σi1 σs1 → m1.(m_step) σi1 e σi2 →
      m1.(m_is_ub) σi1 ∨ σs1 ~{ m2, option_list (Vis <$> e) }~> (λ σs2, (inv σi2 σs2 ∨ has_no_behavior m1 σi2))) →
  m1 ⊑ m2.
Proof.
  move => Hinvinit Hinvsafe Hinvstep.
  constructor => // κs.
  move: m1.(ms_state) m2.(ms_state) Hinvinit => σi1 σs1 Hinv Hsteps.
  elim: Hsteps σs1 Hinv => {σi1 κs}.
  - by eauto using TraceEnd.
  - move => σi1 σi2 σi3 κ κs Hstep Hsteps IH σs1 Hinv.
    case: (Hinvstep _ _ _ _ Hinv Hstep) => [|?]. {
      move => /Hinvsafe Hub. apply: (has_trace_trans []); [naive_solver|].
      done.
    }
    apply: has_trace_trans; [done|] => ? [?| Hnb].
    + naive_solver.
    + move: Hsteps => /Hnb ->. by apply: TraceEnd.
  - move => ??? /Hinvsafe Hs σs Hinv.
    apply: (has_trace_trans []); naive_solver.
Qed.
 *)
(*
(* This does not seem nice to work work. *)
Lemma inv_implies_refines_equiv {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → m2.(m_state) → Prop):
  inv m1.(ms_state) m2.(ms_state) →
  (∀ σi σs, inv σi σs → m1.(m_is_ub) σi → σs ~{ m2, [] }~> (λ _, False)) →
  (∀ σi σs, inv σs σi → m2.(m_is_ub) σi → σs ~{ m1, [] }~> (λ _, False)) →
  (∀ σi1 σs1 σi2 e, inv σi1 σs1 → m1.(m_step) σi1 e σi2 →
      m1.(m_is_ub) σi1 ∨ σs1 ~{ m2, option_list (Vis <$> e) }~> (λ σs2, (inv σi2 σs2 ∨ has_no_behavior m1 σi2))) →
  (∀ σi1 σs1 σs2 e, inv σi1 σs1 → m2.(m_step) σs1 e σs2 →
      m2.(m_is_ub) σs1 ∨ σi1 ~{ m1, option_list (Vis <$> e) }~> (λ σi2, (inv σi2 σs2 ∨ has_no_behavior m2 σs2))) →
  refines_equiv m1 m2.
Proof.
  move => Hinvinit Hinvsafe1 Hinvsafe2 Hinvstep1 Hinvstep2.
  split; [ apply: inv_implies_refines' => //; naive_solver |].
  apply: (inv_implies_refines' _ _ (flip inv)) => //=; naive_solver.
Qed.
*)
(* This does not seem nice to work work. *)
(* Lemma link_merge_calls {EV1 EV2 EV3} (m1 : module EV1) (m2 : module EV2) (m3 : module EV3) (inv : m1.(m_state) → m2.(m_state) → m3.(m_state) → Prop) R : *)
(*   let R' e1 e2 e3 := if (e1, e2) is (None, None) then e3 = None else R e1 e2 e3 in *)
(*   inv m1.(m_initial) m2.(m_initial) m3.(m_initial) → *)
(*   (∀ σ1 σ2 σ3, inv σ1 σ2 σ3 → m3.(m_is_ub) σ3 ↔ (m1.(m_is_ub) σ1 ∨ m2.(m_is_ub) σ2)) → *)
(*   (∀ σ1 σ2 σ3, inv σ1 σ2 σ3 → ∀ e σ32, m_step m3 σ3 e σ32 → ∃ σ12 σ22, link_step m1 m2 R (σ1, σ2) e (σ12, σ22) ∧ inv σ12 σ22 σ32) → *)
(*   (∀ σ1 σ2 σ3, inv σ1 σ2 σ3 → ∀ e σ12 e', m_step m1 σ1 e σ12 → R' e None e' → ∃ σ32, m3.(m_step) σ3 e' σ32 ∧ inv σ12 σ2 σ32) → *)
(*   (∀ σ1 σ2 σ3, inv σ1 σ2 σ3 → ∀ e σ22 e', m_step m2 σ2 e σ22 → R' None e e' → ∃ σ32, m3.(m_step) σ3 e' σ32 ∧ inv σ1 σ22 σ32) → *)
(*   (∀ σ1 σ2 σ3, inv σ1 σ2 σ3 → ∀ e1 e2 σ12 σ22 e', m_step m1 σ1 (Some e1) σ12 → m_step m2 σ2 (Some e2) σ22 → R (Some e1) (Some e2) e' → ∃ σ32, m3.(m_step) σ3 e' σ32 ∧ inv σ12 σ22 σ32) → *)
(*   refines_equiv (link m1 m2 R) m3. *)
(* Proof. *)
(*   move => R' Hinit Hub Hmstep3 Hmstep1 Hmstep2 Hmstepboth. *)
(*   apply: (inv_implies_refines_equiv (link m1 m2 R) m3 (λ '(σ1, σ2) σ3, inv σ1 σ2 σ3)). *)
(*   - done. *)
(*   - move => [??] ?. naive_solver. *)
(*   - move => [σ11 σ21] σ31 [σ12 σ22] e Hinv Hstep. inversion Hstep; simplify_eq/=. *)
(*     + revert select (m_step _ _ _ _) => /(Hmstep1 _ _ _ Hinv) Hm3. *)
(*       destruct e1; simplify_eq; move: (Hm3 _ ltac:(done)) => [σ32 [? ?]]. *)
(*       all: eexists σ32; split => //; apply: has_trace_add_empty; apply: TraceStep => //; by apply: TraceEnd. *)
(*     + revert select (m_step _ _ _ _) => /(Hmstep2 _ _ _ Hinv) Hm3. *)
(*       destruct e2; simplify_eq; move: (Hm3 _ ltac:(done)) => [σ32 [? ?]]. *)
(*       all: eexists σ32; split => //; apply: has_trace_add_empty; apply: TraceStep => //; by apply: TraceEnd. *)
(*     + revert select (m_step _ _ _ _) => /(Hmstepboth _ _ _ Hinv) Hm3. *)
(*       revert select (m_step _ _ _ _) => /Hm3 {}Hm3. *)
(*       revert select (R _ _ _) => /Hm3 [σ32 [? ?]]. *)
(*       eexists σ32; split => //. *)
(*       apply: has_trace_add_empty. *)
(*       apply: TraceStep => //. *)
(*       by apply: TraceEnd. *)
(*   - move => [σ11 σ21] σ31 σ32 e Hinv /(Hmstep3 _ _ _ Hinv) [σ12 [σ22 [? ?]]]. *)
(*     eexists (σ12, σ22). split => //. *)
(*     apply: has_trace_add_empty. *)
(*     apply: TraceStep => //. *)
(*     by apply: TraceEnd. *)
(* Qed. *)

(*
Definition next_states {EV} (m : module EV) (σ : m.(m_state)) : propset (option (event EV) * m.(m_state)) :=
  {[ eσ | ∃ e, Vis <$> e = eσ.1 ∧ m.(m_step) σ e eσ.2 ]} ∪ {[ eσ | m.(m_is_ub) σ ]}.

Lemma in_next_states_has_trace {EV} (m : module EV) e σ1 σ2 :
  (e, σ2) ∈ next_states m σ1 → σ1 ~{ m, option_list e }~> σ2.
Proof.
  move => [[? /= [<- ?]]| ?].
  - apply: has_trace_add_empty. apply: TraceStep => //. by apply: TraceEnd.
  - by apply: TraceUb.
Qed.

Definition all_states_in {A B} (a : propset A) (e : propset B) (Φ : A → B → Prop) : Prop :=
  ∀ x, x ∈ a → ∃ y, y ∈ e ∧ Φ x y.

Definition all_states_in_equiv {A B} (a : propset A) (e : propset B) (Φ : A → B → Prop) : Prop :=
  all_states_in a e Φ ∧ all_states_in e a (flip Φ).

Global Instance all_states_in_proper {A B} : Proper ((≡) ==> (≡) ==> (pointwise_relation A (pointwise_relation B impl)) ==> impl) (@all_states_in A B).
Proof.
  move => a1 a2 Ha e1 e2 He Φ1 Φ2 HΦ Hall x. rewrite -Ha => Hx.
  case: (Hall _ Hx) => y. rewrite He => -[??]. eexists. split => //.
  by apply: HΦ.
Qed.

Global Instance all_states_in_equiv_proper {A B} : Proper ((≡) ==> (≡) ==> (pointwise_relation A (pointwise_relation B impl)) ==> impl) (@all_states_in_equiv A B).
Proof.
  move => ???????? HΦ [??]. split; [ by apply: all_states_in_proper|].
  apply: all_states_in_proper; [..| done] => //. move => ?? /=?. by apply: HΦ.
Qed.

Definition deterministic_step {EV} (m : module EV) (σ1 : m.(m_state)) (e : option EV) (σ2 : m.(m_state)) : Prop :=
  m.(m_step) σ1 e σ2 ∧ (∀ e' σ2', m.(m_step) σ1 e' σ2' → e' = e ∧ σ2' = σ2).

Lemma next_states_det {EV} (m : module EV) σ1 e σ2:
  deterministic_step m σ1 e σ2 → ¬ m.(m_is_ub) σ1 →
  next_states m σ1 ≡ {[(Vis <$> e, σ2)]}.
Proof.
  move => [Hdet1 Hdet2] Hub [??]. split.
  - move => [[?/=[<- /Hdet2 ?]]|//]. naive_solver.
  - move => [<- <-]. left. set_solver.
Qed.

Lemma next_states_empty {EV} (m : module EV) σ1:
  (¬ ∃ e σ2, m.(m_step) σ1 e σ2) → ¬ m.(m_is_ub) σ1 →
  next_states m σ1 ≡ ∅.
Proof. move => Hnotstep Hub [??]. split; set_solver. Qed.

Lemma all_states_in_equiv_singleton {A B} a e x y (Φ : A → B → Prop) :
  a ≡ {[ x ]} →
  e ≡ {[ y ]} →
  Φ x y →
  all_states_in_equiv a e Φ.
Proof. move => -> -> ?. split => ?; set_solver. Qed.

Lemma all_states_in_equiv_empty {A B} a e (Φ : A → B → Prop) :
  a ≡ ∅ →
  e ≡ ∅ →
  all_states_in_equiv a e Φ.
Proof. move => -> ->. split => ?; set_solver. Qed.

Lemma next_states_implies_refines {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → m2.(m_state) → Prop):
  inv m1.(ms_state) m2.(ms_state) →
  (∀ σi σs, inv σi σs → all_states_in (next_states m1 σi) (next_states m2 σs) (λ eσi2 eσs2,
      m2.(m_is_ub) σs ∨ (eσi2.1 = eσs2.1 ∧ (m2.(m_is_ub) eσs2.2 ∨ inv eσi2.2 eσs2.2)) )) →
  m1 ⊑ m2.
Proof.
  move => Hinvinit Hinvstep.
  constructor => // κs [σi2].
  move: m1.(ms_state) m2.(ms_state) Hinvinit => σi1 σs1 Hinv Hsteps.
  elim: Hsteps σs1 Hinv => {σi1 σi2 κs}.
  - by eauto using TraceEnd.
  - move => σi1 σi2 σi3 κ κs Hstep Hsteps IH σs1 Hinv.
    case: (Hinvstep _ _ Hinv (Vis<$> κ, σi2)). { set_solver. }
    move => [? σ2] [/in_next_states_has_trace ? /= [ Hub | [? Hor]]]; simplify_eq/=.
    { eexists _. by apply: TraceUbRefl. }
    case: Hor => [? | Hinv2]. { exists σ2. apply: has_trace_trans => //. by apply: TraceUb. }
    case: (IH _ Hinv2) => ? ?.
    eexists. by apply: has_trace_trans.
  - move => σi1 ?? ? σs Hinv.
    case: (Hinvstep _ _ Hinv (Some Ub, σi1)). { set_solver. }
    move => [? ?] [Hin [? |[??]]]; simplify_eq/=.
    { eexists _. by apply: TraceUbRefl. }
    eexists. apply: TraceUbRefl. case: Hin; [ | set_solver].
    by move => [[?|][/=??]].
Qed.

Lemma next_states_implies_refines_equiv {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → m2.(m_state) → Prop):
  inv m1.(ms_state) m2.(ms_state) →
  (∀ σi σs, inv σi σs → all_states_in_equiv (next_states m1 σi) (next_states m2 σs) (λ eσi2 eσs2,
      (m1.(m_is_ub) σi ∧ m2.(m_is_ub) σs) ∨ (eσi2.1 = eσs2.1 ∧ ((m1.(m_is_ub) eσi2.2 ∧ m2.(m_is_ub) eσs2.2) ∨ inv eσi2.2 eσs2.2)) )) →
  refines_equiv m1 m2.
Proof.
  move => Hinvinit Hinvstep.
  split.
  - apply: (next_states_implies_refines m1 m2 inv) => // σi σs Hinv.
    case: (Hinvstep _ _ Hinv) => ? _.
    apply: all_states_in_proper => // -[? ?] [??] /= ?. naive_solver.
  - apply: (next_states_implies_refines m2 m1 (flip inv)) => // σi σs Hinv.
    case: (Hinvstep _ _ Hinv) => _ ?.
    apply: all_states_in_proper => // -[? ?] [??] /= ?. naive_solver.
Qed.
*)
Inductive wp {EV} (m1 m2 : module EV) : nat → m1.(m_state) -> m2.(m_state) -> Prop :=
| Wp_step'' σi1 σs1 n:
    (∀ σi2 κ n', n = S n' → m_ub_step m1 σi1 κ σi2 -> ∃ Pσ2,
      σs1 ~{ m2, option_list κ }~> Pσ2 ∧
      ∀ σs2, Pσ2 σs2 → wp m1 m2 n' σi2 σs2) ->
    wp m1 m2 n σi1 σs1
.

Lemma Wp_step {EV} (m1 m2 : module EV) σi1 σs1 n:
    (∀ σi2 κ n', n = S n' → m_ub_step m1 σi1 κ σi2 ->
      σs1 ~{ m2, option_list κ }~> (λ σs2, wp m1 m2 n' σi2 σs2)) ->
    wp m1 m2 n σi1 σs1
.
Proof. move => ?. constructor. naive_solver. Qed.

Lemma wp_implies_refines {EV} (m1 m2 : mod_state EV):
  (∀ n, wp m1 m2 n m1.(ms_state) m2.(ms_state)) →
  m1 ⊑ m2.
Proof.
  move => Hwp.
  constructor => κs.
  move: m1.(ms_state) Hwp => σi1.
  move: m2.(ms_state) => σs1.
  move => Hwp Hsteps.
  move: σs1 Hwp. apply: forall_to_ex.
  elim: Hsteps => {σi1 κs}.
  - move => σi1. exists 0 => σs1 Hwp. by apply: TraceEnd.
  - move => σi1 σi2 σi3 κ κs Hstep Hsteps [n IH]. exists (S n) => σs1 Hwp.
    inversion_clear Hwp as [??? Hwp2]; subst.
    have [|?[??]]:= (Hwp2 _ _ n _ ltac:(by constructor)) => //.
    apply: has_trace_trans; naive_solver.
  - move => σ1 ???. exists 1 => ? Hwp.
    inversion_clear Hwp as [??? Hwp2]; subst.
    have [|?[/has_trace_ub_inv??]]:= (Hwp2 _ _ 0 _ ltac:(by constructor)) => //.
    by apply: (has_trace_trans []).
Qed.

Ltac invert_all_tac f :=
  let do_invert H := inversion H; clear H in
  repeat lazymatch goal with
         | H : f |- _ => do_invert H
         | H : f _ |- _ => do_invert H
         | H : f _ _|- _ => do_invert H
         | H : f _ _ _|- _ => do_invert H
         | H : f _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _ _ _ _ _|- _ => do_invert H
         end.

Tactic Notation "invert_all" constr(f) := invert_all_tac f; simplify_eq/=.
Tactic Notation "invert_all'" constr(f) := invert_all_tac f.


Ltac inv_step := invert_all' @m_ub_step; invert_all @m_step.

Definition module_empty {A} : module A := {|
  m_state := unit;
  m_step _ _ _ := False;
  m_is_ub s := False;
|}.
Global Instance module_empty_inst A : Empty (module A) := module_empty.

(*** Tests *)

(*
  TODO: prove the following refinement for which wp is probably not enough

            A     B
           /- 2  --- 3
  spec: 1 -
           \- 2' --- 4
            A     C

                  B
           A     /- 3
  impl: 1 --- 2 -
                 \- 4
                 C

*)
Module test.

(*   2
  1 --- 2 (done)
 *)
Inductive mod1_step : bool → option nat → bool → Prop :=
| T1False: mod1_step false (Some 2) true.


Definition mod1 : module nat := {|
  m_state := bool;
  m_step := mod1_step;
  m_is_ub s:= False;
|}.

(*         2
  1 --- 2 --- 3 (done)
 *)
Inductive mod2_state := | S1 | S2 | S3.
Inductive mod2_step : mod2_state → option nat → mod2_state → Prop :=
| T2S1: mod2_step S1 None S2
| T2S2: mod2_step S2 (Some 2) S3.
Definition mod2 : module nat := {|
  m_state := mod2_state;
  m_step := mod2_step;
  m_is_ub s:= False;
|}.

Definition t2_to_t1_inv (σ1 : mod2_state) (σ2 : bool) : Prop :=
  σ2 = match σ1 with
  | S1 | S2 => false
  | _ => true
  end.
Lemma test_refines1 :
  MS mod2 S1 ⊑ MS mod1 false.
Proof.
  apply (inv_implies_refines (MS mod2 S1) (MS mod1 false) t2_to_t1_inv).
  - done.
  - move => σi1 σs1 σi2 e -> ?. inv_step => //.
    + by apply: TraceEnd.
    + apply: TraceStepSome; last by apply: TraceEnd. constructor.
Qed.

Definition mod_loop {A} : module A := {|
  m_state := unit;
  m_step _ e _ := e = None;
  m_is_ub s:= False;
|}.
Lemma test_refines2 {A} (m : mod_state A) :
  MS mod_loop tt ⊑ m.
Proof.
  apply: (inv_implies_refines (MS mod_loop tt) m (λ _ _, True)).
  - done.
  - move => ??????. inv_step => //. by apply: TraceEnd.
Qed.

Lemma test_refines2_wp {A} (m : mod_state A) :
  MS mod_loop tt ⊑ m.
Proof.
  apply: wp_implies_refines => /=.
  move => n. elim/lt_wf_ind: n => n Hloop.
  apply: Wp_step => -[]  κ n' ??.
  inv_step => //. apply: TraceEnd.
  naive_solver lia.
Qed.


(*   1
      /- 2 (done)
  1 --
      \- 3 (stuck)
     2
 *)

Inductive stuck1_state := | S1S1 | S1S2 | S1S3.
Inductive stuck1_step : stuck1_state → option nat → stuck1_state → Prop :=
| S1_1To2: stuck1_step S1S1 (Some 1) S1S2
| S1_1To3: stuck1_step S1S1 (Some 2) S1S3.
Definition mod_stuck1 : module nat := {|
  m_state := stuck1_state;
  m_step := stuck1_step;
  m_is_ub s:= s = S1S3;
|}.

Lemma test_refines_stuck1 :
  MS mod_stuck1 S1S1 ⊑ MS mod_stuck1 S1S1.
Proof.
  apply: (inv_implies_refines (MS mod_stuck1 S1S1) (MS mod_stuck1 S1S1) (λ σ1 σ2, σ1 = σ2 ∧ σ1 ≠ S1S3)).
  - done.
  - move => σi1 σs1 σi2 e [-> ?] ?. inv_step => //.
    + (* 1 -> 2 *) apply: TraceStepSome; last by apply: TraceEnd. constructor.
    + (* 1 -> 3 *)
      apply: TraceStepSome; [constructor|]. by constructor.
Qed.

(*   1
      /- 2 (done)
  1 --
      \- 3 ---- 4 (stuck)
     2      3
 *)

Inductive stuck2_state := | S2S1 | S2S2 | S2S3 | S2S4.
Inductive stuck2_step : stuck2_state → option nat → stuck2_state → Prop :=
| S2_1To2: stuck2_step S2S1 (Some 1) S2S2
| S2_1To3: stuck2_step S2S1 (Some 2) S2S3
| S2_3To4: stuck2_step S2S3 (Some 3) S2S4.
Definition mod_stuck2 : module nat := {|
  m_state := stuck2_state;
  m_step := stuck2_step;
  m_is_ub s:= s = S2S4;
|}.

Definition stuck2_inv (σ1 : stuck2_state) (σ2 : stuck1_state) :=
  (* We could prove an even stronger invariant with also σ1 ≠ S2S3
  since we don't need to reestablish it for a stuck source state. *)
  σ1 ≠ S2S4 ∧
  σ2 = match σ1 with | S2S1 => S1S1 | S2S2 => S1S2 | S2S3 => S1S3 | S2S4 => S1S1 end.

Lemma test_refines_stuck2 :
  MS mod_stuck2 S2S1 ⊑ MS mod_stuck1 S1S1.
Proof.
  apply: (inv_implies_refines (MS mod_stuck2 S2S1) (MS mod_stuck1 S1S1) stuck2_inv).
  - done.
  - move => σi1 σs1 σi2 e [? ->] ?. inv_step.
    + (* 1 -> 2 *) apply: TraceStepSome; last by constructor. constructor.
    + (* 1 -> 3 *) apply: TraceStepSome; last by constructor. constructor.
    + (* 3 -> 4 *) by apply: TraceUb.
Qed.

Lemma test_refines_stuck2_wp :
  MS mod_stuck2 S2S1 ⊑ MS mod_stuck1 S1S1.
Proof.
  apply: wp_implies_refines => n.
  (* S2S1 *)
  apply: Wp_step => σ2 ????. inv_step => //.
  - (* S2S2 *)
    apply: TraceStepSome; [ constructor |].
    apply: TraceEnd.
    apply: Wp_step => {}σ2 ????; inv_step.
  - (* S2S3 *)
    apply: TraceStepSome; [ constructor |].
    apply: TraceEnd.
    apply: Wp_step => {}σ2 ????; inv_step.
    by apply: TraceUb.
Qed.

(*   1       3
      /- 2 ---- 4 (done)
  1 --
      \- 3 (stuck)
     2
 *)

Inductive stuck3_state := | S3S1 | S3S2 | S3S3 | S3S4.
Inductive stuck3_step : stuck3_state → option nat → stuck3_state → Prop :=
| S3_1To2: stuck3_step S3S1 (Some 1) S3S2
| S3_1To3: stuck3_step S3S1 (Some 2) S3S3
| S3_2To4: stuck3_step S3S2 (Some 3) S3S4.
Definition mod_stuck3 : module nat := {|
  m_state := stuck3_state;
  m_step := stuck3_step;
  m_is_ub s:= s = S3S3;
|}.

Definition stuck3_inv (σ1 : stuck3_state) (σ2 : stuck1_state) :=
  σ1 ≠ S3S3 ∧
  σ2 = match σ1 with | S3S1 => S1S1 | S3S2 => S1S2 | S3S3 => S1S3 | S3S4 => S1S2 end.

(* The following is not provable: *)
Lemma test_refines_stuck3 :
  MS mod_stuck3 S3S1 ⊑ MS mod_stuck1 S1S1.
Proof.
  apply: (inv_implies_refines (MS mod_stuck3 S3S1) (MS mod_stuck1 S1S1) stuck3_inv).
  - done.
  - move => σi1 σs1 σi2 e [? ->] ?. inv_step.
    + (* 1 -> 2 *) apply: TraceStepSome; last by constructor. constructor.
    + (* 1 -> 3 *)
      apply: TraceStepSome; [ constructor|]. by apply: TraceUb.
    + (* 2 -> 4 *) apply: TraceStepSome; last by constructor.
      (* Not provable! *)
Abort.


Record call_event : Type := {
  call_nat : nat;
}.
(*
     Call 1
  1 -------- 2
 *)

Inductive call1_step : bool → option call_event → bool → Prop :=
| C1_1To2: call1_step false (Some ({| call_nat := 1 |})) true.
Definition mod_call1 : module call_event := {|
  m_state := bool;
  m_step := call1_step;
  m_is_ub s := False;
|}.

(*
            -> Call n     1 + n
  1 (done) ---------- 2 -------- 3
 *)

Inductive call2_state := | C2S1 | C2S2 (n : nat) | C2S3.
Inductive call2_step : call2_state → option (call_event + nat) → call2_state → Prop :=
| C2_1To2 cn: call2_step C2S1 (Some (inl cn)) (C2S2 cn.(call_nat))
| C2_2To3 n: call2_step (C2S2 n) (Some (inr (1 + n))) C2S3.
Definition mod_call2 : module _ := {|
  m_state := call2_state;
  m_step := call2_step;
  m_is_ub s := False;
|}.

Inductive call_merge_rel : option call_event → option (call_event + nat) → option nat → Prop :=
| CallMergeCall ev:
    call_merge_rel (Some ev) (Some (inl ev)) None
| CallMergeOut n:
    call_merge_rel None (Some (inr n)) (Some n).

Definition call_merge_inv (σ1 : bool * call2_state * unit) (σ2 : bool) :=
  match σ1.1.1, σ1.1.2 with
  | false, C2S3 => False
  | false, C2S2 _ => False
  | _, C2S2 n => n = 1
  | _, _ => True
  end ∧ σ2 = if σ1.1.2 is C2S3 then true else false.
Lemma test_refines_call_merge :
  MS (link mod_call1 mod_call2 (stateless_mediator call_merge_rel)) (false, C2S1, tt) ⊑ MS mod1 false.
Proof.
  apply: (inv_implies_refines (MS (link mod_call1 mod_call2 (stateless_mediator call_merge_rel)) (false, C2S1, tt)) (MS mod1 _) call_merge_inv).
  - done.
  - move => σi1 σs1 σi2 e [??] ?.
    inv_step; try match goal with | H : call_merge_rel _ _ _ |- _ => inversion H; clear H end; simplify_eq/=.
    + (* mod_call2 *)
      destruct σ0 => //. simplify_eq/=.
      apply: TraceStepSome; last by constructor. constructor.
    + (* mod_call1 *)
        by constructor.
    + naive_solver.
Qed.

Definition call_split_inv (σ1 : bool) (σ2 : bool * call2_state * unit) :=
  if σ1 then True else σ2 = (false, C2S1, tt).
Lemma test_refines_call_split :
  MS mod1 false ⊑ MS (link mod_call1 mod_call2 (stateless_mediator call_merge_rel)) (false, C2S1, tt).
Proof.
  apply: (inv_implies_refines (MS mod1 _) (MS (link mod_call1 mod_call2 (stateless_mediator call_merge_rel)) _) call_split_inv).
  - done.
  - move => σi1 [σs1 σs2] σi2 e Hinv ?. inv_step => //.
    apply: (TraceStepNone _ (link mod_call1 mod_call2 (stateless_mediator _)) (true, C2S2 1, tt)). {
      apply: LinkStepBoth. 3: constructor. all: constructor.
    }
    apply: TraceStepSome. 2: by constructor.
    apply: LinkStepR. constructor => //. simpl. constructor.
    Unshelve.
    constructor.
Qed.

Lemma test_refines_call_merge_wp :
  MS (link mod_call1 mod_call2 (stateless_mediator call_merge_rel)) (false, C2S1, tt) ⊑ MS mod1 false.
Proof.
  apply: (wp_implies_refines) => n.
  apply: Wp_step => σi1 n' ? ? Hstep. subst.
  inv_step; try match goal with | H : call_merge_rel _ _ _ |- _ => inversion H; clear H end; simplify_eq/=. 2: naive_solver.
  apply: TraceEnd.

  apply: Wp_step => σi1 n' ? ? Hstep. subst.
  inv_step; try match goal with | H : call_merge_rel _ _ _ |- _ => inversion H; clear H end; simplify_eq/=. 2: naive_solver.
  apply: TraceStepSome; [constructor| apply: TraceEnd].

  apply: Wp_step => σi1 n' ? ? Hstep. subst.
  inv_step; try match goal with | H : call_merge_rel _ _ _ |- _ => inversion H; clear H end; simplify_eq/=.
  naive_solver.
Qed.

Lemma test_refines_call_split_wp :
  MS mod1 false ⊑ MS (link mod_call1 mod_call2 (stateless_mediator call_merge_rel)) (false, C2S1, tt).
Proof.
  apply: (wp_implies_refines) => n.
  apply: Wp_step => σi1 n' ? ? Hstep. subst.
  inv_step => //.
  apply: (TraceStepNone _ (link mod_call1 mod_call2 (stateless_mediator _)) (true, C2S2 1, tt)). {
      apply: LinkStepBoth. 3: constructor. all: constructor.
    }
  apply: TraceStepSome. { apply: LinkStepR. constructor => //. simpl. constructor. }
  apply: TraceEnd.


  apply: Wp_step => σi1 n' ? ? Hstep. subst.
  inv_step => //.
  Unshelve. constructor.
Qed.

Definition call_equiv_inv (σ1 : bool * call2_state * unit) (σ2 : bool) :=
  match σ1, σ2 with
  | (false, C2S1, _), false => True
  | (true, C2S2 n, _), false => n = 1
  | (true, C2S3, _), true => True
  | _, _ => False
  end.

Lemma test_refines_call_equiv :
  refines_equiv (MS (link mod_call1 mod_call2 (stateless_mediator call_merge_rel)) (false, C2S1, tt)) (MS mod1 false).
Proof.
  apply: (inv_implies_refines_equiv (MS (link mod_call1 mod_call2 (stateless_mediator _)) _) (MS mod1 _) call_equiv_inv).
  - done.
  - move => σi1 σs1 σi2 e ? ?.
    inv_step; try match goal with | H : call_merge_rel _ _ _ |- _ => inversion H; clear H end; simplify_eq/=. 3: naive_solver.
    + destruct σ0, σs1 => //. simplify_eq.
      apply: TraceStepSome; [econstructor|]. by apply: TraceEnd.
    + destruct σs1 => //. by apply: TraceEnd.
  - move => [[σi11 σi12] ?] σs1 σi2 e ? ?. inv_step => //.
    destruct σi11, σi12 => //; simplify_eq.
    (* TODO: it is quite bad that we have two subproofs here while with the other methods we only have 1 *)
    + apply: TraceStepSome. { apply: LinkStepR. constructor => //. simpl. constructor. }
      by apply: TraceEnd.
    + apply: (TraceStepNone _ (link mod_call1 mod_call2 (stateless_mediator _)) (true, C2S2 1, tt)). {
        apply: LinkStepBoth. 3: constructor. all: constructor.
      }
      apply: TraceStepSome. { apply: LinkStepR. constructor => //. simpl. constructor. }
      by apply: TraceEnd.

      Unshelve. all: constructor.
Qed.

(* Definition call_equiv_inv2 (σ1 : bool) (σ2 : call2_state) (σ3 : mod2_state) := *)
(*   match σ1, σ2, σ3 with *)
(*   | false, C2S1, S1 => True *)
(*   | true, C2S2 n, S2 => n = 1 *)
(*   | true, C2S3, S3 => True *)
(*   | _, _, _ => False *)
(*   end. *)

(* Lemma test_refines_call_equiv' : *)
(*   refines_equiv (link mod_call1 mod_call2 call_merge_rel) mod2. *)
(* Proof. *)
(*   apply: (link_merge_calls mod_call1 mod_call2 mod2 call_equiv_inv2). *)
(*   - done. *)
(*   - naive_solver. *)
(*   - move => σ1 σ2 ? Hinv ???. inv_step; destruct σ1, σ2 => //. *)
(*     + eexists true, (C2S2 1). split => //. apply: LinkStepBoth. 3: constructor. all: constructor. *)
(*     + eexists true, C2S3. simplify_eq/=. split => //. apply: LinkStepR. by constructor. simpl. constructor. *)
(*   - move => ?????????. *)
(*     inv_step; match goal with | H : call_merge_rel _ _ _ |- _ => inversion H; clear H end; simplify_eq/=. *)
(*   - move => σ1 σ2 σ3 ??????. *)
(*     inv_step; match goal with | H : call_merge_rel _ _ _ |- _ => inversion H; clear H end; simplify_eq/=. *)
(*     destruct σ1, σ3 => //. simplify_eq/=. exists S3. split => //. constructor. *)
(*   - move => σ1 σ2 σ3 ?????????. *)
(*     match goal with | H : call_merge_rel _ _ _ |- _ => inversion H; clear H end; simplify_eq/=. *)
(*     match goal with | H : call1_step _ _ _ |- _ => inversion H; clear H end; simplify_eq/=. *)
(*     match goal with | H : call2_step _ _ _ |- _ => inversion H; clear H end; simplify_eq/=. *)
(*     destruct σ3 => //. eexists S2. split => //. constructor. *)
(* Qed. *)
(*
Definition call_equiv_inv2 (σ1 : bool * call2_state * unit) (σ2 : mod2_state) :=
  match σ1, σ2 with
  | (false, C2S1, _), S1 => True
  | (true, C2S2 n, _), S2 => n = 1
  | (true, C2S3, _), S3 => True
  | _, _ => False
  end.

Local Ltac solve_refines_call_next_equiv_det :=
  split; [ by repeat econstructor | move => ???; invert_all @m_step; destruct_hyps; by invert_all call_merge_rel].
Lemma test_refines_call_next_equiv :
  refines_equiv (MS (link mod_call1 mod_call2 (stateless_mediator call_merge_rel)) (false, C2S1, tt)) (MS mod2 S1).
Proof.
  apply (next_states_implies_refines_equiv (MS (link mod_call1 mod_call2 (stateless_mediator call_merge_rel)) _) (MS mod2 _) (call_equiv_inv2)).
  - done.
  - move => [[σi1 σi2] []] σs /=.
    destruct σi1, σi2, σs => //= [->|_|_].
    + apply: all_states_in_equiv_singleton;
        [ rewrite next_states_det; [done| solve_refines_call_next_equiv_det |naive_solver].. |].
      naive_solver.
    + apply: all_states_in_equiv_empty;
        (rewrite next_states_empty; [done | move => [?[??]]; inv_step | naive_solver]).
    + apply: all_states_in_equiv_singleton;
        [ rewrite next_states_det; [done| solve_refines_call_next_equiv_det |naive_solver].. |].
      naive_solver.
Qed.
*)

End test.
