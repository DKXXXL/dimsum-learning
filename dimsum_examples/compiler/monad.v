From dimsum.core Require Export base.
From dimsum.core Require Import axioms.

Set Default Proof Using "Type".

(** * Monad used by some passes of the compiler *)

(** * Monoid for appending *)
Record compiler_monoid := {
  cm_car :> Type;
  cm_empty : cm_car;
  cm_comp : cm_car → cm_car → cm_car;
  cm_left_id : LeftId (=) cm_empty cm_comp;
  cm_right_id : RightId (=) cm_empty cm_comp;
  cm_assoc : Assoc (=) cm_comp;
}.
Global Existing Instance cm_left_id.
Global Existing Instance cm_right_id.
Global Existing Instance cm_assoc.

Canonical Structure list_compiler_monoid A : compiler_monoid := {|
  cm_car := list A;
  cm_empty := [];
  cm_comp := app;
|}.

Program Canonical Structure fn_compiler_monoid A : compiler_monoid := {|
  cm_car := A → A;
  cm_empty := id;
  cm_comp := compose;
|}.
Next Obligation. done. Qed.
Next Obligation. done. Qed.
Next Obligation. done. Qed.

(** * Success result of the monad *)
Inductive compiler_success {E R : Type} :=
| CSuccess (res : R) | CError (err : E).
Arguments compiler_success : clear implicits.

Global Instance compiler_success_fmap E : FMap (compiler_success E) :=
  λ RA RB f x,
    match x with
    | CSuccess y => CSuccess (f y)
    | CError e => CError e
    end.

Lemma compiler_success_fmap_success E RA RB (f : RA → RB) x y :
  f <$> x = @CSuccess E RB y ↔
  ∃ x', x = CSuccess x' ∧ y = f x'.
Proof. destruct x => //=; naive_solver. Qed.

Definition compiler_success_fmap_error {E1 E2 R} (f : E1 → E2) (x : compiler_success E1 R) : compiler_success E2 R :=
  match x with
  | CSuccess y => CSuccess y
  | CError e => CError (f e)
  end.

Lemma compiler_success_fmap_error_success E1 E2 R (f : E1 → E2) x (y : R) :
  compiler_success_fmap_error f x = CSuccess y ↔ x = CSuccess y.
Proof. destruct x => //=. naive_solver. Qed.

Global Instance compiler_success_bind E : MBind (compiler_success E) :=
  λ RA RB f c,
    match c with
    | CSuccess x => f x
    | CError e => CError e
    end.

Lemma compiler_success_bind_success E RA RB (f : RA → compiler_success E RB) x y :
  x ≫= f = @CSuccess E RB y ↔
  ∃ x', x = CSuccess x' ∧ f x' = CSuccess y.
Proof. destruct x => //=; naive_solver. Qed.

(** * Monad definition *)
(** The compiler monad is a combination of state, writer, and error monad. *)
Record compiler_result {S : Type} {A : compiler_monoid} {E R : Type} := CResult {
  c_state : S;
  c_prog : A;
  c_result : compiler_success E R;
}.
Arguments CResult {_ _ _ _}.
Arguments compiler_result : clear implicits.
Add Printing Constructor compiler_result.

Definition compiler_monad S A E R : Type := S → compiler_result S A E R.

Global Instance cbind S A E: MBind (compiler_monad S A E) :=
  λ RA RB f c s,
    let ra := c s in
    match ra.(c_result) with
    | CSuccess r =>
        let rb := f r ra.(c_state) in
        CResult rb.(c_state) (cm_comp A ra.(c_prog) rb.(c_prog)) rb.(c_result)
    | CError e => CResult ra.(c_state) ra.(c_prog) (CError e)
    end.

Global Instance cret S A E : MRet (compiler_monad S A E) :=
  λ RA x s, CResult s (cm_empty A) (CSuccess x).

Fixpoint cmap {B C S} {A : compiler_monoid} {E} (l : list B) (n : nat) (f : nat → B → compiler_monad S A E C) : compiler_monad S A E (list C) :=
  match l with
  | [] => mret []
  | x::l =>
      c ← f n x;
      cs ← cmap l (Datatypes.S n) f;
      mret (c :: cs)
  end.

Definition cerror {S A E R} : E → compiler_monad S A E R :=
  λ err s, CResult s (cm_empty A) (CError err).

Definition cassert {S A E} (err : E) (P : Prop) `{!Decision P} : compiler_monad S A E unit :=
  if bool_decide P then mret tt else cerror err.

Definition cassert_opt {S A E R} : E → option R → compiler_monad S A E R :=
  λ err o, if o is Some r then mret r else cerror err.

Definition cget {S A E} : compiler_monad S A E S :=
  λ s, CResult s (cm_empty A) (CSuccess s).

Definition cput {S A E} : S → compiler_monad S A E S :=
  λ s' s, CResult s' (cm_empty A) (CSuccess s).

Definition cappend {S} {A : compiler_monoid} {E} : A → compiler_monad S A E unit :=
  λ a s, CResult s a (CSuccess tt).

Definition cscope {S A E R} : compiler_monad S A E R → compiler_monad S A E (R * A) :=
  λ c s,
    let r := c s in
    match r.(c_result) with
    | CSuccess res => CResult r.(c_state) (cm_empty A) (CSuccess (res, r.(c_prog)))
    | CError err => CResult r.(c_state) (cm_empty A) (CError err)
    end.

Definition crun {S A E R} : S → compiler_monad S A E R → compiler_result S A E R :=
  λ s c, c s.

Global Typeclasses Opaque compiler_monad.

Section compiler_monad.
  Context {S : Type}  {A : compiler_monoid} {E : Type}.
  Local Notation M := (compiler_monad S A E).

  Lemma run_cbind_cret {RA RB} y (f : RA → M RB) s:
    crun s (mret y ≫= f) = crun s (f y).
  Proof. rewrite /crun/mbind/cbind/= left_id_L. by destruct (f y s). Qed.

  Lemma run_cbind_cbind {RA RB RC} x (f : RA → M RB) (g : RB → M RC) s:
    crun s ((x ≫= f) ≫= g) = crun s (x ≫= λ y, f y ≫= g).
  Proof.
    rewrite /crun/mbind/cbind/=.
    repeat case_match; simplify_eq/= => //.
    by rewrite assoc_L.
  Qed.

  Lemma cmap_S {B C} xs f n:
    cmap xs n f = cmap (A:=A) (S:=S) (B:=B) (C:=C) (E:=E) xs (Datatypes.S n) (f ∘ pred).
  Proof.
    elim: xs n f => //= ?? IH n f.
    f_equal. apply AxFunctionalExtensionality => ?. by rewrite IH.
  Qed.

  Lemma cret_success R (r' : R) (s s' : S) (a : A) (r : R):
    crun (E:=E) s (mret r') = CResult s' a (CSuccess r) ↔ s' = s ∧ a = cm_empty A ∧ r = r'.
  Proof. rewrite /crun/mret/cret/=. naive_solver. Qed.

  Lemma cbind_success {RA RB} x (f : RA → M RB) s1 s3 r3 a3:
    crun s1 (x ≫= f) = CResult s3 a3 (CSuccess r3) ↔
    ∃ s2 a2 r2 a3',
      crun s1 x = CResult s2 a2 (CSuccess r2) ∧
      crun s2 (f r2) = CResult s3 a3' (CSuccess r3) ∧
      a3 = cm_comp A a2 a3'.
  Proof.
    rewrite /crun/mbind/cbind/=.
    destruct (x s1) as [xs ? ?].
    repeat case_match; simplify_eq/= => //. 2: naive_solver.
    split => ?; destruct!.
    + destruct (f res xs) eqn: Heq. naive_solver.
    + revert select (f _ _ = _) => -> /=. done.
  Qed.

  Lemma cerror_success R (e : E) (s s' : S) (a : A) (r : R):
    crun s (cerror e) = CResult s' a (CSuccess r) ↔ False.
  Proof. rewrite /crun/cerror/=. naive_solver. Qed.

  Lemma cassert_success P `{!Decision P} (e : E) (s : S) s' a r:
    crun s (cassert e P) = CResult s' a (CSuccess r) ↔
     s' = s ∧ a = cm_empty A ∧ r = tt ∧ P.
  Proof.
    rewrite /crun/cassert/=. case_bool_decide.
    - rewrite cret_success. naive_solver.
    - rewrite cerror_success. naive_solver.
  Qed.

  Lemma cassert_opt_success R (x : option R) (e : E) (s : S) s' a r:
    crun s (cassert_opt e x) = CResult s' a (CSuccess r) ↔
     s' = s ∧ a = cm_empty A ∧ x = Some r.
  Proof.
    rewrite /crun/=. destruct x => /=.
    - rewrite cret_success. naive_solver.
    - rewrite cerror_success. naive_solver.
  Qed.

  Lemma cget_success (s : S) s' a' r:
    crun (E:=E) s cget = CResult s' a' (CSuccess r) ↔
     s' = s ∧ a' = cm_empty A ∧ r = s.
  Proof. rewrite /crun/cget/=. naive_solver. Qed.

  Lemma cput_success (s : S) s' s'' a' r:
    crun (E:=E) s (cput s'') = CResult s' a' (CSuccess r) ↔
     s' = s'' ∧ a' = cm_empty A ∧ r = s.
  Proof. rewrite /crun/cput/=. naive_solver. Qed.

  Lemma cappend_success (s : S) s' (a : A) a' r:
    crun (E:=E) s (cappend a) = CResult s' a' (CSuccess r) ↔
     s' = s ∧ a = a' ∧ r = tt.
  Proof. rewrite /crun/cappend/=. naive_solver. Qed.

  Lemma cscope_success R (s : S) s' c a' (r : R * A):
    crun (E:=E) s (cscope c) = CResult s' a' (CSuccess r) ↔
     crun (E:=E) s c = CResult s' r.2 (CSuccess r.1) ∧ a' = cm_empty A.
  Proof. rewrite /crun/cscope/=. case_match => //=; destruct (c s), r; naive_solver. Qed.

End compiler_monad.

Tactic Notation "simplify_crun_eq" :=
  repeat (match goal with
          | H : crun _ (mret _) = CResult _ _ (CSuccess _) |- _ =>
              apply cret_success in H;
              destruct H as (?&?&?)
          | H : crun _ (_ ≫= _) = CResult _ _ (CSuccess _) |- _ =>
              apply cbind_success in H;
              destruct H as (?&?&?&?&?&?&?)
          | H : crun _ (cerror _) = CResult _ _ (CSuccess _) |- _ =>
              apply cerror_success in H;
              destruct H as []
          | H : crun _ (cassert _ _) = CResult _ _ (CSuccess _) |- _ =>
              apply cassert_success in H;
              destruct H as (?&?&?&?)
          | H : crun _ (cassert_opt _ _) = CResult _ _ (CSuccess _) |- _ =>
              apply cassert_opt_success in H;
              destruct H as (?&?&?)
          | H : crun _ cget = CResult _ _ (CSuccess _) |- _ =>
              apply cget_success in H;
              destruct H as (?&?&?)
          | H : crun _ (cput _) = CResult _ _ (CSuccess _) |- _ =>
              apply cput_success in H;
              destruct H as (?&?&?)
          | H : crun _ (cappend _) = CResult _ _ (CSuccess _) |- _ =>
              apply cappend_success in H;
              destruct H as (?&?&?)
          | H : crun _ (cscope _) = CResult _ _ (CSuccess _) |- _ =>
              apply cscope_success in H;
              destruct H as (?&?)
          end || simplify_eq/=).

(** * Tests *)
Module compiler_test.

Local Open Scope Z_scope.

Definition M_test := compiler_monad Z (list_compiler_monoid Z) string.

Definition test_fn : M_test Z :=
  x ← mret 1;
  cput x;;
  y ← cget;
  cappend [1];;
  cappend [2];;
  '(_, z) ← cscope (cappend [3];; cappend [4]);
  mret (y + sum_list (Z.to_nat <$> z)).

Goal crun 0 test_fn = CResult 1 [1; 2] (CSuccess 8).
  vm_compute. match goal with | |- ?x = ?x => exact: eq_refl end.
Abort.

Definition test_error : M_test Z :=
  x ← cerror "a";
  cappend [1];;
  mret x.

Goal crun 0 test_error = CResult 0 [] (CError "a").
  vm_compute. match goal with | |- ?x = ?x => exact: eq_refl end.
Abort.

Definition M_test2 := compiler_monad Z (fn_compiler_monoid (list Z)) string.

Definition test_fn2 : M_test2 Z :=
  x ← mret 1;
  cappend (λ x, 0::x);;
  cappend (λ x, 1::x);;
  mret x.

Goal crun 0 test_fn2 = CResult 0 (λ x : list Z, 0 :: 1 :: x) (CSuccess 1).
  vm_compute. match goal with | |- ?x = ?x => exact: eq_refl end.
Abort.

End compiler_test.
