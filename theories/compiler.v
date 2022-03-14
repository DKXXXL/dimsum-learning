Require Import refframe.base.
(* We require functional extensionality such that we can use leibniz
equiality for compiler_monad. *)
(* Require Import refframe.axioms. *)

Set Default Proof Using "Type".

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

Inductive compiler_success {R E : Type} :=
| CSuccess (res : R) | CError (err : E).
Arguments compiler_success : clear implicits.

Record compiler_result {S : Type} {A : compiler_monoid} {E R : Type} := CResult {
  c_state : S;
  c_prog : A;
  c_result : compiler_success R E;
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

Definition cerror {S A E R} : E → compiler_monad S A E R :=
  λ err s, CResult s (cm_empty A) (CError err).

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

End compiler_monad.

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
