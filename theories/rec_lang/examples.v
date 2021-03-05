From refframe.rec_lang Require Export proofmode.
From refframe.rec_lang Require Import adequacy.

Section examples.
Context `{!reclangG Σ}.

Inductive test_state : Type :=
| TSInit | TSCall (n : Z) | TSFinal | TSUb.
Inductive test_step : test_state → option rec_event → test_state → Prop :=
| TSSInit n:
  test_step TSInit (Some $ CallEvt "extfn" [ValNum n]) (TSCall n)
| TSSCall n v:
  test_step (TSCall n) (Some $ RecvRetEvt v) (if bool_decide (v = n) then TSFinal else TSUb).
Definition test_module : module rec_event := {|
  m_state := test_state;
  m_step := test_step;
  m_is_ub σ := σ = TSUb;
|}.

Definition test_main : lang.expr :=
  LetE "n" (BinOp 1 AddOp 1) $
  LetE "ret" (Call "extfn" [ Var "n" ] ) $
  BinOp (Var "ret") EqOp 2.

Lemma wp_test_main :
  fntbl_entry "extfn" None -∗
  own_module module_spec_name test_module TSInit -∗
  WP test_main {{ v, ⌜v = 1⌝ }}.
Proof.
  iIntros "#Hextfn Hm".
  rewrite /test_main.
  iStartProof.
  wp_bind (BinOp _ _ _).
  iApply wp_binop. iModIntro.
  iApply wp_let. simpl. iModIntro.
  wp_bind (Call _ _).
  iApply (wp_ext_call [_]) => //.

  iApply (wpspec_cons with "Hm"). { apply: TraceStepSome; [|apply:TraceEnd]. econstructor. }
  iIntros "Hm". iApply wpspec_nil. iIntros (v).
  iApply (wpspec_cons with "Hm"). { apply: TraceStepSome; [|apply:TraceEnd]. econstructor. }
  iIntros "Hm". iMod (noub_use with "Hm") as (Hub) "Hm".
  iApply wpspec_nil.
  case_bool_decide; subst. 2: { contradict Hub. eexists _. by apply: TraceUbRefl. }

  iApply wp_let => /=. iModIntro.
  iApply wp_binop. iPureIntro. by case_bool_decide.
Qed.

Definition test_concurrent : lang.expr :=
  Call "extfn" [ Val 1 ].

Inductive test_concurrent_step : nat → option rec_event → nat → Prop :=
| TCSCall n:
  test_concurrent_step n (Some $ CallEvt "extfn" [ValNum 1]) (S n)
| TSSRet n v:
  test_concurrent_step (S n) (Some $ RecvRetEvt v) n.
Definition test_concurrent_module : module rec_event := {|
  m_state := nat;
  m_step := test_concurrent_step;
  m_is_ub σ := False;
|}.
(*   own_module module_spec_name test_module TSInit -∗ *)

(* Lemma wp_test_concurrent : *)
(*   fntbl_entry "extfn" None -∗ *)
(*   WP test_concurrent {{ v, True }}. *)
(* Proof. *)

End examples.

Lemma test_main_adequate :
  (∀ κs, LEM (TSInit ~{ test_module, κs }~> -)) →
  MS (iris_module rec_lang) ([test_main], {| st_fns := ∅ |}) ⊑ MS test_module TSInit.
Proof.
  move => HLEM.
  set Σ : gFunctors := #[reclangΣ].
  apply: (reclang_adequacy Σ) => //.
  iIntros (?) "Hown #Hfn /=". iModIntro. iSplitL => //.
  iApply wp_mono. by iIntros (?) "_".
  iApply wp_test_main => //. by iApply (fntbl_entry_intro with "Hfn").
Qed.

(* Print Assumptions test_main_adequate. *)
