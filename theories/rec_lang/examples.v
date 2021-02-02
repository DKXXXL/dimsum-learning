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
  m_initial := TSInit;
  m_step := test_step;
  m_is_ub σ := σ = TSUb;
|}.

Definition test_main : lang.expr :=
  LetE "n" (BinOp 1 AddOp 1) $
  LetE "ret" (Call "extfn" [ Var "n" ] ) $
  BinOp (Var "ret") EqOp 2.

Lemma wp_test_main :
  fntbl_entry "extfn" None -∗
  own_module rec_event module_spec_name test_module TSInit -∗
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

  iExists test_module.
  iMod (fupd_intro_mask' _ ∅) as "HE" => //. do 2 iModIntro.
  iExists _. iFrame "Hm".
  iExists _. iSplit. { iPureIntro. apply: TraceStepSome. econstructor. constructor. }
  iIntros "Hm" (_). iMod "HE" as %_.
  iIntros "!>" (v).

  iExists test_module.
  iMod (fupd_intro_mask' _ ∅) as "HE" => //. do 2 iModIntro.
  iExists _. iFrame "Hm".
  iExists _. iSplit. { iPureIntro. apply: TraceStepSome. econstructor. constructor. }
  iIntros "Hm" (Hub). iMod "HE" as %_.
  case_bool_decide; subst. 2: {
    contradict Hub. eexists _. apply: TraceStepSome. econstructor.
    econstructor. by case_bool_decide.
  }
  iIntros "!>".

  iApply wp_let => /=. iModIntro.
  iApply wp_binop. iPureIntro. by case_bool_decide.
  Unshelve.
  apply: TSInit.
Qed.

End examples.

Lemma test_main_adequate :
  (∀ κs, LEM (test_module.(m_initial) ~{ test_module, κs }~> -)) →
  iris_module rec_lang ([test_main], {| st_fns := ∅ |}) ⊑ test_module.
Proof.
  move => HLEM.
  set Σ : gFunctors := #[reclangΣ].
  apply: (reclang_adequacy Σ) => //.
  iIntros (?) "Hown #Hfn /=". iModIntro. iSplitL => //.
  iApply wp_mono. by iIntros (?) "_".
  iApply wp_test_main => //. by iApply (fntbl_entry_intro with "Hfn").
Qed.

(* Print Assumptions test_main_adequate. *)
