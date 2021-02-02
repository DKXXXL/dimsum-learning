From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From refframe.rec_lang Require Export lang heap.
Set Default Proof Using "Type".
Import uPred.

Class reclangG Σ := RecLangG {
  rec_lang_invG : invG Σ;
  rec_lang_gen_heapG :> heapG Σ
}.

Instance rec_irisG `{!reclangG Σ} : irisG rec_lang Σ := {
  iris_invG := rec_lang_invG;
  state_interp σ κs _ := state_ctx σ κs;
  fork_post _ := True%I;
}.
Global Opaque iris_invG.

Local Hint Extern 0 (reducible _ _) => eexists _, _, _, _; simpl : core.
Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core.

Section lifting.
Context `{!reclangG Σ}.

Lemma wp_binop Φ (n1 n2 : Z) op E:
  ▷ Φ (ValNum (match op with | AddOp => n1 + n2 | EqOp => Z_of_bool (bool_decide (n1 = n2)) end))%Z -∗
  WP BinOp (Val n1) op (Val n2) @ E {{ Φ }}.
Proof.
  iIntros "HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "Hctx !>".
  iSplit; first by eauto using BinOpStep.
  iIntros "!# /=" (e2 σ2 efs Hst). invert_all lang.step.
  iModIntro. iFrame. iSplit => //. by case_match.
Qed.

Lemma wp_let E Φ n v e:
  ▷ WP (subst n v e) @ E {{ Φ }} -∗
  WP LetE n (Val v) e @ E {{ Φ }}.
Proof.
  iIntros "HΦ".
  iApply wp_lift_pure_det_head_step_no_fork'; eauto using LetStep.
  move => /= *. invert_all lang.step. naive_solver.
Qed.

Lemma wp_if E Φ e1 e2 n:
  ▷ WP (if bool_decide (n ≠ 0) then e1 else e2) @ E {{ Φ }} -∗
  WP If (Val n) e1 e2 @ E {{ Φ }}.
Proof.
  iIntros "HΦ".
  iApply wp_lift_pure_det_head_step_no_fork'; eauto using IfStep.
  move => /= *. invert_all lang.step. do 2 case_bool_decide; naive_solver.
Qed.

Lemma wp_call E Φ f vs fn:
  length vs = length fn.(fd_args) →
  fntbl_entry f (Some fn) -∗
  ▷ WP (subst_l fn.(fd_args) vs fn.(fd_body)) @ E {{ Φ }} -∗
  WP Call f (Val <$> vs) @ E {{ Φ }}.
Proof.
  iIntros (?) "Hfn HΦ".
  iApply wp_lift_head_step; auto.
  iIntros (σ1 κ κs n) "(Hfctx & Hsctx)".
  iDestruct (fntbl_entry_lookup with "Hfctx Hfn") as %?.
  iMod (fupd_intro_mask' _ ∅) as "HE". set_solver.
  iModIntro.
  iSplit; first by eauto using CallInternalStep.
  iIntros "!# /=" (e2 σ2 efs Hst). iMod "HE". invert_all lang.step.
  iModIntro. iFrame.
Qed.

Lemma wp_ext_call vs E Φ f:
  fntbl_entry f None -∗
  WPspec rec_event module_spec_name [CallEvt f vs] E (∀ v, WPspec rec_event module_spec_name [RecvRetEvt v] E (Φ v))  -∗
  WP Call f (Val <$> vs) @ E {{ Φ }}.
Proof.
  iIntros "Hfn HΦ".
  iApply wp_lift_head_step; auto.
  iIntros (σ1 κ κs n) "(#Hfctx & Hsctx)".
  iDestruct (fntbl_entry_lookup with "Hfctx Hfn") as %?.
  iMod "HΦ". iModIntro.
  iSplit; first by eauto using CallExternalStep.
  iIntros "!# /=" (e2 σ2 efs Hst). invert_all lang.step.

  iDestruct "HΦ" as (??) "[Hm HΦ]".
  iDestruct "Hsctx" as (κsstart σscur Hfull Htrace Hnub) "Hm2".
  iDestruct (ghost_var_agree with "Hm Hm2") as %Heq.
  Require Import Coq.Program.Equality.
  dependent destruction Heq.
  iDestruct "HΦ" as (? ?) "HΦ".
  iMod (ghost_var_update_halves with "Hm Hm2") as "[Hm Hm2]".
  iMod ("HΦ" with "Hm [%]") as "HΦ". {
    contradict Hnub. move: Hnub => [? /(has_trace_cons_inv _ _) [? [? [? Hor]]]].
    rewrite Hfull fmap_app fmap_cons /= -app_assoc.
    eexists _. apply: has_trace_trans => //=. apply: (has_trace_trans []) => //.
    case: Hor => [?|[? /has_trace_ub_inv [?[??]]]]. { by apply: TraceUbRefl. }
    apply: TraceStepSome; [done|]. apply: (has_trace_trans []) => //. by apply: TraceUb.
  }
  iModIntro.
  iSplitL "Hm2". {
    iSplit => //. iExists _, _. iFrame. iPureIntro. rewrite {1}Hfull. rewrite cons_middle app_assoc.
    split_and! => //. rewrite fmap_app. by apply: has_trace_trans.
  }
  iSplit => //.

Admitted.



End lifting.
