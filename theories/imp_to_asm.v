Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.filter.
Require Import refframe.product.
Require Import refframe.seq_product.
Require Import refframe.proof_techniques.
Require Import refframe.imp.
Require Import refframe.asm.
Require Import refframe.itree.

(*** [mod_seq_map] *)
Inductive mod_seq_map_state {EV1 : Type} :=
| SMProg
| SMProgRecv (e : EV1)
| SMFilter
| SMFilterRecv (e : EV1)
.
Arguments mod_seq_map_state _ : clear implicits.

Inductive mod_seq_map_filter {EV1 EV2} :
  mod_seq_map_state EV1 → (seq_product_event EV1 (EV1 + EV2)) → option EV2 → mod_seq_map_state EV1 → Prop :=
| SeqMapToFilter e:
  mod_seq_map_filter SMProg (SPELeft e SPRight) None (SMFilterRecv e)
| SeqMapFilterRecv e:
  mod_seq_map_filter (SMFilterRecv e) (SPERight (inl e) SPRight) None SMFilter
| SeqMapFilterOut e:
  mod_seq_map_filter SMFilter (SPERight (inr e) SPRight) (Some e) SMFilter
| SeqMapFilterToProg e:
  mod_seq_map_filter SMFilter (SPERight (inl e) SPLeft) (None) (SMProgRecv e)
| SeqMapProgRecv e:
  mod_seq_map_filter (SMProgRecv e) (SPELeft e SPLeft) None SMProg
.

Definition mod_seq_map {EV1 EV2} (m : module EV1) (f : module (EV1 + EV2)) : module EV2 :=
  mod_map (mod_seq_product m f) mod_seq_map_filter.

Lemma mod_seq_map_step_filter_i {EV1 EV2} m (f : module (EV1 + EV2)) σ σf P `{!TStepI f σf P} :
  TStepI (mod_seq_map m f) (SPRight, σ, σf, SMFilter) (λ G, P (λ b κ P',
    match κ with
    | None => G b None (λ G', P' (λ x, G' (SPRight, σ, x, SMFilter)))
    | Some (inr e) => G b (Some e) (λ G', P' (λ x, G' (SPRight, σ, x, SMFilter)))
    | Some (inl e) => G b None (λ G', P' (λ x, G' (SPLeft, σ, x, SMProgRecv e)))
    end)).
Proof.
  constructor => G /tstepi_proof?.
  apply: (steps_impl_submodule _ (mod_seq_map _ _) (λ x, (SPRight, σ, x, SMFilter))); [done| |].
  - move => /= ?? [?[? HG']]. eexists _. split; [done|] => /= ? /HG'. naive_solver.
  - move => /= ??? Hs. invert_all' @filter_step; simplify_eq. invert_all' @m_step; simplify_eq/=.
    case_match; simplify_eq. all: eexists _, _; split; [done|] => /=; split_and! => /= *; destruct_all?.
    + eexists _. split; [done|]. move => /= ? /H0 [?[??]]. eexists (_, _, _, _). naive_solver.
    + naive_solver.
    + admit.
    + naive_solver.
Admitted.
Global Hint Resolve mod_seq_map_step_filter_i | 1 : tstep.

Lemma mod_seq_map_step_filter_s {EV1 EV2} m (f : module (EV1 + EV2)) σ σf P `{!TStepS f σf P} :
  TStepS (mod_seq_map m f) (SPRight, σ, σf, SMFilter) (λ G, P (λ κ P',
    match κ with
    | None => G None (λ G', P' (λ x, G' (SPRight, σ, x, SMFilter)))
    | Some (inr e) => G (Some e) (λ G', P' (λ x, G' (SPRight, σ, x, SMFilter)))
    | Some (inl e) => G None (λ G', P' (λ x, G' (SPLeft, σ, x, SMProgRecv e)))
    end)).
Proof.
  constructor => G /tsteps_proof [κ [? [? HG']]].
  destruct κ as [[e|e]|]. all: eexists _, _; split; [done|] => G' /= /HG' /steps_spec_has_trace_1 Ht.
  all: apply steps_spec_has_trace_elim.
Admitted.
Global Hint Resolve mod_seq_map_step_filter_s | 1 : tstep.

(** * imp_to_asm *)
Definition imp_to_asm_args (rs : gmap string Z) (vs : list val) : Prop := True.

Definition imp_to_asm_itree_from_env (ins : gset Z) (fns : gmap string Z) : itree (moduleE (imp_event + asm_event) ()) () :=
  pc ← TExist Z;;;
  rs ← TExist _;;;
  TVis (inr (EARecvJump pc rs));;;;
  TAssert (pc ∈ ins);;;;
  b ← TExist bool;;;
  if b then
    f ← TAll _;;;
    TAssume (fns !! f = Some pc);;;;
    vs ← TAll _;;;
    TAssume (imp_to_asm_args rs vs);;;;
    TVis (inl (EIRecvCall f vs))
  else
    Ret ()
.

Definition imp_to_asm_itree_to_env (ins : gset Z) (fns : gmap string Z) : itree (moduleE (imp_event + asm_event) ()) () :=
  Ret ().

Definition imp_to_asm_itree (ins : gset Z) (fns : gmap string Z) : itree (moduleE (imp_event + asm_event) ()) () :=
  ITree.forever (imp_to_asm_itree_from_env ins fns;;;; imp_to_asm_itree_to_env ins fns).

Definition imp_to_asm (m : module imp_event)
 : module asm_event :=
  mod_seq_map m (mod_itree (imp_event + asm_event) ()).

Definition initial_imp_to_asm_state (m : module imp_event) (σ : m.(m_state)) (ins : gset Z) (fns : gmap string Z) : (imp_to_asm m).(m_state) :=
  (SPRight, σ, (imp_to_asm_itree ins fns, ()), SMFilter).

Definition imp_to_asm_combine_inv (m1 m2 : module imp_event) (ins1 ins2 : gset Z) (fns1 fns2 : gmap string Z)
  (σ1 : (asm_prod ins1 ins2 (imp_to_asm m1) (imp_to_asm m2)).(m_state))
  (σ2 : (imp_to_asm (imp_prod (dom _ fns1) (dom _ fns2) m1 m2)).(m_state)) : Prop :=
  let '(σpa, (σpi1, σi1, (t1, _), σf1), (σpi2, σi2, (t2, _), σf2), σfa) := σ1 in
  let '(σps, (σpi, σs1, σs2, σf), (t, _), σfs) := σ2 in
  let ins := (ins1 ∪ ins2) in
  let fns := (fns1 ∪ fns2) in
  σi1 = σs1 ∧
  σi2 = σs2 ∧
  match σfa with
  | APFNone =>
      σpa = SPNone ∧ σfs = SMFilter ∧ σps = SPRight ∧ t = imp_to_asm_itree ins fns
      ∧ t1 = imp_to_asm_itree ins1 fns1 ∧ t2 = imp_to_asm_itree ins2 fns2
      ∧ σf1 = SMFilter ∧ σf2 = SMFilter ∧ σpi1 = SPRight ∧ σpi2 = SPRight
  (* | APFRecvL pc rs =>  *)
  (*     ∃ f vs, σpa = SPLeft ∧  *)
  (*     σfs = SMProgRecv (EIRecvCall f vs) ∧ σps = SPLeft ∧ *)
  (*     t = (imp_to_asm_itree_to_env ins fns;;;; imp_to_asm_itree ins fns) *)
  | _ => False
  end.

Hint Constants Transparent : tstep.

Lemma itree_step_forever_i EV S R (t : itree (moduleE EV S) R) s:
  TStepI (mod_itree EV S) (ITree.forever t, s)
         (λ G, G false None (λ G', itree_rel G' (t;;;;ITree.forever t, s))).
Proof. constructor => ??. Admitted.
Global Hint Resolve itree_step_forever_i : tstep.

Lemma itree_step_forever_s EV S R (t : itree (moduleE EV S) R) s:
  TStepS (mod_itree EV S) (ITree.forever t, s)
         (λ G, G None (λ G', itree_rel G' (t;;;;ITree.forever t, s))).
Proof.
  constructor => ??. eexists _, _. split; [done|] => ? /= ?.
  apply itree_rel_spec_intro. rewrite unfold_forever. setoid_rewrite tau_eutt.
  by apply steps_spec_end.
Qed.
Global Hint Resolve itree_step_forever_s : tstep.

Axiom ELIM_EUTT : ∀ EV R (t1 t2 : itree EV R), t1 ≈ t2 -> t1 = t2.

Lemma tstep_i_generic EV (m : module EV) σ:
  TStepI m σ (λ G, ∀ κ Pσ, m.(m_step) σ κ Pσ → G true κ (λ G', ∃ σ', Pσ σ' ∧ G' σ')).
Proof. constructor => ? HG. apply: steps_impl_step_end => ?? /HG ?. eexists _. split; [done|]. naive_solver. Qed.
Global Hint Resolve tstep_i_generic | 1000 : tstep.

Lemma tstep_s_generic EV (m : module EV) σ:
  TStepS m σ (λ G, ∃ κ, G κ (λ G', ∃ Pσ, m.(m_step) σ κ Pσ ∧ ∀ σ', Pσ σ' → G' σ')).
Proof.
  constructor => ? [??]. eexists _, _. split; [done|] => ? /= [?[??]].
  by apply: steps_spec_step_end; [done|].
Qed.
Global Hint Resolve tstep_s_generic | 1000 : tstep.

Lemma imp_to_asm_combine ins1 ins2 fns1 fns2 m1 m2 σ1 σ2:
  trefines (MS (asm_prod ins1 ins2 (imp_to_asm m1) (imp_to_asm m2))
               (SPNone, initial_imp_to_asm_state m1 σ1 ins1 fns1, initial_imp_to_asm_state m2 σ2 ins2 fns2, APFNone))
           (MS (imp_to_asm (imp_prod (dom _ fns1) (dom _ fns2) m1 m2))
               (initial_imp_to_asm_state (imp_prod _ _ _ _)
                  (SPNone, σ1, σ2, (IPFState IPFNone [])) (ins1 ∪ ins2) (fns1 ∪ fns2))
).
Proof.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { exact (λ _, imp_to_asm_combine_inv _ _ _ _ _ _). }
  { naive_solver. } { done. }
  move => /= {σ1 σ2} {}n Hloop [[[σpa [[[σpi1 σi1] [t1 []]] σf1]] [[[σpi2 σi2] [t2 []]] σf2]] σfa].
  move => [[[σps [[[σpi σs1] σs2] σf]] [t []]] σfs] /= ?.
  case_match; destruct_all?; simplify_eq.
  (* - admit. *)
  (* - admit. *)
  - tstep_s => ? /= /ELIM_EUTT <-. rewrite -/(imp_to_asm_itree _ _).
    tstep_s => ? /= /ELIM_EUTT <-. tstep_s => ? /= /ELIM_EUTT <-.
    tstep_i => ????. invert_all asm_prod_filter.
    + tstep_s. eexists _. move => ? /= /ELIM_EUTT <-.
      tstep_s => ? /= /ELIM_EUTT <-. tstep_s. eexists _. move => ? /= /ELIM_EUTT <-.
      tstep_s => ? /= /ELIM_EUTT <-. tstep_s. split; [done|]. move => ? /= /ELIM_EUTT <-.
      tstep_s => ? /= /ELIM_EUTT <-. tstep_s. split; [admit|]. move => ? /= /ELIM_EUTT <-.
      tstep_s => ? /= /ELIM_EUTT <-. tstep_s. eexists true. move => ? /= /ELIM_EUTT <-.
      tstep_s => ? /= /ELIM_EUTT <-. tstep_s => f. move => ? /= /ELIM_EUTT <-.
      tstep_s => ? /= /ELIM_EUTT <-. tstep_s => Hf. move => ? /= /ELIM_EUTT <-.
      tstep_s => ? /= /ELIM_EUTT <-. tstep_s => vs. move => ? /= /ELIM_EUTT <-.
      tstep_s => ? /= /ELIM_EUTT <-. tstep_s => Hvs. move => ? /= /ELIM_EUTT <-.
      tstep_s => ? /= /ELIM_EUTT <-.
      tstep_i => ? -> ?? [-> ->] ? /= /ELIM_EUTT <-.
      admit.
    + admit.

(* tstep_s. eexists true. move => ? /= /ELIM_EUTT <-. *)
(*       tstep_s => ? /= /ELIM_EUTT <-. tstep_s. eexists _. move => ? /= /ELIM_EUTT <-. *)
(*       tstep_s => ? /= /ELIM_EUTT <-. tstep_s. eexists _. move => ? /= /ELIM_EUTT <-. *)
(*       tstep_s => ? /= /ELIM_EUTT <-. tstep_s. split; [done|]. move => ? /= /ELIM_EUTT <-. *)
(*       tstep_s => ? /= /ELIM_EUTT <-. tstep_s. split; [admit|]. move => ? /= /ELIM_EUTT <-. *)
(*       tstep_s => ? /= /ELIM_EUTT <-. tstep_s => f. move => ? /= /ELIM_EUTT <-. *)
(*       tstep_s => ? /= /ELIM_EUTT <-. tstep_s => Hf. move => ? /= /ELIM_EUTT <-. *)
(*       tstep_s => ? /= /ELIM_EUTT <-. tstep_s => vs. move => ? /= /ELIM_EUTT <-. *)
(*       tstep_s => ? /= /ELIM_EUTT <-. tstep_s => Hvs. move => ? /= /ELIM_EUTT <-. *)
(*       tstep_s => ? /= /ELIM_EUTT <-. *)
 (* apply: Hloop. naive_solver. *)
  (* - admit. *)
  (* - admit. *)
Abort.
