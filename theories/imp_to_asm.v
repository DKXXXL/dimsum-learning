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
Global Hint Transparent mod_seq_map : tstep.

Lemma mod_seq_map_nil_l {EV1 EV2} m (f : module (EV1 + EV2)) σ Pσ Pσf σf κs σm:
  σ ~{ m, tnil }~>ₜ Pσ →
  (∀ σ', Pσ σ' → (SPLeft, σ', σf, σm) ~{ mod_seq_map m f, κs }~>ₜ Pσf) →
  (SPLeft, σ, σf, σm) ~{ mod_seq_map m f, κs }~>ₜ Pσf.
Proof.
  move => Hσ Hcont.
  apply: mod_map_nil.
  - by apply: seq_product_nil_l.
  - move => [[??]?] /=. naive_solver.
Qed.

Lemma mod_seq_map_nil_r {EV1 EV2} m (f : module (EV1 + EV2)) σ Pσ Pσf σf κs σm:
  σf ~{ f, tnil }~>ₜ Pσ →
  (∀ σ', Pσ σ' → (SPRight, σ, σ', σm) ~{ mod_seq_map m f, κs }~>ₜ Pσf) →
  (SPRight, σ, σf, σm) ~{ mod_seq_map m f, κs }~>ₜ Pσf.
Proof.
  move => Hσ Hcont.
  apply: mod_map_nil.
  - by apply: seq_product_nil_r.
  - move => [[??]?] /=. naive_solver.
Qed.

Lemma mod_seq_map_step_filter_i {EV1 EV2} m (f : module (EV1 + EV2)) σ σf P `{!TStepI f σf P} :
  TStepI (mod_seq_map m f) (SPRight, σ, σf, SMFilter) (λ G, P (λ b κ P',
    match κ with
    | None => G b None (λ G', P' (λ x, G' (SPRight, σ, x, SMFilter)))
    | Some (inr e) => G b (Some e) (λ G', P' (λ x, G' (SPRight, σ, x, SMFilter)))
    | Some (inl e) => G b None (λ G', P' (λ x, G' (SPLeft, σ, x, SMProgRecv e)))
    end)).
Proof.
  constructor => G /tstepi_proof?. clear TStepI0.
  (* Set Typeclasses Debug. *)
  (* tstep_i.  *)
  (* apply: steps_impl_mono; [done|]. *)
  (* move => ? κ ?/= [?[?[?[??]]]] ?? κ' ??. *)
  (* destruct κ as [[e|e]|]; simplify_eq/=. *)
  apply: (steps_impl_submodule _ (mod_seq_map _ _) (λ x, (SPRight, σ, x, SMFilter))); [done| |].
  - move => /= ?? [?[? [? [? HG']]]]. eexists _, _. split_and!; [done..|] => /= ? /HG'. naive_solver.
  - move => /= ??? Hs. invert_all' @filter_step; simplify_eq. invert_all' @m_step; simplify_eq/=.
    case_match; simplify_eq. all: eexists _, _; split; [done|] => /=; split_and! => /= *; destruct_all?.
    + eexists _, _. split_and!; [done..|]. move => /= ? /H2 [?[??]]. eexists (_, _, _, _). naive_solver.
    + naive_solver.
    + admit.
    + naive_solver.
Admitted.
Global Hint Resolve mod_seq_map_step_filter_i | 1 : tstep.

Lemma mod_seq_map_step_filter_recv_i {EV1 EV2} m (f : module (EV1 + EV2)) σ σf P `{!TStepI f σf P} e :
  TStepI (mod_seq_map m f) (SPRight, σ, σf, SMFilterRecv e) (λ G, P (λ b κ P',
       if κ is Some e' then inl e = e' → G b None (λ G', P' (λ x, G' (SPRight, σ, x, SMFilter)))
       else G b None (λ G', P' (λ x, G' (SPRight, σ, x, SMFilterRecv e))))).
Proof. Admitted.
Global Hint Resolve mod_seq_map_step_filter_recv_i | 1 : tstep.

Lemma mod_seq_map_step_prog_i {EV1 EV2} m (f : module (EV1 + EV2)) σ σf P `{!TStepI m σ P}:
  TStepI (mod_seq_map m f) (SPLeft, σ, σf, SMProg) (λ G, P (λ b κ P',
   G b None (λ G', P' (λ x, if κ is Some e then G' (SPRight, x, σf, SMFilterRecv e)
                            else G' (SPLeft, x, σf, SMProg))))).
Proof. Admitted.
Global Hint Resolve mod_seq_map_step_prog_i | 1 : tstep.

Lemma mod_seq_map_step_prog_recv_i {EV1 EV2} m (f : module (EV1 + EV2)) σ σf P `{!TStepI m σ P} e:
  TStepI (mod_seq_map m f) (SPLeft, σ, σf, SMProgRecv e) (λ G, P (λ b κ P',
   if κ is Some e' then e = e' → G b None (λ G', P' (λ x, G' (SPLeft, x, σf, SMProg)))
                 else G b None (λ G', P' (λ x, G' (SPLeft, x, σf, SMProgRecv e))))).
Proof. Admitted.
Global Hint Resolve mod_seq_map_step_prog_recv_i | 1 : tstep.

Lemma mod_seq_map_step_filter_s {EV1 EV2} m (f : module (EV1 + EV2)) σ σf P `{!TStepS f σf P} :
  TStepS (mod_seq_map m f) (SPRight, σ, σf, SMFilter) (λ G, P (λ κ P',
    match κ with
    | None => G None (λ G', P' (λ x, G' (SPRight, σ, x, SMFilter)))
    | Some (inr e) => G (Some e) (λ G', P' (λ x, G' (SPRight, σ, x, SMFilter)))
    | Some (inl e) => G None (λ G', P' (λ x, G' (SPLeft, σ, x, SMProgRecv e)))
    end)).
Proof.
  constructor => G /tsteps_proof [κ [? [? HG']]]. clear TStepS0.
  destruct κ as [[e|e]|]. all: eexists _, _; split; [done|] => G' /= /HG'?; tstep_s.
  - eexists (Some (inl e)), _. split; [done|]. eexists _, _ => /=. split_and!; [econs|done|done].
  - eexists (Some (inr e)), _. split; [done|]. eexists _, _ => /=. split_and!; [econs|done|done].
  - eexists None, _. split; [done|]. eexists _, _ => /=. naive_solver.
Qed.
Global Hint Resolve mod_seq_map_step_filter_s | 1 : tstep.

Lemma mod_seq_map_step_filter_recv_s {EV1 EV2} m (f : module (EV1 + EV2)) σ σf P `{!TStepS f σf P} e:
  TStepS (mod_seq_map m f) (SPRight, σ, σf, SMFilterRecv e) (λ G, P (λ κ P',
   G None (λ G', if κ is Some e' then inl e = e' ∧ P' (λ x, G' (SPRight, σ, x, SMFilter))
                 else P' (λ x, G' (SPRight, σ, x, SMFilterRecv e))))).
Proof.
  constructor => G /tsteps_proof [κ [? [? HG']]]. eexists _, _. split; [done|].
  move => ? /=?. clear TStepS0. tstep_s. eexists κ, _. split; [by case_match|].
  case_match; destruct_all?; simplify_eq; eexists _, _ => /=.
  - split_and!; [econs|done|]. by apply HG'.
  - split_and!; [done..|]. by apply HG'.
Qed.
Global Hint Resolve mod_seq_map_step_filter_recv_s | 1 : tstep.

Lemma mod_seq_map_step_prog_s {EV1 EV2} m (f : module (EV1 + EV2)) σ σf P `{!TStepS m σ P}:
  TStepS (mod_seq_map m f) (SPLeft, σ, σf, SMProg) (λ G, P (λ κ P',
   G None (λ G', P' (λ x, if κ is Some e then G' (SPRight, x, σf, SMFilterRecv e)
                          else G' (SPLeft, x, σf, SMProg))))).
Proof.
  constructor => G /tsteps_proof [κ [? [? HG']]]. eexists _, _. split; [done|].
  move => ? /=?. clear TStepS0. tstep_s.
  eexists κ; case_match; eexists _; (split; [done|]); eexists _, _ => /=.
  - split_and!; [econs|done|naive_solver].
  - split_and!; [done..|naive_solver].
Qed.
Global Hint Resolve mod_seq_map_step_prog_s | 1 : tstep.

Lemma mod_seq_map_step_prog_recv_s {EV1 EV2} m (f : module (EV1 + EV2)) σ σf P `{!TStepS m σ P} e:
  TStepS (mod_seq_map m f) (SPLeft, σ, σf, SMProgRecv e) (λ G, P (λ κ P',
   G None (λ G', if κ is Some e' then e = e' ∧ P' (λ x, G' (SPLeft, x, σf, SMProg))
                 else P' (λ x, G' (SPLeft, x, σf, SMProgRecv e))))).
Proof.
  constructor => G /tsteps_proof [κ [? [? HG']]]. eexists _, _. split; [done|].
  move => ? /=?. clear TStepS0. tstep_s. eexists κ, _. split; [by case_match|].
  case_match; destruct_all?; simplify_eq; eexists _, _ => /=.
  - split_and!; [econs|done|]. by apply HG'.
  - split_and!; [done..|]. by apply HG'.
Qed.
Global Hint Resolve mod_seq_map_step_prog_recv_s | 1 : tstep.

(** * imp_to_asm *)
Definition imp_to_asm_args (ret : Z) (rs : gmap string Z) (vs : list val) : Prop.
(* args correspond to registers *)
(* R30 contain ret *)
Admitted.

Definition imp_to_asm_ret (rs rsold : gmap string Z) (v : val) : Prop.
(* registers stay the same / get clobbered *)
(* R0 contain representation of v *)
Admitted.

Definition imp_to_asm_itree_from_env (ins : gset Z) (fns : gset string) (f2i : gmap string Z) : itree (moduleE (imp_event + asm_event) ()) () :=
  pc ← TExist Z;;;
  rs ← TExist _;;;
  TVis (inr (EARecvJump pc rs));;;;
  (* env chooses if this is a function call or return *)
  b ← TAll bool;;;
  if b then
    (* env chooses return address *)
    ret ← TAll _;;;
    (* env chooses function name *)
    f ← TAll _;;;
    (* env chooses arguments *)
    vs ← TAll _;;;
    (* env proves that function name is valid *)
    TAssume (f ∈ fns);;;;
    (* env proves it calls the right address *)
    TAssume (f2i !! f = Some pc);;;;
    (* env proves that rs corresponds to vs and ret  *)
    TAssume (imp_to_asm_args ret rs vs);;;;
    TVis (inl (EIRecvCall f vs))
  else
    (* env chooses return value *)
    v ← TAll _;;;
    (* env chooses old registers *)
    rsold ← TAll _;;;
    (* TODO: get rsold from call stack *)
    (* env proves that rs is updated correctly *)
    TAssume (imp_to_asm_ret rs rsold v);;;;
    TVis (inl (EIRecvReturn v))
.

Definition imp_to_asm_itree_to_env (ins : gset Z) (fns : gset string) (f2i : gmap string Z) : itree (moduleE (imp_event + asm_event) ()) () :=
  pc ← TExist Z;;;
  rs ← TExist _;;;
  (* program chooses whether it returns or makes a function call *)
  b ← TExist bool;;;
  if b then
    (* program chooses return address *)
    ret ← TExist Z;;;
    (* program chooses which function it calls *)
    f ← TExist _;;;
    (* program chooses the arguments of the function *)
    vs ← TExist _;;;
    (* program proves that this function is external *)
    TAssert (f ∉ fns);;;;
    (* program proves that the address is correct *)
    TAssert (f2i !! f = Some pc);;;;
    (* program proves that rs corresponds to vs and ret  *)
    TAssert (imp_to_asm_args ret rs vs);;;;
    TVis (inl (EICall f vs));;;;
    TVis (inr (EAJump pc rs))
  else
    (* program chooses return value *)
    v ← TExist _;;;
    (* program chooses old registers *)
    rsold ← TExist _;;;
    (* TODO: get rsold from call stack *)
    (* env proves that rs is updated correctly *)
    TAssert (imp_to_asm_ret rs rsold v);;;;
    TVis (inl (EIReturn v));;;;
    TVis (inr (EAJump pc rs)).

Definition imp_to_asm_itree (ins : gset Z) (fns : gset string) (f2i : gmap string Z) : itree (moduleE (imp_event + asm_event) ()) () :=
  ITree.forever (imp_to_asm_itree_from_env ins fns f2i;;;; imp_to_asm_itree_to_env ins fns f2i).

Definition imp_to_asm (m : module imp_event) : module asm_event :=
  mod_seq_map m (mod_itree (imp_event + asm_event) ()).

Definition initial_imp_to_asm_state (m : module imp_event) (σ : m.(m_state)) (ins : gset Z) (fns : gset string) (f2i : gmap string Z) : (imp_to_asm m).(m_state) :=
  (SPRight, σ, (imp_to_asm_itree ins fns f2i, ()), SMFilter).

Definition imp_to_asm_combine_inv (m1 m2 : module imp_event)
           (ins1 ins2 : gset Z) (fns1 fns2 : gset string) (f2i1 f2i2 : gmap string Z)
  (σ1 : (asm_prod ins1 ins2 (imp_to_asm m1) (imp_to_asm m2)).(m_state))
  (σ2 : (imp_to_asm (imp_prod fns1 fns2 m1 m2)).(m_state)) : Prop :=
  let '(σpa, (σpi1, σi1, (t1, _), σf1), (σpi2, σi2, (t2, _), σf2), σfa) := σ1 in
  let '(σps, (σpi, σs1, σs2, σf), (t, _), σfs) := σ2 in
  let ins := (ins1 ∪ ins2) in
  let fns := (fns1 ∪ fns2) in
  let f2i := (f2i1 ∪ f2i2) in
  σi1 = σs1 ∧
  σi2 = σs2 ∧
  ((∃ cs,
      σfa = APFNone ∧
      σpa = SPNone ∧ σfs = SMFilter ∧ σps = SPRight ∧ t = imp_to_asm_itree ins fns f2i
      ∧ t1 = imp_to_asm_itree ins1 fns1 f2i1 ∧ t2 = imp_to_asm_itree ins2 fns2 f2i2
      ∧ σf1 = SMFilter ∧ σf2 = SMFilter ∧ σpi1 = SPRight ∧ σpi2 = SPRight
      ∧ σpi = SPNone ∧ σf = IPFState IPFNone cs) ∨
  (∃ cs,
      ( (∃ f vs, σf = IPFState (IPFLeftRecvCall f vs) cs ∧ σf1 = SMProgRecv (EIRecvCall f vs))
      ∨ (∃ v, σf = IPFState (IPFLeftRecvReturn v) cs ∧ σf1 = SMProgRecv (EIRecvReturn v))
      ∨ σf = IPFState IPFLeft cs ∧ σf1 = SMProg)
      ∧ σfa = APFLeft ∧ σpa = SPLeft ∧ σfs = SMProg ∧ σps = SPLeft
      ∧ t = (imp_to_asm_itree_to_env ins fns f2i;;;; imp_to_asm_itree ins fns f2i)
      ∧ t1 = (imp_to_asm_itree_to_env ins1 fns1 f2i1;;;; (imp_to_asm_itree ins1 fns1 f2i1))
      ∧ t2 = imp_to_asm_itree ins2 fns2 f2i2
      ∧ σf2 = SMFilter ∧ σpi1 = SPLeft ∧ σpi2 = SPRight
      ∧ σpi = SPLeft) ∨
  (∃ cs,
      ((∃ f vs, σf = IPFState (IPFRightRecvCall f vs) cs ∧ σf2 = SMProgRecv (EIRecvCall f vs))
      ∨ (∃ v, σf = IPFState (IPFRightRecvReturn v) cs ∧ σf2 = SMProgRecv (EIRecvReturn v))
      ∨ σf = IPFState IPFRight cs ∧ σf2 = SMProg)
      ∧ σfa = APFRight ∧ σpa = SPRight ∧ σfs = SMProg ∧ σps = SPLeft
      ∧ t = (imp_to_asm_itree_to_env ins fns f2i;;;; imp_to_asm_itree ins fns f2i)
      ∧ t1 = imp_to_asm_itree ins1 fns1 f2i1
      ∧ t2 = (imp_to_asm_itree_to_env ins2 fns2 f2i2;;;; (imp_to_asm_itree ins2 fns2 f2i2))
      ∧ σf1 = SMFilter ∧ σpi1 = SPRight ∧ σpi2 = SPLeft
      ∧ σpi = SPRight)).
Hint Constants Transparent : tstep.

Program Definition itree_step_forever_s EV S R (t : itree (moduleE EV S) R) s :=
  @eq_it_to_tstep_s EV S s (ITree.forever t) (t;;;;ITree.forever t) _.
Next Obligation. move => *. setoid_rewrite unfold_forever at 1. by setoid_rewrite tau_eutt. Qed.
Global Hint Resolve itree_step_forever_s : tstep.

Program Definition itree_step_forever_i EV S R (t : itree (moduleE EV S) R) s :=
  @eq_it_to_tstep_i EV S s (ITree.forever t) (t;;;; (ITree.forever t)) _.
Next Obligation. move => *. setoid_rewrite unfold_forever at 1. by setoid_rewrite tau_eutt. Qed.
Global Hint Resolve itree_step_forever_i : tstep.

Axiom ELIM_EUTT : ∀ EV R (t1 t2 : itree EV R), t1 ≈ t2 -> t1 = t2.
Local Ltac go :=
      unfold itree_rel; intros; destruct_all?; simplify_eq/=; repeat lazymatch goal with | H : _ ≈ _ |- _ => apply ELIM_EUTT in H; subst end.
Local Ltac go_i := tstep_i; go.
Local Ltac go_s := tstep_s; go.

Lemma imp_to_asm_combine ins1 ins2 fns1 fns2 f2i1 f2i2 m1 m2 σ1 σ2 `{!VisNoAll m1} `{!VisNoAll m2}:
  ins1 ## ins2 →
  fns1 ## fns2 →
  (∀ f, f ∈ fns1 → ∃ i, i ∈ ins1 ∧ f2i1 !! f = Some i) →
  (∀ f, f ∈ fns2 → ∃ i, i ∈ ins2 ∧ f2i2 !! f = Some i) →
  (∀ f i1 i2, f2i1 !! f = Some i1 → f2i2 !! f = Some i2 → i1 = i2) →
  (∀ f i, f2i1 !! f = Some i → i ∈ ins2 → f ∈ fns2) →
  (∀ f i, f2i2 !! f = Some i → i ∈ ins1 → f ∈ fns1) →
  trefines (MS (asm_prod ins1 ins2 (imp_to_asm m1) (imp_to_asm m2))
               (SPNone, initial_imp_to_asm_state m1 σ1 ins1 fns1 f2i1,
                 initial_imp_to_asm_state m2 σ2 ins2 fns2 f2i2, APFNone))
           (MS (imp_to_asm (imp_prod fns1 fns2 m1 m2))
               (initial_imp_to_asm_state (imp_prod _ _ _ _)
                  (SPNone, σ1, σ2, (IPFState IPFNone [])) (ins1 ∪ ins2) (fns1 ∪ fns2) (f2i1 ∪ f2i2))
).
Proof.
  move => Hdisji Hdisjf Hin1 Hin2 Hagree Ho1 Ho2.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { exact (λ _, imp_to_asm_combine_inv _ _ _ _ _ _ f2i1 f2i2). }
  { naive_solver. } { done. }
  move => /= {σ1 σ2} {}n Hloop [[[σpa [[[σpi1 σi1] [t1 []]] σf1]] [[[σpi2 σi2] [t2 []]] σf2]] σfa].
  move => [[[σps [[[σpi σs1] σs2] σf]] [t []]] σfs] /= ?.
  destruct_all?; simplify_eq.
  - go_s. rewrite -/(imp_to_asm_itree _ _).
    go_s. go_s. go_i. invert_all asm_prod_filter.
    + go_s. eexists _. go.
      go_s. go_s. eexists _. go. go_s. go_s. split; [done|]. go.
      go_s. go_s. rename x into b.
      go_i. rewrite -/(imp_to_asm_itree _ _). go_i. go_i. go_i.
      go_i. go_i. go_i. go_i.
      invert_all asm_prod_filter.
      go_i. go_i. eexists b. go. destruct b.
      * go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s.
        revert select (_ ∈ (_ ∪ _)) => Hin. revert select ((_ ∪ _) !! _ = Some _) => Hf2i.
        move: Hin => /elem_of_union [Hf|Hf]. 2: {
          move: (Hf) => /Hin2[?[??]]. move: Hf2i => /lookup_union_Some_raw[?|[??]]; simplify_eq => //. naive_solver.
        }
        move: (Hf) => /Hin1[f[??]].
        have ?: x = f. { move: Hf2i => /lookup_union_Some_raw[?|[??]]; simplify_eq => //. } subst.
        eexists _, _, _. split; [apply IPFCallExtToLeft|]. { done. } { by apply: Hdisjf. } simpl.
        split; [done|].
        go_i. go_i. eexists _. go. go_i. go_i. eexists _. go. go_i. go_i. eexists _. go.
        go_i. go_i. split; [done|]. go. go_i. go_i. split; [done|]. go.
        go_i. go_i. split; [done|]. go.
        go_i. apply Hloop. naive_solver.
        (* split_and! => //. right.  naive_solver. *)
      * go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s.
        have [cs' ?]: ∃ cs', cs = IPFLeft :: cs' by admit. subst.
        eexists _, _, _. split; [apply IPFReturnExtToLeft|]. simpl. split; [done|].
        go_i. go_i. eexists _. go. go_i. go_i. eexists _. go.
        go_i. go_i. split; [done|]. go.
        go_i. apply Hloop. naive_solver.
    + go_s. eexists _. go.
      go_s. go_s. eexists _. go. go_s. go_s. split; [done|]. go.
      go_s. go_s. rename x into b.
      go_i. rewrite -/(imp_to_asm_itree _ _). go_i. go_i. go_i.
      go_i. go_i. go_i. go_i.
      invert_all asm_prod_filter.
      go_i. go_i. eexists b. go. destruct b.
      * go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s.
        revert select (_ ∈ (_ ∪ _)) => Hin. revert select ((_ ∪ _) !! _ = Some _) => Hf2i.
        move: Hin => /elem_of_union [Hf|Hf]. 1: {
          move: (Hf) => /Hin1[?[??]]. move: Hf2i => /lookup_union_Some_raw[?|[??]]; simplify_eq => //.
        }
        move: (Hf) => /Hin2[f[??]].
        have ?: x = f. { move: Hf2i => /lookup_union_Some_raw[?|[??]]; simplify_eq => //. naive_solver. } subst.
        eexists _, _, _. split; [apply IPFCallExtToRight|]. { move => ?. by apply: Hdisjf. } { done. } simpl.
        split; [done|].
        go_i. go_i. eexists _. go. go_i. go_i. eexists _. go. go_i. go_i. eexists _.  go.
        go_i. go_i. split; [done|]. go. go_i. go_i. split; [done|]. go.
        go_i. go_i. split; [done|]. go.
        go_i. apply Hloop. naive_solver.
      * go_s. go_s. go_s. go_s. go_s. go_s. go_s. go_s.
        have [cs' ?]: ∃ cs', cs = IPFRight :: cs' by admit. subst.
        eexists _, _, _. split; [apply IPFReturnExtToRight|]. simpl. split; [done|].
        go_i. go_i. eexists _. go. go_i. go_i. eexists _. go.
        go_i. go_i. split; [done|]. go.
        go_i. apply Hloop.  naive_solver.
  - tstep_both.
    apply steps_impl_step_end => κ Pσ2. go. case_match; go.
    + tstep_s. eexists (Some (EIRecvCall f vs)), _. split; [done|]. eexists _, _. split; [econs|].
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. naive_solver.
    + tstep_s. eexists None, _. split; [done|]. eexists _, _. split; [done|].
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. naive_solver.
  - tstep_both.
    apply steps_impl_step_end => κ Pσ2. go. case_match; go.
    + tstep_s. eexists (Some (EIRecvReturn v)), _. split; [done|]. eexists _, _. split; [econs|].
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. naive_solver.
    + tstep_s. eexists None, _. split; [done|]. eexists _, _. split; [done|].
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. naive_solver.
  - tstep_both.
    apply steps_impl_step_end => κ Pσ2. go. destruct κ as [e|]; go.
    + tend. have [σ' Hσ'] := vis_no_all _ _ _ ltac:(done). eexists σ'. split; [naive_solver|].
      go_i. go_i. go_i. go_i. go_i. go_i. destruct x1.
      * go_i. go_i. go_i. go_i. go_i. go_i.
        go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i.
        invert_all asm_prod_filter.
        -- go_i. go_i. go_i. go_i. go_i. go_i.
           go_i. go_i. invert_all asm_prod_filter.
           go_i. go_i. eexists true. go. go_i. go_i. eexists _. go.
           go_i. go_i. eexists _. go. go_i. go_i. eexists _. go.
           go_i. go_i. split; [ naive_solver|]. go. go_i. go_i. split; [naive_solver|]. go.
           go_i. go_i. split; [done|]. go. go_i.
           go_s. eexists (Some _), _. split; [done|]. eexists _, _ => /=.
           split; [econs|]. { naive_solver. } { naive_solver. }
           apply: steps_spec_step_end; [done|] => ??.
           apply: Hloop. naive_solver.
        -- go_s. eexists (Some _), _. split; [done|]. eexists _, _ => /=. split; [apply IPFCallLeftToExt|].
           { naive_solver. } { naive_solver. }
           apply: steps_spec_step_end; [done|] => ??.
           go_s. go_s. eexists _. go. go_s. go_s. eexists _. go.
           go_s. go_s. eexists true. go. go_s. go_s. eexists _. go.
           go_s. go_s. eexists _. go. go_s. go_s. eexists _. go.
           go_s. go_s. split. { apply not_elem_of_union. naive_solver. }
           go. go_s. go_s. split. { apply lookup_union_Some_raw. naive_solver. }
           go. go_s. go_s. split; [done|]. go. go_s. go_s. split; [done|]. go. go_s. split; [done|]. go.
           apply: Hloop. naive_solver.
      * go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i.
        invert_all asm_prod_filter.
        -- go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i.
           invert_all asm_prod_filter.
           have [cs' ?]: ∃ cs', cs = IPFRight :: cs' by admit. subst.
           go_i. go_i. eexists false. go. go_i. go_i. eexists _. go.
           go_i. go_i. eexists _. go. go_i. go_i. split; [done|]. go.
           go_i.
           go_s. eexists (Some _), _. split; [done|]. eexists _, _ => /=.
           split; [apply IPFReturnLeftToRight|].
           apply: steps_spec_step_end; [done|] => ??.
           apply: Hloop. naive_solver.
        -- have [cs' ?]: ∃ cs', cs = IPFNone :: cs' by admit. subst.
           go_s. eexists (Some _), _. split; [done|]. eexists _, _ => /=.
           split; [apply IPFReturnLeftToExt|].
           apply: steps_spec_step_end; [done|] => ??.
           go_s. go_s. eexists _. go. go_s. go_s. eexists _. go.
           go_s. go_s. eexists false. go. go_s. go_s. eexists _. go.
           go_s. go_s. eexists _. go. go_s. go_s. split; [done|]. go.
           go_s. go_s. split; [done|]. go. go_s. split; [done|]. go.
           apply: Hloop. naive_solver.
    + tstep_s. eexists None, _. split; [done|]. eexists _, _. split; [done|].
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. naive_solver.
  - tstep_both.
    apply steps_impl_step_end => κ Pσ2. go. case_match; go.
    + tstep_s. eexists (Some (EIRecvCall f vs)), _. split; [done|]. eexists _, _. split; [econs|].
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. naive_solver.
    + tstep_s. eexists None, _. split; [done|]. eexists _, _. split; [done|].
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. naive_solver.
  - tstep_both.
    apply steps_impl_step_end => κ Pσ2. go. case_match; go.
    + tstep_s. eexists (Some (EIRecvReturn v)), _. split; [done|]. eexists _, _. split; [econs|].
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. naive_solver.
    + tstep_s. eexists None, _. split; [done|]. eexists _, _. split; [done|].
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. naive_solver.
  - tstep_both.
    apply steps_impl_step_end => κ Pσ2. go. destruct κ as [e|]; go.
    + tend. have [σ' Hσ'] := vis_no_all _ _ _ ltac:(done). eexists σ'. split; [naive_solver|].
      go_i. go_i. go_i. go_i. go_i. go_i. destruct x1.
      * go_i. go_i. go_i. go_i. go_i. go_i.
        go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i.
        invert_all asm_prod_filter.
        -- go_i. go_i. go_i. go_i. go_i. go_i.
           go_i. go_i. invert_all asm_prod_filter.
           go_i. go_i. eexists true. go. go_i. go_i. eexists _. go.
           go_i. go_i. eexists _. go. go_i. go_i. eexists _. go.
           go_i. go_i. split; [ naive_solver|]. go. go_i. go_i. split; [naive_solver|]. go.
           go_i. go_i. split; [done|]. go. go_i.
           go_s. eexists (Some _), _. split; [done|]. eexists _, _ => /=.
           split; [econs|]. { naive_solver. } { naive_solver. }
           apply: steps_spec_step_end; [done|] => ??.
           apply: Hloop. naive_solver.
        -- go_s. eexists (Some _), _. split; [done|]. eexists _, _ => /=. split; [apply IPFCallRightToExt|].
           { naive_solver. } { naive_solver. }
           apply: steps_spec_step_end; [done|] => ??.
           go_s. go_s. eexists _. go. go_s. go_s. eexists _. go.
           go_s. go_s. eexists true. go. go_s. go_s. eexists _. go.
           go_s. go_s. eexists _. go. go_s. go_s. eexists _. go.
           go_s. go_s. split. { apply not_elem_of_union. naive_solver. }
           go. go_s. go_s. split.
           { apply lookup_union_Some_raw. destruct (f2i1 !! x2) as [?|] eqn:?; naive_solver. }
           go. go_s. go_s. split; [done|]. go. go_s. go_s. split; [done|]. go. go_s. split; [done|]. go.
           apply: Hloop. naive_solver.
      * go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i.
        invert_all asm_prod_filter.
        -- go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i.
           invert_all asm_prod_filter.
           have [cs' ?]: ∃ cs', cs = IPFLeft :: cs' by admit. subst.
           go_i. go_i. eexists false. go. go_i. go_i. eexists _. go.
           go_i. go_i. eexists _. go. go_i. go_i. split; [done|]. go.
           go_i.
           go_s. eexists (Some _), _. split; [done|]. eexists _, _ => /=.
           split; [apply IPFReturnRightToLeft|].
           apply: steps_spec_step_end; [done|] => ??.
           apply: Hloop. naive_solver.
        -- have [cs' ?]: ∃ cs', cs = IPFNone :: cs' by admit. subst.
           go_s. eexists (Some _), _. split; [done|]. eexists _, _ => /=.
           split; [apply IPFReturnRightToExt|].
           apply: steps_spec_step_end; [done|] => ??.
           go_s. go_s. eexists _. go. go_s. go_s. eexists _. go.
           go_s. go_s. eexists false. go. go_s. go_s. eexists _. go.
           go_s. go_s. eexists _. go. go_s. go_s. split; [done|]. go.
           go_s. go_s. split; [done|]. go. go_s. split; [done|]. go.
           apply: Hloop. naive_solver.
    + tstep_s. eexists None, _. split; [done|]. eexists _, _. split; [done|].
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. naive_solver.
Abort.
