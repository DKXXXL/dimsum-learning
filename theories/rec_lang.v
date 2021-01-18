Require Import refframe.base.
Require Import stdpp.strings.
Require Import stdpp.propset.
Require Import refframe.module.

Import version7.

(*** stuff to move *)
Definition state_set_refines {EV} (mimpl mspec : module EV) (σi : mimpl.(m_state)) (σs : propset mspec.(m_state)) : Prop :=
  ∀ κs σi2, has_trace mimpl σi κs σi2 → ∃ σs1 σs2, σs1 ∈ σs ∧ has_trace mspec σs1 κs σs2.

Lemma inv_set_implies_refines {EV} (m1 m2 : module EV) (inv : m1.(m_state) → propset m2.(m_state) → Prop):
  inv m1.(m_initial) {[ m2.(m_initial) ]} →
  (∀ σi σs, inv σi σs → ∃ σ, σ ∈ σs) →
  (∀ σi σs, inv σi σs → m1.(m_is_ub) σi → ∃ σs1 σs2, σs1 ∈ σs ∧ has_trace m2 σs1 [Ub] σs2) →
  (∀ σi1 σs1 σi2 e, inv σi1 σs1 → m1.(m_step) σi1 e σi2 →
      ∃ σs2, inv σi2 σs2 ∧ σs2 ⊆ {[ σ2 | ∃ σ1, σ1 ∈ σs1 ∧ has_trace m2 σ1 (option_list (Vis <$> e)) σ2 ]}) →
  refines m1 m2.
Proof.
  move => Hinvinit Hinvnonempty Hinvsafe Hinvstep.
  constructor => // κs σi2.
  move: m1.(m_initial) Hinvinit => σi1 Hinv Hsteps.
  have : (∃ σs1 σs2, σs1 ∈ ({[m_initial m2]} : propset _) ∧ has_trace m2 σs1 κs σs2); last set_solver.
  move: {[ m2.(m_initial) ]} Hinv => σs1 Hinv.
  elim: Hsteps σs1 Hinv => {σi1 σi2 κs}.
  - move => ? ? /Hinvnonempty [??].  eexists _, _. split => //. by apply: TraceEnd.
  - move => σi1 σi2 σi3 κ κs Hstep Hsteps IH σs1 Hinv.
    have [σs2 [Hinv2 Hsub]]:= Hinvstep _ _ _ _ Hinv Hstep.
    have [σs3 [σs4 [Hin ?]]]:= IH _ Hinv2.
    have [σ1 [??]]:= Hsub _ Hin.
    eexists _, _. split => //. by apply: has_trace_trans.
  - move => ??? /Hinvsafe Hs σs Hinv.
    have [? [? [? /has_trace_ub_inv[σs2[??]]]]]:= Hs _ Hinv.
    eexists _, _. split => //. apply: (has_trace_trans []); [ done |]. by apply: TraceUbRefl.
Qed.

Lemma state_set_refines_initial {EV} (m1 m2 : module EV):
  refines m1 m2 →
  state_set_refines m1 m2 (m_initial m1) {[m_initial m2]}.
Proof. move => [Hr] ?? /Hr[??]. naive_solver. Qed.

Lemma state_set_refines_step {EV} (m1 m2 : module EV) σi1 σs1 σi2 e:
  state_set_refines m1 m2 σi1 σs1 →
  m1.(m_step) σi1 e σi2 →
  state_set_refines m1 m2 σi2 {[ σ2 | ∃ σ1, σ1 ∈ σs1 ∧ has_trace m2 σ1 (option_list (Vis <$> e)) σ2 ]}.
Proof.
  move => Hinv Hstep κs σi3 Hκs.
  have [|? [? [? /has_trace_app_inv[?[??]]]]]:= Hinv (option_list (Vis <$> e) ++ κs) σi3.
  { by apply: TraceStep. }
  set_solver.
Qed.

Lemma state_set_refines_step_None {EV} (m1 m2 : module EV) σi1 σs1 σi2:
  state_set_refines m1 m2 σi1 σs1 →
  m1.(m_step) σi1 None σi2 →
  state_set_refines m1 m2 σi2 σs1.
Proof.
  move => Hinv Hstep κs σi3 Hκs.
  have [|? [? [? ?]]]:= Hinv κs σi3.
  { by apply: TraceStepNone. }
  set_solver.
Qed.

Lemma state_set_refines_non_empty {EV} (m1 m2 : module EV) σi σs:
  state_set_refines m1 m2 σi σs → ∃ σ, σ ∈ σs.
Proof.
  move => Hs.
  have [|?[?[??]]]:= Hs [] σi. by apply: TraceEnd.
  naive_solver.
Qed.

Lemma state_set_refines_ub {EV} (m1 m2 : module EV) σi σs:
  state_set_refines m1 m2 σi σs →
  m1.(m_is_ub) σi →
  ∃ σ σ', σ ∈ σs ∧ has_trace m2 σ [Ub] σ'.
Proof. move => Hs Hub. apply: Hs. by apply: TraceUbRefl. Qed.

Lemma refines_implies_inv_set {EV} (m1 m2 : module EV):
  refines m1 m2 →
  ∃ (inv : m1.(m_state) → propset m2.(m_state) → Prop),
  inv m1.(m_initial) {[ m2.(m_initial) ]} ∧
  (∀ σi σs, inv σi σs → ∃ σ, σ ∈ σs) ∧
  (∀ σi σs, inv σi σs → m1.(m_is_ub) σi → ∃ σs1 σs2, σs1 ∈ σs ∧ has_trace m2 σs1 [Ub] σs2) ∧
  (∀ σi1 σs1 σi2 e, inv σi1 σs1 → m1.(m_step) σi1 e σi2 →
      ∃ σs2, inv σi2 σs2 ∧ σs2 ⊆ {[ σ2 | ∃ σ1, σ1 ∈ σs1 ∧ has_trace m2 σ1 (option_list (Vis <$> e)) σ2 ]}).
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

Module rec.
Definition fn_name := string.
Definition var_name := string.

Inductive binop : Set :=
| AddOp.

Inductive cmp : Set :=
| EqCmp.

Inductive expr : Set :=
| Var (v : var_name)
| Const (n : Z)
| BinOp (v1 : var_name) (o : binop) (v2 : var_name)
| If (v1 : var_name) (c : cmp) (v2 : var_name) (e1 e2 : expr)
| LetE (v : var_name) (e1 e2 : expr)
| Call (f : fn_name) (args : list var_name)
.
Record fndef : Type := {
  fd_args : list var_name;
  fd_body : expr;
}.
Record cont := {
  c_var : var_name;
  c_env : gmap var_name Z;
  c_expr : expr;
}.

(*
                          -----------
                         v           \
  WaitingForCall -> Running -> WaitingForReturn
                       |
                       v
                    Finished


                          -----------
                         v           \          Push
  WaitingForCall -> Running -> WaitingForReturn --> WaitingForCall
                       |
                       v
                    Finished
*)
Inductive state_kind : Set :=
| Running (e : expr) | WaitingForCall | WaitingForReturn | Finished | Stuck.
Record state := {
  st_exp : state_kind;
  st_env : gmap var_name Z;
  st_conts : list cont;
  st_fns : gmap fn_name fndef;
}.
Inductive rec_event : Type :=
| RecvCallEvt (fn : string) (args: list Z) | RecvRetEvt (ret: Z)
| CallEvt (fn : string) (args: list Z) | DoneEvt (ret: Z).

Inductive step : state → option rec_event → state → Prop :=
(* Internal steps *)
| VarStep v ρ fns n cs:
    ρ !! v = Some n →
    step {| st_exp := Running (Var v); st_env := ρ; st_conts := cs; st_fns := fns |}
         None
         {| st_exp := Running (Const n); st_env := ρ; st_conts := cs; st_fns := fns |}
| BinOpStep v1 v2 o ρ fns n1 n2 nr cs:
    ρ !! v1 = Some n1 →
    ρ !! v2 = Some n2 →
    nr = match o with | AddOp => n1 + n2 end%Z →
    step {| st_exp := Running (BinOp v1 o v2); st_env := ρ; st_conts := cs; st_fns := fns |}
         None
         {| st_exp := Running (Const nr); st_env := ρ; st_conts := cs; st_fns := fns |}
| IfStep v1 v2 c ρ fns n1 n2 b e1 e2 cs:
    ρ !! v1 = Some n1 →
    ρ !! v2 = Some n2 →
    b = match c with | EqOp => bool_decide (n1 = n2) end →
    step {| st_exp := Running (If v1 c v2 e1 e2); st_env := ρ; st_conts := cs; st_fns := fns |}
         None
         {| st_exp := Running (if b then e1 else e2); st_env := ρ; st_conts := cs; st_fns := fns |}
| LetStep v e1 e2 ρ fns cs:
    step {| st_exp := Running (LetE v e1 e2); st_env := ρ; st_conts := cs; st_fns := fns |}
         None
         {| st_exp := Running e1; st_env := ρ; st_conts := {|c_var := v; c_env := ρ; c_expr := e2|} :: cs; st_fns := fns |}
| CallInternalStep f vas ρ cs fns nas fn:
    Forall2 (λ n v, ρ !! n = Some v) vas nas →
    fns !! f = Some fn →
    length vas = length fn.(fd_args) →
    step {| st_exp := Running (Call f vas); st_env := ρ; st_conts := cs; st_fns := fns |}
         None
         {| st_exp := Running fn.(fd_body); st_env := list_to_map (zip fn.(fd_args) nas); st_conts := cs; st_fns := fns |}
(* External Calls *)
| CallExternalStep f vas ρ cs fns nas:
    Forall2 (λ n v, ρ !! n = Some v) vas nas →
    fns !! f = None →
    step {| st_exp := Running (Call f vas); st_env := ρ; st_conts := cs; st_fns := fns |}
         (Some (CallEvt f nas))
         {| st_exp := WaitingForReturn; st_env := ρ; st_conts := cs; st_fns := fns |}
| RecvReturnStep ρ cs fns n:
    step {| st_exp := WaitingForReturn; st_env := ρ; st_conts := cs; st_fns := fns |}
         (Some (RecvRetEvt n))
         {| st_exp := Running (Const n); st_env := ρ; st_conts := cs; st_fns := fns |}
| RecvCallStep ρ cs fns nas σ fn f:
    fns !! f = Some fn →
    σ = (if bool_decide (length nas = length fn.(fd_args)) then Running fn.(fd_body) else Stuck) →
    step {| st_exp := WaitingForCall; st_env := ρ; st_conts := cs; st_fns := fns |}
         (Some (RecvCallEvt f nas))
         {| st_exp := σ; st_env := list_to_map (zip fn.(fd_args) nas); st_conts := cs; st_fns := fns |}
(* Const steps *)
| ConstConsStep n c ρ fns cs:
    step {| st_exp := Running (Const n); st_env := ρ; st_conts := c::cs; st_fns := fns |}
         None
         {| st_exp := Running c.(c_expr); st_env := <[c.(c_var) := n]>c.(c_env); st_conts := cs; st_fns := fns |}
| ConstNilStep n ρ fns:
    step {| st_exp := Running (Const n); st_env := ρ; st_conts := []; st_fns := fns |}
         (Some (DoneEvt n))
         {| st_exp := Finished; st_env := ρ; st_conts := []; st_fns := fns |}
.

Definition rec_fns := gmap string fndef.

Definition is_ub (σ : state) : Prop :=
  ¬ ((σ.(st_exp) = Finished ∨ σ.(st_exp) = WaitingForCall) ∨ ∃ e σ', step σ e σ').

Definition initial_state (fns: rec_fns) : state :=
  {|
    st_exp := WaitingForCall;
    st_conts := [];
    st_fns := fns;
    st_env := ∅;
  |}.

Definition rec_module (fns: rec_fns) : module rec_event := {|
  m_state := state;
  m_initial := initial_state fns;
  m_step := step;
  m_is_ub := is_ub;
|}.

Definition rec_link (fns1 fns2 : rec_fns) : rec_fns := fns1 ∪ fns2.

Definition ctx_refines (fnsi fnss : rec_fns) :=
  ∀ C, refines (rec_module (rec_link fnsi C)) (rec_module (rec_link fnss C)).

Definition ctx_equiv (fnsi fnss : rec_fns) :=
  ctx_refines fnsi fnss ∧ ctx_refines fnss fnsi.


(*** Call module *)
Record call_module_info (EV : Type) := {
  (* TODO: Should these go into Prop instead? That would be more
  expressive, but call_step already requires these properties to be
  basically decidable, so it probably does not make a difference in
  practice and this version is nicer to use. *)
  cmi_final : EV → bool;
  cmi_waiting : EV → bool;
}.
Arguments cmi_final {_}.
Arguments cmi_waiting {_}.

Record call_state {EV} (m : module EV) := {
  cs_stack : list m.(m_state);
  cs_waiting : bool;
}.
Arguments cs_stack {_ _}.
Arguments cs_waiting {_ _}.

Inductive call_step {EV} (m : module EV) (i : call_module_info EV) : (call_state m) → option EV → (call_state m) → Prop :=
| CStep σ σs σ' e w cs:
    m.(m_step) σ e σ' →
    cs = (if default false (i.(cmi_final) <$> e) then [] else [σ']) ++ σs →
    call_step m i {| cs_stack := (σ :: σs); cs_waiting := w |}
              e {| cs_stack := cs; cs_waiting := default w (i.(cmi_waiting) <$> e) |}
| CWaiting σs:
    call_step m i {| cs_stack := σs; cs_waiting := true |}
              None {| cs_stack := m.(m_initial) :: σs; cs_waiting := false |}
.

Definition call_module {EV} (m : module EV) (i : call_module_info EV) : module EV := {|
  m_state := call_state m;
  m_initial := {| cs_stack := []; cs_waiting := true |};
  m_step := call_step m i;
  m_is_ub σ := default False (m.(m_is_ub) <$> head σ.(cs_stack));
|}.

Definition call_module_refines_inv {EV} (m1 m2 : module EV) (i : call_module_info EV) (σ1 : (call_module m1 i).(m_state)) (sσ2 : propset (call_module m2 i).(m_state)) : Prop :=
  ∃ Ts, Forall2 (state_set_refines m1 m2) σ1.(cs_stack) Ts
    ∧ sσ2 ≡ {[ σ2 | σ1.(cs_waiting) = σ2.(cs_waiting) ∧ Forall2 elem_of σ2.(cs_stack) Ts ]}.

  (* ∀ σ2, σ2 ∈ sσ2 → ( *)
  (*         (* Forall2 elem_of σ2.(cs_stack) (PropSet <$> (state_refines m1 m2 <$> σ1.(cs_stack)))). *) *)

  (* Forall2 (state_refines m1 m2) σ1.(cs_stack) σ2.(cs_stack) ∧ *)
  (* σ1.(cs_waiting) = σ2.(cs_waiting)). *)

Lemma call_empty_steps {EV} (m : module EV) i σ σ' w σs:
  has_trace m σ [] σ' →
  has_trace (call_module m i) {| cs_stack := σ :: σs; cs_waiting := w |} []
            {| cs_stack := σ' :: σs; cs_waiting := w |}.
Proof.
  move Hκ: ([]) => κ Hsteps.
  elim: Hsteps Hκ.
  - move => ?. by econstructor.
  - move => σ1 σ2 σ3 [?|] κs //= ?? IH ?. subst.
    apply: TraceStepNone; [ | by apply: IH]. by apply: CStep.
  - move => ?????. by apply: TraceUb => /=.
Qed.

Lemma state_set_refines_exists_Forall2 {EV} (m1 m2 : module EV) σ σs:
  Forall2 (state_set_refines m1 m2) σ σs →
  ∃ σs', Forall2 elem_of σs' σs.
Proof.
  elim. { eexists []. constructor. }
  move => ???? /state_set_refines_non_empty[??] ? [??].
  eexists. by constructor.
Qed.

Lemma call_module_refines {EV} (m1 m2 : module EV) (i : call_module_info EV) :
  refines m1 m2 →
  refines (call_module m1 i) (call_module m2 i).
Proof.
  move => Href.
  apply (inv_set_implies_refines _ _ (call_module_refines_inv _ _ _)).
  - eexists []. split_and!; [ by constructor |].
    set_unfold; move => [??] /=. split; first naive_solver.
    move => [-> Hall]. inversion Hall. naive_solver.
  - move => [??] ? [Ts [/state_set_refines_exists_Forall2 [??] Hσs]].
    eexists (Build_call_state _ _ _ _). by rewrite {}Hσs.
  - move => [csi wi] σs /= [Ts [Hall Hσs]] Hub. destruct csi => //; simplify_eq/=.
    move: Hall => /(Forall2_cons_inv_l _ _ _)[? [? [ /state_set_refines_ub [//|σ1 [σ1' [? Hub2]]] [/state_set_refines_exists_Forall2[??] ?]]]] /=. subst.
    move: Hub2 => /has_trace_ub_inv[? [??]].
    eexists (Build_call_state _ _ _ _), _. rewrite {}Hσs. split.
    { split => //. by constructor. }
    apply: (has_trace_trans []); [ by apply: call_empty_steps|].
    by apply: TraceUbRefl.
  - move => [csi wi] σs [csi2 wi2] e [Ts [Hall Hσs]] /= Hstep.
    invert_all @call_step.
    + revert select (m_step _ _ _ _) => Hstep.
      move: Hall => /(Forall2_cons_inv_l _ _ _)[? [Ts' [Hs[??]]]]. subst.
      destruct e as [e|] => /=. 2: {
        eexists σs. split.
        - eexists _. split; [|set_solver].
          constructor => //. by apply: state_set_refines_step_None.
        - move => σ1 ?. eexists σ1. split => //. apply: TraceEnd.
      }
      eexists _. split. {
        eexists ((if cmi_final i e then [] else [_]) ++ Ts').
        split => //.
        apply: Forall2_app => //.
        case_match. constructor. constructor; [|by constructor].
          by apply: state_set_refines_step.
      }
      move => /= [??] [? Hall]. simplify_eq/=.
      case_match; simplify_eq/=.
      * have /state_set_refines_non_empty[σa [σb /= [? Ht]]] := state_set_refines_step _ _ _ _ _ _ Hs Hstep.
        eexists (Build_call_state _ _ _ _). rewrite {}Hσs.
        split. { split => //. apply: Forall2_cons => //. }
        move: Ht => /(has_trace_cons_inv _ _ _)[? [? [? Hor]]].
        apply: (has_trace_trans []); [ by apply: call_empty_steps|].
        case: Hor => [?|[??]]; [by apply: TraceUb|].
        apply: TraceStepSome; [|by apply: TraceEnd].
        apply: CStep => //. case_match => //. simplify_eq/=. congruence.
      * move: Hall => /(Forall2_cons_inv_r _ _ _ _)[σa [Ts [[σb [? Ht]][??]]]].
        simplify_eq.
        eexists (Build_call_state _ _ _ _). rewrite {}Hσs.
        split. { split => //. apply: Forall2_cons => //. }
        move: Ht => /(has_trace_cons_inv _ _ _)[? [? [? Hor]]].
        apply: (has_trace_trans []); [ by apply: call_empty_steps|].
        case: Hor => [?|[??]]; [by apply: TraceUb|].
        apply: TraceStepSome. { by apply: CStep. }
        case_match => //; simplify_eq/=; try congruence.
        by apply: call_empty_steps.
    + eexists _. split_and!. {
        eexists _. split; [|done]. apply: Forall2_cons; [|done].
          by apply: state_set_refines_initial.
      }
      move => [??] [? /(Forall2_cons_inv_r _ _ _ _) [? [?[? [??]]]]]. simplify_eq/=.
      eexists (Build_call_state _ _ _ _). rewrite Hσs.
      split. { split => //. }
      apply: TraceStepNone; [|by apply: TraceEnd].
      set_unfold; subst. by apply CWaiting.
      (* 3: { move => ??. eexists _. apply: TraceStepNone; [|by apply: TraceEnd]. apply: CWaiting. } *)
      (* split => //. constructor => //. by apply: ref_subset. *)
Qed.

Definition call_module_link_inv {EV} (m1 m2 m3 : module EV) (i : call_module_info EV) (M : link_mediator EV EV EV) (σ1 : (call_module m1 i).(m_state)) (σ2 : (call_module m2 i).(m_state)) (σ3 : (call_module m3 i).(m_state)) (σm : M.(lm_state)) : Prop :=
  True.

Lemma call_module_refines_link {EV} (m1 m2 m3 : module EV) (i : call_module_info EV) M :
  refines_equiv (call_module m1 i) (link (call_module m2 i) (call_module m3 i) M).
Proof.
  apply (inv_implies_refines_equiv _ (link _ _ _) (curry ∘ curry ∘ (call_module_link_inv _ _ _ _ _))).
  - done.
  - admit.
  - admit.
  - move => [cs1 ws1] [[[cs2 ws2] [cs3 ws3]] σm] [??] ?/= ? ?.
    invert_all @call_step.
    * right.
      admit.
    * admit.
  - move => [cs1 ws1] [[[cs2 ws2] [cs3 ws3]] σm] [??] ?/= ? ?.
    admit.
    (* invert_all @link_step. *)
Admitted.

Definition call_intro_mediator {EV} (is_init : EV → bool) : link_mediator EV Empty_set EV := {|
  lm_state := bool;
  lm_initial := false;
  lm_step b e1 _ e2 b' := e1 = e2 ∧ b' = true ∧
      if b is false then True else if is_init <$> e1 is Some true then False else True;
|}.

(* Lemma no_behavior_no_step {EV} (m : module EV) σ: *)
(*   (¬ ∃ e σ', m.(m_step) σ e σ') → ¬( m_is_ub m σ) → has_no_behavior m σ. *)
(* Proof. move => ???? Htrace. inversion Htrace; simplify_eq/= => //; naive_solver. Qed. *)

Lemma no_behavior_step {EV} (m : module EV) σ:
  (∀ e σ', m.(m_step) σ e σ' → e = None ∧ has_no_behavior m σ') → ¬(m_is_ub m σ) → has_no_behavior m σ.
Proof. move => Hstep ??? Htrace. inversion Htrace; simplify_eq/= => //. efeed pose proof Hstep => //. naive_solver. Qed.
Inductive has_non_ub_trace {EV} (m : module EV) : m.(m_state) → list EV → m.(m_state) → Prop :=
| NUBTraceEnd σ:
    has_non_ub_trace m σ [] σ
| NUBTraceStep σ1 σ2 σ3 κ κs:
    m.(m_step) σ1 κ σ2 →
    has_non_ub_trace m σ2 κs σ3 →
    has_non_ub_trace m σ1 (option_list κ ++ κs) σ3
.

Lemma NUBTraceStepNone {EV} κs (m : module EV) σ2 σ1 σ3 :
  m.(m_step) σ1 None σ2 →
  has_non_ub_trace m σ2 κs σ3 →
  has_non_ub_trace m σ1 κs σ3.
Proof. move => ??. by apply: (NUBTraceStep _ _ _ _ None). Qed.

Lemma NUBTraceStepSome {EV} κs (m : module EV) σ2 σ1 σ3 κ :
  m.(m_step) σ1 (Some κ) σ2 →
  has_non_ub_trace m σ2 κs σ3 →
  has_non_ub_trace m σ1 (κ :: κs) σ3.
Proof. move => ??. by apply: (NUBTraceStep _ _ _ _ (Some _)). Qed.

Lemma has_non_ub_trace_trans {EV} κs1 κs2 (m : module EV) σ1 σ2 σ3 :
  has_non_ub_trace m σ1 κs1 σ2 →
  has_non_ub_trace m σ2 κs2 σ3 →
  has_non_ub_trace m σ1 (κs1 ++ κs2) σ3.
Proof.
  elim => //.
  move => ?????????. rewrite -app_assoc. econstructor; eauto.
Qed.

Lemma has_trace_add_empty {EV} κs1 (m : module EV) σ1 σ2 :
  has_trace m σ1 (κs1 ++ []) σ2 →
  has_trace m σ1 κs1 σ2.
Proof. by rewrite -{2}[κs1](right_id_L [] (++)). Qed.

Definition call_intro_inv {EV} (m : module EV) (i : call_module_info EV) (is_init : EV → bool) (σ1 : m.(m_state)) (σ2 : (call_module m i).(m_state)) (σ3 : (@module_empty Empty_set).(m_state)) (σm : (call_intro_mediator is_init).(lm_state)) : Prop :=
  match σ2.(cs_stack) with
  | [] => σ1 = m.(m_initial) ∧ σ2.(cs_waiting) = true ∧ σm = false
  | [σ] => σ1 = σ ∧ if σm then ∃ σ' e κs, m.(m_step) m.(m_initial) e σ' ∧ has_non_ub_trace m σ' κs σ else σ = m.(m_initial) ∧ σ2.(cs_waiting) = false
  | _ => False
  end.
Lemma call_intro {EV} (m : module EV) (i : call_module_info EV) (is_init : EV → bool):
  (∀ e σ, m.(m_step) m.(m_initial) e σ → ∃ κ, e = Some κ ∧ is_init κ) → (* TODO: Is this necessary? *)
  ¬ m_is_ub m (m_initial m) →
  (∀ σ1 e σ2, m.(m_step) σ1 (Some e) σ2 → i.(cmi_final) e → has_no_behavior m σ2) →
  (∀ σ'' σ' σ e κs e', m.(m_step) m.(m_initial) e σ' → has_non_ub_trace m σ' κs σ → m.(m_step) σ (Some e') σ'' → ¬ is_init e') →
  refines_equiv m (link (call_module m i) ∅ (call_intro_mediator is_init)).
Proof.
  move => HSome Hnotub Hfinal Hnoinit.
  apply (inv_implies_refines_equiv _ (link _ _ _) (curry ∘ curry ∘ (call_intro_inv _ _ _))).
  - done.
  - rewrite /call_intro_inv. move => ? [[[[|?[|??]] ?] ?] ?] //= ? ?; destruct_and?; simplify_eq/= => //.
    eexists _. apply: TraceUbRefl => /=. by left.
  - rewrite /call_intro_inv. move => [[[[|?[|??]] ?] ?] ?] ? /= ? [?|?]//; destruct_and?. simplify_eq/=.
    eexists _. by apply: TraceUbRefl.
  - rewrite {1}/call_intro_inv. move => ? [[[[|?[|??]] ?] ?] ?] //= ? e ? Hstep; right; destruct_and?; simplify_eq/=.
    + have [?[??]]:= HSome _ _ Hstep. simplify_eq.
      eexists (_, _, _). split. 2: {
        apply: TraceStepNone. { apply: LinkStepL. apply: CWaiting. done. }
        apply: has_trace_add_empty.
        apply: TraceStep. { apply: LinkStepL. apply: CStep => //. done. }
        apply: TraceEnd.
      }
      simpl. case_match; [right | left]. { apply: Hfinal => //. naive_solver. }
      split => //. eexists _, _, _. split_and! => //. by apply: NUBTraceEnd.
    + eexists (_, _, true). split. 2: {
        apply: has_trace_add_empty.
        apply: TraceStep; [|by apply: TraceEnd].
        apply: LinkStepL. apply: CStep => //.
        case_match; destruct_and?; simplify_eq.
        - case_match => //. split_and! => //=.
          revert select (∃ e, _) => -[? [?[?[??]]]].
          case_match => //.
          exfalso. apply: Hnoinit => //. naive_solver.
        - have [?[??]]:= HSome _ _ Hstep. simplify_eq. by constructor.
      }
      simpl.
      destruct (default false (cmi_final i <$> e)) eqn: Hf; [right | left].
      { destruct e => //. apply: Hfinal => //. naive_solver. }
      split => //. case_match; destruct_and?; simplify_eq.
      * revert select (∃ e, _) => -[? [?[?[??]]]]. eexists _, _, _. split_and!; [done|..].
        apply: has_non_ub_trace_trans => //. apply: NUBTraceStep => //. apply: NUBTraceEnd.
      * have [?[??]]:= HSome _ _ Hstep; simplify_eq. eexists _, _, _. split_and! => //.
        by apply: NUBTraceEnd.
  - rewrite {1}/call_intro_inv. move => ? [[[[|?[|??]] ?] ?] ?] //= ? e ??; right; destruct_and?; simplify_eq/=; invert_all @link_step => //; invert_all @call_step; destruct_and?; simplify_eq/=.
    + eexists _. split; [|by apply: TraceEnd]. by left.
    + have ?: e = e1 by destruct e1; naive_solver. simplify_eq.
      eexists _. split. 2: { apply: has_trace_add_empty. apply: TraceStep => //. apply: TraceEnd. }
      destruct (default false (cmi_final i <$> e1)) eqn: Hf. {
        destruct e1 => //.
        right. apply: no_behavior_step. 2: { move => [] //. }
        move => ?? ?. inv_step. destruct_and!. simplify_eq. split => //.
        apply: no_behavior_step. 2: { move => [] //. }
        move => ???. inv_step.
        revert select (m_step _ _ _ _) => Hstep.
        have [?[??]]:= HSome _ _ Hstep. simplify_eq/=. destruct_and!. case_match; naive_solver.
      }
      left.
      rewrite /call_intro_inv/=. split => //. case_match; destruct_and?; simplify_eq. {
        case_match; destruct_and?; simplify_eq.
        - revert select (∃ e, _) => -[? [?[?[??]]]]. eexists _,_, _. split_and!; [done|..].
          apply: has_non_ub_trace_trans => //. apply: NUBTraceStep => //. apply: NUBTraceEnd.
        - revert select (m_step _ _ _ _) => Hstep.
          have [?[??]]:= HSome _ _ Hstep; simplify_eq. eexists _, _, _. split_and! => //.
          by apply: NUBTraceEnd. }
      case_match; [| naive_solver].
      revert select (∃ e, _) => -[? [?[?[??]]]]. eexists _, _, _. split_and!; [done|..].
      apply: has_non_ub_trace_trans => //. apply: NUBTraceStep => //. apply: NUBTraceEnd.
    + eexists _. split; [|by apply: TraceEnd]. right. case_match; destruct_and?; simplify_eq/= => //.
      apply: no_behavior_step.
      * move => ? ??. exfalso. inv_step.
        revert select (m_step _ _ _ _) => Hstep.
        have [?[??]]:= HSome _ _ Hstep. simplify_eq/=. destruct_and!. by case_match.
      * simpl. contradict Hnotub. naive_solver.
Qed.
(*** rec linking *)
Definition rec_cmi : call_module_info rec_event := {|
  cmi_final e := if e is DoneEvt _ then true else false;
  cmi_waiting e := if e is CallEvt _ _ then true else false;
|}.

Definition rec_link_mediator (fns1 fns2 : gset string) : link_mediator rec_event rec_event rec_event.
Admitted.

Lemma rec_link_ok fns1 fns2:
  fns1 ##ₘ fns2 →
  refines_equiv (call_module (rec_module (rec_link fns1 fns2)) rec_cmi)
          (link (call_module (rec_module fns1) rec_cmi) (call_module (rec_module fns2) rec_cmi)
                (rec_link_mediator (dom _ fns1) (dom _ fns2))).
Proof.
  move => ?.
  apply call_module_refines_link.
Admitted.

Lemma rec_refines_call fns:
  refines_equiv (rec_module fns) (link (call_module (rec_module fns) rec_cmi) ∅ (call_intro_mediator (λ e, if e is RecvCallEvt _ _ then true else false))).
Proof.
  apply: call_intro.
  - move => ???. inv_step. naive_solver.
  - apply. naive_solver.
  - move => ? [] // ?? ? ?. inv_step.
    apply: no_behavior_step.
    + move => ???. inv_step.
    + apply. naive_solver.
  - move => σ'' σ' σ e κs e' Hstep Htrace.
    have {Hstep} : σ'.(st_exp) ≠ WaitingForCall by inv_step; case_match.
    elim: Htrace.
    + move => ???. inv_step; naive_solver.
    + move => ??????? IH ???. apply: IH => //. by inv_step.
Qed.

Lemma refines_implies_rec_ctx_refines fnsi fnss :
  dom (gset string) fnsi = dom (gset string) fnss →
  refines (rec_module fnsi) (rec_module fnss) →
  ctx_refines fnsi fnss.
Proof.
  move => Hdom Href C.
  rewrite /rec_link map_difference_union_r (map_difference_union_r fnss).
  apply: refines_vertical. { apply rec_refines_call. }
  apply: refines_vertical. 2: { apply rec_refines_call. }
  apply: refines_horizontal. 2: { apply refines_reflexive. }

  apply: refines_vertical. { apply rec_link_ok. apply: map_disjoint_difference_r'. }
  apply: refines_vertical. 2: { apply rec_link_ok. apply: map_disjoint_difference_r'. }
  rewrite !dom_difference_L !Hdom.
  apply: refines_horizontal.
  - apply: call_module_refines. apply: Href.
  - rewrite (map_difference_eq_dom_L _ _ _ Hdom).
    apply refines_reflexive.
Qed.

Lemma refines_equiv_implies_rec_ctx_equiv fnsi fnss :
  dom (gset string) fnsi = dom (gset string) fnss →
  refines_equiv (rec_module fnsi) (rec_module fnss) →
  ctx_equiv fnsi fnss.
Proof. move => ? [??]. split; by apply refines_implies_rec_ctx_refines. Qed.

Lemma refines_equiv_equiv_rec_ctx_equiv fnsi fnss :
  dom (gset string) fnsi = dom (gset string) fnss →
  refines_equiv (rec_module fnsi) (rec_module fnss) ↔
  ctx_equiv fnsi fnss.
Proof.
  move => ?. split; [by apply: refines_equiv_implies_rec_ctx_equiv|].
  move => [Hi Hs].
  pose proof (Hi ∅) as Hi.
  pose proof (Hs ∅) as Hs.
  rewrite /rec_link !right_id_L in Hi Hs.
  done.
Qed.

(*** Test module *)
Module test.
  Local Open Scope Z_scope.

  Definition add1 : fndef := {|
    fd_args := ["a"];
    fd_body := LetE "1" (Const 1) $ BinOp "a" AddOp "1";
  |}.

  Definition add1_cumbersome : fndef := {|
    fd_args := ["a"];
    fd_body :=
      LetE "2" (Const 2) $
      LetE "-1" (Const (-1)) $
      LetE "res" (BinOp "a" AddOp "2") $
      (BinOp "res" AddOp "-1") ;
  |}.

  Definition ret2 : fndef := {|
    fd_args := [];
    fd_body := Const 2;
  |}.

  Definition ret2_call : fndef := {|
    fd_args := [];
    fd_body :=
      LetE "1" (Const 1) $
      Call "add1" ["1"]
  |}.

  Definition const_prop_pre : fndef := {|
    fd_args := [];
    fd_body :=
      LetE "2" (Const 2) $
      LetE "u" (Call "unknown" []) $
      BinOp "u" AddOp "2"
  |}.

  Definition const_prop_post : fndef := {|
    fd_args := [];
    fd_body :=
      LetE "u" (Call "unknown" []) $
      LetE "2" (Const 2) $
      BinOp "u" AddOp "2"
  |}.

  Lemma add1_refines_cumbersome add1_name :
    refines (rec_module {[ add1_name := add1 ]}) (rec_module {[ add1_name := add1_cumbersome ]}).
  Proof.
    apply: wp_implies_refines => n.
    constructor. split. { apply. right. eexists _, _. econstructor => //. by apply: lookup_insert. }
    move => ? ? ? ? ?. inv_step. simplify_map_eq.
    destruct (decide (length nas = 1%nat)). 2: {
      eexists _. left. apply: TraceStepSome. { econstructor => //. apply: lookup_insert. }
      apply: TraceUbRefl => /=. case_bool_decide => //.
      move => [[?|?]//|[? [??]]]. invert_all step.
    }
    eexists _. right. split. {
      apply: TraceStepSome; [|by apply: TraceEnd].
      econstructor => //. by apply: lookup_insert.
    }
    simpl. case_bool_decide => //.
    destruct nas as [|n [|]] => //.

    constructor. split. { apply. right. eexists _, _. by econstructor. }
    move => ?????. inv_step.
    eexists. right. split. { apply: TraceEnd. }

    constructor. split. { apply. right. eexists _, _. by econstructor. }
    move => ?????. inv_step.
    eexists. right. split. { apply: TraceEnd. }

    constructor. split. { apply. right. eexists _, _. by econstructor. }
    move => ?????. inv_step.
    eexists. right. split. { apply: TraceEnd. }

    constructor. split. { apply. right. eexists _, _. by econstructor. }
    move => ?????. inv_step. simplify_map_eq.
    eexists. right. split. {
      simpl. apply: TraceStepNone. { by econstructor. }
      simpl. apply: TraceStepNone. { by econstructor. }
      simpl. apply: TraceStepNone. { by econstructor. }
      simpl. apply: TraceStepNone. { by econstructor. }
      simpl. apply: TraceStepNone. { by econstructor. }
      simpl. apply: TraceStepNone. { by econstructor. }
      simpl. apply: TraceStepNone. { by econstructor. }
      simpl. apply: TraceStepNone. { by econstructor. }
      simpl. apply: TraceStepSome. {
        have -> : (n1 + 2 + -1) = n1 + 1 by lia.
        by econstructor.
      }
      apply: TraceEnd.
    }

    constructor. split. { apply. naive_solver. }
    move => ?????. inv_step.
    Unshelve.
    apply: inhabitant.
  Qed.

  Lemma ret2_refines_call :
    refines (rec_module (<[ "add1" := add1]> {["ret2" := ret2 ]})) (rec_module (<[ "add1" := add1]> {["ret2" := ret2_call ]})).
  Proof.
    apply: wp_implies_refines => n.
  Admitted.

  Lemma const_prop_post_refines_pre  :
    refines (rec_module {[ "cp" := const_prop_post ]}) (rec_module {[ "cp" := const_prop_pre ]}).
  Proof.
    apply: wp_implies_refines => n.
    constructor. split. { apply. right. eexists _, _. econstructor => //. by apply: lookup_insert. }
    move => ? ? ? ? ?. inv_step. simplify_map_eq.
    destruct (decide (length nas = 0%nat)). 2: {
      eexists _. left. apply: TraceStepSome. { econstructor => //. }
      apply: TraceUbRefl => /=. case_bool_decide => //.
      move => [[?|?]//|[? [??]]]. invert_all step.
    }
    eexists _. right. split. {
      apply: TraceStepSome; [|by apply: TraceEnd].
      econstructor => //.
    }
    simpl. case_bool_decide => //.
    destruct nas as [|n [|]] => //.

    constructor. split. { apply. right. eexists _, _. by econstructor. }
    move => ?????. inv_step.
    eexists. right. split. { apply: TraceEnd. }

    constructor. split. { apply. right. eexists _, _. by econstructor. }
    move => ?????. inv_step.
    revert select (Forall2 _ [] _) => /Forall2_nil_inv_l ->.
    eexists. right. split. {
      simpl. apply: TraceStepNone. { by econstructor. }
      simpl. apply: TraceStepNone. { by econstructor. }
      simpl. apply: TraceStepNone. { by econstructor. }
      simpl. apply: TraceStepSome. { by econstructor. }
      apply: TraceEnd.
    }
    constructor. split. { apply. right. eexists _, _. by econstructor. }
    move => ?????. inv_step.
    eexists. right. split. {
      simpl. apply: TraceStepSome. { by econstructor. }
      apply: TraceEnd.
    }

    constructor. split. { apply. right. eexists _, _. by econstructor. }
    move => ?????. inv_step.
    eexists. right. split. { apply: TraceEnd. }

    constructor. split. { apply. right. eexists _, _. by econstructor. }
    move => ?????. inv_step.
    eexists. right. split. { apply: TraceEnd. }

    constructor. split. { apply. right. eexists _, _. by econstructor. }
    move => ?????. inv_step.
    eexists. right. split. { apply: TraceEnd. }

    constructor. split. { apply. right. eexists _, _. by econstructor. }
    move => ?????. inv_step. simplify_map_eq.
    eexists. right. split. { apply: TraceEnd. }

    constructor. split. { apply. right. eexists _, _. by econstructor. }
    move => ?????. inv_step.
    eexists. right. split. {
      simpl. apply: TraceStepNone. { by econstructor. }
      simpl. apply: TraceStepNone. { by econstructor. }
      simpl. apply: TraceStepSome. { by econstructor. }
      apply: TraceEnd.
    }

    constructor. split. { apply. naive_solver. }
    move => ?????. inv_step.
    Unshelve.
    all: apply: inhabitant.
  Qed.
End test.

(*** Safety property stuff *)
Definition example_code : rec_fns.
Admitted.
Definition example_code_spec : module rec_event.
Admitted.

(* TODO: should safety violation simply be UB? *)
Definition safety_property EV := module (EV + ()).

Definition example_safety_prop : safety_property rec_event := {|
  m_state := bool;
  m_initial := false;
  m_step b e b' :=
    if b is true then e = Some (inr ()) ∧ b' = false else
      if e is Some (inl (CallEvt "dont_call_with_2" [2%Z])) then b' = true
      else False;
  m_is_ub b := False;
|}.

Inductive link_safety_prop_mediator {EV} : option EV → option (EV + ()) → option (EV + ()) → Prop :=
| LSPLeft e1:
    link_safety_prop_mediator (Some e1) (Some (inl e1)) (Some (inl e1))
(* TODO: we probably don't want the following line*)
| LSPIgnore e1:
    link_safety_prop_mediator (Some e1) None (Some (inl e1))
| LSPRight:
    link_safety_prop_mediator None (Some (inr ())) (Some (inr ())).

Definition link_safety_prop {EV} (m : module EV) (s : safety_property EV) :=
  link m s (stateless_mediator link_safety_prop_mediator).

Lemma link_safety_prop_refines {EV} (m1 m2 : module EV) s1 s2:
  refines m1 m2 → refines s1 s2 → refines (link_safety_prop m1 s1) (link_safety_prop m2 s2).
Proof. apply: refines_horizontal. Qed.

Definition omap_module {EV1 EV2} (f : EV1 → option EV2) (m : module EV1) : module EV2 :=
  link m ∅ (stateless_mediator (λ e1 (e2 : option unit) e3, ∃ κ, e1 = Some κ ∧ e3 = f κ)).

Lemma omap_module_refines {EV1 EV2} (f : EV1 → option EV2) m1 m2:
  refines m1 m2 → refines (omap_module f m1) (omap_module f m2).
Proof. move => ?. apply: refines_horizontal => //. apply: refines_reflexive. Qed.

Definition fmap_module {EV1 EV2} (f : EV1 → EV2) (m : module EV1) : module EV2 :=
  link m ∅ (stateless_mediator (λ e1 (e2 : option unit) e3, ∃ κ, e1 = Some κ ∧ e3 = Some (f κ))).

Lemma fmap_module_refines {EV1 EV2} (f : EV1 → EV2) m1 m2:
  refines m1 m2 → refines (fmap_module f m1) (fmap_module f m2).
Proof. move => ?. apply: refines_horizontal => //. apply: refines_reflexive. Qed.

Definition is_safe {EV} (m : module (EV + ())) : Prop :=
  refines (omap_module (λ e, if e is inr _ then Some () else None) m) ∅.

Lemma is_safe_refines {EV} (m1 m2 : module (EV + ())):
  refines m1 m2 → is_safe m2 → is_safe m1.
Proof. move => ??. apply: refines_vertical => //. by apply: omap_module_refines. Qed.

Lemma example_code_refines_spec :
  refines (rec_module example_code) example_code_spec.
Admitted.

Lemma spec_is_safe:
  is_safe (link_safety_prop example_code_spec example_safety_prop).
Admitted.

Lemma code_is_safe :
  is_safe (link_safety_prop (rec_module example_code) example_safety_prop).
Proof.
  apply: is_safe_refines.
  - apply: link_safety_prop_refines; [ | apply: refines_reflexive ].
    apply: example_code_refines_spec.
  - apply: spec_is_safe.
Qed.

Definition unreachable (self : fn_name) : fndef := {|
  fd_args := [];
  fd_body := Call self [];
|}.

Definition check_safety_prop (unreachable : fn_name) : fndef := {|
  fd_args := ["n"];
  fd_body :=
    LetE "2" (Const 2) $
         If "n" EqCmp "2" (
           LetE "_" (Call "assert_failed" []) $
           Call unreachable []) $
         (Call "dont_call_with_2" ["n"])
|}.

Definition example_safety_prop_impl (f funreachable : fn_name) : rec_fns :=
  <[funreachable := (unreachable funreachable)]>
  {[f := check_safety_prop funreachable]}.

Lemma example_safety_prop_impl_refines_safety_prop (f fu : fn_name) :
  (* TODO: This does not yet make sense *)
  refines (fmap_module inl (rec_module (example_safety_prop_impl f fu))) example_safety_prop.
Proof.
Admitted.

Fixpoint rename_fn (f1 f2 : fn_name) (e : expr) :=
  match e with
  | Var v => Var v
  | Const n => Const n
  | BinOp v1 o v2 => BinOp v1 o v2
  | If v1 c v2 e1 e2 => If v1 c v2 (rename_fn f1 f2 e1) (rename_fn f1 f2 e2)
  | LetE v e1 e2 => LetE v (rename_fn f1 f2 e1) (rename_fn f1 f2 e2)
  | Call f args => Call (if bool_decide (f = f1) then f2 else f) args
  end.

Fixpoint rename_fn_in_def (f1 f2 : fn_name) (fd : fndef) := {|
  fd_args := fd.(fd_args);
  fd_body := rename_fn f1 f2 fd.(fd_body);
|}.

Lemma implement_example_safety_prop (fns : rec_fns) f fu:
  "assert_failed" ∉ dom (gset _) fns →
  "dont_call_with_2" ∉ dom (gset _) fns →
  f ∉ dom (gset _) fns →
  fu ∉ dom (gset _) fns →
  refines (fmap_module (λ e, if e is CallEvt "assert_failed" [] then inr () else inl e)
       (rec_module (((rename_fn_in_def "dont_call_with_2" f) <$> fns) ∪ example_safety_prop_impl f fu)))
    (link_safety_prop (rec_module fns) example_safety_prop).
Admitted.
(* TODO: we either need to disallow the environment to call f and fu
in the spec or we should add a notion of internal functions that
cannot be called by the environment and add f and fu there *)
(* TODO: idea: Does something like this allow using a tool that only
can verify no-ub for closed programs (Something like current RefinedC)
to verify arbitrary safety properties about open programs? I.e. give
an implementation for the safety property, then use the tool to verify
the original program linked with the safety property implementation,
then show that this linked program is refined by the original program
linked with the safety property (does this direction hold?).
Simultaneously one can verify an implementation of the interface,
assuming that the client fulfills the specification and link the
implementations in the end and get that it is ub free. For giving the implementation, one needs
an instruction that non-determinisitically chooses a return value. *)
