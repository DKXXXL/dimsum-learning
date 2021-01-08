Require Import refframe.base.
Require Import stdpp.strings.
Require Import stdpp.propset.
Require Import refframe.module.

Import version7.

Definition var_name := string.

Inductive wbinop : Set :=
| WAddOp | WEqOp.
Inductive wstmt : Set :=
| WAssignConst (d : var_name) (c : Z)
| WAssignOp (d : var_name) (o : wbinop) (v1 v2 : var_name)
| WCall (r : var_name) (f : var_name) (args : list var_name)
| WIf (v : var_name) (t : list wstmt)
| WWhile (b : list wstmt) (v : var_name) (body : list wstmt)
| WReturn (v : var_name)
.

Record while_fndef : Type := {
  wf_args : list var_name;
  wf_body : list wstmt;
}.
Record while_fnstate : Type := {
  wf_name : string;
  wf_env : gmap var_name Z;
  wf_stmts : list wstmt;
}.
Record while_stack_frame : Type := {
  ws_fnstate : while_fnstate;
  ws_internal : bool;
  ws_ret_var : var_name;
}.
Definition update_ws_internal (s : while_stack_frame) (b : bool) : while_stack_frame := {|
  ws_internal := b;
  ws_fnstate := s.(ws_fnstate);
  ws_ret_var := s.(ws_ret_var);
|}.

Inductive while_state_kind :=
| WInFn (fn : while_fnstate) | WWaiting | WUb.
Record while_state : Type := {
  ws_cur : while_state_kind;
  ws_call_stack : list while_stack_frame;
  ws_fns : gmap string while_fndef;
}.
Global Instance while_state_inhabited : Inhabited while_state := populate {| ws_cur := WWaiting; ws_call_stack := []; ws_fns := ∅; |}.

Inductive while_event : Type :=
| WCallEvt (fn : string) (args: list Z) | WRetEvt (ret: Z)
| WExtCallEvt (fn : string) (args: list Z) | WDoneEvt (ret: Z).


Inductive while_step : while_state → option while_event → while_state → Prop :=
| WSAssignConst fns stack env S d c cf:
  while_step {| ws_cur := WInFn ({| wf_env := env; wf_stmts := WAssignConst d c :: S; wf_name := cf|});
                ws_call_stack := stack; ws_fns := fns; |} None
             {| ws_cur := WInFn ({| wf_env := <[d := c]>env; wf_stmts := S; wf_name := cf|});
                ws_call_stack := stack; ws_fns := fns; |}
| WSAssignOp fns stack env S d o v1 v2 res c1 c2 cf:
    env !! v1 = Some c1 → env !! v2 = Some c2 →
    res = match o with | WAddOp => c1 + c2 | WEqOp => if bool_decide (c1 = c2) then 1 else 0 end%Z →
  while_step {| ws_cur := WInFn ({| wf_env := env; wf_stmts := WAssignOp d o v1 v2 :: S; wf_name := cf|});
                ws_call_stack := stack; ws_fns := fns; |} None
             {| ws_cur := WInFn ({| wf_env := <[d := res]>env; wf_stmts := S; wf_name := cf|});
                ws_call_stack := stack; ws_fns := fns; |}
| WSIf fns stack env S S' v c thn cf:
    env !! v = Some c →
    S' = (if bool_decide (c = 0) then S else thn)%Z →
  while_step {| ws_cur := WInFn ({| wf_env := env; wf_stmts := WIf v thn :: S; wf_name := cf|});
                ws_call_stack := stack; ws_fns := fns; |} None
             {| ws_cur := WInFn ({| wf_env := env; wf_stmts := S'; wf_name := cf|});
                ws_call_stack := stack; ws_fns := fns; |}
| WSWhile fns stack env S v b body cf:
  while_step {| ws_cur := WInFn ({| wf_env := env; wf_stmts := WWhile b v body :: S; wf_name := cf|});
                ws_call_stack := stack; ws_fns := fns; |} None
             {| ws_cur := WInFn ({| wf_env := env; wf_stmts := b ++ WIf v (body ++ (WWhile b v body :: S)) :: S ; wf_name := cf|});
                ws_call_stack := stack; ws_fns := fns; |}
| WSCall fns stack env S retname fnname args argnames e σ' cf:
  (if fns !! fnname is Some fn then e = None else e = (Some (WExtCallEvt fnname args))) →
  (if fns !! fnname is Some fn then
     σ' = WInFn ({| wf_env := list_to_map (zip fn.(wf_args) args); wf_stmts := fn.(wf_body); wf_name := fnname|})
     ∧ length args = length fn.(wf_args)
   else
     σ' = WWaiting
  ) →
  Forall2 (λ n v, env !! n = Some v) argnames args →
  while_step {| ws_cur := WInFn ({| wf_env := env; wf_stmts := WCall retname fnname argnames :: S; wf_name := cf|});
                ws_call_stack := stack; ws_fns := fns; |} e
             {| ws_cur := σ';
                ws_call_stack := ({| ws_fnstate := {| wf_env := env; wf_stmts := S; wf_name := cf|};
                                     ws_internal := bool_decide (is_Some (fns !! fnname));
                                     ws_ret_var := retname|}) :: stack; ws_fns := fns; |}
| WSReturn ret fns env retname stack e σ' stk' cf:
    env !! retname = Some ret →
    (if stack is {| ws_fnstate := fs; ws_internal := true; ws_ret_var := d|}::stack' then
       σ' = WInFn ({| wf_env := <[d := ret]>fs.(wf_env); wf_stmts := fs.(wf_stmts); wf_name := fs.(wf_name)|})
       ∧ stk' = stack'
       ∧ e = None
     else
       σ' = WWaiting
       ∧ stk' = stack
       ∧ e = Some (WDoneEvt ret)
    ) →
  while_step {| ws_cur := WInFn ({| wf_env := env; wf_stmts := [WReturn retname]; wf_name := cf|});
                ws_call_stack := stack; ws_fns := fns; |} e
             {| ws_cur := σ'; ws_call_stack := stk'; ws_fns := fns; |}
(* The following are for interaction with the environment: *)
| WSRecvCall args fn fns stack def σ':
    fns !! fn = Some def →
    (* It is important to accept all events *)
  (if bool_decide (length def.(wf_args) = length args) then
    σ' = WInFn ({| wf_env := list_to_map (zip def.(wf_args) args); wf_stmts := def.(wf_body); wf_name := fn|})
  else
    σ' = WUb) →
  while_step {| ws_cur := WWaiting;
                ws_call_stack := stack; ws_fns := fns; |} (Some (WCallEvt fn args))
             {| ws_cur := σ';
                ws_call_stack := stack; ws_fns := fns; |}
| WSRecvRet ret fns stack st:
    st = (if stack is {| ws_fnstate := fs; ws_internal := false; ws_ret_var := d|}::stack' then
            WInFn ({| wf_env := <[d := ret]>fs.(wf_env); wf_stmts := fs.(wf_stmts); wf_name := fs.(wf_name)|})
          else
            WUb
    ) →
  while_step {| ws_cur := WWaiting;
                ws_call_stack := stack; ws_fns := fns; |} (Some (WRetEvt ret))
             {| ws_cur := st;
                ws_call_stack := tail stack; ws_fns := fns; |}
(* | WSExtCall fns stack env S retname fnname args argnames: *)
(*   fns !! fnname = None → *)
(*   Forall2 (λ n v, env !! n = Some v) argnames args → *)
(*   while_step {| ws_cur := WInFn ({| wf_env := env; wf_stmts := WCall retname fnname argnames :: S|}); *)
(*                 ws_call_stack := stack; ws_fns := fns; |} (Some (WExtCallEvt fnname args)) *)
(*              {| ws_cur := WWaiting; *)
(*                 ws_call_stack := ({| wf_env := env; wf_stmts := S|}, false, retname) :: stack; ws_fns := fns; |} *)
(* | WSDone ret fns env retname stack: *)
(*     env !! retname = Some ret → *)
(*     match stack with | [] | (_, false, _) :: _ => True | _ => False end → *)
(*   while_step {| ws_cur := WInFn ({| wf_env := env; wf_stmts := [WReturn retname]|}); *)
(*                 ws_call_stack := stack; ws_fns := fns; |} (Some (WDoneEvt ret)) *)
(*              {| ws_cur := WWaiting; *)
(*                 ws_call_stack := stack; ws_fns := fns; |} *)
.

Definition while_fns := gmap string while_fndef.

Definition while_module (fns: while_fns) : module while_event := {|
  m_state := while_state;
  m_initial := {|
    ws_cur := WWaiting;
    ws_call_stack := [];
    ws_fns := fns;
  |};
  m_step := while_step;
  m_is_ub σ := ¬ ∃ e σ', while_step σ e σ';
|}.

Definition while_link (fns1 fns2 : while_fns) : while_fns := fns1 ∪ fns2.

Definition while_ctx_refines (fnsi fnss : while_fns) :=
  (* TODO: Should this maybe be: ∀ C, C ##ₘ fnss → C ##ₘ fnsi ∧ refines (while_module (while_link fnsi C)) (while_module (while_link fnss C)) ? Or fns and fnsi swapped? *)
  ∀ C, refines (while_module (while_link fnsi C)) (while_module (while_link fnss C)).

Inductive while_link_mediator_state_kind : Type := | WMSWait | WMSSide (l : bool).
Record while_link_mediator_state : Type := {
  wlm_cur : while_link_mediator_state_kind;
  wlm_stack : list (bool * bool);
}.
Global Instance while_link_mediator_state_inhabited : Inhabited while_link_mediator_state := populate {| wlm_cur := WMSWait; wlm_stack := inhabitant |}.
Inductive while_link_mediator_step (fns1 fns2 : gset string) : while_link_mediator_state → option while_event → option while_event → option while_event → while_link_mediator_state → Prop :=
| WLMCallLeftToOut fnname args stack:
    fnname ∉ fns2 →
    while_link_mediator_step fns1 fns2 {| wlm_cur := WMSSide true; wlm_stack := stack |}
      (Some (WExtCallEvt fnname args)) None (Some (WExtCallEvt fnname args))
      {| wlm_cur := WMSWait; wlm_stack := (true, false)::stack |}
| WLMCallRightToOut fnname args stack:
    fnname ∉ fns1 →
    while_link_mediator_step fns1 fns2 {| wlm_cur := WMSSide false; wlm_stack := stack |}
      None (Some (WExtCallEvt fnname args)) (Some (WExtCallEvt fnname args))
      {| wlm_cur := WMSWait; wlm_stack := (false, false)::stack |}
| WLMCallLeftToRight fnname args stack:
    fnname ∈ fns2 →
    while_link_mediator_step fns1 fns2 {| wlm_cur := WMSSide true; wlm_stack := stack |}
      (Some (WExtCallEvt fnname args)) (Some (WCallEvt fnname args)) None
      {| wlm_cur := WMSSide false; wlm_stack := (true, true)::stack |}
| WLMCallRightToLeft fnname args stack:
    fnname ∈ fns1 →
    while_link_mediator_step fns1 fns2 {| wlm_cur := WMSSide false; wlm_stack := stack |}
      (Some (WCallEvt fnname args)) (Some (WExtCallEvt fnname args)) None
      {| wlm_cur := WMSSide true; wlm_stack := (false, true)::stack |}
| WLMDoneLeftOut retval stack:
    (if stack is (_, true)::_ then False else True) →
    while_link_mediator_step fns1 fns2 {| wlm_cur := WMSSide true; wlm_stack := stack |}
      (Some (WDoneEvt retval)) None (Some (WDoneEvt retval))
      {| wlm_cur := WMSWait; wlm_stack := stack |}
| WLMDoneRightOut retval stack:
    (if stack is (_, true)::_ then False else True) →
    while_link_mediator_step fns1 fns2 {| wlm_cur := WMSSide false; wlm_stack := stack |}
      None (Some (WDoneEvt retval)) (Some (WDoneEvt retval))
      {| wlm_cur := WMSWait; wlm_stack := stack |}
| WLMDoneLeftToRight retval stack stack':
    (if stack is (_, true)::s' then stack' = s' else False) →
    while_link_mediator_step fns1 fns2 {| wlm_cur := WMSSide true; wlm_stack := stack |}
      (Some (WDoneEvt retval)) (Some (WRetEvt retval)) None
      {| wlm_cur := WMSSide false; wlm_stack := stack' |}
| WLMDoneRightToLeft retval stack stack':
    (if stack is (_, true)::s' then stack' = s' else False) →
    while_link_mediator_step fns1 fns2 {| wlm_cur := WMSSide false; wlm_stack := stack |}
      (Some (WRetEvt retval)) (Some (WDoneEvt retval)) None
      {| wlm_cur := WMSSide true; wlm_stack := stack' |}
| WLMRecvCallLeft fnname args stack:
    fnname ∈ fns1 →
    while_link_mediator_step fns1 fns2 {| wlm_cur := WMSWait; wlm_stack := stack |}
      (Some (WCallEvt fnname args)) None (Some (WCallEvt fnname args))
      {| wlm_cur := WMSSide true; wlm_stack := stack |}
| WLMRecvCallRight fnname args stack:
    fnname ∈ fns2 →
    while_link_mediator_step fns1 fns2 {| wlm_cur := WMSWait; wlm_stack := stack |}
      None (Some (WCallEvt fnname args)) (Some (WCallEvt fnname args))
      {| wlm_cur := WMSSide false; wlm_stack := stack |}
| WLMRecvRetLeft s retval stack:
    s.1 = true →
    while_link_mediator_step fns1 fns2 {| wlm_cur := WMSWait; wlm_stack := s::stack |}
      (Some (WRetEvt retval)) None (Some (WRetEvt retval))
      {| wlm_cur := WMSSide s.1; wlm_stack := stack |}
| WLMRecvRetRight s retval stack:
    s.1 = false →
    while_link_mediator_step fns1 fns2 {| wlm_cur := WMSWait; wlm_stack := s::stack |}
      None (Some (WRetEvt retval)) (Some (WRetEvt retval))
      {| wlm_cur := WMSSide s.1; wlm_stack := stack |}
(* At least one of the following is necessary to trigger UB when recieving a ret without a stack *)
| WLMRecvRetEmptyLeft retval :
    while_link_mediator_step fns1 fns2 {| wlm_cur := WMSWait; wlm_stack := [] |}
      (Some (WRetEvt retval)) None (Some (WRetEvt retval))
      {| wlm_cur := WMSSide true; wlm_stack := [] |}
| WLMRecvRetEmptyRight retval :
    while_link_mediator_step fns1 fns2 {| wlm_cur := WMSWait; wlm_stack := [] |}
      None (Some (WRetEvt retval)) (Some (WRetEvt retval))
      {| wlm_cur := WMSSide false; wlm_stack := [] |}
.
Definition while_link_mediator (fns1 fns2 : gset string) : link_mediator while_event while_event while_event := {|
  lm_state := while_link_mediator_state;
  lm_initial := {| wlm_cur := WMSWait ; wlm_stack := [] |};
  lm_step := while_link_mediator_step fns1 fns2;
|}.

Fixpoint while_link_proj_state_stack (prev : bool) (has_stack : list bool) (stack : list while_stack_frame) : list while_stack_frame :=
  match has_stack, stack with
  | b::has_stack', s::stack' => (if b then [update_ws_internal s (prev && s.(ws_internal))] else []) ++ while_link_proj_state_stack b has_stack' stack'
  | _, _ => []
  end.

Definition while_link_proj_state' (fns : while_fns) (σ : while_state) (is_cur : bool) (has_stack : list bool) : while_state := {|
  ws_cur := if σ.(ws_cur) is WWaiting then WWaiting else if is_cur then σ.(ws_cur) else WWaiting;
  ws_call_stack := while_link_proj_state_stack is_cur has_stack σ.(ws_call_stack);
  ws_fns := fns;
|}.

Fixpoint while_link_proj_med_stack (prev : bool) (has_stack : list bool) (stack : list while_stack_frame) : list (bool * bool) :=
  match has_stack, stack with
  | b::has_stack', s::stack' => (if s.(ws_internal) && eqb prev b then [] else [(b, s.(ws_internal))]) ++ while_link_proj_med_stack b has_stack' stack'
  | _, _ => []
  end.
Definition while_link_proj_med' (σ3 : while_state) (is_cur : bool) (has_stack : list bool) : while_link_mediator_state := {|
  wlm_cur := if σ3.(ws_cur) is WWaiting then WMSWait else WMSSide is_cur;
  wlm_stack := while_link_proj_med_stack is_cur has_stack σ3.(ws_call_stack);
|}.

Definition while_state_wf (σ : while_state) : Prop :=
  (∀ s stack, σ.(ws_cur) = WWaiting → σ.(ws_call_stack) = s :: stack → s.(ws_internal) = false).

Definition while_link_inv' (fns1 fns2 : while_fns) (σ3 σ1 σ2: while_state) (σm : while_link_mediator_state) : Prop :=
  ∃ cur_inl stack_inl,
  length stack_inl = length σ3.(ws_call_stack) ∧
  σ3.(ws_fns) = fns1 ∪ fns2 ∧
  σ1 = while_link_proj_state' fns1 σ3 cur_inl stack_inl ∧
  σ2 = while_link_proj_state' fns2 σ3 (negb cur_inl) (negb <$> stack_inl) ∧
  σm = while_link_proj_med' σ3 cur_inl stack_inl ∧
  while_state_wf σ3 ∧
  while_state_wf σ1 ∧
  while_state_wf σ2
 (* (σ3.(ws_fns) = σ1.(ws_fns) ∪ σ2.(ws_fns)) *)
 (* ∧ ( *)
 (*   (σ3.(ws_cur) = WWaiting ∧ σ1.(ws_cur) = WWaiting ∧ σ2.(ws_cur) = WWaiting ∧ σm = WMSWait) *)
 (* ∨ (∃ code, σ3.(ws_cur) = WInFn code ∧ ((σ1.(ws_cur) = WInFn code ∧ σ2.(ws_cur) = WWaiting ∧ σm = WMSLeft) ∨ (σ1.(ws_cur) = WWaiting ∧ σ2.(ws_cur) = WInFn code ∧ σm = WMSRight))) *)
.

Lemma while_link_proj_state_stack_change_prev has_stack stack prev1 prev2 σ:
  while_state_wf σ →
  σ.(ws_cur) = WWaiting →
  σ.(ws_call_stack) = stack →
  while_link_proj_state_stack prev1 has_stack stack = while_link_proj_state_stack prev2 has_stack stack.
Proof. destruct stack, has_stack => //= Hwf /Hwf {}Hwf /Hwf ->. by rewrite !andb_false_r. Qed.

Lemma while_link_proj_med_stack_change_prev has_stack stack prev1 prev2 σ:
  while_state_wf σ →
  σ.(ws_cur) = WWaiting →
  σ.(ws_call_stack) = stack →
  while_link_proj_med_stack prev1 has_stack stack = while_link_proj_med_stack prev2 has_stack stack.
Proof. destruct stack, has_stack => //= Hwf /Hwf {}Hwf /Hwf -> //. Qed.

Lemma while_link_proj_state_stack_prev_false has_stack stack:
  if while_link_proj_state_stack false has_stack stack is {| ws_internal := true |}::_ then False else True.
Proof. elim: has_stack stack => // -[] ? IH []// ??. Qed.

Ltac own_simplify_map_eq :=
  simplify_map_eq;
  repeat match goal with
  | H : _ ∉ dom (gset string) _ |- _ => move/not_elem_of_dom in H
  | H : (_ ∪ _) !! _ = Some _ |- _ => move/lookup_union_Some_raw in H
  | H : (_ ∪ _) !! _ = None |- _ => move/lookup_union_None in H
  end.


Lemma while_link_ok' fns1 fns2:
  fns1 ##ₘ fns2 →
  refines_equiv (while_module (while_link fns1 fns2)) (link (while_module fns1) (while_module fns2) (while_link_mediator (dom _ fns1) (dom _ fns2))).
Proof.
  move => Hdisj.
  have Hnotin1 : ∀ fn def, fns1 !! fn = Some def → fns2 !! fn = None. {
    move: Hdisj => /map_disjoint_spec ? fn ??. destruct (fns2 !! fn) eqn: ? => //. naive_solver.
  }
  have Hnotin2 : ∀ fn def, fns2 !! fn = Some def → fns1 !! fn = None. {
    move: Hdisj => /map_disjoint_spec ? fn ??. destruct (fns1 !! fn) eqn: ? => //. naive_solver.
  }
  apply (inv_implies_refines_equiv (while_module _) (link (while_module _) (while_module _) (while_link_mediator _ _)) (curry ∘ curry ∘ (while_link_inv' fns1 fns2))). { eexists true, []. split_and! => //. } {
    move => [cur3 sk3 f3] [[? ?] ?] /= [cur_inl [stack_inl [/= ? [?[? [? [? [Hwf3 [Hwf1 Hwf2]]]]]]]]]. subst.
    destruct cur3; simplify_eq/=.
    + move => Hub.
      eexists _. apply: TraceUbRefl => /=.
      destruct cur_inl; [left | right]; contradict Hub.
      all: move: Hub => [? [??]]; invert_all while_step; simplify_map_eq; try by eexists _, _; econstructor => //.
      * destruct ((fns1 ∪ fns2) !! fnname) eqn: ?.
        all: eexists _, _; econstructor => //; simplify_map_eq => //. split => //.
        admit.
      * destruct sk3 as [|[?[]?]?]; eexists _, _; econstructor => //.
      * destruct ((fns1 ∪ fns2) !! fnname) eqn: ?.
        all: eexists _, _; econstructor => //; simplify_map_eq => //. split => //.
        admit.
      * destruct sk3 as [|[?[]?]?]; eexists _, _; econstructor => //.
    + move => Hx. contradict Hx. eexists _, _. by econstructor.
    + move => ?. eexists (_, _, _). apply: TraceUb.
      destruct cur_inl; [left|right] => /= -[?[??]]; invert_all while_step.
  } {
    move => [[? ?] ?] [cur3 sk3 f3] /= [cur_inl [stack_inl [/= ? [?[? [? [? [Hwf3 [Hwf1 Hwf2]]]]]]]]]. subst.
    destruct cur3; simplify_eq/=.
    + move => [|] Hub; eexists _; apply: TraceUbRefl => //=; contradict Hub; unfold while_link_proj_state' => /=; case_match; try by eexists _, _; econstructor.
      all: move: Hub => [? [??]]; invert_all while_step; simplify_map_eq; try by eexists _, _; econstructor.
      * destruct (fns1 !! fnname) eqn: ?; eexists _, _; econstructor => //; by simplify_map_eq.
      * repeat case_match; destruct_and?; simplify_eq; destruct stack_inl as [ | w ?] => //.
        eexists _, _. econstructor => //.
        eexists _, _. econstructor => //. admit.
        eexists _, _. econstructor => //. admit.
      * destruct (fns2 !! fnname) eqn: ?; eexists _, _; econstructor => //; by simplify_map_eq.
      * admit.
    + move => [|] Hx; contradict Hx; eexists _, _; by econstructor.
    + move => ?. eexists _. apply: TraceUb. move => /= -[?[??]]. invert_all while_step.
  }
  - move => [cur3 sk3 f3] [[? ?] ?] [? ? ?] ? /= [cur_inl [stack_inl [/= ? [?[? [? [? [Hwf3 [Hwf1 Hwf2]]]]]]]]] ?. subst.
    destruct cur3; simplify_eq/=.
    + invert_all while_step.
      * right. set cur_inl' := cur_inl. destruct cur_inl.
        all: eexists (_, _, _); split; [ | apply: TraceStepNone; [| by apply: TraceEnd] ; unfold while_link_proj_state' in *; simpl in *; simplify_map_eq; by repeat econstructor].
        all: eexists cur_inl', stack_inl; split_and! => //=; unfold while_link_proj_state' in *; simpl in *; simplify_map_eq => //.
      * right. set cur_inl' := cur_inl. destruct cur_inl.
        all: eexists (_, _, _); split; [ | apply: TraceStepNone; [| by apply: TraceEnd] ; unfold while_link_proj_state' in *; simpl in *; simplify_map_eq; by repeat econstructor].
        all: eexists cur_inl', stack_inl; split_and! => //=; unfold while_link_proj_state' in *; simpl in *; simplify_map_eq => //.
      * right. set cur_inl' := cur_inl. destruct cur_inl.
        all: eexists (_, _, _); split; [ | apply: TraceStepNone; [| by apply: TraceEnd] ; unfold while_link_proj_state' in *; simpl in *; simplify_map_eq; by repeat econstructor].
        all: eexists cur_inl', stack_inl; split_and! => //=; unfold while_link_proj_state' in *; simpl in *; simplify_map_eq => //.
      * right. set cur_inl' := cur_inl. destruct cur_inl.
        all: eexists (_, _, _); split; [ | apply: TraceStepNone; [| by apply: TraceEnd] ; unfold while_link_proj_state' in *; simpl in *; simplify_map_eq; by repeat econstructor].
        all: eexists cur_inl', stack_inl; split_and! => //=; unfold while_link_proj_state' in *; simpl in *; simplify_map_eq => //.
      * (* Call *) case_match; destruct_and?; simplify_eq.
        -- (* Call inside spec *)
          right.
          set old_cur_inl := cur_inl.
          revert select ((_ ∪ _) !! _ = _) => /lookup_union_Some_raw [Hn1 |[? Hn2]]; [set cur_inl' :=true|set cur_inl' :=false]; destruct cur_inl.
          all: eexists (_, _, _); split.
          all: try ( apply: TraceStepNone; [ |by apply: TraceEnd]).
          all: try by econstructor; [ by econstructor; simplify_map_eq|].
          all: try (apply: LinkStepBoth; econstructor; simplify_map_eq => //; rewrite ?bool_decide_true ?elem_of_dom; naive_solver).
          all: eexists cur_inl', (old_cur_inl :: stack_inl); split_and! => //=; try by f_equal.
          all: rewrite /while_link_proj_state'/while_link_proj_med'/= ?(Hnotin1 _ _ Hn1) ?(Hnotin2 _ _ Hn2); simplify_map_eq => //.
          all: try by rewrite /while_state_wf; naive_solver.
        -- (* Call to outside *)
          revert select ((_ ∪ _) !! _ = _) => /lookup_union_None[Hn1 Hn2].
          right.
          set cur_inl' := cur_inl. destruct cur_inl.
          all: eexists (_, _, _); split.
          all: try ( apply: TraceStepSome; [ |by apply: TraceEnd]).
          all: try by econstructor; [by econstructor; simplify_map_eq|]; econstructor; by apply not_elem_of_dom.
          all: eexists cur_inl', (cur_inl' :: stack_inl); split_and! => //.
          all: try by simpl; f_equal.
          all: rewrite /while_link_proj_state'/while_link_proj_med'/= ?Hn1 ?Hn2 //.
          all: try by rewrite /while_state_wf; naive_solver.
      * (* Return *)
        right.
        destruct sk3 as [|[? [] ?] sk3]; destruct_and?; simplify_eq; destruct stack_inl as [| new_cur_inl ] => //; simplify_eq/=.
        -- destruct cur_inl.
           all: eexists (_, _, _); split.
           all: try ( apply: TraceStepSome; [ |by apply: TraceEnd]).
           all: try by  econstructor; [by econstructor|]; by econstructor.
           all: eexists true, []; split_and! => //.
        -- set cur_inl' := cur_inl. set new_cur_inl' := new_cur_inl. destruct cur_inl, new_cur_inl.
           all: eexists (_, _, _); split.
           all: try ( apply: TraceStepNone; [ |by apply: TraceEnd]).
           all: try by econstructor; [by econstructor|]; by econstructor.
           all: try (apply: LinkStepBoth; try apply: WSRecvRet; try apply: WSReturn; move => //=).
           all: try by pose proof (while_link_proj_state_stack_prev_false stack_inl sk3); unfold new_cur_inl'; by repeat case_match => //; simplify_eq.
           all: try by pose proof (while_link_proj_state_stack_prev_false (negb <$> stack_inl) sk3); unfold new_cur_inl'; by repeat case_match => //; simplify_eq.
           all: try by econstructor.
           all: eexists new_cur_inl', stack_inl; split_and! => //=.
           all: unfold while_state_wf; intros; simplify_eq/= => //.
           pose proof (while_link_proj_state_stack_prev_false stack_inl sk3); by repeat case_match => //; simplify_eq.
           pose proof (while_link_proj_state_stack_prev_false (negb <$> stack_inl) sk3); by repeat case_match => //; simplify_eq.
        -- set cur_inl' := cur_inl. set new_cur_inl' := new_cur_inl. destruct cur_inl, new_cur_inl.
           all: eexists (_, _, _); split.
           all: try ( apply: TraceStepSome; [ |by apply: TraceEnd]).
           all: try by econstructor; [by econstructor|]; by econstructor.
           all: try by econstructor; [ econstructor; [done| simpl;
            pose proof (while_link_proj_state_stack_prev_false stack_inl sk3);
            unfold new_cur_inl'; by repeat case_match => //]|]; by econstructor.
           all: try by econstructor; [ econstructor; [done| simpl;
            pose proof (while_link_proj_state_stack_prev_false (negb <$> stack_inl) sk3);
            unfold new_cur_inl'; by repeat case_match => //]|]; by econstructor.
           all: eexists new_cur_inl', (new_cur_inl' :: stack_inl); split_and! => //=.
           all: try by f_equal.
           all: unfold while_state_wf; intros; simplify_eq/= => //.

           pose proof (while_link_proj_state_stack_prev_false stack_inl sk3); by repeat case_match => //; simplify_eq.
           pose proof (while_link_proj_state_stack_prev_false (negb <$> stack_inl) sk3); by repeat case_match => //; simplify_eq.

           all: eexists cur_inl', []; split_and! => //.
    + invert_all while_step.
      * (* Recv Call *)
        right.
        revert select ((_ ∪ _) !! _ = _) => /lookup_union_Some_raw [?|[??]]; [set cur_inl' :=true|set cur_inl' :=false].
        all: case_bool_decide.
        all: eexists (_, _, _); split.
        all: try ( apply: TraceStepSome; [ |by apply: TraceEnd]).
        all: try (econstructor; [econstructor;[done| first [ by rewrite bool_decide_true | by rewrite bool_decide_false] ]|]).
        all: try (econstructor; apply elem_of_dom; naive_solver).
        all: simplify_eq/=.
        all: eexists cur_inl', stack_inl; split_and! => //.
        all: rewrite /while_link_proj_state'/while_link_proj_med'/= ?Hn1 ?Hn2 //.
        all: f_equal.
        all: try by apply: while_link_proj_state_stack_change_prev; [apply: Hwf3|..].
        all: try by apply: while_link_proj_med_stack_change_prev; [apply: Hwf3|..].
      * destruct sk3 as [| [? [] ?] sk3]. {
          destruct stack_inl => //.
          right. eexists (_,_,_). split.
          all: try ( apply: (TraceStepSome); [ |by apply: TraceEnd]).
          all: try by econstructor; [by apply: WSRecvRet|]; simpl; econstructor.
          by eexists true, [].
        }
        { unfold while_state_wf in *; naive_solver. }
        right.
        destruct stack_inl as [|s stack_inl] => //; simplify_eq/=.
        set s' := s. destruct s.
        all: eexists (_, _, _); split.
        all: try ( apply: (TraceStepSome); [ |by apply: TraceEnd]).
        all: try by econstructor; [by apply: WSRecvRet|]; simpl; econstructor.
        all: eexists s', stack_inl; split_and! => //.
        all: rewrite /while_link_proj_state'/while_link_proj_med'/= //.
        all: try by repeat case_match => //.
        all: repeat case_match; simplify_eq/=; try by destruct cur_inl; try naive_solver.
    + invert_all while_step.
  - move => [cur3 sk3 f3] [[? ?] ?] [[? ?] ?] ? /= [cur_inl [stack_inl [/= ? [?[? [? [? [Hwf3 [Hwf1 Hwf2]]]]]]]]] ?. subst.
    destruct cur3 as [[? ? stmts] | |]; simplify_eq/=.
    + set cur_inl' := cur_inl.
      destruct stmts as [|[]?].
      * left. left. move => [? [? ?]]. invert_all while_step.
      * invert_all @link_step => //; invert_all while_step; destruct_and?; destruct cur_inl; simplify_eq/= => //.
        all: try by invert_all while_link_mediator_step.
        all: try by right; eexists _; split; [ | apply: TraceStepNone; [|apply: TraceEnd]; by econstructor];
        eexists cur_inl', stack_inl; split_and! => //=; unfold while_link_proj_state' in *; simpl in *; simplify_map_eq => //.
      * invert_all @link_step => //; invert_all while_step; destruct_and?; destruct cur_inl; simplify_eq/= => //.
        all: try by invert_all while_link_mediator_step.
        all: try by right; eexists _; split; [ | apply: TraceStepNone; [|apply: TraceEnd]; by econstructor];
        eexists cur_inl', stack_inl; split_and! => //=; unfold while_link_proj_state' in *; simpl in *; simplify_map_eq => //.
      * (* Call *)
        invert_all @link_step => //; invert_all while_step; destruct_and?; destruct cur_inl; simplify_eq/= => //;
          invert_all while_link_mediator_step.
        -- case_match; simplify_eq/=; destruct_and?; simplify_eq/=; invert_all while_link_mediator_step.
           all: right; eexists _; split.
           all: try ( apply: TraceStepNone; [ | apply: TraceEnd ]).
           all: try ( apply: TraceStepSome; [ | apply: TraceEnd ]).
           all: try by econstructor => //; by simplify_map_eq.
           all: try by econstructor; own_simplify_map_eq => //; case_match; own_simplify_map_eq => //; naive_solver.
           ++ rewrite bool_decide_true. { eexists _. by apply: lookup_union_Some_l. }
              eexists true, (cur_inl' :: stack_inl). split_and! => //=. by f_equal.
           ++ rewrite bool_decide_false. { move => [? ?]. own_simplify_map_eq. naive_solver. }
           eexists false, (cur_inl' :: stack_inl). split_and! => //=. by f_equal.
           all: unfold while_state_wf; naive_solver.
        -- case_match; simplify_eq/=; destruct_and?; simplify_eq/=; invert_all while_link_mediator_step.
           all: right; eexists _; split.
           all: try ( apply: TraceStepNone; [ | apply: TraceEnd ]).
           all: try ( apply: TraceStepSome; [ | apply: TraceEnd ]).
           all: try by econstructor => //; by simplify_map_eq.
           all: try by econstructor; own_simplify_map_eq => //; case_match; own_simplify_map_eq => //; naive_solver.
           ++ rewrite bool_decide_true. { eexists _. by apply: lookup_union_Some_r. }
              eexists false, (cur_inl' :: stack_inl). split_and! => //=. by f_equal.
           ++ rewrite bool_decide_false. { move => [? ?]. own_simplify_map_eq. naive_solver. }
              eexists true, (cur_inl' :: stack_inl). split_and! => //=. by f_equal.
           all: unfold while_state_wf; naive_solver.
        -- case_match; case_match => //; destruct_and?; simplify_eq.
           all: case_bool_decide => //.
           2: {
             left. left. move => [? [??]]. invert_all while_step; case_match; own_simplify_map_eq.
             2: naive_solver.
             destruct_and!.
             revert select (_ ≠ _). apply.
             repeat match goal with | H : Forall2 _ _ _ |- _ => move: H => /Forall2_length ? end.
             destruct_or?; destruct_and?; simplify_eq; try naive_solver.
             congruence.
           }
           right; eexists _; split.
           all: try ( apply: TraceStepNone; [ | apply: TraceEnd ]).
           2: {
               econstructor => //; case_match; own_simplify_map_eq; try (exfalso; naive_solver); move => //;
                 destruct_or?; naive_solver.
           }
           simplify_eq/=. rewrite bool_decide_true. { eexists _. by apply: lookup_union_Some_l. }
           eexists (negb cur_inl'), (cur_inl' :: stack_inl). split_and! => //=. by f_equal.
           all: unfold while_state_wf; naive_solver.
        -- destruct (fns2 !! f) eqn:?; simplify_map_eq.
        -- case_match; case_match => //; destruct_and?; simplify_eq.
           all: case_bool_decide => //.
           2: {
             left. left. move => [? [??]]. invert_all while_step; case_match; own_simplify_map_eq.
             2: naive_solver.
             destruct_and!.
             revert select (_ ≠ _). apply.
             repeat match goal with | H : Forall2 _ _ _ |- _ => move: H => /Forall2_length ? end.
             destruct_or?; destruct_and?; simplify_eq; try naive_solver.
             congruence.
           }
           right; eexists _; split.
           all: try ( apply: TraceStepNone; [ | apply: TraceEnd ]).
           2: {
               econstructor => //; case_match; own_simplify_map_eq; try (exfalso; naive_solver); move => //;
                 destruct_or?; naive_solver.
           }
           simplify_eq/=. rewrite bool_decide_true. { eexists _. by apply: lookup_union_Some_r. }
           eexists (negb cur_inl'), (cur_inl' :: stack_inl). split_and! => //=. by f_equal.
           all: unfold while_state_wf; naive_solver.
        -- destruct (fns1 !! f) eqn:?; simplify_map_eq.
      * invert_all @link_step => //; invert_all while_step; destruct_and?; destruct cur_inl; simplify_eq/= => //.
        all: try by invert_all while_link_mediator_step.
        all: try by right; eexists _; split; [ | apply: TraceStepNone; [|apply: TraceEnd]; by econstructor];
        eexists cur_inl', stack_inl; split_and! => //=; unfold while_link_proj_state' in *; simpl in *; simplify_map_eq => //.
      * invert_all @link_step => //; invert_all while_step; destruct_and?; destruct cur_inl; simplify_eq/= => //.
        all: try by invert_all while_link_mediator_step.
        all: try by right; eexists _; split; [ | apply: TraceStepNone; [|apply: TraceEnd]; by econstructor];
        eexists cur_inl', stack_inl; split_and! => //=; unfold while_link_proj_state' in *; simpl in *; simplify_map_eq => //.
      * invert_all @link_step => //; invert_all while_step; destruct_and?; destruct cur_inl; simplify_eq/= => //;
          invert_all while_link_mediator_step.
        -- admit.
        -- admit.
        -- admit.
        -- admit.
        -- admit.
        -- admit.
    + invert_all @link_step => //; invert_all while_step; destruct_and?; simplify_eq/= => //;
          invert_all while_link_mediator_step.
      -- admit.
      -- destruct stack_inl, sk3 as [|[?[]?]?] => //. { unfold while_state_wf in *; naive_solver. }
         simplify_eq/=. right. rewrite andb_false_r.
         eexists _. split.
         all: try ( apply: TraceStepSome; [ | apply: TraceEnd ]).
         all: try by econstructor.
         eexists true, (stack_inl). split_and! => //=.
      -- admit.
      -- admit.
      -- destruct stack_inl, sk3 as [|[?[]?]?] => //. { unfold while_state_wf in *; naive_solver. }
         simplify_eq/=. right. rewrite andb_false_r.
         eexists _. split.
         all: try ( apply: TraceStepSome; [ | apply: TraceEnd ]).
         all: try by econstructor.
         eexists false, (stack_inl). split_and! => //=.
      -- admit.
    + left. left. move => [? [? ?]]. invert_all while_step.
Admitted.


(* Definition while_link_proj_state (fns : while_fns) (σ : while_state) : while_state := {| *)
(*   ws_cur := if σ.(ws_cur) is WInFn c then if fns !! c.(wf_name) is Some _ then WInFn c else WWaiting else σ.(ws_cur); *)
(*   ws_call_stack := []; *)
(*   ws_fns := fns; *)
(* |}. *)

(* Definition while_link_inv (fns1 fns2 : while_fns) (σ3 σ1 σ2: while_state) (σm : list while_link_mediator_state) : Prop := *)
(*   (if σ3.(ws_cur) is WInFn c then is_Some (σ3.(ws_fns) !! c.(wf_name)) else True) ∧ *)
(*   σ3.(ws_fns) = fns1 ∪ fns2 ∧ *)
(*   σ1 = while_link_proj_state fns1 σ3 ∧ *)
(*   σ2 = while_link_proj_state fns2 σ3 *)
(*  (* (σ3.(ws_fns) = σ1.(ws_fns) ∪ σ2.(ws_fns)) *) *)
(*  (* ∧ ( *) *)
(*  (*   (σ3.(ws_cur) = WWaiting ∧ σ1.(ws_cur) = WWaiting ∧ σ2.(ws_cur) = WWaiting ∧ σm = WMSWait) *) *)
(*  (* ∨ (∃ code, σ3.(ws_cur) = WInFn code ∧ ((σ1.(ws_cur) = WInFn code ∧ σ2.(ws_cur) = WWaiting ∧ σm = WMSLeft) ∨ (σ1.(ws_cur) = WWaiting ∧ σ2.(ws_cur) = WInFn code ∧ σm = WMSRight))) *) *)
(* . *)

(* Lemma all_states_in_equiv_forall {A B} R a e (Φ : A → B → Prop) : *)
(*   (∀ x, x ∈ a → ∃ y, y ∈ e ∧ R x y) → *)
(*   (∀ y, y ∈ e → ∃ x, x ∈ a ∧ R x y) → *)
(*   (∀ x y, x ∈ a → y ∈ e → R x y → Φ x y) → *)
(*   all_states_in_equiv a e Φ. *)
(* Proof. move => Hin. split => ?; naive_solver. Qed. *)

(* Lemma all_states_in_equiv_forall_id {A B} a e (Φ : A → B → Prop) : *)
(*   ((∃ x, x ∈ a) ↔ (∃ y, y ∈ e)) → *)
(*   (∀ x y, x ∈ a → y ∈ e → Φ x y) → *)
(*   all_states_in_equiv a e Φ. *)
(* Proof. move => Hin. split => ?; naive_solver. Qed. *)

(* Lemma all_states_in_remove_ub {A B} (Φ : A → B → Prop) P1 P2 (Q1 Q2 : Prop) `{!Inhabited B} : *)
(*   (∀ x y, Q1 → Q2 → Φ x y) → *)
(*   (Q1 → Q2) → *)
(*   all_states_in P1 P2 Φ → *)
(*   all_states_in (P1 ∪ {[ _ | Q1 ]}) (P2 ∪ {[ _ | Q2 ]}) Φ. *)
(* Proof. *)
(*   move => HΦ Hub Hin x [/Hin | Hub1]; [ set_solver|]. move: (Hub1) => /Hub ?. *)
(*   eexists inhabitant. split; [ set_solver|]. apply: HΦ; set_solver. *)
(* Qed. *)

(* Lemma all_states_in_equiv_remove_ub {A B} (Φ : A → B → Prop) P1 P2 (Q1 Q2 : Prop) `{!Inhabited A} `{!Inhabited B} : *)
(*   (∀ x y, Q1 → Q2 → Φ x y) → *)
(*   (Q1 ↔ Q2) → *)
(*   all_states_in_equiv P1 P2 Φ → *)
(*   all_states_in_equiv (P1 ∪ {[ _ | Q1 ]}) (P2 ∪ {[ _ | Q2 ]}) Φ. *)
(* Proof. move => HΦ Hub [? ?]. split; apply: all_states_in_remove_ub; naive_solver. Qed. *)

(* Lemma all_states_in_equiv_ub {A B} (Φ : A → B → Prop) P1 P2 (Q1 Q2 : Prop) `{!Inhabited A} `{!Inhabited B} : *)
(*   (∀ x y, Q1 → Q2 → Φ x y) → *)
(*   Q1 → Q2 → *)
(*   all_states_in_equiv (P1 ∪ {[ _ | Q1 ]}) (P2 ∪ {[ _ | Q2 ]}) Φ. *)
(* Proof. move => HΦ Hub1 Hub2. split => ??; eexists inhabitant; set_solver. Qed. *)

(* Lemma while_link_ok fns1 fns2: *)
(*   fns1 ##ₘ fns2 → *)
(*   refines_equiv (while_module (while_link fns1 fns2)) (link (while_module fns1) (while_module fns2) while_link_mediator). *)
(* Proof. *)
(*   move => Hdisj. *)
(*   have Hnotin1 : ∀ fn def, fns1 !! fn = Some def → fns2 !! fn = None. { *)
(*     move: Hdisj => /map_disjoint_spec ? fn ??. destruct (fns2 !! fn) eqn: ? => //. naive_solver. *)
(*   } *)
(*   have Hnotin2 : ∀ fn def, fns2 !! fn = Some def → fns1 !! fn = None. { *)
(*     move: Hdisj => /map_disjoint_spec ? fn ??. destruct (fns1 !! fn) eqn: ? => //. naive_solver. *)
(*   } *)
(*   apply (next_states_implies_refines_equiv (while_module _) (link (while_module _) (while_module _) while_link_mediator) (curry ∘ curry ∘ (while_link_inv fns1 fns2))). { split_and! => //. } *)
(*   move => [cur3 sk3 f3] [[[cur1 sk1 f1] [cur2 sk2 f2]] σm] /=[/= Hin [? [-> ->]]]. subst. *)
(*   destruct cur3. *)
(*   - apply: all_states_in_equiv_remove_ub => /=. *)
(*     1: naive_solver. { *)
(*       split. *)
(*       + move => Hub. *)
(*         move: Hin => [? /lookup_union_Some [//|?|?]]; [left | right]; contradict Hub. *)
(*         all: move: Hub => [? [??]]; invert_all while_step; simplify_map_eq; try by eexists _, _; econstructor => //. *)
(*         * destruct ((fns1 ∪ fns2) !! fnname) eqn: ?. *)
(*           all: eexists _, _; econstructor => //; simplify_map_eq => //. split => //. *)
(*           admit. *)
(*         * destruct sk3 as [|[?[]?]?]; eexists _, _; econstructor => //. *)
(*         * destruct ((fns1 ∪ fns2) !! fnname) eqn: ?. *)
(*           all: eexists _, _; econstructor => //; simplify_map_eq => //. split => //. *)
(*           admit. *)
(*         * destruct sk3 as [|[?[]?]?]; eexists _, _; econstructor => //. *)
(*       + move => [|] Hub; contradict Hub; unfold while_link_proj_state => /=; case_match; try by eexists _, _; econstructor. *)
(*         all: move: Hub => [? [??]]; invert_all while_step; simplify_map_eq; try by eexists _, _; econstructor. *)
(*         * destruct (fns1 !! fnname) eqn: ?; eexists _, _; econstructor => //; by simplify_map_eq. *)
(*         * destruct (fns2 !! fnname) eqn: ?; eexists _, _; econstructor => //; by simplify_map_eq. *)
(*     } *)
(*     apply: (all_states_in_equiv_forall_id). { *)
(*       split. *)
(*       - move => [[??] [?[??]]]. simplify_eq/=. *)
(*         move: Hin => [? /lookup_union_Some [//|?|?]]. *)
(*         all: unfold while_link_proj_state; simplify_map_eq. *)
(*         all: invert_all while_step. *)
(*         all: try by eexists (None, (_, _, _)); eexists None; split => //=;repeat econstructor. *)
(*         admit. *)
(*         admit. *)
(*         admit. *)
(*         admit. *)
(*       - move => [[??] [?[??]]]. simplify_eq/=. *)
(*         move: Hin => [? /lookup_union_Some [//|?|?]]. *)
(*         all: unfold while_link_proj_state in *; simplify_map_eq. *)
(*         all: invert_all @link_step => //; try case_match => //; destruct_and!; simplify_eq. *)
(*         all: invert_all while_step. *)
(*         all: try by eexists (None, _), None; split; [done|] => /=; econstructor. *)
(*         * destruct ((fns1 ∪ fns2) !! fnname) eqn: ?. *)
(*           all: eexists (_, _), _; split; [done|]; econstructor => //; simplify_map_eq => //. *)
(*           split => //. admit. *)
(*         * destruct sk3 as [|[?[]?]?]; eexists (_, _), _; (split; [done|]); by econstructor. *)
(*         * destruct ((fns1 ∪ fns2) !! fnname) eqn: ?. *)
(*           all: eexists (_, _), _; split; [done|]; econstructor => //; simplify_map_eq => //. *)
(*           split => //. admit. *)
(*         * destruct sk3 as [|[?[]?]?]; eexists (_, _), _; (split; [done|]); by econstructor. *)
(*     } *)
(*     (* apply: (all_states_in_equiv_forall (λ eσ1 eσ2, eσ1.1 = eσ2.1)). { *) *)
(*     (*   move => [??] [? [<- /= ?]]. *) *)
(*     (*   invert_all while_step; move: Hin => [? /lookup_union_Some [//|?|?]]. *) *)
(*     (*   all: eexists (_, (_, _, _)); (split; [|done]); eexists None; split => //=. *) *)
(*     (*   all: unfold while_link_proj_state; simplify_map_eq. *) *)
(*     (*   all: try by repeat econstructor. *) *)
(*     (*   all: try by apply: LinkStepL; unfold while_link_proj_state; simplify_map_eq. constructor. done. *) *)
(*     (*   apply: LinkStepR. unfold while_link_proj_state; simplify_map_eq. constructor. done. *) *)
(*     (*   ; [apply: LinkStepL | apply: LinkStepR ]. *) *)
(*     (*   unfold while_link_proj_state; simplify_map_eq. *) *)


(*     (*   admit. *) *)
(*     (* } *) *)

(*     move => [??] [??] [? [??]] [? [??]]; simplify_eq/=. right. *)
(*     invert_all while_step. *)
(*     + invert_all @link_step => //; case_match => //; destruct_and!; simplify_eq/=. *)
(*       all: unfold while_link_proj_state in *; simpl in *; case_match; invert_all while_step. *)
(*       all: split => //; right; split => //; unfold while_link_proj_state in *; simpl; simplify_map_eq => //. *)
(*     + invert_all @link_step => //; case_match => //; destruct_and!; simplify_eq/=. *)
(*       all: unfold while_link_proj_state in *; simpl in *; case_match; invert_all while_step. *)
(*       all: split => //; right; split => //; unfold while_link_proj_state in *; simpl; simplify_map_eq => //. *)
(*     + invert_all @link_step => //; case_match => //; destruct_and!; simplify_eq/=. *)
(*       all: unfold while_link_proj_state in *; simpl in *; case_match; invert_all while_step. *)
(*       all: split => //; right; split => //; unfold while_link_proj_state in *; simpl; simplify_map_eq => //. *)
(*     + invert_all @link_step => //; case_match => //; destruct_and!; simplify_eq/=. *)
(*       all: unfold while_link_proj_state in *; simpl in *; case_match; invert_all while_step. *)
(*       all: split => //; right; split => //; unfold while_link_proj_state in *; simpl; simplify_map_eq => //. *)
(*     + case_match; destruct_and?; simplify_eq. *)
(*       * revert select ((_ ∪ _) !! _ = Some _) => Hcup. move: (Hcup) => /lookup_union_Some[//|?|?]. *)
(*         -- invert_all @link_step => //; case_match => //; destruct_and!; simplify_eq/=. *)
(*            all: unfold while_link_proj_state in *; simpl in *; case_match; invert_all while_step. *)
(*            all: split => //; right; split => //; unfold while_link_proj_state in *; simpl; simplify_map_eq => //. *)
(*            1: naive_solver. *)
(*            split_and! => //. destruct_and!. simplify_eq. repeat f_equal. admit. admit. *)
(*         -- invert_all @link_step => //; case_match => //; destruct_and!; simplify_eq/=. *)
(*            all: unfold while_link_proj_state in *; simpl in *; case_match; invert_all while_step. *)
(*            all: split => //; right; split => //; unfold while_link_proj_state in *; simpl; simplify_map_eq => //. *)
(*            1: naive_solver. *)
(*            split_and! => //. destruct_and!. simplify_eq. admit. *)
(*       * revert select ((_ ∪ _) !! _ = _) => Hcup. move: (Hcup) => /lookup_union_None[??]. *)
(*         invert_all @link_step => //; case_match => //; destruct_and!; simplify_eq/=. *)
(*         all: unfold while_link_proj_state in *; simpl in *; case_match; invert_all while_step; simplify_map_eq. *)
(*     + destruct_hyps. destruct sk3 as [|[?[]?] ?]; destruct_and!; simplify_eq/=. *)
(*       * invert_all @link_step => //; case_match => //; destruct_and!; simplify_eq/=. *)
(*         all: unfold while_link_proj_state in *; simpl in *; case_match; invert_all while_step; destruct_and! => //. *)
(*       * invert_all @link_step => //; case_match => //; destruct_and!; simplify_eq/=. *)
(*         all: unfold while_link_proj_state in *; simpl in *; case_match; invert_all while_step; destruct_and! => //. *)
(*       * invert_all @link_step => //; case_match => //; destruct_and!; simplify_eq/=. *)
(*         all: unfold while_link_proj_state in *; simpl in *; case_match; invert_all while_step; destruct_and! => //. *)
(*   - apply: all_states_in_equiv_remove_ub => /=. 1: naive_solver. { *)
(*       split. *)
(*       + move => Hx. contradict Hx. eexists _, _. by econstructor. *)
(*       + move => [|] Hx; contradict Hx; eexists _, _; by econstructor. *)
(*     } *)
(*     admit. *)
(*   - apply: all_states_in_equiv_ub; [ naive_solver | |left]. *)
(*     all: move => [? [? ?]]; invert_all while_step. *)
(* Admitted. *)


Lemma refines_implies_while_ctx_refines fnsi fnss :
  dom (gset string) fnsi = dom (gset string) fnss →
  refines (while_module fnsi) (while_module fnss) →
  while_ctx_refines fnsi fnss.
Proof.
  move => Hdom Href C.
  rewrite /while_link map_difference_union_r (map_difference_union_r fnss).
  apply: refines_vertical. { apply (while_link_ok'). apply: map_disjoint_difference_r'. }
  apply: refines_vertical. 2: { apply while_link_ok'. apply: map_disjoint_difference_r'. }
  rewrite !dom_difference_L !Hdom.
  apply: refines_horizontal.
  - apply: Href.
  - rewrite (map_difference_eq_dom_L _ _ _ Hdom).
    apply refines_reflexive.
Qed.


Module test.
  Local Open Scope Z_scope.

  Definition add1 : while_fndef := {|
    wf_args := ["a"];
    wf_body := [WAssignConst "1" 1; WAssignOp "res" WAddOp "a" "1"; WReturn "res"];
  |}.

  Definition add1_cumbersome : while_fndef := {|
    wf_args := ["a"];
    wf_body := [WAssignConst "2" 2; WAssignConst "-1" (-1);
               WAssignOp "res" WAddOp "a" "2"; WAssignOp "res" WAddOp "res" "-1";
               WReturn "res"];
  |}.

  Definition ret2 : while_fndef := {|
    wf_args := [];
    wf_body := [WAssignConst "2" 2; WReturn "2"];
  |}.

  Definition ret2_call : while_fndef := {|
    wf_args := [];
    wf_body := [WAssignConst "1" 1; WCall "ret" "add1" ["1"] ; WReturn "ret"];
  |}.

  Definition const_prop_pre : while_fndef := {|
    wf_args := [];
    wf_body := [WAssignConst "2" 2; WCall "unk" "unknown" []; WAssignOp "res" WAddOp "unk" "2"; WReturn "res"];
  |}.

  Definition const_prop_post : while_fndef := {|
    wf_args := [];
    wf_body := [WCall "unk" "unknown" []; WAssignConst "2" 2; WAssignOp "res" WAddOp "unk" "2"; WReturn "res"];
  |}.

  Lemma add1_refines_cumbersome add1_name :
    refines (while_module {[ add1_name := add1 ]}) (while_module {[ add1_name := add1_cumbersome ]}).
  Proof.
    apply: wp_implies_refines => n.
    elim/lt_wf_ind: n => ? Hloop.

    constructor. split. {
      apply. eexists _, _. apply: (WSRecvCall [0]). by apply: lookup_insert. done.
    }
    move => ? ? ? ? ?. inv_step. 2: {
      eexists. left. apply: TraceStepSome. { by econstructor. }
      apply: TraceUbRefl => -[? [? Hstep]]. inversion Hstep.
    }
    revert select ({[ _:=_]} !! _ = Some _) => /lookup_insert_Some[[??]|[??]]; subst. 2: set_solver.
    destruct args as [|arg [|??]] => //.
    eexists. right. split. {
      apply: TraceStepSome; [|by apply: TraceEnd]. constructor. by apply: lookup_insert. done.
    }
    simpl.
    constructor. split. { apply. eexists _, _. apply: WSAssignConst. }
    move => ? ? ? ? ?. inv_step. eexists _. right. split. { apply: TraceEnd. }

    constructor. split. { apply. eexists _, _. by apply: WSAssignOp. }
    move => ? ? ? ? ?. inv_step. simplify_map_eq. eexists _. right. split. { apply: TraceEnd. }

    constructor. split. { apply. eexists _, _. by econstructor. }
    move => ? ? ? ? ?. inv_step. destruct_and!. simplify_map_eq. eexists _. right. split. {
      apply: TraceStepNone. { by econstructor. }
      apply: TraceStepNone. { by econstructor. }
      apply: TraceStepNone. { by econstructor. }
      apply: TraceStepNone. { by econstructor. }
      apply: TraceStepSome. { econstructor => //. split_and! => //. simplify_map_eq. do 2 f_equal. lia. }
      apply: TraceEnd.
    }
    apply: Hloop. lia.
  Qed.

  Lemma ret2_refines_call :
    refines (while_module (<[ "add1" := add1]> {["ret2" := ret2 ]})) (while_module (<[ "add1" := add1]> {["ret2" := ret2_call ]})).
  Proof.
    apply: wp_implies_refines => n.
    elim/lt_wf_ind: n => ? Hloop.

    constructor. split. {
      apply. eexists _, _. apply: (WSRecvCall [0]). by apply: lookup_insert. done.
    }
    move => ? ? ? ? ?. inv_step.  2: {
      eexists. left. apply: TraceStepSome. { by econstructor. }
      apply: TraceUbRefl => -[? [? Hstep]]. inversion Hstep.
    }
    revert select (<[ _:=_]> _ !! _ = Some _) => /lookup_insert_Some[[??]|[??]]; subst.
    {
      destruct args as [|arg [|??]] => //.
      eexists. right. split. {
        apply: TraceStepSome; [|by apply: TraceEnd]. constructor. by apply: lookup_insert. done.
      }
      simpl.
      constructor. split. { apply. eexists _, _. apply: WSAssignConst. }
      move => ? ? ? ? ?. inv_step. eexists _. right. split. { apply: TraceEnd. }

      constructor. split. { apply. eexists _, _. by apply: WSAssignOp. }
      move => ? ? ? ? ?. inv_step. simplify_map_eq. eexists _. right. split. { apply: TraceEnd. }

      constructor. split. { apply. eexists _, _. by econstructor. }
      move => ? ? ? ? ?. inv_step. destruct_and!. simplify_map_eq. eexists _. right. split. {
        apply: TraceStepNone. { by econstructor. }
        apply: TraceStepNone. { by econstructor. }
        apply: TraceStepSome. { econstructor => //. }
        apply: TraceEnd.
      }
      apply: Hloop. lia.
    }
    revert select (_ !! _ = Some _) => /lookup_insert_Some[[??]|[??]]; subst. 2: set_solver.
    destruct args => //.
    eexists. right. split. {
      apply: TraceStepSome; [|by apply: TraceEnd]. constructor. by apply: lookup_insert_ne. done.
    }
    simpl.
    constructor. split. { apply. eexists _, _. apply: WSAssignConst. }
    move => ? ? ? ? ?. inv_step. eexists _. right. split. { apply: TraceEnd. }

    constructor. split. { apply. eexists _, _. by econstructor. }
    move => ? ? ? ? ?. inv_step. destruct_and!. simplify_map_eq. eexists _. right. split. {
      apply: TraceStepNone. { by econstructor. }
      apply: TraceStepNone. { econstructor. done. 2: repeat constructor. done. }
      apply: TraceStepNone. { by econstructor. }
      apply: TraceStepNone. { by econstructor. }
      apply: TraceStepNone. { by econstructor. }
      apply: TraceStepSome. { econstructor => //. }
      apply: TraceEnd.
    }
    apply: Hloop. lia.
  Qed.

  Lemma const_prop_post_refines_pre  :
    refines (while_module {[ "cp" := const_prop_post ]}) (while_module {[ "cp" := const_prop_pre ]}).
  Proof.
    apply: wp_implies_refines => n.
    elim/lt_wf_ind: n => ? Hloop.

    constructor. split. {
      apply. eexists _, _. apply: (WSRecvCall []). by apply: lookup_insert. done.
    }
    move => ? ? ? ? ?. inv_step. 2: {
      eexists. left. apply: TraceStepSome. { by econstructor. }
      apply: TraceUbRefl => -[? [? Hstep]]. inversion Hstep.
    }
    revert select ({[ _:=_]} !! _ = Some _) => /lookup_insert_Some[[??]|[??]]; subst. 2: set_solver.
    destruct args => //.
    eexists. right. split. {
      apply: TraceStepSome; [|by apply: TraceEnd]. constructor. by apply: lookup_insert. done.
    }
    simpl.
    constructor. split. { apply. eexists _, _. econstructor. done. 2: by econstructor. done. }
    move => ? ? ? ? ?. inv_step. case_match => //. simplify_eq.
    revert select (Forall2 _ _ _) => /Forall2_nil_inv_l ->.
    eexists _. right. split. {
      apply: TraceStepNone. { by econstructor. }
      apply: TraceStepSome. { econstructor. done. 2: constructor. done. }
      apply: TraceEnd.
    }

    constructor. split. {
      apply. eexists _, _. apply: (WSRecvCall []). by apply: lookup_insert. done.
    }
    move => ? ? ? ? ?. inv_step; simplify_map_eq. { admit. }
    eexists. right. split. {
      apply: TraceStepSome. { by econstructor. }
      apply: TraceEnd.
    }
    constructor. split. { apply. eexists _, _. apply: WSAssignConst. }
    move => ? ? ? ? ?. inv_step. eexists _. right. split. { apply: TraceEnd. }
    constructor. split. { apply. eexists _, _. by econstructor. }
    move => ? ? ? ? ?. inv_step. eexists _. right. split. { apply: TraceEnd. }

    constructor. split. { apply. eexists _, _. by econstructor. }
    move => ? ? ? ? ?. inv_step. destruct_and!. simplify_map_eq. eexists _. right. split. {
      apply: TraceStepNone. { by econstructor. }
      apply: TraceStepSome. { econstructor => //. }
      apply: TraceEnd.
    }
    apply: Hloop. lia.
  Admitted.
End test.
