Require Import refframe.base.
Require Import stdpp.gmap.
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
  wf_env : gmap var_name Z;
  wf_stmts : list wstmt;
}.
Inductive while_state_kind :=
| WInFn (fn : while_fnstate) | WWaiting | WUb.
Record while_state : Type := {
  ws_cur : while_state_kind;
  ws_call_stack : list (while_fnstate * bool * var_name);
  ws_fns : gmap string while_fndef;
}.
Global Instance while_state_inhabited : Inhabited while_state := populate {| ws_cur := WWaiting; ws_call_stack := []; ws_fns := ∅; |}.

Inductive while_event : Type :=
| WCallEvt (fn : string) (args: list Z) | WRetEvt (ret: Z)
| WExtCallEvt (fn : string) (args: list Z) | WDoneEvt (ret: Z).


Inductive while_step : while_state → option while_event → while_state → Prop :=
| WSAssignConst fns stack env S d c:
  while_step {| ws_cur := WInFn ({| wf_env := env; wf_stmts := WAssignConst d c :: S|});
                ws_call_stack := stack; ws_fns := fns; |} None
             {| ws_cur := WInFn ({| wf_env := <[d := c]>env; wf_stmts := S|});
                ws_call_stack := stack; ws_fns := fns; |}
| WSAssignOp fns stack env S d o v1 v2 res c1 c2:
    env !! v1 = Some c1 → env !! v2 = Some c2 →
    res = match o with | WAddOp => c1 + c2 | WEqOp => if bool_decide (c1 = c2) then 1 else 0 end%Z →
  while_step {| ws_cur := WInFn ({| wf_env := env; wf_stmts := WAssignOp d o v1 v2 :: S|});
                ws_call_stack := stack; ws_fns := fns; |} None
             {| ws_cur := WInFn ({| wf_env := <[d := res]>env; wf_stmts := S|});
                ws_call_stack := stack; ws_fns := fns; |}
| WSIf fns stack env S S' v c thn:
    env !! v = Some c →
    S' = (if bool_decide (c = 0) then S else thn)%Z →
  while_step {| ws_cur := WInFn ({| wf_env := env; wf_stmts := WIf v thn :: S|});
                ws_call_stack := stack; ws_fns := fns; |} None
             {| ws_cur := WInFn ({| wf_env := env; wf_stmts := S'|});
                ws_call_stack := stack; ws_fns := fns; |}
| WSWhile fns stack env S v b body:
  while_step {| ws_cur := WInFn ({| wf_env := env; wf_stmts := WWhile b v body :: S|});
                ws_call_stack := stack; ws_fns := fns; |} None
             {| ws_cur := WInFn ({| wf_env := env; wf_stmts := b ++ WIf v (body ++ (WWhile b v body :: S)) :: S|});
                ws_call_stack := stack; ws_fns := fns; |}
| WSCall fns stack env S retname fn fnname args argnames:
  fns !! fnname = Some fn →
  Forall2 (λ n v, env !! n = Some v) argnames args →
  while_step {| ws_cur := WInFn ({| wf_env := env; wf_stmts := WCall retname fnname argnames :: S|});
                ws_call_stack := stack; ws_fns := fns; |} None
             {| ws_cur := WInFn ({| wf_env := list_to_map (zip fn.(wf_args) args); wf_stmts := fn.(wf_body)|});
                ws_call_stack := ({| wf_env := env; wf_stmts := S|}, true, retname) :: stack; ws_fns := fns; |}
| WSReturn ret fns env retname stack d denv S:
    env !! retname = Some ret →
  while_step {| ws_cur := WInFn ({| wf_env := env; wf_stmts := [WReturn retname]|});
                ws_call_stack := ({| wf_env := denv; wf_stmts := S|}, true, d)::stack; ws_fns := fns; |} None
             {| ws_cur := WInFn ({| wf_env := <[d := ret]>denv; wf_stmts := S|});
                ws_call_stack := stack; ws_fns := fns; |}
(* The following are for interaction with the environment: *)
| WSRecvCall args fn fns stack def:
  fns !! fn = Some def →
  length def.(wf_args) = length args →
  while_step {| ws_cur := WWaiting;
                ws_call_stack := stack; ws_fns := fns; |} (Some (WCallEvt fn args))
             {| ws_cur := WInFn ({| wf_env := list_to_map (zip def.(wf_args) args); wf_stmts := def.(wf_body)|});
                ws_call_stack := stack; ws_fns := fns; |}
| WSRecvRet ret fns stack st:
    st = match stack with
         | ({| wf_env := denv; wf_stmts := stmts|}, false, d)::_ =>
           WInFn ({| wf_env := <[d := ret]>denv; wf_stmts := stmts|})
         | _ => WUb
         end →
  while_step {| ws_cur := WWaiting;
                ws_call_stack := stack; ws_fns := fns; |} (Some (WRetEvt ret))
             {| ws_cur := st;
                ws_call_stack := tail stack; ws_fns := fns; |}
| WSExtCall fns stack env S retname fnname args argnames:
  fns !! fnname = None →
  Forall2 (λ n v, env !! n = Some v) argnames args →
  while_step {| ws_cur := WInFn ({| wf_env := env; wf_stmts := WCall retname fnname argnames :: S|});
                ws_call_stack := stack; ws_fns := fns; |} (Some (WExtCallEvt fnname args))
             {| ws_cur := WWaiting;
                ws_call_stack := ({| wf_env := env; wf_stmts := S|}, false, retname) :: stack; ws_fns := fns; |}
| WSDone ret fns env retname stack:
    env !! retname = Some ret →
    match stack with | [] | (_, false, _) :: _ => True | _ => False end →
  while_step {| ws_cur := WInFn ({| wf_env := env; wf_stmts := [WReturn retname]|});
                ws_call_stack := stack; ws_fns := fns; |} (Some (WDoneEvt ret))
             {| ws_cur := WWaiting;
                ws_call_stack := stack; ws_fns := fns; |}
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
  ∀ C, refines (while_module (while_link fnsi C)) (while_module (while_link fnss C)).

Inductive while_link_mediator_state : Type := | WMSWait | WMSLeft | WMSRight.
Global Instance while_link_mediator_state_inhabited : Inhabited while_link_mediator_state := populate WMSWait.
Definition while_link_mediator : link_mediator while_event while_event while_event := {|
  lm_state := while_link_mediator_state;
  lm_initial := WMSWait;
  lm_step _ _ _ _ _:= True;
|}.

Definition while_link_inv (σ3 σ1 σ2: while_state) (σm : while_link_mediator_state) : Prop :=
 (σ3.(ws_fns) = σ1.(ws_fns) ∪ σ2.(ws_fns))
 ∧ (
   (σ3.(ws_cur) = WWaiting ∧ σ1.(ws_cur) = WWaiting ∧ σ2.(ws_cur) = WWaiting ∧ σm = WMSWait)
 ∨ (∃ code, σ3.(ws_cur) = WInFn code ∧ ((σ1.(ws_cur) = WInFn code ∧ σ2.(ws_cur) = WWaiting ∧ σm = WMSLeft) ∨ (σ1.(ws_cur) = WWaiting ∧ σ2.(ws_cur) = WInFn code ∧ σm = WMSRight)))
).

Lemma all_states_in_equiv_forall {A B} R a e (Φ : A → B → Prop) :
  (∀ x, x ∈ a → ∃ y, y ∈ e ∧ R x y) →
  (∀ y, y ∈ e → ∃ x, x ∈ a ∧ R x y) →
  (∀ x y, x ∈ a → y ∈ e → R x y → Φ x y) →
  all_states_in_equiv a e Φ.
Proof. move => Hin. split => ?; naive_solver. Qed.

Lemma all_states_in_equiv_forall_id {A B} a e (Φ : A → B → Prop) :
  ((∃ x, x ∈ a) ↔ (∃ y, y ∈ e)) →
  (∀ x y, x ∈ a → y ∈ e → Φ x y) →
  all_states_in_equiv a e Φ.
Proof. move => Hin. split => ?; naive_solver. Qed.

Lemma all_states_in_remove_ub {A B} (Φ : A → B → Prop) P1 P2 (Q1 Q2 : Prop) `{!Inhabited B} :
  (∀ x y, Q1 → Q2 → Φ x y) →
  (Q1 → Q2) →
  all_states_in P1 P2 Φ →
  all_states_in (P1 ∪ {[ _ | Q1 ]}) (P2 ∪ {[ _ | Q2 ]}) Φ.
Proof.
  move => HΦ Hub Hin x [/Hin | Hub1]; [ set_solver|]. move: (Hub1) => /Hub ?.
  eexists inhabitant. split; [ set_solver|]. apply: HΦ; set_solver.
Qed.

Lemma all_states_in_equiv_remove_ub {A B} (Φ : A → B → Prop) P1 P2 (Q1 Q2 : Prop) `{!Inhabited A} `{!Inhabited B} :
  (∀ x y, Q1 → Q2 → Φ x y) →
  (Q1 ↔ Q2) →
  all_states_in_equiv P1 P2 Φ →
  all_states_in_equiv (P1 ∪ {[ _ | Q1 ]}) (P2 ∪ {[ _ | Q2 ]}) Φ.
Proof. move => HΦ Hub [? ?]. split; apply: all_states_in_remove_ub; naive_solver. Qed.

Lemma all_states_in_equiv_ub {A B} (Φ : A → B → Prop) P1 P2 (Q1 Q2 : Prop) `{!Inhabited A} `{!Inhabited B} :
  (∀ x y, Q1 → Q2 → Φ x y) →
  Q1 → Q2 →
  all_states_in_equiv (P1 ∪ {[ _ | Q1 ]}) (P2 ∪ {[ _ | Q2 ]}) Φ.
Proof. move => HΦ Hub1 Hub2. split => ??; eexists inhabitant; set_solver. Qed.

Lemma while_link_ok fns1 fns2:
  refines_equiv (while_module (while_link fns1 fns2)) (link (while_module fns1) (while_module fns2) while_link_mediator).
Proof.
  apply (next_states_implies_refines_equiv (while_module _) (link (while_module _) (while_module _) while_link_mediator) (curry ∘ curry ∘ while_link_inv)). { split => //. left. done. }
  move => [cur3 sk3 f3] [[[cur1 sk1 f1] [cur2 sk2 f2]] σm] /=[ /= -> [?|[[env stmts] [? [?|?]]]]]; destruct_hyps.
  - apply: all_states_in_equiv_remove_ub => /=.
    1: naive_solver.
    admit.
    apply all_states_in_equiv_forall_id. admit.
    move => [??] [??] [? [??]] [? [??]]; simplify_eq/=. right.
    invert_all while_step.
    admit.
    admit.
  - destruct stmts as [|[]].
    + apply: all_states_in_equiv_ub; [naive_solver |..]; [|left]; move => [?[??]]; invert_all while_step.
    + apply: all_states_in_equiv_remove_ub => /=.
      1: naive_solver. {
        split => [Hn |[Hn|Hn]]; [left|..]; contradict Hn; move: Hn => [?[??]]; invert_all while_step.
        all: eexists _, _; by econstructor.
      }
      apply (all_states_in_equiv_forall (λ eσ1 eσ2, eσ1.1 = eσ2.1)). {
        move => [??] [/=?[? ?]]. invert_all while_step. eexists (_, _). split => //.
        eexists _. split => //=. by apply fmap_None. by apply: LinkStepL; [ econstructor|].
      } {
        move => [??] [/=?[? ?]]. invert_all @link_step; invert_all while_step; destruct_hyps.
        eexists (_, _). split => //. eexists _. split => //=. by apply fmap_None. by econstructor.
        admit.
        admit.
      }
      move => [??] [??] [? [??]] [? [??]]; simplify_eq/= => ?. right.
      invert_all @link_step; invert_all while_step.
      split => //. right. split; naive_solver.
      admit.
      admit.
    + apply: all_states_in_equiv_remove_ub => /=.
      1: naive_solver. {
        split => [Hn |[Hn|Hn]]; [left|..]; contradict Hn; move: Hn => [?[??]]; invert_all while_step.
        all: eexists _, _; by econstructor.
      }
      apply all_states_in_equiv_forall_id. admit.
      move => [??] [??] [? [??]] [? [??]]; simplify_eq/=. right.
      invert_all while_step.
      admit.
    + apply: all_states_in_equiv_remove_ub => /=.
      1: naive_solver. {
        split => [Hn |[Hn|Hn]]; [left|..]; contradict Hn; move: Hn => [?[??]]; invert_all while_step.
        all: admit.
      }
      apply all_states_in_equiv_forall_id. admit.
      move => [??] [??] [? [??]] [? [??]]; simplify_eq/=. right.
      invert_all while_step.
      admit.
      admit.
    + apply: all_states_in_equiv_remove_ub => /=.
      1: naive_solver. {
        split => [Hn |[Hn|Hn]]; [left|..]; contradict Hn; move: Hn => [?[??]]; invert_all while_step.
        all: eexists _, _; by econstructor.
      }
      apply all_states_in_equiv_forall_id. admit.
      move => [??] [??] [? [??]] [? [??]]; simplify_eq/=. right.
      invert_all while_step.
      admit.
    + apply: all_states_in_equiv_remove_ub => /=.
      1: naive_solver. {
        split => [Hn |[Hn|Hn]]; [left|..]; contradict Hn; move: Hn => [?[??]]; invert_all while_step.
        all: eexists _, _; by econstructor.
      }
      apply all_states_in_equiv_forall_id. admit.
      move => [??] [??] [? [??]] [? [??]]; simplify_eq/=. right.
      invert_all while_step.
      admit.
    + apply: all_states_in_equiv_remove_ub => /=.
      1: naive_solver. {
        split => [Hn |[Hn|Hn]]; [left|..]; contradict Hn; move: Hn => [?[??]]; invert_all while_step.
        all: admit.
      }
      apply all_states_in_equiv_forall_id. admit.
      move => [??] [??] [? [??]] [? [??]]; simplify_eq/=. right.
      invert_all while_step.
      admit.
      admit.
  - admit.
Admitted.

Lemma refines_implies_while_ctx_refines fnsi fnss :
  refines (while_module fnsi) (while_module fnss) →
  while_ctx_refines fnsi fnss.
Proof.
  move => Href C.
  apply: refines_vertical; [apply while_link_ok|].
  apply: refines_vertical; [|apply while_link_ok].
  apply: refines_horizontal; [|apply refines_reflexive].
  apply: Href.
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

    constructor. split. { apply. eexists _, _. by apply: WSDone. }
    move => ? ? ? ? ?. inv_step. simplify_map_eq. eexists _. right. split. {
      apply: TraceStepNone. { by econstructor. }
      apply: TraceStepNone. { by econstructor. }
      apply: TraceStepNone. { by econstructor. }
      apply: TraceStepNone. { by econstructor. }
      apply: TraceStepSome. { econstructor => //. simplify_map_eq. f_equal. lia. }
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

      constructor. split. { apply. eexists _, _. by apply: WSDone. }
      move => ? ? ? ? ?. inv_step. simplify_map_eq. eexists _. right. split. {
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

    constructor. split. { apply. eexists _, _. by apply: WSDone. }
    move => ? ? ? ? ?. inv_step. simplify_map_eq. eexists _. right. split. {
      apply: TraceStepNone. { by econstructor. }
      apply: TraceStepNone. { econstructor. done. repeat constructor. }
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
    constructor. split. { apply. eexists _, _. econstructor; [done|]. constructor. }
    move => ? ? ? ? ?. inv_step.
    revert select (Forall2 _ _ _) => /Forall2_nil_inv_l ->.
    eexists _. right. split. {
      apply: TraceStepNone. { by econstructor. }
      apply: TraceStepSome. { econstructor; [done|]. constructor. }
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

    constructor. split. { apply. eexists _, _. by apply: WSDone. }
    move => ? ? ? ? ?. inv_step. simplify_map_eq. eexists _. right. split. {
      apply: TraceStepNone. { by econstructor. }
      apply: TraceStepSome. { econstructor => //. }
      apply: TraceEnd.
    }
    apply: Hloop. lia.
  Admitted.
End test.
