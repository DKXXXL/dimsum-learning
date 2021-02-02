Require Import refframe.base.
Require Import stdpp.strings.
Require Import stdpp.propset.
Require Import refframe.module.

Class IoPartition EV IN OUT := {
  io_input : EV → IN;
  io_output : EV → OUT;
}.

Record computational_module EV IN OUT `{!IoPartition EV IN OUT} := {
  cm_state : Type;
  cm_initial : cm_state;
  cm_next : cm_state → IN → option (option (OUT * cm_state));
}.
Arguments cm_state {_ _ _ _}.
Arguments cm_initial {_ _ _ _}.
Arguments cm_next {_ _ _ _}.
Definition cm_to_module {EV IN OUT} `{!IoPartition EV IN OUT} (cm : computational_module EV IN OUT) : module EV := {|
  m_state := option cm.(cm_state);
  m_initial := Some cm.(cm_initial);
  m_step σ e σ' := if σ is Some σm then if e is Some κ then
                     match cm.(cm_next) σm (io_input κ) with
                     | None => False
                     | Some None => σ' = None
                     | Some (Some (out, σm')) => σ' = Some σm' ∧ io_output κ = out
                     end
                   else False else False;
  m_is_ub σ := σ = None;
|}.
Coercion cm_to_module : computational_module >-> module.

Module test.
Inductive call_event : Type :=
| CRecvCallEvt (fn : string) (args: list Z) | CRecvRetEvt (ret: Z)
| CCallEvt (fn : string) (args: list Z) | CDoneEvt (ret: Z).

Inductive call_event_in : Type :=
| InRecvCallEvt (fn : string) (args: list Z) | InRecvRetEvt (ret: Z)
| InCallEvt | InDoneEvt.
Inductive call_event_out : Type :=
| OutRecvCallEvt | OutRecvRetEvt
| OutCallEvt (fn : string) (args: list Z) | OutDoneEvt (ret: Z).
Global Instance call_event_partition : IoPartition call_event call_event_in call_event_out := {|
  io_input e := match e with
                | CRecvCallEvt fn args => InRecvCallEvt fn args
                | CRecvRetEvt ret => InRecvRetEvt ret
                | CCallEvt fn args => InCallEvt
                | CDoneEvt ret => InDoneEvt
                end;
  io_output e := match e with
                | CRecvCallEvt fn args => OutRecvCallEvt
                | CRecvRetEvt ret => OutRecvRetEvt
                | CCallEvt fn args => OutCallEvt fn args
                | CDoneEvt ret => OutDoneEvt ret
                end;
|}.

Inductive test_cm_state : Type :=
| TCMInit | TCMRecvd (n : Z) | TCMWait (n : Z) | TCMRet (n : Z).
Definition test_cm : (computational_module call_event call_event_in call_event_out)  := {|
  cm_state := test_cm_state;
  cm_initial := TCMInit;
  cm_next σ i :=
    match σ, i with
    | TCMInit, InRecvCallEvt "test" [n] =>
      Some (Some (OutRecvCallEvt, TCMRecvd n))
    | TCMRecvd n, InCallEvt =>
      Some (Some (OutCallEvt "id" [n], TCMWait n))
    | TCMWait n, InRecvRetEvt ret =>
      if bool_decide (n = ret) then
        Some (Some (OutRecvRetEvt, TCMRet n))
      else Some None
    | TCMRet n, InDoneEvt =>
      Some (Some (OutDoneEvt n, TCMInit))
    | _, _ => None
    end
  ;
|}.

Goal ∀ n, ∃ σ,
      Some TCMInit ~{ test_cm, [Vis (CRecvCallEvt "test" [n]); Vis (CCallEvt "id" [n]); Vis (CRecvRetEvt n); Vis (CDoneEvt n)] }~> σ.
Proof.
  move => ?. eexists _.
  apply: TraceStepSome. done.
  apply: TraceStepSome. done.
  apply: TraceStepSome. simpl. case_bool_decide => //.
  apply: TraceStepSome. done.
  apply: TraceEnd.
Qed.
End test.
