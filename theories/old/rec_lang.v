Require Import refframe.base.
Require Import stdpp.strings.
Require Import stdpp.propset.
Require Import refframe.module.

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

Definition rec_module : module rec_event := {|
  m_state := state;
  m_step := step;
  m_is_ub := is_ub;
|}.

Definition rec_link (fns1 fns2 : rec_fns) : rec_fns := fns1 ∪ fns2.

Definition ctx_refines (fnsi fnss : rec_fns) :=
  ∀ C, MS rec_module (initial_state (rec_link fnsi C)) ⊑ MS rec_module (initial_state (rec_link fnss C)).

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

Inductive call_step {EV} (m : mod_state EV) (i : call_module_info EV) : (call_state m) → option EV → (call_state m) → Prop :=
| CStep σ σs σ' e w cs:
    m.(m_step) σ e σ' →
    cs = (if default false (i.(cmi_final) <$> e) then [] else [σ']) ++ σs →
    call_step m i {| cs_stack := (σ :: σs); cs_waiting := w |}
              e {| cs_stack := cs; cs_waiting := default w (i.(cmi_waiting) <$> e) |}
| CWaiting σs:
    call_step m i {| cs_stack := σs; cs_waiting := true |}
              None {| cs_stack := m.(ms_state) :: σs; cs_waiting := false |}
.

Definition call_module_init {EV} (m : module EV) : call_state m :=
  {| cs_stack := []; cs_waiting := true |}.

Definition call_module {EV} (m : mod_state EV) (i : call_module_info EV) : module EV := {|
  m_state := call_state m;
  m_step := call_step m i;
  m_is_ub σ := default False (m.(m_is_ub) <$> head σ.(cs_stack));
|}.

Definition call_module_refines_inv {EV} (m1 m2 : mod_state EV) (i : call_module_info EV) (σ1 : (call_module m1 i).(m_state)) (sσ2 : propset (call_module m2 i).(m_state)) : Prop :=
  ∃ Ts, Forall2 (state_set_refines m1 m2) σ1.(cs_stack) Ts
    ∧ {[ σ2 | σ1.(cs_waiting) = σ2.(cs_waiting) ∧ Forall2 elem_of σ2.(cs_stack) Ts ]} ⊆ sσ2.

Lemma call_empty_steps {EV} (m : mod_state EV) i σ Pσ' w σs:
  σ ~{ m, [] }~> Pσ' →
  {| cs_stack := σ :: σs; cs_waiting := w |} ~{ call_module m i, [] }~> (λ σ', ∃ σh,
     σ'.(cs_waiting) = w ∧ tail σ'.(cs_stack) = σs ∧ head σ'.(cs_stack) = Some σh ∧ Pσ' σh).
Proof.
  move Hκ: ([]) => κ Hsteps.
  elim: Hsteps Hκ.
  - move => ????. apply: TraceEnd. naive_solver.
  - move => σ1 σ2 σ3 [?|] κs //= ?? IH ?. subst.
    apply: TraceStepNone; [ | by apply: IH]. by apply: CStep.
  - move => ?????. by apply: TraceUb => /=.
Qed.

Lemma power_mono' {EV} (m : module EV) σ1 σ2 κs (Pσ : _ → Prop):
  σ1 ~{ power_module m, κs }~> (λ σ, ∀ σ', σ ⊆ σ' → Pσ σ') →
  σ1 ⊆ σ2 →
  σ2 ~{ power_module m, κs }~> Pσ.
Proof.
  remember (λ σ : m_state (power_module m), ∀ σ' : m_state (power_module m), σ ⊆ σ' → Pσ σ') as Pσ'.
  move => HT. elim: HT σ2 HeqPσ'.
  - move => ??????. subst. apply: TraceEnd. naive_solver.
  - move => ??????? IH ???. subst.
    have [?[??]]:= power_step_mono _ _ _ _ _ ltac:(done) ltac:(done).
    apply: TraceStep; [done|]. by apply: IH.
  - move => ???????. apply: TraceUb. simplify_eq/=. set_solver.
Qed.


Lemma power_nil_2 {EV} (m : module EV) σs Pσ:
  (∃ σs', σs' ⊆ (power_reach m σs []) ∧ (m_is_ub (power_module m) σs' ∨ Pσ σs')) →
  σs ~{ power_module m, [] }~> Pσ.
Proof.
Admitted.

Lemma call_empty_steps' {EV} (m : mod_state EV) (i : call_module_info EV) σm Pm Pσ:
  σm ~{power_module m, [] }~> Pm →
  (∀ σ, σ ∈ Pσ → ∃ oh, head (cs_stack σ) = Some oh ∧ oh ∈ σm) →
  (∃ σ, σ ∈ Pσ) →
  Pσ ~{power_module (call_module m i), [] }~> (λ σ',
     ∃ σm', Pm σm' ∧
     {[ σ2 | ∃ σ, σ ∈ Pσ ∧ σ2.(cs_waiting) = σ.(cs_waiting) ∧
                 ∃ σh, head σ2.(cs_stack) = Some σh ∧
                         tail σ2.(cs_stack) = tail σ.(cs_stack)
                         ∧ σh ∈ σm' (* ??? *)
    ]} ⊆ σ').
Proof.
  move => /power_nil[?[? Hor]] Hs [σi ?].
  apply: power_nil_2.
  eexists _. split. done.
  case: Hor => [[?[??]]|?].
  - left => /=.
    have [?[??]]:= Hs _ ltac:(done).
    destruct σi as [[|??]?]; simplify_eq/=.
    eexists _. split. eexists _. split; [done|].
    by apply: TraceEnd. simpl.
    admit.
  - right.
    eexists _. split; [done|].
    set_unfold.
    move => ? [[??][?[?[?[?[??]]]]]].
    have [? [??]]:= Hs _ ltac:(done).
    eexists _. split; [done|]. simplify_eq/=.
Admitted.

Lemma CStepPower {EV} (m : mod_state EV) (i : call_module_info EV) e σm Pm Pσ:
  σm ~{power_module m, option_list (Vis <$> e)}~> Pm →
  (∀ σ, σ ∈ Pσ → is_Some (head (cs_stack σ))) →
  Pσ ~{power_module (call_module m i), option_list (Vis <$> e)}~> (λ σ',
    {[ σ2 | ∃ σ, σ ∈ Pσ ∧ σ2.(cs_waiting) = default σ.(cs_waiting) (i.(cmi_waiting) <$> e) ∧
                 if default false (i.(cmi_final) <$> e) then
                   σ2.(cs_stack) = tail σ.(cs_stack)
                 else
                   ∃ σh, head σ2.(cs_stack) = Some σh ∧
                         tail σ2.(cs_stack) = tail σ.(cs_stack)
                         (* ∧ σh ∈ Pm (* ??? *) *)
    ]} ⊆ σ').
Proof.
  move => ??.
  apply: has_trace_add_empty.
  apply: TraceStep. split. done. admit.
  apply: TraceEnd.
  set_unfold.

  admit.

Admitted.

Lemma state_set_refines_exists_Forall2 {EV} (m1 m2 : module EV) σ σs:
  Forall2 (state_set_refines m1 m2) σ σs →
  ∃ σs', Forall2 elem_of σs' σs.
Proof.
  elim. { eexists []. constructor. }
  move => ???? /state_set_refines_inhabited[??] ? [??].
  eexists. by constructor.
Qed.

(* Lemma power_trace_equiv {EV} (m : module EV) σ1 σ2 κs Pσ1 Pσ2: *)
(*   σ1 ≡ σ2 → *)
(*   σ1 ~{ power_module m, κs }~> Pσ1 → *)
(*   σ2 ~{ power_module m, κs }~> Pσ2. *)
(* Proof. Admitted. *)
  (* move => Heq HT. elim: HT σ2 Heq. *)
  (* - move => ???? <- ?. by apply: TraceEnd. *)
  (* - move => ??????? IH ???. subst. *)
    (* have [?[??]]:= power_step_mono _ _ _ _ _ ltac:(done) ltac:(done). *)
    (* apply: TraceStep; [done|]. by apply: IH. *)
  (* - move => ???????. apply: TraceUb. simplify_eq/=. set_solver. *)
(* Qed. *)

(* Lemma subset_of_power_reach {EV} (m : module EV) σ σ' σs κs: *)
(*   (∀ σ, σ ∈ σ1 → ∃ σ', σ) *)
(*   σ1 ⊆ power_reach m σ2 κs. *)
(* Proof. move => ?. eexists _. naive_solver. Qed. *)

(* Lemma power_step {EV} (m : module EV): *)
(*   (∀ σ, σ ∈ σs1 → m.(m_step) σ κ) *)
(*   σs1 ~{ power_module m, option_list (Vis <$> κ) }~> Pσ, *)



Lemma call_module_refines {EV} (m1 m2 : mod_state EV) (i : call_module_info EV) :
  m1 ⊑ m2 →
  MS (call_module m1 i) (call_module_init m1) ⊑ MS (call_module m2 i) (call_module_init m2).
Proof.
  move => Href.
  apply (inv_set_implies_refines (MS (call_module m1 i) _) (MS (call_module m2 i) _) (call_module_refines_inv _ _ _)).
  - eexists []. split_and!; [ by constructor |].
    set_unfold; move => [??] /=. rewrite /call_module_init.
    move => [-> Hall]. inversion Hall. naive_solver.
  - move => [csi wi] σs [csi2 wi2] e [Ts [Hall Hσs]] /= Hstep.
    inv_step.
    + move: Hall => /(Forall2_cons_inv_l _ _ _)[T [Ts' [Hs[??]]]]. subst.
      apply: power_mono'; [|done]. clear σs Hσs.
      destruct κ => /=. 2: {
        apply: TraceEnd.
        move => ??/=. eexists _. split; [|done].
        constructor; [|done]. by apply: state_set_refines_step_None.
      }
      admit.

      (* apply: has_trace_mono. *)
      (* apply: CStepPower. { apply: state_set_refines_ub_step; [ done|]. by constructor. } *)
      (* { admit. } *)
      (* move => /= ????. *)
      (* eexists ((if default false (cmi_final i <$> κ) then [] else [_]) ++ Ts'). *)
      (* split. { *)
      (*     apply: Forall2_app; [|done]. case_match; constructor; [|constructor]. *)
      (*       by apply: state_set_refines_step. *)
      (* } *)
      (* etrans; [| done]. *)
      (* etrans; [| done]. *)
      (* simpl. *)
      (* set_unfold. *)
      (* move => [??] [? ?]. *)
      (* case_match. *)

      (* * eexists (Build_call_state _ _ _ _). *)
      (*   split_and! => //. constructor => /=. 3: done. 2: done. admit. *)

      (* * eexists (Build_call_state _ _ _ _). *)
      (*   split_and! => //. constructor => /=. admit. admit. *)

      (*
      have ?:= state_set_refines_step _ _ _ _ _ _ ltac:(done) ltac:(done).

      have : (
               {[ σ2 | default wi (cmi_waiting i <$> κ) = cs_waiting σ2 ∧ Forall2 elem_of (cs_stack σ2) ((if default false (cmi_final i <$> κ) then [] else [(power_reach m2 T (option_list (Vis <$> κ)))]) ++ Ts') ]} ~{ power_module (call_module m2 i),
  []
  }~> (λ σ0 : m_state (power_module (call_module m2 i)),
         ∀ σ'0 : m_state (power_module (call_module m2 i)),
           σ0 ⊆ σ'0
           → call_module_refines_inv m1 m2 i
               {|
               cs_stack := (if default false (cmi_final i <$> κ) then [] else [σ']) ++ σs0;
               cs_waiting := default wi (cmi_waiting i <$> κ) |} σ'0)).

      {
        apply: TraceEnd.
        move => ??.
        eexists _.
        split. { constructor; [|done]. by apply: state_set_refines_initial. }
        etrans; [|done].
        set_unfold.
        move => [??] /= [? /(Forall2_cons_inv_r _ _ _ _)[?[?[?[??]]]]]. subst.
        eexists (Build_call_state _ _ _ _). split; [done|].
        apply: TraceStepNone; [by apply: CWaiting | apply: TraceEnd].
        set_solver.
                                                           2: apply: TraceEnd.




      apply: has_trace_add_empty.
      apply: has_trace_trans. _ _ (power_module (call_module _ _)) _ {[ σ2 | wi = cs_waiting σ2 ∧ Forall2 elem_of (cs_stack σ2) (T :: Ts') ]}).
      *)

      (* TODO: ideally we want to apply CStep here with an automatic lifting to power module. *)

      (* apply: (TraceStep' _ []). 2: by rewrite right_id. *)
      (* * simpl. split; [done|]. admit. *)
      (* * apply: TraceEnd. *)
      (*   eexists ((if default false (cmi_final i <$> κ) then [] else [_]) ++ Ts'). *)
      (*   split. { *)
      (*     apply: Forall2_app; [|done]. case_match; constructor; [|constructor]. *)
      (*       by apply: state_set_refines_step. *)
      (*   } *)
      (*   etrans; [| done]. clear H. *)

      (*   set_unfold. *)
      (*   move => [??] /= [? ?]. subst. *)

      (*   (* case_match. *) *)

      (*   eexists (Build_call_state _ _ _ _). split; [split; [done|] |]. constructor. *)

      (*   3: { *)
      (*     apply: (TraceStep' _ []); [| by rewrite right_id |]. *)
      (*     apply: CStep. *)
      (*     admit. *)
      (*     admit. *)
      (*     admit. *)
      (*   } *)
      (*   admit. *)
      (*   admit. *)
      (*
      apply: (TraceStep' _ []). 2: by rewrite right_id.
      * simpl. split; [done|]. admit.
      * apply: TraceEnd.
        eexists ((if default false (cmi_final i <$> κ) then [] else [_]) ++ Ts').
        split. {
          apply: Forall2_app; [|done]. case_match; constructor; [|constructor].
            by apply: state_set_refines_step.
        }
        etrans; [| by apply (power_reach_subseteq_proper (call_module _ _))].
        set_unfold.
        move => [??] /= [? ?]. subst.
        eexists (Build_call_state _ _ _ _). split; [split; [done|] |]. constructor.

        3: {
          apply: (TraceStep' _ []); [| by rewrite right_id |].
          apply: CStep. done.
        apply: TraceStepNone; [by apply: CWaiting | apply: TraceEnd].
        set_solver.
        admit.
*)
    + apply: power_mono'; [|done].
      apply: TraceStepNone.
      * simpl. split; [done|].
        move: Hall => /state_set_refines_exists_Forall2[??].
        eexists (Build_call_state _ _ _ _).
        apply: elem_of_subseteq_1; [apply: (power_reach_refl (call_module _ _))|].
        done.
      * apply: TraceEnd.
        eexists _.
        split. { constructor; [|done]. by apply: state_set_refines_initial. }
        etrans; [|done].
        set_unfold.
        move => [??] /= [? /(Forall2_cons_inv_r _ _ _ _)[?[?[?[??]]]]]. subst.
        eexists (Build_call_state _ _ _ _). split; [done|].
        apply: TraceStepNone; [by apply: CWaiting | apply: TraceEnd].
        set_solver.
    + destruct csi2 => //=.
      move: Hall => /(Forall2_cons_inv_l _ _ _)[T [Ts' [Hs[??]]]]. subst.
      apply: power_mono'; [|done].
      have ? := state_set_refines_ub _ _ _ _ ltac:(done) ltac:(done).
      apply: (has_trace_trans []).
      apply: call_empty_steps'; [done| |].
      admit.
      admit.
      set_unfold.
      (* TODO: we need a version of call_empty_steps for power_module *)
      admit.

(*


        apply: elem_of_power_reach.
        2: apply: TraceStep'. 2: apply: CStep => //.
        eexists _. split. simpl.
      apply: state_set_refines_ub_step.
      destruct e as [e|] => /=. 2: {
        eexists σs. split.
        - eexists _. split; [|set_solver].
          constructor => //. by apply: state_set_refines_step_None.
        - move => σ1 ?. eexists σ1. split => //. apply: TraceEnd.
      }


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
  - move => [csi wi] σs /=.

  - move => [??] ? [Ts [/state_set_refines_exists_Forall2 [??] Hσs]].
    eexists (Build_call_state _ _ _ _). by rewrite {}Hσs.
  - move => [csi wi] σs /= [Ts [Hall Hσs]] Hub. destruct csi => //; simplify_eq/=.
    move: Hall => /(Forall2_cons_inv_l _ _ _)[? [? [ /state_set_refines_ub [//|σ1 [? [? Hub2]]] [/state_set_refines_exists_Forall2[??] ?]]]] /=. subst.
    move: Hub2 => /has_trace_ub_inv[? [??]].
    eexists (Build_call_state _ _ _ _). rewrite {}Hσs. split.
    { split => //. by constructor. }
    eexists _. apply: (has_trace_trans []); [ by apply: call_empty_steps|].
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
 *)
Admitted.

Definition call_module_link_inv {EV} (m1 m2 m3 : mod_state EV) (i : call_module_info EV) (M : link_mediator EV EV EV) (σ1 : (call_module m1 i).(m_state)) (σ2 : (call_module m2 i).(m_state)) (σ3 : (call_module m3 i).(m_state)) (σm : M.(lm_state)) : Prop :=
  True.


(* This should be nicely provable if we use the language interface
from Iris, in particular at least ectx_lang since what we need about
the language might be exactly the bind rule. If we have it, it should
be fine to move ectxs between different modules. (similar to Simuliris) *)
Lemma call_module_refines_link {EV} (m1 m2 m3 : mod_state EV) (i : call_module_info EV) M :
  refines_equiv (MS (call_module m1 i) (call_module_init m1)) (MS (link (call_module m2 i) (call_module m3 i) M) (call_module_init m2, call_module_init m3, M.(lm_initial))).
Proof.
  apply (inv_implies_refines_equiv (MS (call_module m1 i) _) (MS (link (call_module m2 i) (call_module m3 i) M) _) (curry ∘ curry ∘ (call_module_link_inv _ _ _ _ _))).
  - done.
  - admit.
  - admit.
  (* - move => [cs1 ws1] [[[cs2 ws2] [cs3 ws3]] σm] [??] ?/= ? ?. *)
  (*   invert_all @call_step. *)
  (*   * right. *)
  (*     admit. *)
  (*   * admit. *)
  (* - move => [cs1 ws1] [[[cs2 ws2] [cs3 ws3]] σm] [??] ?/= ? ?. *)
  (*   admit. *)
    (* invert_all @link_step. *)
Admitted.

Definition call_intro_mediator {EV} (is_init : EV → bool) : link_mediator EV Empty_set EV := {|
  lm_state := bool;
  lm_initial := false;
  lm_step b e1 _ e2 b' := e1 = e2 ∧ b' = true ∧
      if b is false then True else if is_init <$> e1 is Some true then False else True;
|}.

Definition call_intro_inv {EV} (m : mod_state EV) (i : call_module_info EV) (is_init : EV → bool) (σ1 : m.(m_state)) (σ2 : (call_module m i).(m_state)) (σ3 : (@module_empty Empty_set).(m_state)) (σm : (call_intro_mediator is_init).(lm_state)) : Prop :=
  match σ2.(cs_stack) with
  | [] => σ1 = m.(ms_state) ∧ σ2.(cs_waiting) = true ∧ σm = false
  | [σ] => σ1 = σ ∧ if σm then ∃ σ' e κs, m.(m_step) m.(ms_state) e σ' ∧ has_non_ub_trace m σ' κs σ else σ = m.(ms_state) ∧ σ2.(cs_waiting) = false
  | _ => False
  end.
(* TODO: this is currently broken because has_no_behavior was removed from the invariant proof technique. *)
Lemma call_intro {EV} (m : mod_state EV) (i : call_module_info EV) (is_init : EV → bool):
  (∀ e σ, m.(m_step) m.(ms_state) e σ → ∃ κ, e = Some κ ∧ is_init κ) → (* TODO: Is this necessary? *)
  ¬ m_is_ub m (ms_state m) →
  (∀ σ1 e σ2, m.(m_step) σ1 (Some e) σ2 → i.(cmi_final) e → has_no_behavior m σ2) →
  (∀ σ'' σ' σ e κs e', m.(m_step) m.(ms_state) e σ' → σ' ~{ m, κs }~>ₙ σ → m.(m_step) σ (Some e') σ'' → ¬ is_init e') →
  refines_equiv m (MS (link (call_module m i) ∅ (call_intro_mediator is_init)) (call_module_init m, tt, false)).
Proof.
Admitted.
(*
  move => HSome Hnotub Hfinal Hnoinit.
  apply (inv_implies_refines_equiv _ (MS (link _ _ _) _) (curry ∘ curry ∘ (call_intro_inv _ _ _))).
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
*)
(*** rec linking *)
Definition rec_cmi : call_module_info rec_event := {|
  cmi_final e := if e is DoneEvt _ then true else false;
  cmi_waiting e := if e is CallEvt _ _ then true else false;
|}.

Definition rec_link_mediator (fns1 fns2 : gset string) : link_mediator rec_event rec_event rec_event.
Admitted.

Lemma rec_link_ok fns1 fns2:
  fns1 ##ₘ fns2 →
  refines_equiv (MS (call_module (MS rec_module (initial_state (rec_link fns1 fns2))) rec_cmi) (call_module_init rec_module))
          (MS (link (call_module (MS rec_module (initial_state fns1)) rec_cmi) (call_module (MS rec_module (initial_state fns2)) rec_cmi)
                (rec_link_mediator (dom _ fns1) (dom _ fns2))) (call_module_init rec_module, call_module_init rec_module, (rec_link_mediator (dom _ fns1) (dom _ fns2)).(lm_initial))).
Proof.
  move => ?.
  apply call_module_refines_link.
Admitted.

Lemma rec_refines_call fns:
  refines_equiv (MS rec_module (initial_state fns)) (MS (link (call_module (MS rec_module (initial_state fns)) rec_cmi) ∅ (call_intro_mediator (λ e, if e is RecvCallEvt _ _ then true else false))) (call_module_init rec_module, tt, false)).
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
  MS rec_module (initial_state fnsi) ⊑ MS rec_module (initial_state fnss) →
  ctx_refines fnsi fnss.
Proof.
  move => Hdom Href C.
  rewrite /rec_link map_difference_union_r (map_difference_union_r fnss).
  etrans. { apply rec_refines_call. }
  etrans. 2: { apply rec_refines_call. } simpl.
  apply: refines_horizontal. 2: { reflexivity. }

  etrans. { apply rec_link_ok. apply: map_disjoint_difference_r'. }
  etrans. 2: { apply rec_link_ok. apply: map_disjoint_difference_r'. }
  rewrite !dom_difference_L !Hdom.
  apply: refines_horizontal.
  - apply: call_module_refines. apply: Href.
  - rewrite (map_difference_eq_dom_L _ _ _ Hdom).
    reflexivity.
Qed.

Lemma refines_equiv_implies_rec_ctx_equiv fnsi fnss :
  dom (gset string) fnsi = dom (gset string) fnss →
  refines_equiv (MS rec_module (initial_state fnsi)) (MS rec_module (initial_state fnss)) →
  ctx_equiv fnsi fnss.
Proof. move => ? [??]. split; by apply refines_implies_rec_ctx_refines. Qed.

Lemma refines_equiv_equiv_rec_ctx_equiv fnsi fnss :
  dom (gset string) fnsi = dom (gset string) fnss →
  refines_equiv (MS rec_module (initial_state fnsi)) (MS rec_module (initial_state fnss)) ↔
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

  Lemma TraceUbFalse {EV} (m : module EV) σ1 κs:
    m_is_ub m σ1 → σ1 ~{ m, κs }~> (λ _, False).
   Proof. move => ?. by apply: TraceUb. Qed.


  Lemma add1_refines_cumbersome add1_name :
    MS rec_module (initial_state {[ add1_name := add1 ]}) ⊑ MS rec_module (initial_state {[ add1_name := add1_cumbersome ]}).
  Proof.
    apply: wp_implies_refines => n.
    constructor => ? ? ? ? ?. inv_step; simplify_map_eq. 2: {
      eexists _. split; [apply: TraceUbFalse|done] => ?. naive_solver.
    }
    destruct (decide (length nas = 1%nat)). 2: {
      eexists _. split.
      - apply: TraceStepSome. { econstructor => //. apply: lookup_insert. }
        apply: TraceUbFalse => /=. case_bool_decide => //.
        move => [[?|?]//|[? [??]]]. invert_all step.
      - done.
    }
    eexists _. split. {
      apply: TraceStepSome; [|by apply: TraceEnd'].
      econstructor => //. by apply: lookup_insert.
    }
    move => /= ? <-. case_bool_decide => //.
    destruct nas as [|n [|]] => //.

    constructor => ?????. inv_step. 2: {
      eexists _. split; [apply: TraceUbFalse|done] => -[[//|//]|] [?[??]]. apply: H0.
      right. eexists _, _. by econstructor.
    }
    eexists. split. { apply: TraceEnd'. }
    move => /= ? <-.

    constructor => ?????. inv_step. 2: {
      eexists _. split; [apply: TraceUbFalse|done] => -[[//|//]|] [?[??]]. apply: H.
      right. eexists _, _. by econstructor.
    }
    eexists. split. { apply: TraceEnd'. }
    move => /= ? <-.

    constructor => ?????. inv_step. 2: {
      eexists _. split; [apply: TraceUbFalse|done] => -[[//|//]|] [?[??]]. apply: H.
      right. eexists _, _. by econstructor.
    }
    eexists. split. { apply: TraceEnd'. }
    move => /= ? <-.

    constructor => ?????. inv_step. 2: {
      eexists _. split; [apply: TraceUbFalse|done] => -[[//|//]|] [?[??]]. apply: H.
      right. eexists _, _. by econstructor.
    }
    simplify_map_eq.
    eexists. split. {
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
      by apply: TraceEnd'.
    }
    move => /= ? <-.

    constructor => ?????. inv_step. contradict H. naive_solver.
  Qed.

  Lemma ret2_refines_call :
    MS rec_module (initial_state $ <[ "add1" := add1]> {["ret2" := ret2 ]}) ⊑ MS rec_module (initial_state $ <[ "add1" := add1]> {["ret2" := ret2_call ]}).
  Proof.
    apply: wp_implies_refines => n.
  Admitted.

  Lemma const_prop_post_refines_pre  :
    MS rec_module (initial_state {[ "cp" := const_prop_post ]}) ⊑ MS rec_module (initial_state {[ "cp" := const_prop_pre ]}).
  Proof. Admitted.
  (*
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
*)
End test.

(*** Safety property stuff *)
(*
Definition example_code : rec_fns.
Admitted.
Definition example_code_spec : module rec_event.
Admitted.

(* TODO: should safety violation simply be UB? *)
Definition safety_property EV := module (EV + ()).

Definition example_safety_prop : safety_property rec_event := {|
  m_state := bool;
  (* m_initial := false; *)
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
  m1 ⊑ m2 → omap_module f m1 ⊑ (omap_module f m2).
Proof. move => ?. apply: refines_horizontal => //. Qed.

Definition fmap_module {EV1 EV2} (f : EV1 → EV2) (m : module EV1) : module EV2 :=
  link m ∅ (stateless_mediator (λ e1 (e2 : option unit) e3, ∃ κ, e1 = Some κ ∧ e3 = Some (f κ))).

Lemma fmap_module_refines {EV1 EV2} (f : EV1 → EV2) m1 m2:
  m1 ⊑ m2 → fmap_module f m1 ⊑ (fmap_module f m2).
Proof. move => ?. apply: refines_horizontal => //. Qed.

Definition is_safe {EV} (m : module (EV + ())) : Prop :=
  omap_module (λ e, if e is inr _ then Some () else None) m ⊑ ∅.

Lemma is_safe_refines {EV} (m1 m2 : module (EV + ())):
  m1 ⊑ m2 → is_safe m2 → is_safe m1.
Proof. unfold is_safe. move => ??. etrans; [|done]. by apply: omap_module_refines. Qed.

Lemma example_code_refines_spec :
  rec_module example_code ⊑ example_code_spec.
Admitted.

Lemma spec_is_safe:
  is_safe (link_safety_prop example_code_spec example_safety_prop).
Admitted.

Lemma code_is_safe :
  is_safe (link_safety_prop (rec_module example_code) example_safety_prop).
Proof.
  apply: is_safe_refines.
  - apply: link_safety_prop_refines; [ | reflexivity ].
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
  fmap_module inl (rec_module (example_safety_prop_impl f fu)) ⊑ example_safety_prop.
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

Definition rename_fn_in_def (f1 f2 : fn_name) (fd : fndef) := {|
  fd_args := fd.(fd_args);
  fd_body := rename_fn f1 f2 fd.(fd_body);
|}.

Lemma implement_example_safety_prop (fns : rec_fns) f fu:
  "assert_failed" ∉ dom (gset _) fns →
  "dont_call_with_2" ∉ dom (gset _) fns →
  f ∉ dom (gset _) fns →
  fu ∉ dom (gset _) fns →
  fmap_module (λ e, if e is CallEvt "assert_failed" [] then inr () else inl e)
       (rec_module (((rename_fn_in_def "dont_call_with_2" f) <$> fns) ∪ example_safety_prop_impl f fu))
       ⊑
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
*)
End rec.
