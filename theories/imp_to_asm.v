Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.filter.
Require Import refframe.product.
Require Import refframe.seq_product.
Require Import refframe.link.
Require Import refframe.proof_techniques.
Require Import refframe.imp.
Require Import refframe.asm.
Require Import refframe.itree.

Local Open Scope Z_scope.

(** * imp_to_asm *)
Definition imp_val_to_asm_val (pb : gmap prov (option Z)) (v : val) : option Z :=
  match v with
  | ValNum z => Some z
  | ValBool b => Some (bool_to_Z b)
  | ValLoc l => pb !! l.1 ≫= λ o, (λ x, x + l.2) <$> o
  end.

Definition args_registers : list string :=
  ["R0"; "R1"; "R2"; "R3"; "R4"; "R5"; "R6"; "R7" ; "R8"].

Definition tmp_registers : list string :=
  args_registers ++ ["R9"; "R10"; "R11"; "R12"; "R13"; "R14"; "R15"; "R16"; "R17"; "R30"; "PC"].

Definition saved_registers : list string :=
  ["R19"; "R20"; "R21"; "R22"; "R23"; "R24"; "R25"; "R26"; "R27"; "R28"; "R29"; "SP"].

Definition touched_registers : list string :=
  tmp_registers ++ saved_registers.

Definition imp_to_asm_args (pb : gmap prov (option Z)) (ret : Z) (rs : gmap string Z) (vs : list val) : Prop :=
  rs !! "R30" = Some ret ∧
  Forall2 (λ v r, imp_val_to_asm_val pb v = Some (rs !!! r)) vs (take (length vs) args_registers) ∧
  map_list_included tmp_registers rs ∧
  map_list_included saved_registers rs.

Definition imp_to_asm_ret (pb : gmap prov (option Z)) (rs rsold : gmap string Z) (v : val) : Prop :=
  imp_val_to_asm_val pb v = Some (rs !!! "R0") ∧
  map_list_included tmp_registers rs ∧
  map_preserved saved_registers rsold rs.

Definition imp_to_asm_mem_rel (sp : Z) (amem amemold : gmap Z Z) : Prop :=
  ∀ a, sp ≤ a → amem !!! a = amemold !!! a.

Definition imp_to_asm_phys_blocks_extend (p1 p2 : gmap prov (option Z)) : Prop :=
  p1 ⊆ p2.

Global Instance imp_to_asm_phys_blocks_extend_preorder : (PreOrder imp_to_asm_phys_blocks_extend).
Proof. apply _. Qed.
Global Typeclasses Opaque imp_to_asm_phys_blocks_extend.

Record imp_to_asm_stack_item := I2AI {
  i2as_extern : bool;
  i2as_ret : Z;
  i2as_regs : gmap string Z;
  i2as_mem : gmap Z Z;
  i2as_heap : heap_state;
}.
Add Printing Constructor imp_to_asm_stack_item.

Record imp_to_asm_state := I2A {
  i2a_calls : list imp_to_asm_stack_item;
  i2a_phys_blocks : gmap prov (option Z);
  i2a_last_regs : gmap string Z;
}.
Add Printing Constructor imp_to_asm_state.

Definition imp_to_asm_itree_from_env (ins : gset Z) (fns : gset string) (f2i : gmap string Z) : itree (moduleE (imp_event + asm_event) imp_to_asm_state) () :=
  pc ← TExist Z;;;
  rs ← TExist _;;;
  mem ← TExist _;;;
  s ← TGet;;;
  TVis (inr (Incoming, EAJump pc rs mem));;;;
  (* env chooses if this is a function call or return *)
  b ← TAll bool;;;
  if b then
    (* env chooses return address *)
    ret ← TAll _;;;
    (* env chooses function name *)
    f ← TAll _;;;
    (* env chooses arguments *)
    vs ← TAll _;;;
    (* env chooses heap *)
    h ← TAll _;;;
    (* env chooses new physical blocks *)
    pb ← TAll _;;;
    (* env proves that function name is valid *)
    TAssume (f ∈ fns);;;;
    (* env proves it calls the right address *)
    TAssume (f2i !! f = Some pc);;;;
    (* env proves that ret is not in invs *)
    TAssume (ret ∉ ins);;;;
    (* env proves pb is an increment *)
    TAssume (imp_to_asm_phys_blocks_extend s.(i2a_phys_blocks) pb);;;;
    (* env proves that rs corresponds to vs and ret *)
    TAssume (imp_to_asm_args pb ret rs vs);;;;
    (* track the registers and return address (false means ret belongs to env) *)
    TPut (I2A ((I2AI false ret rs mem h)::s.(i2a_calls)) pb rs);;;;
    TVis (inl (Incoming, EICall f vs h))
  else
    (* env chooses return value *)
    v ← TAll _;;;
    (* env chooses heap *)
    h ← TAll _;;;
    (* env chooses new physical blocks *)
    pb ← TAll _;;;
    (* env chooses old registers *)
    rsold ← TAll _;;;
    (* env chooses old mem *)
    memold ← TAll _;;;
    (* env chooses old heap *)
    hold ← TAll _;;;
    (* env chooses rest of cs *)
    cs' ← TAll _;;;
    (* get registers from stack (true means pc belongs to the program) *)
    TAssume (s.(i2a_calls) = (I2AI true pc rsold memold hold)::cs');;;;
    (* env proves pb is an increment *)
    TAssume (imp_to_asm_phys_blocks_extend s.(i2a_phys_blocks) pb);;;;
    (* env proves that rs is updated correctly *)
    TAssume (imp_to_asm_ret pb rs rsold v);;;;
    (* env proves memory is updated correctly *)
    TAssume (imp_to_asm_mem_rel (rs !!! "SP") mem memold);;;;
    TPut (I2A cs' pb rs);;;;
    TVis (inl (Incoming, EIReturn v h))
.

Definition imp_to_asm_itree_to_env (ins : gset Z) (fns : gset string) (f2i : gmap string Z) : itree (moduleE (imp_event + asm_event) imp_to_asm_state) () :=
  pc ← TExist Z;;;
  rs ← TExist _;;;
  mem ← TExist _;;;
  s ← TGet;;;
  (* program chooses whether it returns or makes a function call *)
  b ← TExist bool;;;
  if b then
    (* program chooses return address *)
    ret ← TExist Z;;;
    (* program chooses which function it calls *)
    f ← TExist _;;;
    (* program chooses the arguments of the function *)
    vs ← TExist _;;;
    (* program chooses heap *)
    h ← TExist _;;;
    (* program chooses new physical blocks *)
    pb ← TExist _;;;
    (* program proves that this function is external *)
    TAssert (f ∉ fns);;;;
    (* program proves that the address is correct *)
    TAssert (f2i !! f = Some pc);;;;
    (* program proves that ret is in ins *)
    TAssert (ret ∈ ins);;;;
    (* prog proves pb is an increment *)
    TAssert (imp_to_asm_phys_blocks_extend s.(i2a_phys_blocks) pb);;;;
    (* program proves that rs corresponds to vs and ret  *)
    TAssert (imp_to_asm_args pb ret rs vs);;;;
    (* program proves it only touched a specific set of registers *)
    TAssert (map_scramble touched_registers s.(i2a_last_regs) rs);;;;
    (* track the registers and return address (true means ret belongs to program) *)
    TPut (I2A ((I2AI true ret rs mem h)::s.(i2a_calls)) pb s.(i2a_last_regs));;;;
    TVis (inl (Outgoing, EICall f vs h));;;;
    TVis (inr (Outgoing, EAJump pc rs mem))
  else
    (* program chooses return value *)
    v ← TExist _;;;
    (* program chooses heap *)
    h ← TExist _;;;
    (* program chooses new physical blocks *)
    pb ← TExist _;;;
    (* program chooses old registers *)
    rsold ← TExist _;;;
    (* program chooses old mem *)
    memold ← TExist _;;;
    (* program chooses old heap *)
    hold ← TExist _;;;
    (* program chooses rest of cs *)
    cs' ← TExist _;;;
    (* get registers from stack (false means pc belongs to the env) *)
    TAssert (s.(i2a_calls) = (I2AI false pc rsold memold hold)::cs');;;;
    (* prog proves pb is an increment *)
    TAssert (imp_to_asm_phys_blocks_extend s.(i2a_phys_blocks) pb);;;;
    (* prog proves that rs is updated correctly *)
    TAssert (imp_to_asm_ret pb rs rsold v);;;;
    (* prog proves memory is updated correctly *)
    TAssert (imp_to_asm_mem_rel (rs !!! "SP") mem memold);;;;
    (* program proves it only touched a specific set of registers *)
    TAssert (map_scramble touched_registers s.(i2a_last_regs) rs);;;;
    TPut (I2A cs' pb s.(i2a_last_regs));;;;
    TVis (inl (Outgoing, EIReturn v h));;;;
    TVis (inr (Outgoing, EAJump pc rs mem)).

Definition imp_to_asm_itree' (ins : gset Z) (fns : gset string) (f2i : gmap string Z) : itree (moduleE (imp_event + asm_event) imp_to_asm_state) () :=
  (ITree.forever (imp_to_asm_itree_from_env ins fns f2i;;;; imp_to_asm_itree_to_env ins fns f2i)).
Definition imp_to_asm_itree :=
(* This is sadly necessary as assumption goes crazy in some cases without it. *)
  locked imp_to_asm_itree'.

Definition imp_to_asm (m : module imp_event) : module asm_event :=
  mod_seq_map m (mod_itree (imp_event + asm_event) imp_to_asm_state).

Definition initial_imp_to_asm_state (m : module imp_event) (σ : m.(m_state)) (ins : gset Z) (fns : gset string) (f2i : gmap string Z) : (imp_to_asm m).(m_state) :=
  (SMFilter, σ, (imp_to_asm_itree ins fns f2i, I2A [] ∅ ∅)).

Lemma imp_to_asm_trefines m m' σ σ' ins fns f2i `{!VisNoAll m}:
  trefines (MS m σ) (MS m' σ') →
  trefines (MS (imp_to_asm m) (initial_imp_to_asm_state m σ ins fns f2i))
           (MS (imp_to_asm m') (initial_imp_to_asm_state m' σ' ins fns f2i)).
Proof. move => ?. by apply: mod_seq_map_trefines. Qed.

Inductive imp_to_asm_combine_stacks (ins1 ins2 : gset Z) :
  mod_link_state imp_ev → list seq_product_state →
  list imp_to_asm_stack_item → list imp_to_asm_stack_item → list imp_to_asm_stack_item →
 Prop :=
| IAC_nil :
  imp_to_asm_combine_stacks ins1 ins2 MLFNone [] [] [] []
| IAC_NoneLeft ret rs ics cs cs1 cs2 mem h:
  ret ∉ ins1 →
  ret ∉ ins2 →
  imp_to_asm_combine_stacks ins1 ins2 MLFNone ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 MLFLeft (SPNone :: ics) ((I2AI false ret rs mem h) :: cs) ((I2AI false ret rs mem h) :: cs1) cs2
| IAC_NoneRight ret rs ics cs cs1 cs2 mem h:
  ret ∉ ins1 →
  ret ∉ ins2 →
  imp_to_asm_combine_stacks ins1 ins2 MLFNone ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 MLFRight (SPNone :: ics) ((I2AI false ret rs mem h) :: cs) cs1 ((I2AI false ret rs mem h) :: cs2)
| IAC_LeftRight ret rs ics cs cs1 cs2 mem h:
  ret ∈ ins1 →
  imp_to_asm_combine_stacks ins1 ins2 MLFLeft ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 MLFRight (SPLeft :: ics) cs ((I2AI true ret rs mem h) :: cs1) ((I2AI false ret rs mem h) :: cs2)
| IAC_LeftNone ret rs ics cs cs1 cs2 mem h:
  ret ∈ ins1 →
  imp_to_asm_combine_stacks ins1 ins2 MLFLeft ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 MLFNone (SPLeft :: ics) ((I2AI true ret rs mem h) :: cs) ((I2AI true ret rs mem h) :: cs1) cs2
| IAC_RightLeft ret rs ics cs cs1 cs2 mem h:
  ret ∈ ins2 →
  imp_to_asm_combine_stacks ins1 ins2 MLFRight ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 MLFLeft (SPRight :: ics) cs ((I2AI false ret rs mem h) :: cs1) ((I2AI true ret rs mem h) :: cs2)
| IAC_RightNone ret rs ics cs cs1 cs2 mem h:
  ret ∈ ins2 →
  imp_to_asm_combine_stacks ins1 ins2 MLFRight ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 MLFNone (SPRight :: ics) ((I2AI true ret rs mem h) :: cs) cs1 ((I2AI true ret rs mem h) :: cs2)
.

Definition imp_to_asm_combine_inv (m1 m2 : module imp_event)
           (ins1 ins2 : gset Z) (fns1 fns2 : gset string) (f2i1 f2i2 : gmap string Z)
  (σ1 : (asm_prod ins1 ins2 (imp_to_asm m1) (imp_to_asm m2)).(m_state))
  (σ2 : (imp_to_asm (imp_prod fns1 fns2 m1 m2)).(m_state)) : Prop :=
  let '(σfa, _, (σf1, σi1, (t1, I2A cs1 pb1 lr1)), (σf2, σi2, (t2, I2A cs2 pb2 lr2))) := σ1 in
  let '(σfs, (σpi, ics, σs1, σs2), (t, I2A cs pb lr)) := σ2 in
  let ins := (ins1 ∪ ins2) in
  let fns := (fns1 ∪ fns2) in
  let f2i := (f2i1 ∪ f2i2) in
  ∃ ips,
  σi1 = σs1 ∧
  σi2 = σs2 ∧
  imp_to_asm_combine_stacks ins1 ins2 ips ics cs cs1 cs2 ∧
  (( σfa = MLFNone ∧ σfs = SMFilter
     ∧ t ≈ (imp_to_asm_itree ins fns f2i)
      ∧ t1 ≳ (imp_to_asm_itree ins1 fns1 f2i1)
      ∧ t2 ≳ imp_to_asm_itree ins2 fns2 f2i2
      ∧ σf1 = SMFilter ∧ σf2 = SMFilter
      ∧ σpi = MLFNone
      ∧ ips = MLFNone
      ∧ imp_to_asm_phys_blocks_extend pb1 pb
      ∧ imp_to_asm_phys_blocks_extend pb2 pb
    ) ∨
  (( (∃ e, σpi = MLFRecvL e ∧ σf1 = SMProgRecv (Incoming, e))
      ∨ σpi = MLFLeft ∧ σf1 = SMProg)
      ∧ σfa = MLFLeft ∧ σfs = SMProg
      ∧ t ≈ (imp_to_asm_itree_to_env ins fns f2i;;;; (imp_to_asm_itree ins fns f2i))
      ∧ t1 ≳ (imp_to_asm_itree_to_env ins1 fns1 f2i1;;;; (imp_to_asm_itree ins1 fns1 f2i1))
      ∧ t2 ≳ imp_to_asm_itree ins2 fns2 f2i2
      ∧ σf2 = SMFilter
      ∧ ips = MLFLeft
      ∧ map_scramble touched_registers lr lr1
      ∧ imp_to_asm_phys_blocks_extend pb pb1
      ∧ imp_to_asm_phys_blocks_extend pb2 pb1) ∨
  (((∃ e, σpi = MLFRecvR e ∧ σf2 = SMProgRecv (Incoming, e))
      ∨ σpi = MLFRight ∧ σf2 = SMProg)
      ∧ σfa = MLFRight ∧ σfs = SMProg
      ∧ t ≈ (imp_to_asm_itree_to_env ins fns f2i;;;; (imp_to_asm_itree ins fns f2i))
      ∧ t1 ≳ (imp_to_asm_itree ins1 fns1 f2i1)
      ∧ t2 ≳ (imp_to_asm_itree_to_env ins2 fns2 f2i2;;;; (imp_to_asm_itree ins2 fns2 f2i2))
      ∧ σf1 = SMFilter
      ∧ ips = MLFRight
      ∧ map_scramble touched_registers lr lr2
      ∧ imp_to_asm_phys_blocks_extend pb pb2
      ∧ imp_to_asm_phys_blocks_extend pb1 pb2)).

Lemma itree_tstep_imp_to_asm_itree ins fns f2i b:
  ITreeTStep false b (imp_to_asm_itree ins fns f2i) (imp_to_asm_itree_from_env ins fns f2i;;;; imp_to_asm_itree_to_env ins fns f2i;;;; imp_to_asm_itree ins fns f2i).
Proof. rewrite /imp_to_asm_itree. unlock. constructor. rewrite -bind_bind. eapply itree_tstep_forever. Qed.
Global Hint Resolve itree_tstep_imp_to_asm_itree : tstep.

Local Ltac go := clear_itree; repeat match goal with | x : asm_ev |- _ => destruct x end;
                 destruct_all?; simplify_eq/=; destruct_all?; simplify_eq/=.
Local Ltac go_i := tstep_i; intros; go.
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
               (MLFNone, tt, initial_imp_to_asm_state m1 σ1 ins1 fns1 f2i1,
                 initial_imp_to_asm_state m2 σ2 ins2 fns2 f2i2))
           (MS (imp_to_asm (imp_prod fns1 fns2 m1 m2))
               (initial_imp_to_asm_state (imp_prod _ _ _ _)
                  (MLFNone, [], σ1, σ2) (ins1 ∪ ins2) (fns1 ∪ fns2) (f2i1 ∪ f2i2))
).
Proof.
  move => Hdisji Hdisjf Hin1 Hin2 Hagree Ho1 Ho2.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { exact (λ _, imp_to_asm_combine_inv _ _ _ _ _ _ f2i1 f2i2). }
  { split!. econs. } { done. }
  move => /= {σ1 σ2} {}n _ Hloop [[[σfa []] [[σf1 σi1] [t1 [cs1 pb1 lr1]]] [[σf2 σi2] [t2 [cs2 pb2 lr2]]]]].
  move => [[σfs [[[σpi ics] σs1] σs2]] [t [cs pb lr]]] /= ?.
  destruct_all?; simplify_eq.
  - go_s. go_i.
    go_s. eexists _; go. go_s. eexists _; go. go_s. eexists _; go.
    go_s. go_s. split; [done|]; go.
    go_s => b; go.
    destruct b.
    + go_s => ?; go.
      go_s => f; go.
      go_s => ?; go.
      go_s => ?; go.
      go_s => ?; go.
      go_s => Hin; go.
      go_s => Hf2i; go.
      go_s => /not_elem_of_union[??]; go.
      go_s => ?; go.
      go_s => ?; go.
      go_s. go_s. go_s.
      eexists (EICall _ _ _). split!; [..|done|]. { repeat case_bool_decide => //; set_solver. }
      have [[?[??]]|[?[??]]]: (pc0 ∈ ins1 ∧ f ∈ fns1 ∧ f2i1 !! f = Some pc0 ∨
                         pc0 ∈ ins2 ∧ f ∈ fns2 ∧ f2i2 !! f = Some pc0). {
        move: Hin => /elem_of_union [Hf|Hf]; [left|right];
          move: (Hf); [move=>/Hin1[?[??]]|move=>/Hin2[?[??]]].
        all: move: Hf2i => /lookup_union_Some_raw[?|[??]]; simplify_eq => //; naive_solver.
      }
      all: simpl_map_decide.
      * go_i. go_i.
        go_i. go_i.
        go_i. go_i.
        go_i. eexists true; go.
        go_i. eexists _; go.
        go_i. eexists _; go.
        go_i. eexists _; go.
        go_i. eexists _; go.
        go_i. eexists _; go.
        go_i. split; [done|]; go.
        go_i. split; [done|]; go.
        go_i. split; [done|]; go.
        go_i. split; [by etrans|]; go.
        go_i. split; [done|]; go.
        go_i. go_i.
        apply Hloop. split!; [by econs|done|done|by etrans].
      * go_i. go_i.
        go_i. go_i.
        go_i. go_i.
        go_i. eexists true; go.
        go_i. eexists _; go.
        go_i. eexists _; go.
        go_i. eexists _; go.
        go_i. eexists _; go.
        go_i. eexists _; go.
        go_i. split; [done|]; go.
        go_i. split; [done|]; go.
        go_i. split; [done|]; go.
        go_i. split; [by etrans|]; go.
        go_i. split; [done|]; go.
        go_i. go_i.
        apply Hloop. split!; [by econs|done|done|by etrans].
    + go_s => ?; go.
      go_s => ?; go.
      go_s => ?; go.
      go_s => ?; go.
      go_s => ?; go.
      go_s => ?; go.
      go_s => ?; go.
      go_s => ?; go.
      go_s => ?; go.
      go_s => ?; go.
      go_s => ?; go.
      go_s.
      go_s.
      go_s.
      revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; simplify_eq/= => //.
      * eexists (EIReturn _ _). split!; [done..|]. simpl_map_decide.
        go_i. go_i. go_i. go_i. go_i. go_i.
        go_i. eexists false; go. go_i. eexists _; go.
        go_i. eexists _; go. go_i. eexists _; go.
        go_i. eexists _; go. go_i. eexists _; go.
        go_i. eexists _; go. go_i. eexists _; go.
        go_i. split; [done|]. go.
        go_i. split; [by etrans|]. go.
        go_i. split; [done|]. go.
        go_i. split; [done|]. go.
        go_i. go_i. apply Hloop. split!; [done..|]. by etrans.
      * eexists (EIReturn _ _). split!; [done..|]. simpl_map_decide.
        go_i. go_i. go_i. go_i. go_i. go_i.
        go_i. eexists false; go. go_i. eexists _; go.
        go_i. eexists _; go. go_i. eexists _; go.
        go_i. eexists _; go. go_i. eexists _; go.
        go_i. eexists _; go. go_i. eexists _; go.
        go_i. split; [done|]. go.
        go_i. split; [by etrans|]. go.
        go_i. split; [done|]. go.
        go_i. split; [done|]. go.
        go_i. go_i. apply Hloop. split!; [done..|]. by etrans.
  - tstep_both.
    apply steps_impl_step_end => κ Pσ2 ?. case_match; intros; go.
    + tstep_s. eexists (Some (Incoming, _)). split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop. by split!.
    + tstep_s. eexists None.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop. by split!.
  - tstep_both.
    apply steps_impl_step_end => κ Pσ2 ? *. go. destruct κ as [e|]; go.
    + tend. have [σ' Hσ'] := vis_no_all _ _ _ ltac:(done). eexists σ'. split; [naive_solver|].
      go_i. go_i. go_i. go_i. go_i. destruct x2.
      * go_i. go_i. go_i. go_i. go_i. go_i.
        go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i.
        repeat case_bool_decide => //.
        -- go_i. go_i. go_i. go_i. go_i. go_i.
           go_i. eexists true; go. go_i. eexists _; go.
           go_i. eexists _; go. go_i. eexists _; go.
           go_i. eexists _; go. go_i. eexists _; go.
           go_i. split; [naive_solver|]. go.
           go_i. split; [naive_solver|]. go.
           go_i. split; [by apply: Hdisji|]. go.
           go_i. split; [by etrans|]. go.
           go_i. split; [done|]. go.
           go_i. go_i.
           go_s. eexists (Some (Outgoing, (EICall x3 _ _))), SPRight.
           split!. { repeat case_bool_decide => //; naive_solver. }
           apply: steps_spec_step_end; [done|] => ??.
           apply: Hloop. split!; [ naive_solver| by econs| done| done|by etrans|by etrans].
        -- have ?: x3 ∉ fns2. { revert select (_ ∉ ins2) => Hin. contradict Hin. naive_solver. }
           go_s. eexists (Some (Outgoing, (EICall x3 _ _))), SPNone. split!; simpl_map_decide => //.
           apply: steps_spec_step_end; [done|] => ??.
           go_s. eexists _; go. go_s. eexists _; go. go_s. eexists _; go.
           go_s. go_s. eexists true; go. go_s. eexists _; go.
           go_s. eexists _; go. go_s. eexists _; go.
           go_s. eexists _; go. go_s. eexists _; go.
           go_s. split. { apply not_elem_of_union. naive_solver. } go.
           go_s. split. { apply lookup_union_Some_raw. naive_solver. } go.
           go_s. split; [apply elem_of_union; by left|]. go.
           go_s. split; [by etrans|]. go.
           go_s. split; [done|]. go.
           go_s. split; [by etrans|]. go.
           go_s. go_s. split; [done|]; go.
           go_s. split; [done|]. go.
           apply: Hloop. split!; [naive_solver|by econs|by etrans].
      * go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i.
        repeat case_bool_decide => //.
        -- go_i. go_i. go_i. go_i. go_i. go_i.
           revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
           inversion Hstack; simplify_eq/= => //.
           go_i. eexists false; go. go_i. eexists _; go. go_i. eexists _; go.
           go_i. eexists _; go. go_i. eexists _; go.
           go_i. eexists _; go.
           go_i. eexists _; go.
           go_i. eexists _; go.
           go_i. split; [done|]; go.
           go_i. split; [by etrans|]; go.
           go_i. split; [done|]; go.
           go_i. split; [done|]; go.
           go_i. go_i.
           go_s. eexists (Some (Outgoing, (EIReturn _ _))). split!; [done..|].
           apply: steps_spec_step_end; [done|] => ??.
           apply: Hloop. split!; [naive_solver|done|done|done|by etrans|by etrans].
        -- revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
           inversion Hstack; simplify_eq/= => //.
           go_s. eexists (Some (Outgoing, EIReturn _ _)). split!; [done..|].
           apply: steps_spec_step_end; [done|] => ??.
           go_s. eexists _; go. go_s. eexists _; go. go_s. eexists _; go.
           go_s. go_s. eexists false; go. go_s. eexists _; go.
           go_s. eexists _; go. go_s. eexists _; go. go_s. eexists _; go.
           go_s. eexists _; go. go_s. eexists _; go. go_s. eexists _; go.
           go_s. split; [done|]. go. go_s. split; [by etrans|]. go.
           go_s. split; [done|]. go. go_s. split; [done|]. go.
           go_s. split; [by etrans|]. go.
           go_s. go_s. split; [done|]. go. go_s. split; [done|]. go.
           apply: Hloop. split!; [naive_solver|done|by etrans].
    + tstep_s. eexists None. split!.
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. by split!.
  - tstep_both.
    apply steps_impl_step_end => κ Pσ2 ?. case_match; intros; go.
    + tstep_s. eexists (Some (Incoming, _)). split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop. by split!.
    + tstep_s. eexists None.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop. by split!.
  - tstep_both.
    apply steps_impl_step_end => κ Pσ2 ? *. go. destruct κ as [e|]; go.
    + tend. have [σ' Hσ'] := vis_no_all _ _ _ ltac:(done). eexists σ'. split; [naive_solver|].
      go_i. go_i. go_i. go_i. go_i. destruct x2.
      * go_i. go_i. go_i. go_i. go_i. go_i.
        go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i.
        repeat case_bool_decide => //.
        -- go_i. go_i. go_i. go_i. go_i. go_i.
           go_i. eexists true; go. go_i. eexists _; go.
           go_i. eexists _; go. go_i. eexists _; go. go_i. eexists _; go.
           go_i. eexists _; go.
           go_i. split; [ naive_solver|]. go. go_i. split; [naive_solver|]. go.
           go_i. split. { move => ?. by apply: Hdisji. } go. go_i. split; [by etrans|]. go.
           go_i. split; [done|]. go.
           go_i. go_i.
           go_s. eexists (Some (Outgoing, (EICall x3 _ _))), SPLeft.
           split!. { repeat case_bool_decide => //; naive_solver. }
           apply: steps_spec_step_end; [done|] => ??.
           apply: Hloop. split!; [ naive_solver| by econs| done| done|by etrans|by etrans].
        -- have ?: x3 ∉ fns1. { revert select (_ ∉ ins1) => Hin. contradict Hin. naive_solver. }
           go_s. eexists (Some (Outgoing, (EICall x3 _ _))), SPNone. split!; simpl_map_decide => //.
           apply: steps_spec_step_end; [done|] => ??.
           go_s. eexists _; go. go_s. eexists _; go. go_s. eexists _; go. go_s.
           go_s. eexists true; go. go_s. eexists _; go. go_s. eexists _; go.
           go_s. eexists _; go. go_s. eexists _; go. go_s. eexists _; go.
           go_s. split. { apply not_elem_of_union. naive_solver. } go.
           go_s. split. { apply lookup_union_Some_raw. destruct (f2i1 !! x3) eqn:?; naive_solver. } go.
           go_s. split; [apply elem_of_union; by right|]. go.
           go_s. split; [by etrans|]. go. go_s. split; [done|]; go.
           go_s. split; [by etrans|]. go. go_s. go_s. split; [done|]. go. go_s. split; [done|]. go.
           apply: Hloop. split!; [naive_solver|by econs|by etrans].
      * go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i. go_i.
        repeat case_bool_decide => //.
        -- go_i. go_i. go_i. go_i. go_i. go_i.
           revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
           inversion Hstack; simplify_eq/= => //.
           go_i. eexists false; go. go_i. eexists _; go. go_i. eexists _; go.
           go_i. eexists _; go. go_i. eexists _; go. go_i. eexists _; go.
           go_i. eexists _; go. go_i. eexists _; go.
           go_i. split;[done|]; go. go_i. split;[by etrans|]; go.
           go_i. split;[done|]; go. go_i. split;[done|]; go.
           go_i. go_i.
           go_s. eexists (Some (Outgoing, (EIReturn _ _))). split!; [done..|].
           apply: steps_spec_step_end; [done|] => ??.
           apply: Hloop. split!; [naive_solver|done|done|done|by etrans|by etrans].
        -- revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
           inversion Hstack; simplify_eq/= => //.
           go_s. eexists (Some (Outgoing, EIReturn _ _)). split!; [done..|].
           apply: steps_spec_step_end; [done|] => ??.
           go_s. eexists _; go. go_s. eexists _; go. go_s. eexists _; go.
           go_s. go_s. eexists false; go. go_s. eexists _; go.
           go_s. eexists _; go. go_s. eexists _; go. go_s. eexists _; go.
           go_s. eexists _; go. go_s. eexists _; go. go_s. eexists _; go.
           go_s. split; [done|]. go. go_s. split; [by etrans|]. go.
           go_s. split; [done|]. go. go_s. split; [done|]. go.
           go_s. split; [by etrans|]. go.
           go_s. go_s. split; [done|]. go.
           go_s. split; [done|]. go.
           apply: Hloop. split!; [naive_solver|done|by etrans].
    + tstep_s. eexists None.
      apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
      apply: Hloop. by split!.
Qed.

(* Lemma tsim_remember_stack {EV} {mi ms : module EV} (Pσ : _ → _ → Prop) σi σs b n : *)
(*   Pσ σi σs → *)
(*   (* (∀ n n' σi σs, tiS?b n' ⊆ n → Pσ n σi σs → Pσ n' σi σs) → *) *)
(*   (∀ n' σi σs, *)
(*       tiS?b n' ⊆ n → *)
(*       Pσ σi σs → *)

(*       σi ⪯{mi, ms, n'} σs. *)
(*  ) → *)
(*   σi ⪯{mi, ms, n, b} σs. *)
(* Proof. *)
(*   move => HP HPmono Hsim κs' n' Hn Ht /=. *)
(*   move: HP => /HPmono HP. move: (HP _ ltac:(done)) => {}HP. *)
(*   elim/ti_lt_ind: n' κs' σi σs Hn HP Ht. *)
(*   move => n' IHn κs' σi σs Hn HP Ht. *)
(*   apply: Hsim; [done| |done| |done]. 2: done. *)
(*   move => ??????? /=. eapply IHn; [done| | |done]. *)
(*   - etrans; [|done]. apply tiS_maybe_mono; [done|]. etrans; [|done]. apply ti_le_S. *)
(*   - apply: HPmono; [|done]. etrans; [|done]. by apply tiS_maybe_mono. *)
(* Qed. *)


Inductive imp_to_asm_proof_stack (n : trace_index) (ins : gmap Z asm_instr) (fns : gmap string fndef) (f2i : gmap string Z) :
  bool → list expr_ectx → imp_to_asm_state → Prop :=
| IAPSNil :
  imp_to_asm_proof_stack n ins fns f2i false [] (I2A [] ∅ ∅)
| IAPSStep c cs pb pb' lr lr' K' rs ret K b amem h:
  imp_to_asm_proof_stack n ins fns f2i b K (I2A cs pb lr) →
  imp_to_asm_phys_blocks_extend pb pb' →
  (∀ i rs' amem' pb'' h' v t,
      rs' !! "PC" = Some ret →
      ins !! ret = Some i →
      imp_to_asm_ret pb'' rs' rs v →
      imp_to_asm_mem_rel (rs' !!! "SP") amem' amem →
      imp_to_asm_phys_blocks_extend pb' pb'' →
      t ≈ (imp_to_asm_itree_to_env (dom (gset Z) ins) (dom (gset string) fns) f2i;;;;
              imp_to_asm_itree (dom (gset Z) ins) (dom (gset string) fns) f2i) →
      AsmState (Some i) rs' amem' ins ⪯{asm_module, imp_to_asm imp_module, n, true}
               (SMProg, Imp (expr_fill (K' ++ K) (Val v)) h' fns, (t, I2A (c :: cs) pb'' rs'))) →
  imp_to_asm_proof_stack n ins fns f2i true (K' ++ K) (I2A ((I2AI true ret rs amem h) :: c :: cs) pb' lr')
.


Lemma imp_to_asm_proof ins fns ins_dom fns_dom f2i :
  ins_dom = dom _ ins →
  fns_dom = dom _ fns →
  (∀ n i rs mem K f fn vs h cs t pc ret pb,
      rs !! "PC" = Some pc →
      ins !! pc = Some i →
      fns !! f = Some fn →
      f2i !! f = Some pc →
      imp_to_asm_args pb ret rs vs →
      length vs = length (fd_args fn) →
      (* Call *)
      (∀ K' rs' mem' f' es vs pc' i' ret' b t' h' pb' lr,
          Forall2 (λ e v, e = Val v) es vs →
          rs' !! "PC" = Some pc' →
          ins !! pc' = None →
          fns !! f' = None →
          f2i !! f' = Some pc' →
          imp_to_asm_args pb' ret' rs' vs →
          ins !! ret' = Some i' →
          t' ≈ t →
          imp_to_asm_phys_blocks_extend pb pb' →
          map_scramble touched_registers lr rs' →
          (∀ rs'' mem'' v h'' t'' pb'',
              rs'' !! "PC" = Some ret' →
              imp_to_asm_ret pb'' rs'' rs' v →
              imp_to_asm_mem_rel (rs'' !!! "SP") mem'' mem' →
              imp_to_asm_phys_blocks_extend pb' pb'' →
              t'' ≈ t' →
              AsmState (Some i') rs'' mem'' ins ⪯{asm_module, imp_to_asm imp_module, n, false}
               (SMProg, Imp (expr_fill K (expr_fill K' (Val v))) h'' fns, (t'', I2A cs pb'' rs''))) →
          AsmState (Some []) rs' mem' ins ⪯{asm_module, imp_to_asm imp_module, n, b}
               (SMProg, Imp (expr_fill K (expr_fill K' (imp.Call f' es))) h' fns, (t', I2A cs pb' lr))) →
      (* Return *)
      (∀ rs' mem' v h' b t' pb' lr,
          rs' !! "PC" = Some ret →
          imp_to_asm_ret pb' rs' rs v  →
          imp_to_asm_mem_rel (rs' !!! "SP") mem' mem →
          imp_to_asm_phys_blocks_extend pb pb' →
          map_scramble touched_registers lr rs' →
          t' ≈ t →
          AsmState (Some []) rs' mem' ins ⪯{asm_module, imp_to_asm imp_module, n, b}
               (SMProg, Imp (expr_fill K (Val v)) h' fns, (t', I2A cs pb' lr))) →
      AsmState (Some i) rs mem ins ⪯{asm_module, imp_to_asm imp_module, n, false}
               (SMProg, Imp (expr_fill K (subst_l fn.(fd_args) vs fn.(fd_body))) h fns, (t, I2A cs pb rs))
) →
  trefines (MS asm_module (initial_asm_state ins))
           (MS (imp_to_asm imp_module) (initial_imp_to_asm_state imp_module
             (initial_imp_state fns) ins_dom fns_dom f2i)).
Proof.
  move => -> -> Hf.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { simpl. exact: (λ n' '(AsmState i rs mem ins') '(σfs, Imp e h fns', (t, I2A cs pb lr)),
     ∃ K b pb' lr', i = None ∧ ins = ins' ∧ e = expr_fill K (Waiting b) ∧ fns = fns' ∧
              t ≈ imp_to_asm_itree (dom _ ins) (dom _ fns) f2i ∧ σfs = SMFilter ∧
              imp_to_asm_phys_blocks_extend pb' pb ∧
              imp_to_asm_proof_stack n' ins fns f2i b K (I2A cs pb' lr')
). }
  { eexists []. split!; [done|done|]. econs. } {
    clear => /= n n' [????] [[?[???]][?[???]]] Hsub ?. destruct_all?; simplify_eq. split!; [done..|].
    instantiate (1:=lr').
    elim: H7 n' Hsub; [by econs|].
    move => *. econs; [ naive_solver..|]. move => *. apply: tsim_mono; [|done]. naive_solver.
  }
  move => {}n _ /= IH [i rs mem ins'] [[?[???]][?[???]]] ?. destruct_all?; simplify_eq/=.
  tstep_i => ??????.
  go_s.
  go_s. eexists _; go.
  go_s. eexists _; go.
  go_s. eexists _; go.
  go_s.
  go_s. split; [done|]; go.
  go_s => -[]; go.
  - go_s => ?; go.
    go_s => ?; go.
    go_s => ?; go.
    go_s => ?; go.
    go_s => ?; go.
    go_s => /elem_of_dom[??]; go.
    go_s => ?; go.
    go_s => /not_elem_of_dom ?; go.
    go_s => ?; go.
    go_s => ?; go.
    go_s. go_s. go_s. split!; [done|done|]. case_bool_decide; [|by go_s].
    match goal with | |- context [ReturnExt b ?e] => change (ReturnExt b e) with (expr_fill [ReturnExtCtx b] e) end.
    rewrite -expr_fill_app.
    apply: tsim_mono_b.
    apply: Hf; [done..| |].
    + move => K' rs' mem' f' es vs pc i' ret' ? ? h' ? lr Hall ????????? Hret. go.
      have ?: es = Val <$> vs. { clear -Hall. elim: Hall; naive_solver. } subst.
      tstep_i => ??. simplify_map_eq. rewrite orb_true_r.
      go_s. right. split!.
      go_s. eexists _; go.
      go_s. eexists _; go.
      go_s. eexists _; go.
      go_s.
      go_s. eexists true; go.
      go_s. eexists _; go.
      go_s. eexists _; go.
      go_s. eexists _; go.
      go_s. eexists _; go.
      go_s. eexists _; go.
      go_s. split; [by apply not_elem_of_dom|]; go.
      go_s. split; [done|]; go.
      go_s. split; [by apply elem_of_dom|]; go.
      go_s. split; [done|]; go.
      go_s. split; [done|]; go.
      go_s. split; [done|]; go.
      go_s.
      go_s. split; [done|]; go.
      go_s. split; [done|]; go.
      apply IH.
      split!; [done..|reflexivity|].
      econs; [done..| |]. by etrans; [done|etrans]. move => *. simplify_map_eq.
      rewrite !expr_fill_app /=.
      apply: tsim_mono_b.
      apply Hret; [done..| |].
      by etrans; [|done].
      by etrans; [|done].
    + move => *. go.
      tstep_i => ??. simplify_map_eq. rewrite orb_true_r.
      go_s.
      go_s. eexists _; go.
      go_s. eexists _; go.
      go_s. eexists _; go.
      go_s.
      go_s. eexists false; go.
      go_s. eexists _; go.
      go_s. eexists _; go.
      go_s. eexists _; go.
      go_s. eexists _; go.
      go_s. eexists _; go.
      go_s. eexists _; go.
      go_s. eexists _; go.
      go_s. split; [done|]; go.
      go_s. split; [done|]; go.
      go_s. split; [done|]; go.
      go_s. split; [done|]; go.
      go_s. split; [done|]; go.
      go_s.
      go_s. split; [done|]; go.
      go_s. split; [done|]; go.
      apply IH. split!; [done| |done]. by etrans; [done|etrans].
  - go_s => ?; go.
    go_s => ?; go.
    go_s => ?; go.
    go_s => ?; go.
    go_s => ?; go.
    go_s => ?; go.
    go_s => ?; go.
    go_s => ?; go.
    go_s => ?; go.
    go_s => ?; go.
    go_s => ?; go.
    go_s.
    revert select (imp_to_asm_proof_stack _ _ _ _ _ _ _) => HK.
    inversion HK; clear HK; simplify_eq.
    go_s.
    go_s.
    split!; [done|].
    apply: H12; [done..| |done]. by etrans.
    Unshelve. apply: inhabitant.
Qed.
