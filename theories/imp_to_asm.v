Require Export iris.algebra.lib.gmap_view.
Require Export refframe.module.
Require Import refframe.trefines.
Require Import refframe.filter.
Require Import refframe.product.
Require Import refframe.seq_product.
Require Import refframe.link.
Require Import refframe.prepost.
Require Import refframe.proof_techniques.
Require Import refframe.imp.
Require Import refframe.asm.

Local Open Scope Z_scope.

(*


P1 :=
 X;;
 Y

P2 :=
 A;;
 B


P1 :=
 X;;
 yield();;
 Y

P2 :=
 A;;
 yield();;
 B


Idea:
- have an concurrent operational semantics without explicit and show
  that it can be implemented by an premetive scheduler and a timer
  interrupt
 *)

(* Interesting thing to consider: What if the assembly does two
allocations? Do they necessarily correspond to two different
allocations in IMP?

-> No, build an example which exercises this part. *)

(*
Idea for new ghost state:

asm_mem: gmap Z Z
-> like points-to predicate
- asm_mem_auth (mem : gmap Z Z)
- asm_mem_ptsto (a : Z) (v : Z)

imp_heap: gmap prov (gmap Z val))
- imp_heap_auth ih
- imp_heap_block (b : gmap Z val)
  - exclusive
- imp_heap_dead (p : prov)
  - persistent
  - defined as p -> ∅

physical_blocks: gmap prov Z
-> persistent, only allows extension

Invariant :
λ h mem sp pb, ∃ ih amem,
  asm_mem_auth amem ∗
  imp_heap_auth ih ∗
  physical_blocks pb ∗
  asm_imp_agree pb ∧
  asm_mem_agree mem amem ∧
  imp_heap_agree h ih ∧
  (∀ z, z < sp → amem !! z = None) ∧

imp_heap_agree h ih :=
  dom _ ih ⊆ h_provs h ∧
  ∀ l x, ih !! l.1 = Some b → h !! l = b !! l.2

asm_mem_agree mem amem :=
  ∀ a v, amem !! a = Some v → mem !!! a = v

asm_imp_agree pb :=
  ∀ p a, pb !! p = Some a →
     imp_heap_dead p ∨ ∃ b, imp_heap_block b ∗ [∗ map] o↦v,
       ∃ v', imp_val_to_asm_val pb v = Some v' ∧ asm_mem_ptsto (a + o) v'

-> Idea: if there is an access in the imp program, one can deduce that the heap
   cell cannot be dead and thus there is an asm points to in asm_imp_agree.
   For private blocks, one does not need to put the asm_mem_ptsto into asm_imp_agree
   and thus one can freely modify them. If the source frees a memory block, one
   knows that it is not dead and thus one gets the imp_heap_block and the asm_mem_ptstos
   One probably also needs to know that the block still has the same size as when it
   was allocated, but that could work e.g. by turning h_provs into gmap prov positive
   which tracks the size of blocks.

pb is also used to translate values
*)

(** * imp_to_asm *)
(** ** registers *)
Definition args_registers : list string :=
  ["R0"; "R1"; "R2"; "R3"; "R4"; "R5"; "R6"; "R7" ; "R8"].

Definition tmp_registers : list string :=
  args_registers ++ ["R9"; "R10"; "R11"; "R12"; "R13"; "R14"; "R15"; "R16"; "R17"; "R30"; "PC"].

Definition saved_registers : list string :=
  ["R19"; "R20"; "R21"; "R22"; "R23"; "R24"; "R25"; "R26"; "R27"; "R28"; "R29"; "SP"].

Definition touched_registers : list string :=
  tmp_registers ++ saved_registers.

Definition imp_to_asm_args (ret : Z) (rs : gmap string Z) (avs : list Z) : Prop :=
  rs !! "R30" = Some ret ∧
  Forall2 (λ v r, rs !!! r = v) avs (take (length avs) args_registers) ∧
  map_list_included tmp_registers rs ∧
  map_list_included saved_registers rs.

Definition imp_to_asm_ret (rs rsold : gmap string Z) (av : Z) : Prop :=
  rs !!! "R0" = av ∧
  map_list_included tmp_registers rs ∧
  map_preserved saved_registers rsold rs.

(** ** ghost state  *)
Inductive imp_to_asm_elem :=
| I2AShared (a : Z) | I2AConstant (h : gmap loc val).
Canonical Structure imp_to_asm_elemO := leibnizO imp_to_asm_elem.

Definition imp_to_asmUR : ucmra :=
  prodUR (gmap_viewUR prov imp_to_asm_elemO) (gmap_viewUR Z ZO).

Definition i2a_heap_inj (r : (gmap_viewUR prov imp_to_asm_elemO)) : imp_to_asmUR := (r, ε).
Definition i2a_mem_inj (r : (gmap_viewUR Z ZO)) : imp_to_asmUR := (ε, r).

Definition i2a_heap_auth (h : gmap prov imp_to_asm_elemO) : uPred imp_to_asmUR :=
  uPred_ownM (i2a_heap_inj (gmap_view_auth (DfracOwn 1) h)).
Definition i2a_heap_shared (p : prov) (a : Z) : uPred imp_to_asmUR :=
  uPred_ownM (i2a_heap_inj (gmap_view_frag p DfracDiscarded (I2AShared a))).
Definition i2a_heap_constant (p : prov) (b : gmap loc val) : uPred imp_to_asmUR :=
  uPred_ownM (i2a_heap_inj (gmap_view_frag p (DfracOwn 1) (I2AConstant b))).

Definition i2a_mem_auth (amem : gmap Z Z) : uPred imp_to_asmUR :=
  uPred_ownM (i2a_mem_inj (gmap_view_auth (DfracOwn 1) amem)).
Definition i2a_mem_constant (a : Z) (v : Z) : uPred imp_to_asmUR :=
  uPred_ownM (i2a_mem_inj (gmap_view_frag a (DfracOwn 1) v)).

Lemma i2a_mem_alloc a v amem :
  amem !! a = None →
  i2a_mem_auth amem ==∗ i2a_mem_auth (<[a := v]> amem) ∗ i2a_mem_constant a v.
Proof.
  move => ?.
  rewrite -uPred.ownM_op. apply uPred.bupd_ownM_update.
  rewrite -pair_op_2. apply prod_update; [done|].
  by apply gmap_view_alloc.
Qed.

Lemma i2a_mem_delete a v amem :
  i2a_mem_auth amem ∗ i2a_mem_constant a v ==∗ i2a_mem_auth (delete a amem).
Proof.
  rewrite -uPred.ownM_op. apply uPred.bupd_ownM_update.
  rewrite -pair_op_2. apply prod_update; [done|].
  by apply gmap_view_delete.
Qed.

Lemma i2a_mem_lookup a v amem :
  i2a_mem_auth amem -∗
  i2a_mem_constant a v -∗
  ⌜amem !! a = Some v⌝.
Proof.
  apply bi.wand_intro_r. rewrite -uPred.ownM_op.
  etrans; [apply uPred.ownM_valid|]. iPureIntro. move => [?/gmap_view_both_valid_L?]. naive_solver.
Qed.

(** ** invariants *)
Definition imp_val_to_asm_val (iv : val) (av : Z) : uPred imp_to_asmUR :=
  match iv with
  | ValNum z => ⌜av = z⌝
  | ValBool b => ⌜av = bool_to_Z b⌝
  | ValLoc l => ∃ z, ⌜av = (z + l.2)%Z⌝ ∗ i2a_heap_shared l.1 z
  end.

Definition i2a_mem_agree (mem : gmap Z Z) (amem : gmap Z Z) : Prop :=
  ∀ a v, amem !! a = Some v → mem !!! a = v.

Definition i2a_heap_agree (h : heap_state) (ih : gmap prov imp_to_asm_elem) : Prop :=
  dom _ ih ⊆ h_provs h ∧
  ∀ l b, ih !! l.1 = Some (I2AConstant b) → h_heap h !! l = b !! l.

Definition i2a_mem_sp (sp : Z) (amem : gmap Z Z) : Prop :=
  ∀ a, a < sp → amem !! a = None.

Definition i2a_inv (mem : gmap Z Z) (amem : gmap Z Z)
           (h : heap_state) (ih : gmap prov imp_to_asm_elem) (sp : Z) :=
  i2a_mem_agree mem amem ∧ i2a_heap_agree h ih ∧ i2a_mem_sp sp amem.

Definition i2a_heap_shared_agree (h : gmap loc val) (ih : gmap prov imp_to_asm_elem) : uPred imp_to_asmUR :=
  [∗ map] l↦v∈h,
    if ih !! l.1 is Some (I2AShared a) then
      ∃ av, imp_val_to_asm_val v av ∗ i2a_mem_constant a av
    else
      True.

(* TODO: This really should be a big ∗ not at big ∧ *)
(* Definition i2a_mem_heap_agree (h : heap_state) (ih : gmap prov imp_to_asm_elem) : uPred imp_to_asmUR := *)
(*   ∀ p a, ih !! p = Some (I2AShared a) → *)
(*          ∀ o v, h_heap h !! (p, o) = Some v → ∃ av, imp_val_to_asm_val r v av ∧ i2a_mem_constant a av ≼ r. *)

(* Definition asm_imp_agree (r : imp_to_asmUR) (pb : gmap prov (option Z)) := *)
(*   ∀ p a, pb !! p = Some a → *)
(*      imp_heap_dead p ≼ r ∨  *)
(*        ∃ b, imp_heap_block b ≼ r *)
(*                            [∗ map] o↦v, ∃ v', imp_val_to_asm_val pb v = Some v' ∧ asm_mem_ptsto (a + o) v' *)

(* old *)
(* Definition imp_to_asm_mem_rel (sp : Z) (amem amemold : gmap Z Z) : Prop := *)
  (* ∀ a, sp ≤ a → amem !!! a = amemold !!! a. *)

(* Definition imp_to_asm_phys_blocks_extend (p1 p2 : gmap prov (option Z)) : Prop := *)
  (* p1 ⊆ p2. *)

(* Global Instance imp_to_asm_phys_blocks_extend_preorder : (PreOrder imp_to_asm_phys_blocks_extend). *)
(* Proof. apply _. Qed. *)
(* Global Typeclasses Opaque imp_to_asm_phys_blocks_extend. *)

Record imp_to_asm_stack_item := I2AI {
  i2as_extern : bool;
  i2as_ret : Z;
  i2as_regs : gmap string Z;
}.
Add Printing Constructor imp_to_asm_stack_item.

Record imp_to_asm_state := I2A {
  i2a_calls : list imp_to_asm_stack_item;
  i2a_last_regs : gmap string Z;
}.
Add Printing Constructor imp_to_asm_state.

Definition imp_to_asm_pre (ins : gset Z) (fns : gset string) (f2i : gmap string Z)
 (e : asm_event) (s : imp_to_asm_state) :
 prepost (imp_event * imp_to_asm_state) imp_to_asmUR :=
  match e with
  | (i, EAJump pc rs mem) =>
    (* env chooses if this is a function call or return *)
    pp_quant $ λ b : bool,
    pp_prop (i = Incoming) $
    pp_quant $ λ h,
    pp_quant $ λ amem,
    pp_quant $ λ ih,
    pp_star (i2a_mem_auth amem ∗ i2a_heap_auth ih ∗ i2a_heap_shared_agree (h_heap h) ih) $
    pp_prop (i2a_inv mem amem h ih (rs !!! "SP")) $
    if b then
      (* env chooses return address *)
      pp_quant $ λ ret,
      (* env chooses function name *)
      pp_quant $ λ f,
      (* env chooses arguments *)
      pp_quant $ λ vs,
      pp_quant $ λ avs,
      pp_star ([∗ list] v;a∈vs;avs, imp_val_to_asm_val v a) $
      (* env proves that function name is valid *)
      pp_prop  (f ∈ fns) $
      (* env proves it calls the right address *)
      pp_prop (f2i !! f = Some pc) $
      (* env proves that ret is not in ins *)
      pp_prop (ret ∉ ins) $
      (* env proves that rs corresponds to vs and ret *)
      pp_prop (imp_to_asm_args ret rs avs) $
      (* track the registers and return address (false means ret belongs to env) *)
      pp_end ((i, EICall f vs h), I2A ((I2AI false ret rs)::s.(i2a_calls)) rs)
    else
      (* env chooses return value *)
      pp_quant $ λ v,
      pp_quant $ λ av,
      pp_star (imp_val_to_asm_val v av) $
      (* env chooses old registers *)
      pp_quant $ λ rsold,
      (* env chooses rest of cs *)
      pp_quant $ λ cs',
      (* get registers from stack (true means pc belongs to the program) *)
      pp_prop (s.(i2a_calls) = (I2AI true pc rsold)::cs') $
      (* env proves that rs is updated correctly *)
      pp_prop (imp_to_asm_ret rs rsold av) $
      pp_end ((i, EIReturn v h), I2A cs' rs)
  | _ => pp_prop False $ pp_quant $ λ e, pp_end e
  end.

Definition imp_to_asm_post (ins : gset Z) (fns : gset string) (f2i : gmap string Z) (e : imp_event) (s : imp_to_asm_state) : prepost (asm_event * imp_to_asm_state) imp_to_asmUR :=
  pp_prop (e.1 = Outgoing) $
  pp_quant $ λ pc,
  pp_quant $ λ rs,
  pp_quant $ λ mem,
  pp_quant $ λ amem,
  pp_quant $ λ ih,
  pp_star (i2a_mem_auth amem ∗ i2a_heap_auth ih ∗ i2a_heap_shared_agree (h_heap (heap_of_event e.2)) ih) $
  pp_prop (i2a_inv mem amem (heap_of_event e.2) ih (rs !!! "SP")) $
  match e with
  | (i, EICall f vs h) =>
      pp_quant $ λ avs,
      (* program chooses return address *)
      pp_quant $ λ ret,
      (* program chooses new physical blocks *)
      pp_star ([∗ list] v;a∈vs;avs, imp_val_to_asm_val v a) $
      (* program proves that this function is external *)
      pp_prop (f ∉ fns) $
      (* program proves that the address is correct *)
      pp_prop (f2i !! f = Some pc) $
      (* program proves that ret is in ins *)
      pp_prop (ret ∈ ins) $
      (* program proves that rs corresponds to vs and ret  *)
      pp_prop (imp_to_asm_args ret rs avs) $
      (* program proves it only touched a specific set of registers *)
      pp_prop (map_scramble touched_registers s.(i2a_last_regs) rs) $
      (* track the registers and return address (true means ret belongs to program) *)
      pp_end ((Outgoing, EAJump pc rs mem), (I2A ((I2AI true ret rs)::s.(i2a_calls)) s.(i2a_last_regs)))
  | (i, EIReturn v h) =>
      pp_quant $ λ av,
      (* program chooses new physical blocks *)
      pp_star (imp_val_to_asm_val v av) $
      (* program chooses old registers *)
      pp_quant $ λ rsold,
      (* program chooses rest of cs *)
      pp_quant $ λ cs',
      (* get registers from stack (false means pc belongs to the env) *)
      pp_prop (s.(i2a_calls) = (I2AI false pc rsold)::cs') $
      (* prog proves that rs is updated correctly *)
      pp_prop (imp_to_asm_ret rs rsold av) $
      (* program proves it only touched a specific set of registers *)
      pp_prop (map_scramble touched_registers s.(i2a_last_regs) rs) $
      pp_end ((Outgoing, EAJump pc rs mem), (I2A cs' s.(i2a_last_regs)))
  end.

Definition imp_to_asm (ins : gset Z) (fns : gset string) (f2i : gmap string Z)
           (m : module imp_event) : module asm_event :=
  mod_prepost (imp_to_asm_pre ins fns f2i) (imp_to_asm_post ins fns f2i) m.

Definition initial_imp_to_asm_state (m : module imp_event) (σ : m.(m_state)) :=
  (@SMFilter imp_event, σ, (@PPOutside imp_event asm_event, I2A [] ∅, (True : uPred imp_to_asmUR)%I)).

Lemma imp_to_asm_trefines m m' σ σ' ins fns f2i `{!VisNoAll m}:
  trefines (MS m σ) (MS m' σ') →
  trefines (MS (imp_to_asm ins fns f2i m) (initial_imp_to_asm_state m σ))
           (MS (imp_to_asm ins fns f2i m') (initial_imp_to_asm_state m' σ')).
Proof. move => ?. by apply: mod_prepost_trefines. Qed.

Inductive imp_to_asm_combine_stacks (ins1 ins2 : gset Z) :
  seq_product_state → list seq_product_state →
  list imp_to_asm_stack_item → list imp_to_asm_stack_item → list imp_to_asm_stack_item →
 Prop :=
| IAC_nil :
  imp_to_asm_combine_stacks ins1 ins2 SPNone [] [] [] []
| IAC_NoneLeft ret rs ics cs cs1 cs2:
  ret ∉ ins1 →
  ret ∉ ins2 →
  imp_to_asm_combine_stacks ins1 ins2 SPNone ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 SPLeft (SPNone :: ics) ((I2AI false ret rs) :: cs) ((I2AI false ret rs) :: cs1) cs2
| IAC_NoneRight ret rs ics cs cs1 cs2:
  ret ∉ ins1 →
  ret ∉ ins2 →
  imp_to_asm_combine_stacks ins1 ins2 SPNone ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 SPRight (SPNone :: ics) ((I2AI false ret rs) :: cs) cs1 ((I2AI false ret rs) :: cs2)
| IAC_LeftRight ret rs ics cs cs1 cs2:
  ret ∈ ins1 →
  imp_to_asm_combine_stacks ins1 ins2 SPLeft ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 SPRight (SPLeft :: ics) cs ((I2AI true ret rs) :: cs1) ((I2AI false ret rs) :: cs2)
| IAC_LeftNone ret rs ics cs cs1 cs2:
  ret ∈ ins1 →
  imp_to_asm_combine_stacks ins1 ins2 SPLeft ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 SPNone (SPLeft :: ics) ((I2AI true ret rs) :: cs) ((I2AI true ret rs) :: cs1) cs2
| IAC_RightLeft ret rs ics cs cs1 cs2:
  ret ∈ ins2 →
  imp_to_asm_combine_stacks ins1 ins2 SPRight ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 SPLeft (SPRight :: ics) cs ((I2AI false ret rs) :: cs1) ((I2AI true ret rs) :: cs2)
| IAC_RightNone ret rs ics cs cs1 cs2:
  ret ∈ ins2 →
  imp_to_asm_combine_stacks ins1 ins2 SPRight ics cs cs1 cs2 →
  imp_to_asm_combine_stacks ins1 ins2 SPNone (SPRight :: ics) ((I2AI true ret rs) :: cs) cs1 ((I2AI true ret rs) :: cs2)
.

Local Ltac go := repeat match goal with | x : asm_ev |- _ => destruct x end;
                 destruct_all?; simplify_eq/=; destruct_all?; simplify_eq/=.
Local Ltac go_i := tstep_i; intros; go.
Local Ltac go_s := tstep_s; go.

Local Ltac split_solve :=
  match goal with
  | |- imp_to_asm_args _ _ _ => eassumption
  | |- imp_to_asm_ret _ _ _ => eassumption
  | |- i2a_inv _ _ _ _ _ => eassumption
  | |- ?P ⊣⊢ _ => is_evar P; reflexivity
  | |- map_scramble ?r ?a ?b =>
      assert_fails (has_evar r); assert_fails (has_evar a); assert_fails (has_evar b); by etrans
  end.
Local Ltac split_tac ::=
  repeat (original_split_tac; try split_solve).

Lemma imp_to_asm_combine ins1 ins2 fns1 fns2 f2i1 f2i2 m1 m2 σ1 σ2 `{!VisNoAll m1} `{!VisNoAll m2}:
  ins1 ## ins2 →
  fns1 ## fns2 →
  (∀ f, f ∈ fns1 → ∃ i, i ∈ ins1 ∧ f2i1 !! f = Some i) →
  (∀ f, f ∈ fns2 → ∃ i, i ∈ ins2 ∧ f2i2 !! f = Some i) →
  (∀ f i1 i2, f2i1 !! f = Some i1 → f2i2 !! f = Some i2 → i1 = i2) →
  (∀ f i, f2i1 !! f = Some i → i ∈ ins2 → f ∈ fns2) →
  (∀ f i, f2i2 !! f = Some i → i ∈ ins1 → f ∈ fns1) →
  trefines (MS (asm_prod ins1 ins2 (imp_to_asm ins1 fns1 f2i1 m1) (imp_to_asm ins2 fns2 f2i2 m2))
               (MLFNone, None, initial_imp_to_asm_state m1 σ1,
                 initial_imp_to_asm_state m2 σ2))
           (MS (imp_to_asm (ins1 ∪ ins2) (fns1 ∪ fns2) (f2i1 ∪ f2i2) (imp_prod fns1 fns2 m1 m2))
               (initial_imp_to_asm_state (imp_prod _ _ _ _)
                  (MLFNone, [], σ1, σ2) )
).
Proof.
  move => Hdisji Hdisjf Hin1 Hin2 Hagree Ho1 Ho2.
  unshelve apply: mod_prepost_link. { exact (λ ips '(I2A cs1 lr1) '(I2A cs2 lr2) '(I2A cs lr) x1 x2 x s ics,
  imp_to_asm_combine_stacks ins1 ins2 ips ics cs cs1 cs2 ∧ s = None ∧
  ((ips = SPNone ∧ (x ⊣⊢ x1 ∗ x2)) ∨
  ((ips = SPLeft ∧ x1 = (x ∗ x2)%I
      ∧ map_scramble touched_registers lr lr1) ∨
  (ips = SPRight ∧ x2 = (x ∗ x1)%I
      ∧ map_scramble touched_registers lr lr2)))). }
  { move => ?? [] /=*; naive_solver. }
  { split!. econs. by rewrite right_id. }
  all: move => [cs1 lr1] [cs2 lr2] [cs lr] x1 x2 x ? ics.
  - move => e ? e' /= ? ?.
    destruct_all?; simplify_eq.
    destruct e as [pc rs mem| |]; destruct_all?; simplify_eq/=.
    move => b *. apply pp_to_all_forall => ra ya Hra xa Hxa. eexists b. split!.
    move: ra ya Hra xa Hxa. apply: pp_to_all_forall_2. destruct b => /=.
    + move => ret f vs avs Hin Hf2i /not_elem_of_union[??] ? ??.
      repeat case_bool_decide => //.
      move: Hin => /elem_of_union[?|/Hin2[?[??]]].
      2: { exfalso. move: Hf2i => /lookup_union_Some_raw. naive_solver. }
      split!.
      1: move: Hf2i => /lookup_union_Some_raw; naive_solver.
      1: { setoid_subst. iSatMono. iIntros!. iFrame. }
      1: by simpl_map_decide.
      1: by econs.
    + move => *.
      repeat case_bool_decide => //.
      revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; simplify_eq/= => //. 2: { exfalso. set_solver. }
      split!.
      1: { setoid_subst. iSatMono. iIntros!. iFrame. }
  - move => e ? e' /= ? ?.
    destruct_all?; simplify_eq.
    destruct e as [pc rs mem| |]; destruct_all?; simplify_eq/=.
    move => b *. apply pp_to_all_forall => ra ya Hra xa Hxa. eexists b. split!.
    move: ra ya Hra xa Hxa. apply: pp_to_all_forall_2. destruct b => /=.
    + move => ret f vs avs Hin Hf2i /not_elem_of_union[??] ???.
      repeat case_bool_decide => //.
      move: Hin => /elem_of_union[/Hin1[?[??]]|?].
      1: { exfalso. move: Hf2i => /lookup_union_Some_raw. naive_solver. }
      split!.
      1: move: Hf2i => /lookup_union_Some_raw; naive_solver.
      1: { setoid_subst. iSatMono. iIntros!. iFrame. }
      1: by simpl_map_decide.
      1: by econs.
    + move => *. repeat case_bool_decide => //.
      revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; simplify_eq/= => //.
      split!.
      1: { setoid_subst. iSatMono. iIntros!. iFrame. }
  - move => [? [f vs h|v h]] ? /= *.
    all: destruct_all?; simplify_eq/=.
    + repeat case_bool_decide => //. 2: { exfalso. set_solver. } eexists true => /=.
      split!.
      1: naive_solver.
      1: set_solver.
      1: { iSatMono. iIntros!. iFrame. }
      1: by econs.
    + repeat case_bool_decide => //. eexists false => /=.
      revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; simplify_eq/= => //.
      split!.
      1: { iSatMono. iIntros!. iFrame. }
  - move => [? [f vs h|v h]] ? ? ? /= *.
    all: destruct_all?; simplify_eq/=.
    + repeat case_bool_decide => //. 1: { exfalso. set_solver. }
      split!.
      1: set_solver.
      1: apply lookup_union_Some_raw; naive_solver.
      1: set_solver.
      1: { iSatMono. iIntros!. iFrame. }
      1: by econs.
    + repeat case_bool_decide => //.
      revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; simplify_eq/= => //.
      split!.
      1: { iSatMono. iIntros!. iFrame. }
  - move => [? [f vs h|v h]] ? /= *.
    all: destruct_all?; simplify_eq/=.
    + repeat case_bool_decide => //. 2: { exfalso. set_solver. } eexists true.
      split!.
      1: naive_solver.
      1: set_solver.
      1: { iSatMono. iIntros!. iFrame. }
      1: by econs.
    + repeat case_bool_decide => //.
      revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; simplify_eq/= => //. eexists false.
      split!.
      1: { iSatMono. iIntros!. iFrame. }
  - move => [? [f vs h|v h]] ? /= ? *.
    all: destruct_all?; simplify_eq/=.
    + repeat case_bool_decide => //. 1: { exfalso. set_solver. }
      split!.
      1: set_solver.
      1: apply lookup_union_Some_raw; destruct (f2i1 !! f) eqn:?; naive_solver.
      1: set_solver.
      1: { iSatMono. iIntros!. iFrame. }
      1: by econs.
    + repeat case_bool_decide => //.
      revert select (imp_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; simplify_eq/= => //.
      split!.
      1: { iSatMono. iIntros!. iFrame. }
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
  bool → list expr_ectx → imp_to_asm_state → uPred imp_to_asmUR → Prop :=
| IAPSNil r0 :
  imp_to_asm_proof_stack n ins fns f2i false [] (I2A [] ∅) r0
| IAPSStep c cs lr lr' K' rs ret K b r0 r1:
  imp_to_asm_proof_stack n ins fns f2i b K (I2A cs lr) r0 →
  (∀ i rs' mem' h' av v amem' ih' rf,
      rs' !! "PC" = Some ret →
      ins !! ret = Some i →
      satisfiable (i2a_mem_auth amem' ∗ i2a_heap_auth ih' ∗ i2a_heap_shared_agree (h_heap h') ih'
                                ∗ imp_val_to_asm_val v av ∗ rf ∗ r1) →
      i2a_inv mem' amem' h' ih' (rs' !!! "SP") →
      (* i2a_mem_heap_agree rv' h' ih' → *)
      imp_to_asm_ret rs' rs av →
      AsmState (Some i) rs' mem' ins ⪯{asm_module, imp_to_asm (dom _ ins) (dom _ fns) f2i imp_module, n, true}
               (SMProg, Imp (expr_fill (K' ++ K) (Val v)) h' fns, (PPInside, I2A (c :: cs) rs', rf))) →
  imp_to_asm_proof_stack n ins fns f2i true (K' ++ K) (I2A ((I2AI true ret rs) :: c :: cs) lr') r1
.

Lemma imp_to_asm_proof ins fns ins_dom fns_dom f2i :
  ins_dom = dom _ ins →
  fns_dom = dom _ fns →
  (∀ n i rs mem K f fn avs vs h cs pc ret rf rc amem ih,
      rs !! "PC" = Some pc →
      ins !! pc = Some i →
      fns !! f = Some fn →
      f2i !! f = Some pc →
      satisfiable (i2a_mem_auth amem ∗ i2a_heap_auth ih ∗ i2a_heap_shared_agree (h_heap h) ih ∗ ([∗ list] v;a∈vs;avs, imp_val_to_asm_val v a) ∗ rf ∗ rc) →
      i2a_inv mem amem h ih (rs !!! "SP") →
      (* i2a_mem_heap_agree ra h ih → *)
      imp_to_asm_args ret rs avs →
      length vs = length (fd_args fn) →
      (* Call *)
      (∀ K' rs' mem' f' es avs vs pc' i' ret' b h' lr amem' ih' rf' r',
          Forall2 (λ e v, e = Val v) es vs →
          rs' !! "PC" = Some pc' →
          ins !! pc' = None →
          fns !! f' = None →
          f2i !! f' = Some pc' →
          satisfiable (i2a_mem_auth amem' ∗ i2a_heap_auth ih' ∗ i2a_heap_shared_agree (h_heap h') ih' ∗
                      ([∗ list] v;a∈vs;avs, imp_val_to_asm_val v a) ∗ rf' ∗ rc ∗ r') →
          i2a_inv mem' amem' h' ih' (rs' !!! "SP") →
          (* i2a_mem_heap_agree rvs h' ih' → *)
          imp_to_asm_args ret' rs' avs →
          ins !! ret' = Some i' →
          map_scramble touched_registers lr rs' →
          (∀ rs'' mem'' av v h'' amem'' ih'' rf'',
              rs'' !! "PC" = Some ret' →
              satisfiable (i2a_mem_auth amem'' ∗ i2a_heap_auth ih'' ∗ i2a_heap_shared_agree (h_heap h'') ih'' ∗
                           imp_val_to_asm_val v av ∗ rf'' ∗ rc ∗ r') →
              i2a_inv mem'' amem'' h'' ih'' (rs'' !!! "SP") →
              (* i2a_mem_heap_agree rv'' h'' ih'' → *)
              imp_to_asm_ret rs'' rs' av →
              AsmState (Some i') rs'' mem'' ins ⪯{asm_module, imp_to_asm ins_dom fns_dom f2i imp_module, n, false}
               (SMProg, Imp (expr_fill K (expr_fill K' (Val v))) h'' fns, (PPInside, I2A cs rs'', rf''))) →
          AsmState (Some []) rs' mem' ins ⪯{asm_module, imp_to_asm ins_dom fns_dom f2i imp_module, n, b}
               (SMProg, Imp (expr_fill K (expr_fill K' (imp.Call f' es))) h' fns, (PPInside, I2A cs lr, rf'))) →
      (* Return *)
      (∀ rs' mem' av v h' b lr rf' amem' ih',
          rs' !! "PC" = Some ret →
          satisfiable (i2a_mem_auth amem' ∗ i2a_heap_auth ih' ∗ i2a_heap_shared_agree (h_heap h') ih' ∗
                      imp_val_to_asm_val v av ∗ rf' ∗ rc) →
          i2a_inv mem' amem' h' ih' (rs' !!! "SP") →
          (* i2a_mem_heap_agree rv h' ih' → *)
          imp_to_asm_ret rs' rs av  →
          map_scramble touched_registers lr rs' →
          AsmState (Some []) rs' mem' ins ⪯{asm_module, imp_to_asm ins_dom fns_dom f2i imp_module, n, b}
               (SMProg, Imp (expr_fill K (Val v)) h' fns, (PPInside, I2A cs lr, rf'))) →
      AsmState (Some i) rs mem ins ⪯{asm_module, imp_to_asm ins_dom fns_dom f2i imp_module, n, false}
               (SMProg, Imp (expr_fill K (subst_l fn.(fd_args) vs fn.(fd_body))) h fns, (PPInside, I2A cs rs, rf))
) →
  trefines (MS asm_module (initial_asm_state ins))
           (MS (imp_to_asm ins_dom fns_dom f2i imp_module) (initial_imp_to_asm_state imp_module
             (initial_imp_state fns))).
Proof.
  move => -> -> Hf.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { simpl. exact: (
   λ n' '(AsmState i rs mem ins') '(σfs, Imp e h fns', (t, I2A cs lr, r)),
     ∃ K b lr', i = None ∧ ins = ins' ∧ e = expr_fill K (Waiting b) ∧ fns = fns' ∧
              t = PPOutside ∧ σfs = SMFilter ∧ imp_to_asm_proof_stack n' ins fns f2i b K (I2A cs lr') r
). }
  { eexists []. split!. econs. } {
    clear => /= n n' [????] [[?[???]][[?[??]]?]] Hsub ?. destruct_all?; simplify_eq. split!; [done..|].
    instantiate (1:=lr').
    elim: H6 n' Hsub; [by econs|].
    move => *. econs; [ naive_solver..|]. move => *. apply: tsim_mono; [|done]. naive_solver.
  }
  move => {}n _ /= IH [i rs mem ins'] [[?[???]][[?[??]]?]] ?. destruct_all?; simplify_eq/=.
  tstep_i => ??????.
  go_s. split!.
  go_s => -[] ? /=.
  - move => ???????? /elem_of_dom[??] ? /not_elem_of_dom ? ???.
    go_s. split!. case_bool_decide; [|by go_s].
    match goal with | |- context [ReturnExt b ?e] => change (ReturnExt b e) with (expr_fill [ReturnExtCtx b] e) end.
    rewrite -expr_fill_app.
    apply: tsim_mono_b.
    apply: Hf; [try eassumption..| |].
    { iSatMono. iIntros!. iFrame. iAccu. }
    + iSatClear.
      move => K' rs' mem' f' es avs' vs' pc i' ret' ? h' lr amem' ih' rf' r' Hall ????????? Hret. go.
      have ?: es = Val <$> vs'. { clear -Hall. elim: Hall; naive_solver. } subst.
      tstep_i => ??. simplify_map_eq. rewrite orb_true_r.
      tstep_s. right. split!.
      tstep_s. split!. { by apply not_elem_of_dom. } { by apply elem_of_dom. }
      { iSatMono. iIntros!. iFrame. iAccu. }
      apply IH; [done|].
      split!; [done..|].
      econs; [done..|]. move => *. simplify_map_eq.
      rewrite !expr_fill_app /=.
      apply: tsim_mono_b.
      apply: Hret; [done..].
    + iSatClear. move => *. go.
      tstep_i => ??. simplify_map_eq. rewrite orb_true_r.
      tstep_s.
      tstep_s. split!; [try done..|].
      { iSatMono. iIntros!. iFrame. iAccu. }
      apply IH; [done|]. by split!.
  - move => *.
    revert select (imp_to_asm_proof_stack _ _ _ _ _ _ _ _) => HK.
    inversion HK; clear HK; simplify_eq.
    tstep_s. split!.
    apply: H5. all: try eassumption.
    iSatMono. iIntros!. iFrame.
    Unshelve. apply: inhabitant.
Qed.

(*
(** * closing *)
Inductive imp_to_asm_closed_state :=
| IACStart
| IACStart2 (pc : Z) (rs : gmap string Z)
| IACRunning
.
(* TODO: This needs a call-stack *)

Inductive imp_to_asm_closed_step (ins : gset Z) (fns : gset string) (f2i : gmap string Z) :
  imp_to_asm_closed_state → option (imp_closed_event + asm_closed_event) → (imp_to_asm_closed_state → Prop) → Prop :=
| IACStartS pc rs :
  imp_to_asm_closed_step ins fns f2i IACStart (Some (inr (EACStart pc rs))) (λ σ, σ = IACStart2 pc rs)
| IACStart2S pc rs f avs ret :
  f2i !! f = Some pc →
  imp_to_asm_args ret rs avs →
  imp_to_asm_closed_step ins fns f2i (IACStart2 pc rs)
                         (Some (inl (EICStart f avs))) (λ σ, σ = IACRunning)
.

Definition imp_to_asm_closed_filter_module (ins : gset Z) (fns : gset string) (f2i : gmap string Z) :
  module (imp_closed_event + asm_closed_event) :=
  Mod (imp_to_asm_closed_step ins fns f2i).

Global Instance imp_to_asm_closed_filter_module_vis_no_all ins fns f2i :
  VisNoAll (imp_to_asm_closed_filter_module ins fns f2i).
Proof. move => ????. invert_all @m_step; naive_solver. Qed.

Definition imp_to_asm_closed (ins : gset Z) (fns : gset string) (f2i : gmap string Z)
           (m : module imp_closed_event) : module asm_closed_event :=
  mod_seq_map m (imp_to_asm_closed_filter_module ins fns f2i).

(* TODO: Is this a smart idea? Applying this requires that there is no
special asm behavior in the program that cannot be expressed by imp_to_asm. *)
Lemma imp_to_asm_to_closed m σ ins fns f2i:
  trefines (MS (asm_closed (imp_to_asm ins fns f2i m)) (SMFilter, initial_imp_to_asm_state m σ, ACStart))
           (MS (imp_to_asm_closed ins fns f2i (imp_closed m)) (SMFilter, (SMFilter, σ, ICStart), IACStart)).
Proof.
  apply tsim_implies_trefines => /= n.
Admitted.
*)
