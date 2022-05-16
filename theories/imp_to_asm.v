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

Definition i2a_regs_call (ret : Z) (rs : gmap string Z) : Prop :=
  rs !! "R30" = Some ret ∧
  map_list_included touched_registers rs.

Definition i2a_regs_ret (rs rsold : gmap string Z) (av : Z) : Prop :=
  rs !!! "R0" = av ∧
  map_list_included touched_registers rs ∧
  map_preserved saved_registers rsold rs.

(** ** mapping of provenances *)
Inductive imp_to_asm_elem :=
| I2AShared (a : Z) | I2AConstant (h : gmap loc val).

Definition i2a_ih_shared (ih : gmap prov imp_to_asm_elem) : gmap prov Z :=
  omap (λ k, if k is I2AShared a then Some a else None) ih.

Definition i2a_ih_constant (ih : gmap prov imp_to_asm_elem) : gmap prov (gmap loc val) :=
  omap (λ k, if k is I2AConstant b then Some b else None) ih.

Lemma i2a_ih_shared_Some h p a :
  i2a_ih_shared h !! p = Some a ↔ h !! p = Some (I2AShared a).
Proof.
  rewrite /i2a_ih_shared lookup_omap_Some. split.
  - move => [?[??]]. case_match; naive_solver.
  - move => ?. split!.
Qed.

Lemma i2a_ih_shared_empty:
  i2a_ih_shared ∅ = ∅.
Proof. by rewrite /i2a_ih_shared omap_empty. Qed.

Lemma i2a_ih_shared_insert i h ih:
  i2a_ih_shared (<[i := I2AShared h]> ih) = <[i := h]> (i2a_ih_shared ih).
Proof.
  apply map_eq => ?. apply option_eq => ?. rewrite !i2a_ih_shared_Some.
  rewrite !lookup_insert_Some !i2a_ih_shared_Some. naive_solver.
Qed.

Lemma i2a_ih_shared_insert_const i h ih:
  (∀ x, ih !! i ≠ Some (I2AShared x)) →
  i2a_ih_shared (<[i := I2AConstant h]> ih) = i2a_ih_shared ih.
Proof.
  move => ?.
  apply map_eq => ?. apply option_eq => ?. rewrite !i2a_ih_shared_Some.
  rewrite lookup_insert_Some. naive_solver.
Qed.

Lemma i2a_ih_shared_delete i ih:
  i2a_ih_shared (delete i ih) = delete i (i2a_ih_shared ih).
Proof.
  apply map_eq => ?. apply option_eq => ?.
  by rewrite !i2a_ih_shared_Some !lookup_delete_Some !i2a_ih_shared_Some.
Qed.

Lemma i2a_ih_constant_Some h p a :
  i2a_ih_constant h !! p = Some a ↔ h !! p = Some (I2AConstant a).
Proof.
  rewrite /i2a_ih_constant lookup_omap_Some. split.
  - move => [?[??]]. case_match; naive_solver.
  - move => ?. split!.
Qed.


(** ** ghost state  *)
Canonical Structure imp_to_asm_elemO := leibnizO imp_to_asm_elem.

Definition imp_to_asmUR : ucmra :=
  prodUR (gmap_viewUR prov imp_to_asm_elemO) (gmap_viewUR Z (optionO ZO)).

Definition i2a_heap_inj (r : (gmap_viewUR prov imp_to_asm_elemO)) : imp_to_asmUR := (r, ε).
Definition i2a_mem_inj (r : (gmap_viewUR Z (optionO ZO))) : imp_to_asmUR := (ε, r).

Definition i2a_heap_auth (h : gmap prov imp_to_asm_elemO) : uPred imp_to_asmUR :=
  uPred_ownM (i2a_heap_inj (gmap_view_auth (DfracOwn 1) h)).
Definition i2a_heap_shared (p : prov) (a : Z) : uPred imp_to_asmUR :=
  uPred_ownM (i2a_heap_inj (gmap_view_frag p DfracDiscarded (I2AShared a))).
Definition i2a_heap_constant (p : prov) (b : gmap loc val) : uPred imp_to_asmUR :=
  uPred_ownM (i2a_heap_inj (gmap_view_frag p (DfracOwn 1) (I2AConstant b))).

Definition i2a_mem_auth (amem : gmap Z (option Z)) : uPred imp_to_asmUR :=
  uPred_ownM (i2a_mem_inj (gmap_view_auth (DfracOwn 1) amem)).
Definition i2a_mem_constant (a : Z) (v : option Z) : uPred imp_to_asmUR :=
  uPred_ownM (i2a_mem_inj (gmap_view_frag a (DfracOwn 1) v)).

Definition i2a_mem_map (m : gmap Z (option Z)) : uPred imp_to_asmUR :=
  ([∗ map] a↦v ∈ m, i2a_mem_constant a v).

Lemma i2a_mem_constant_excl a v1 v2 :
  i2a_mem_constant a v1 -∗
  i2a_mem_constant a v2 -∗
  False.
Proof.
  apply bi.wand_intro_r. rewrite -uPred.ownM_op.
  etrans; [apply uPred.ownM_valid|]. iPureIntro. move => [?/=/gmap_view_frag_op_valid[??]].
  naive_solver.
Qed.

Lemma i2a_mem_map_constant_excl m1 a v :
  i2a_mem_map m1 -∗
  i2a_mem_constant a v -∗
  ⌜m1 !! a = None⌝.
Proof.
  iIntros "Hmem Hc".
  destruct (m1 !! a) eqn:? => //.
  iDestruct (big_sepM_lookup with "[$]") as "?"; [done|].
  iDestruct (i2a_mem_constant_excl with "[$] [$]") as %[].
Qed.

Lemma i2a_mem_map_excl m1 m2 :
  i2a_mem_map m1 -∗
  i2a_mem_map m2 -∗
  ⌜m1 ##ₘ m2⌝.
Proof.
  iIntros "Hm1 Hm2". rewrite map_disjoint_alt. iIntros (i).
  destruct (m1 !! i) eqn:?; [|iPureIntro; naive_solver].
  destruct (m2 !! i) eqn:?; [|iPureIntro; naive_solver].
  iDestruct (big_sepM_lookup with "[$]") as "?"; [done|].
  iDestruct (big_sepM_lookup with "[$]") as "?"; [done|].
  iDestruct (i2a_mem_constant_excl with "[$] [$]") as %[].
Qed.

Lemma i2a_heap_alloc' ih p b:
  ih !! p = None →
  i2a_heap_auth ih ==∗ i2a_heap_auth (<[p := I2AConstant b]> ih) ∗ i2a_heap_constant p b.
Proof.
  move => ?.
  rewrite -uPred.ownM_op. apply uPred.bupd_ownM_update.
  rewrite -pair_op_1. apply prod_update; [|done].
  by apply gmap_view_alloc.
Qed.

Lemma i2a_heap_update' p h h' ih :
  i2a_heap_auth ih ∗ i2a_heap_constant p h ==∗ i2a_heap_auth (<[p := I2AConstant h']> ih) ∗ i2a_heap_constant p h'.
Proof.
  rewrite -!uPred.ownM_op. apply uPred.bupd_ownM_update.
  rewrite -!pair_op_1. apply prod_update; [|done].
  by apply gmap_view_update.
Qed.

Lemma i2a_heap_to_shared' p h ih a:
  i2a_heap_auth ih ∗ i2a_heap_constant p h ==∗ i2a_heap_auth (<[p := I2AShared a]> ih) ∗ i2a_heap_shared p a.
Proof.
  rewrite -!uPred.ownM_op. apply uPred.bupd_ownM_update.
  rewrite -!pair_op_1. apply prod_update; [|done].
  etrans; [by apply gmap_view_update|].
  apply cmra_update_op; [done|].
  apply gmap_view_frag_persist.
Qed.

Lemma i2a_heap_free' h p h' :
  i2a_heap_auth h ∗ i2a_heap_constant p h' ==∗ i2a_heap_auth (delete p h).
Proof.
  rewrite -uPred.ownM_op. apply uPred.bupd_ownM_update.
  rewrite -pair_op_1. apply prod_update; [|done].
  by apply gmap_view_delete.
Qed.

Lemma i2a_heap_lookup' h p h' :
  i2a_heap_auth h -∗
  i2a_heap_constant p h' -∗
  ⌜h !! p = Some (I2AConstant h')⌝.
Proof.
  apply bi.wand_intro_r. rewrite -uPred.ownM_op.
  etrans; [apply uPred.ownM_valid|]. iPureIntro. move => [/gmap_view_both_valid_L??]. naive_solver.
Qed.

Lemma i2a_heap_shared_lookup' h p a :
  i2a_heap_auth h -∗
  i2a_heap_shared p a -∗
  ⌜h !! p = Some (I2AShared a)⌝.
Proof.
  apply bi.wand_intro_r. rewrite -uPred.ownM_op.
  etrans; [apply uPred.ownM_valid|]. iPureIntro. move => [/gmap_view_both_valid_L??]. naive_solver.
Qed.

Lemma i2a_heap_shared_ag p a1 a2 :
  i2a_heap_shared p a1 -∗
  i2a_heap_shared p a2 -∗
  ⌜a1 = a2⌝.
Proof.
  apply bi.wand_intro_r. rewrite -uPred.ownM_op.
  etrans; [apply uPred.ownM_valid|]. iPureIntro. move => [/=/gmap_view_frag_op_valid[??]?].
  naive_solver.
Qed.

Lemma i2a_mem_alloc' a v amem :
  amem !! a = None →
  i2a_mem_auth amem ==∗ i2a_mem_auth (<[a := v]> amem) ∗ i2a_mem_constant a v.
Proof.
  move => ?.
  rewrite -uPred.ownM_op. apply uPred.bupd_ownM_update.
  rewrite -pair_op_2. apply prod_update; [done|].
  by apply gmap_view_alloc.
Qed.

Lemma i2a_mem_alloc_big' mem mem' :
  mem' ##ₘ mem →
  i2a_mem_auth mem ==∗ i2a_mem_auth (mem' ∪ mem) ∗ i2a_mem_map mem'.
Proof.
  iIntros (?) "Hmem". rewrite /i2a_mem_map.
  iInduction mem' as [|a v mem' ?] "IH" using map_ind; decompose_map_disjoint.
  { rewrite left_id big_sepM_empty. by iFrame. }
  iMod ("IH" with "[//] [$]") as "[??]". rewrite -insert_union_l.
  iMod (i2a_mem_alloc' a with "[$]") as "[$ ?]". { by apply lookup_union_None. }
  rewrite big_sepM_insert //. by iFrame.
Qed.

Lemma i2a_mem_update' v' a v amem :
  i2a_mem_auth amem ∗ i2a_mem_constant a v ==∗ i2a_mem_auth (<[a := v']> amem) ∗ i2a_mem_constant a v'.
Proof.
  rewrite -!uPred.ownM_op. apply uPred.bupd_ownM_update.
  rewrite -!pair_op_2. apply prod_update; [done|].
  by apply gmap_view_update.
Qed.

Lemma i2a_mem_delete' a v amem :
  i2a_mem_auth amem ∗ i2a_mem_constant a v ==∗ i2a_mem_auth (delete a amem).
Proof.
  rewrite -uPred.ownM_op. apply uPred.bupd_ownM_update.
  rewrite -pair_op_2. apply prod_update; [done|].
  by apply gmap_view_delete.
Qed.

Lemma i2a_mem_lookup' a v amem :
  i2a_mem_auth amem -∗
  i2a_mem_constant a v -∗
  ⌜amem !! a = Some v⌝.
Proof.
  apply bi.wand_intro_r. rewrite -uPred.ownM_op.
  etrans; [apply uPred.ownM_valid|]. iPureIntro. move => [?/gmap_view_both_valid_L?]. naive_solver.
Qed.

Lemma i2a_mem_lookup_big' m mem :
  i2a_mem_auth mem -∗
  i2a_mem_map m -∗
  ⌜m ⊆ mem⌝.
Proof.
  iIntros "Ha Hm". rewrite /i2a_mem_map.
  iInduction m as [|a v m' ?] "IH" using map_ind. { iPureIntro. apply map_empty_subseteq. }
  rewrite big_sepM_insert //. iDestruct "Hm" as "[Hv Hm]".
  iDestruct (i2a_mem_lookup' with "[$] [$]") as %?.
  iDestruct ("IH" with "[$] [$]") as %?. iPureIntro.
  by apply insert_subseteq_l.
Qed.

(** ** invariants *)
Definition i2a_val_rel (iv : val) (av : Z) : uPred imp_to_asmUR :=
  match iv with
  | ValNum z => ⌜av = z⌝
  | ValBool b => ⌜av = bool_to_Z b⌝
  | ValLoc l => ∃ z, ⌜av = (z + l.2)%Z⌝ ∗ i2a_heap_shared l.1 z
  end.

Global Instance i2a_val_rel_pers iv av : Persistent (i2a_val_rel iv av).
Proof. destruct iv; apply _. Qed.

Definition GUARD_PAGE_SIZE : Z := 4096.

(* gp is lower end of guard page *)
Definition i2a_guard_page (gp : Z) : uPred imp_to_asmUR :=
  i2a_mem_map (map_seqZ gp (replicate (locked Z.to_nat GUARD_PAGE_SIZE) None)).

Definition i2a_mem_uninit (a : Z) (len : Z) : uPred imp_to_asmUR :=
  [∗ list] a ∈ seqZ a len, ∃ v, i2a_mem_constant a (Some v).

Definition i2a_mem_inv (sp : Z) (gp : Z) (mem : gmap Z (option Z)) : uPred imp_to_asmUR :=
  ⌜gp + GUARD_PAGE_SIZE ≤ sp⌝ ∗
  i2a_guard_page gp ∗ i2a_mem_uninit (gp + GUARD_PAGE_SIZE) (sp - (gp + GUARD_PAGE_SIZE)) ∗
  i2a_mem_auth mem.

Definition i2a_heap_agree (h : heap_state) (ih : gmap prov imp_to_asm_elem) : Prop :=
  dom _ ih ⊆ h_provs h ∧
  ∀ l b, ih !! l.1 = Some (I2AConstant b) → h_heap h !! l = b !! l.

Definition i2a_heap_shared_agree (h : gmap loc val) (ih : gmap prov imp_to_asm_elem) : uPred imp_to_asmUR :=
  [∗ map] l↦v∈h,
    if ih !! l.1 is Some (I2AShared a) then
      ∃ av, i2a_val_rel v av ∗ i2a_mem_constant (a + l.2) (Some av)
    else
      True.

Definition i2a_heap_inv (h : heap_state) : uPred imp_to_asmUR :=
  ∃ ih, ⌜i2a_heap_agree h ih⌝ ∗ ([∗ map] p↦a ∈ i2a_ih_shared ih, i2a_heap_shared p a) ∗
         i2a_heap_shared_agree (h_heap h) ih ∗ i2a_heap_auth ih.

Definition i2a_args (o : nat) (vs : list val) (rs : gmap string Z) : uPred imp_to_asmUR :=
  ([∗ list] i↦v∈vs, ∃ r av,
      ⌜args_registers !! (o + i)%nat = Some r⌝ ∗
      ⌜rs !! r = Some av⌝ ∗
      i2a_val_rel v av).

Lemma i2a_mem_uninit_split n a l :
  0 ≤ n ≤ l →
  i2a_mem_uninit a l ⊣⊢ i2a_mem_uninit a n ∗ i2a_mem_uninit (a + n) (l - n).
Proof.
  move => ?. rewrite /i2a_mem_uninit.
  have {1} -> : l = (n + (l - n)) by lia.
  rewrite seqZ_app; [|lia..]. rewrite big_sepL_app. done.
Qed.

Lemma i2a_mem_uninit_alt1 a l :
  0 ≤ l →
  i2a_mem_uninit a l -∗ ∃ vs, ⌜length vs = Z.to_nat l⌝ ∗ i2a_mem_map (map_seqZ a (Some <$> vs)).
Proof.
  iIntros (Hl) "Hm". rewrite - {1}(Z2Nat.id l) //.
  iInduction (Z.to_nat l) as [|l'] "IH" forall (a).
  { iExists []. iSplit!. by rewrite /i2a_mem_map big_sepM_empty. }
  rewrite /i2a_mem_uninit Nat2Z.inj_succ seqZ_cons ?Z.pred_succ /=; [|lia].
  iDestruct "Hm" as "[[%v ?] ?]". iDestruct ("IH" with "[$]") as (vs ?) "Hm".
  iExists (v :: vs) => /=. iSplit!; [lia|]. rewrite /i2a_mem_map big_sepM_insert; [by iFrame|].
  apply lookup_map_seqZ_None. lia.
Qed.

Lemma i2a_mem_uninit_alt2 a vs :
  i2a_mem_map (map_seqZ a (Some <$> vs)) -∗
  i2a_mem_uninit a (length vs).
Proof.
  iIntros "Hvs". iInduction vs as [|v vs] "IH" forall (a); csimpl.
  { rewrite /i2a_mem_uninit /=. done. }
  rewrite /i2a_mem_map big_sepM_insert; [|apply lookup_map_seqZ_None; lia].
  iDestruct "Hvs" as "[??]". iDestruct ("IH" with "[$]") as "?".
  rewrite /i2a_mem_uninit /= Nat2Z.inj_succ (seqZ_cons a) ?Z.pred_succ /=; [|lia]. iFrame.
  by iExists _.
Qed.

Lemma i2a_guard_page_lookup a sp gp mem :
  gp ≤ a < gp + GUARD_PAGE_SIZE →
  i2a_mem_inv sp gp mem -∗
  ⌜mem !! a = Some None⌝.
Proof.
  iIntros (?) "(%&Hgp&?&Hauth)". rewrite /i2a_guard_page.
  iDestruct (i2a_mem_lookup_big' with "[$] [$]") as %Hsub.
  iPureIntro. apply: lookup_weaken; [|done]. apply lookup_map_seqZ_Some. split; [lia|].
  apply lookup_replicate. split!. unlock. lia.
Qed.

Lemma i2a_mem_lookup a v mem sp gp:
  i2a_mem_inv sp gp mem -∗
  i2a_mem_constant a v -∗
  ⌜mem !! a = Some v⌝.
Proof.
  iDestruct 1 as (Hsp) "(?&?&Hauth)".
  iIntros "Hconst".
  by iDestruct (i2a_mem_lookup' with "Hauth Hconst") as %?.
Qed.

Lemma i2a_mem_range a v mem sp gp:
  i2a_mem_inv sp gp mem -∗
  i2a_mem_constant a (Some v) -∗
  ⌜¬ (gp ≤ a < sp)⌝.
Proof.
  iIntros "Hinv Hconst" (?).
  iDestruct (i2a_mem_lookup with "[$] [$]") as %?.
  destruct (decide (gp + GUARD_PAGE_SIZE ≤ a)).
  2: { iDestruct (i2a_guard_page_lookup a with "[$]") as %?; [lia|]. simplify_eq. }
  iDestruct "Hinv" as "(%&?&Hsp&?)".
  iDestruct (big_sepL_lookup _ _ (Z.to_nat (a - (gp + GUARD_PAGE_SIZE))) a with "Hsp") as (?) "?".
  - apply lookup_seqZ. lia.
  - iDestruct (i2a_mem_constant_excl with "[$] [$]") as %[].
Qed.

Lemma i2a_mem_exists n sp gp mem :
  0 < n ≤ GUARD_PAGE_SIZE →
  i2a_mem_inv sp gp mem -∗
  ⌜∃ v, mem !! (sp - n) = Some v⌝.
Proof.
  iIntros (?) "Hinv".
  destruct (decide (gp + GUARD_PAGE_SIZE ≤ sp - n)).
  - iDestruct "Hinv" as "(%&?&Hsp&?)".
    iDestruct (big_sepL_lookup _ _ (Z.to_nat ((sp - n) - (gp + GUARD_PAGE_SIZE))) (sp - n) with "Hsp") as (?) "?".
    * apply lookup_seqZ. lia.
    * iDestruct (i2a_mem_lookup' with "[$] [$]") as %?. iSplit!.
  - iAssert ⌜gp + GUARD_PAGE_SIZE ≤ sp⌝%I as %?. { unfold i2a_mem_inv. by iDestruct!. }
    iDestruct (i2a_guard_page_lookup (sp - n) with "[$]") as %?.
    + lia.
    + iSplit!.
Qed.

Lemma i2a_mem_alloc n sp gp mem v :
  mem !! (sp - n) = Some (Some v) →
  0 ≤ n ≤ GUARD_PAGE_SIZE →
  i2a_mem_inv sp gp mem ==∗ ⌜gp ≤ sp - n⌝ ∗ i2a_mem_inv (sp - n) gp mem ∗ i2a_mem_uninit (sp - n) n.
Proof.
  iIntros (? ?) "Hinv". iModIntro.
  destruct (decide (gp + GUARD_PAGE_SIZE ≤ sp - n)).
  - iDestruct "Hinv" as "(%&?&?&?)".
    rewrite (i2a_mem_uninit_split ((sp - n) - (gp + GUARD_PAGE_SIZE))). 2: lia.
    iDestruct!.
    have ->: (gp + GUARD_PAGE_SIZE + (sp - n - (gp + GUARD_PAGE_SIZE))) = (sp - n) by lia.
    have ->: (sp - (gp + GUARD_PAGE_SIZE) - (sp - n - (gp + GUARD_PAGE_SIZE))) = n by lia. iFrame.
    iSplit!; [lia|done..].
  - iAssert ⌜gp + GUARD_PAGE_SIZE ≤ sp⌝%I as %?. { unfold i2a_mem_inv. by iDestruct!. }
    iDestruct (i2a_guard_page_lookup (sp - n) with "[$]") as %?.
    + lia.
    + simplify_eq.
Qed.

Lemma i2a_mem_update v' a v mem sp gp:
  i2a_mem_inv sp gp mem -∗
  i2a_mem_constant a v ==∗
  i2a_mem_inv sp gp (<[a := Some v']> mem) ∗ i2a_mem_constant a (Some v').
Proof.
  iDestruct 1 as (Hsp) "(?&?&Hauth)".
  iIntros "Hconst".
  iDestruct (i2a_mem_lookup' with "[$] [$]") as %?.
  iMod (i2a_mem_update' with "[$]") as "[? $]". iModIntro.
  by iFrame.
Qed.

Lemma i2a_mem_delete n mem sp gp:
  0 ≤ n →
  i2a_mem_inv sp gp mem -∗
  i2a_mem_uninit sp n ==∗
  i2a_mem_inv (sp + n) gp mem.
Proof.
  move => ?.
  iDestruct 1 as (Hsp) "(?&?&Hauth)".
  iIntros "Huninit". iModIntro. iFrame. iSplit!; [lia|].
  iApply (i2a_mem_uninit_split (sp - (gp + GUARD_PAGE_SIZE))); [lia|]. iFrame.
  have -> : (gp + GUARD_PAGE_SIZE + (sp - (gp + GUARD_PAGE_SIZE))) = sp by lia.
  have -> : (sp + n - (gp + GUARD_PAGE_SIZE) - (sp - (gp + GUARD_PAGE_SIZE))) = n by lia.
  done.
Qed.

Lemma i2a_mem_delete_big adrs mem sp sp' gp:
  sp ≤ sp' →
  Forall (λ a, gp ≤ a < sp') adrs →
  length adrs = Z.to_nat (sp' - sp) →
  i2a_mem_inv sp gp mem -∗
  ([∗ list] a∈adrs, ∃ v, i2a_mem_constant a (Some v)) ==∗
  i2a_mem_inv sp' gp mem.
Proof.
  iIntros (? Hall ?) "Hinv Ha".
  iAssert ⌜NoDup adrs⌝%I as %?. {
    rewrite NoDup_alt. iIntros (a1 a2 ???).
    destruct (decide (a1 = a2)) => //.
    rewrite (big_sepL_delete _ _ a1); [|done].
    rewrite (big_sepL_delete _ _ a2); [|done].
    iDestruct!. case_decide => //. iDestruct!.
    iDestruct (i2a_mem_constant_excl with "[$] [$]") as %[].
  }
  iAssert ⌜∀ a, a ∈ adrs → a ∈ seqZ sp (sp' - sp)⌝%I as %Hsub%NoDup_submseteq => //. {
    iIntros (??).
    iDestruct (big_sepL_elem_of with "[$]") as (?) "?"; [done|].
    iDestruct (i2a_mem_range with "[$] [$]") as %?.
    iPureIntro. apply elem_of_seqZ. move: Hall => /Forall_forall. naive_solver lia.
  }
  move: Hsub => /submseteq_Permutation_length_eq ->. 2: { rewrite seqZ_length. lia. }
  have [n [-> ->]]: ∃ n : nat, sp' - sp = Z.of_nat n ∧ sp' = sp + Z.of_nat n.
  { eexists (Z.to_nat (sp' - sp)). lia. }
  iApply (i2a_mem_delete with "[$] [$]"). lia.
Qed.

Lemma i2a_heap_alloc h l n:
  heap_is_fresh h l →
  i2a_heap_inv h ==∗
  i2a_heap_inv (heap_alloc h l n) ∗ i2a_heap_constant l.1 (h_heap (heap_alloc h l n)).
Proof.
  iIntros ([Hl ?]).
  iDestruct 1 as (? [Hdom Hc]) "[Hsh [Hs Hauth]]".
  iMod (i2a_heap_alloc' with "Hauth") as "[? $]".
  { apply not_elem_of_dom. by apply: not_elem_of_weaken; [|done]. }
  iModIntro. iExists _. iFrame. rewrite i2a_ih_shared_insert_const.
  2: { move => ?. contradict Hl. apply Hdom. by apply elem_of_dom. }
  iFrame. iSplit.
  - iPureIntro. split.
    + rewrite dom_insert_L heap_alloc_provs. set_solver.
    + move => ?? /lookup_insert_Some[[??]|[??]]; simplify_eq/= => //.
      rewrite lookup_union_r; [naive_solver|].
      apply not_elem_of_list_to_map. apply/elem_of_list_fmap => -[[[??]?][? /elem_of_list_fmap[?[??]]]].
      simplify_eq.
  - rewrite /i2a_heap_shared_agree big_sepM_union. 2: {
      apply map_disjoint_list_to_map_l, Forall_forall => -[[??]?] /elem_of_list_fmap[?[??]]. simplify_eq/=.
      apply eq_None_not_Some => /heap_wf. done.
    }
    iSplitR.
    + iApply big_sepM_intro. iIntros "!>" (?? (?&?&?)%elem_of_list_to_map_2%elem_of_list_fmap). by simplify_map_eq.
    + iApply (big_sepM_impl with "Hs"). iIntros "!>" (k??) "?".
      rewrite lookup_insert_ne //. contradict Hl. rewrite Hl. by apply heap_wf.
Qed.

Lemma i2a_heap_update h l v b:
  i2a_heap_inv h -∗
  i2a_heap_constant l.1 b ==∗
  i2a_heap_inv (heap_update h l v) ∗ i2a_heap_constant l.1 (h_heap (heap_update h l v)).
Proof.
  iDestruct 1 as (? [Hdom Hc]) "[Hsh [Hs Hauth]]". iIntros "Hc".
  iDestruct (i2a_heap_lookup' with "[$] [$]") as %?.
  iMod (i2a_heap_update' with "[$Hauth $Hc]") as "[? $]".
  iModIntro. iExists _. iFrame. rewrite i2a_ih_shared_insert_const.
  2: { move => ??. simplify_map_eq. } iFrame. iSplit.
  - iPureIntro. split.
    + rewrite dom_insert_L heap_update_provs. etrans; [|done]. apply union_least; [|done].
      apply singleton_subseteq_l. by apply elem_of_dom.
    + move => ?? /lookup_insert_Some[[??]|[??]]; simplify_eq/= => //.
      rewrite lookup_alter_ne; naive_solver.
  - rewrite /i2a_heap_shared_agree /= big_sepM_alter.
    iApply (big_sepM_impl with "Hs"). iIntros "!>" (k ??) "?". case_bool_decide; subst; simplify_map_eq => //.
    by destruct (decide (k.1 = l.1)) as [->|]; simplify_map_eq.
Qed.

Lemma i2a_heap_free h l b:
  i2a_heap_inv h -∗
  i2a_heap_constant l.1 b ==∗
  i2a_heap_inv (heap_free h l).
Proof.
  iDestruct 1 as (? [Hdom Hc]) "[Hsh [Hs Hauth]]". iIntros "Hc".
  iDestruct (i2a_heap_lookup' with "[$] [$]") as %?.
  iMod (i2a_heap_free' with "[$Hauth $Hc]") as "?".
  iModIntro. iExists _. iFrame. iSplit!.
  - split.
    + rewrite dom_delete_L heap_free_provs. set_solver.
    + move => ?? /lookup_delete_Some[??] /=.
      rewrite map_filter_lookup_true; naive_solver.
  - rewrite i2a_ih_shared_delete. by iApply big_sepM_delete_2.
  - rewrite /i2a_heap_shared_agree big_sepM_filter.
    iApply (big_sepM_impl with "Hs"). iIntros "!>" (???) "?". iIntros (?).
    by rewrite lookup_delete_ne.
Qed.

Lemma i2a_heap_lookup_shared h l v z mem ss gp:
  h_heap h !! l = Some v →
  i2a_heap_inv h -∗
  i2a_mem_inv ss gp mem -∗
  i2a_heap_shared l.1 z -∗
  ∃ av, ⌜mem !! (z + l.2)%Z = Some (Some av)⌝ ∗ i2a_val_rel v av.
Proof.
  iIntros (?).
  iDestruct 1 as (? Hag) "[Hsh [Hs Hauth]]".
  iIntros "Hmem Hl".
  iDestruct (i2a_heap_shared_lookup' with "[$] [$]") as %?.
  iDestruct (big_sepM_lookup with "Hs") as "Hv"; [done|]. simplify_map_eq.
  iDestruct "Hv" as (?) "[??]".
  iDestruct (i2a_mem_lookup with "[$] [$]") as %?. subst.
  iSplit!.
Qed.

Lemma i2a_heap_alloc_shared h l a n:
  heap_is_fresh h l →
  i2a_heap_inv h -∗
  ([∗ list] a'∈seqZ a n, i2a_mem_constant a' (Some 0)) ==∗
  i2a_heap_shared l.1 a ∗ i2a_heap_inv (heap_alloc h l n).
Proof.
  iIntros (Hf) "Hinv Ha".
  iMod (i2a_heap_alloc with "Hinv") as "[Hinv Hl]"; [done|].
  destruct Hf as [Hne ?].
  iDestruct "Hinv" as (?[??]) "[Hsh [Hag Hauth]]".
  iMod (i2a_heap_to_shared' with "[$]") as "[? #Hs1]". iModIntro. iFrame "Hs1".
  iExists _. iFrame. iSplit!.
  - split.
    + rewrite ->heap_alloc_provs in *. rewrite dom_insert_L. set_solver.
    + move => ?? /lookup_insert_Some. naive_solver.
  - rewrite i2a_ih_shared_insert. by iApply big_sepM_insert_2.
  - rewrite /i2a_heap_shared_agree /= !big_sepM_union.
    2,3: apply map_disjoint_list_to_map_l, Forall_forall => ? /elem_of_list_fmap[?[??]];
         simplify_eq/=; apply eq_None_not_Some => /heap_wf; naive_solver.
    iDestruct "Hag" as "[_ Hh]".
    iSplitR "Hh".
    + rewrite !big_sepM_list_to_map.
      2: { rewrite -list_fmap_compose. apply NoDup_fmap; [move => ?? /= ?;simplify_eq; lia|]. apply NoDup_seqZ. }
      iEval rewrite big_sepL_fmap. simplify_map_eq/=.
      have ->: a = a + 0 by lia.
      rewrite -(fmap_add_seqZ a 0) big_sepL_fmap.
      iApply (big_sepL_impl with "[$]"). iIntros "!>" (? o ?) "?". iSplit!.
      by have -> : (a + 0 + (l.2 + o)) = a + o by lia.
    + iApply (big_sepM_impl with "Hh"). iIntros "!>" (???) "?".
      rewrite lookup_insert_ne; [done|]. contradict Hne. rewrite Hne. by apply heap_wf.
Qed.

Lemma i2a_heap_free_shared h l a n:
  l.2 = 0 →
  heap_range h l n →
  i2a_heap_inv h -∗
  i2a_heap_shared l.1 a ==∗
  i2a_mem_uninit a n ∗ i2a_heap_inv (heap_free h l).
Proof.
  iIntros (Hl2 Hr).
  iDestruct 1 as (? [Hdom Hc]) "[Hsh [Hs Hauth]]". iIntros "Hl".
  iDestruct (i2a_heap_shared_lookup' with "[$] [$]") as %?.
  iModIntro.
  rewrite /i2a_heap_shared_agree -(map_filter_union_complement (λ '(l', _), l'.1 ≠ l.1) (h_heap h)).
  rewrite big_sepM_union; [|apply map_disjoint_filter_complement].
  iDestruct "Hs" as "[Hs Ha]". iSplitL "Ha".
  - iApply big_sepM_map_seq_0.
    have ?: Inj eq eq (λ n : nat, l +ₗ n) by move => ???; simplify_eq; lia.
    iApply (big_sepM_kmap_intro (λ n : nat, l +ₗ n)).
    iApply (big_sepM_impl_strong' with "[$]").
    iIntros "!>" (??) "Hm". iIntros ([i [?[?[??]%lookup_seqZ]%lookup_map_seq_Some]]%lookup_kmap_Some); [|done].
    simplify_eq/=. rewrite map_filter_lookup_true; [|naive_solver].
    case_match. 2: { exfalso. eapply not_eq_None_Some; [|done]. apply Hr; [done|]. simpl. lia. } simplify_map_eq.
    iDestruct!. iSplit!; [done|]. by rewrite Nat.sub_0_r Hl2.
  - iExists _. iFrame. iPureIntro. split; [done|]. move => ?? /= Hl.
    rewrite map_filter_lookup_true; [naive_solver|]. move => ?? Heq. rewrite Heq in Hl.
    simplify_map_eq.
Qed.

Lemma i2a_heap_free_list_shared h ls h' adrs:
  heap_free_list ls h h' →
  Forall (λ l, l.2 = 0) ls.*1 →
  i2a_heap_inv h -∗
  ([∗ list] l;a∈ls.*1;adrs, i2a_heap_shared l.1 a) ==∗
  ([∗ list] a∈mjoin (zip_with (λ a n, seqZ a n) adrs ls.*2), ∃ v, i2a_mem_constant a (Some v)) ∗
    i2a_heap_inv h'.
Proof.
  elim: ls h h' adrs => /=.
  { iIntros (??? -> ?) "? Hs". iDestruct (big_sepL2_nil_inv_l with "Hs") as %->. iModIntro. by iFrame. }
  move => [l n] ls IH h h' [|a adrs]; try by [iIntros]; csimpl => -[??] /Forall_cons[??]; iIntros "Hh [Hl Hs]".
  iMod (i2a_heap_free_shared with "Hh Hl") as "[$ ?]"; [done..|].
  by iApply (IH with "[$]").
Qed.

Lemma i2a_heap_update_shared h l v z mem ss av gp:
  heap_alive h l →
  i2a_heap_inv h -∗
  i2a_mem_inv ss gp mem -∗
  i2a_heap_shared l.1 z -∗
  i2a_val_rel v av ==∗
  i2a_heap_inv (heap_update h l v) ∗ i2a_mem_inv ss gp (<[z + l.2 := Some av]>mem).
Proof.
  iIntros ([??]).
  iDestruct 1 as (? [Hdom Hag]) "[Hsh [Hs Hauth]]".
  iIntros "Hmem Hl Hv".
  iDestruct (i2a_heap_shared_lookup' with "[$] [$]") as %?.
  rewrite /i2a_heap_shared_agree (big_sepM_delete _ (h_heap h)); [|done]. simplify_map_eq.
  iDestruct "Hs" as "[[% [??]] Hs]".
  iMod (i2a_mem_update with "[$] [$]") as "[$ ?]". iModIntro.
  iExists _. iFrame. iSplit; [iPureIntro|].
  - split; [by rewrite heap_update_provs|]. move => * /=. rewrite lookup_alter_ne; [naive_solver|].
    move => ?. simplify_map_eq'.
  - rewrite /i2a_heap_shared_agree/= (big_sepM_delete _ (alter (λ _, v) _ _) l); [|by simplify_map_eq].
    simplify_map_eq. rewrite delete_alter. iFrame. iExists _. iFrame.
Qed.

Lemma i2a_heap_inv_add_provs h ps :
  i2a_heap_inv h -∗
  i2a_heap_inv (heap_add_provs h ps).
Proof.
  iDestruct 1 as (?[??]) "[??]". iExists _. iFrame.
  iPureIntro. split; [|done]. rewrite heap_add_provs_provs.
  set_solver.
Qed.

Lemma i2a_res_init mem:
  satisfiable (i2a_mem_auth mem ∗ ([∗ map] a↦v∈mem, i2a_mem_constant a v) ∗ i2a_heap_inv initial_heap_state).
Proof.
  apply: (satisfiable_init (i2a_mem_inj (gmap_view_auth (DfracOwn 1) ∅) ⋅
                              i2a_heap_inj (gmap_view_auth (DfracOwn 1) ∅))).
  { split => /=; rewrite ?left_id ?right_id; apply gmap_view_auth_valid. }
  rewrite uPred.ownM_op. iIntros "[Hmem Hh]".
  iMod (i2a_mem_alloc_big' with "[$]") as "[? $]"; [solve_map_disjoint|]. rewrite right_id_L. iFrame.
  iModIntro.
  iExists _. iFrame. iSplit!. by rewrite i2a_ih_shared_empty.
Qed.

(* TODO: refactor this *)
Lemma i2a_mem_inv_init gp sp mem:
  gp + GUARD_PAGE_SIZE ≤ sp →
  (∀ a, gp ≤ a < gp + GUARD_PAGE_SIZE → mem !! a = Some None) →
  (∀ a, gp + GUARD_PAGE_SIZE ≤ a < sp → ∃ v, mem !! a = Some (Some v)) →
  i2a_mem_auth mem -∗
  ([∗ map] a↦v∈mem, i2a_mem_constant a v) -∗
  i2a_mem_inv sp gp mem.
Proof.
  iIntros (? Hgp Hsp) "$ H".
  rewrite -(map_filter_union_complement (λ a, a.1 < gp + GUARD_PAGE_SIZE) mem).
  rewrite big_sepM_union. 2: apply map_disjoint_filter_complement.
  iDestruct "H" as "[H1 H2]".
  iSplit; [done|]. iSplitL "H1".
  - unfold i2a_guard_page.
    iApply (big_sepM_impl_strong' with "[$]").
    iIntros "!>" (k ?) "?". iIntros ([?[? Hlt]%lookup_replicate]%lookup_map_seqZ_Some). simplify_eq.
    unlock in Hlt. rewrite map_filter_lookup_true. 2: naive_solver lia.
    rewrite Hgp. 2: lia. done.
  - unfold i2a_mem_uninit.
    iApply big_sepM_map_seq_0.
    iApply (big_sepM_kmap_intro (λ x, gp + GUARD_PAGE_SIZE + Z.of_nat x)). { move => ???. lia. }
    iApply (big_sepM_impl_strong' with "[$]").
    iIntros "!>" (k ?) "?". iIntros ([a [?[? [??]%lookup_seqZ]%lookup_map_seq_Some]]%lookup_kmap_Some).
    2: { move => ???. lia. } simplify_eq.
    rewrite map_filter_lookup_true. 2: { move => ?? /= Hx. clear -Hx. lia. }
    have [|? ->]:= Hsp (gp + GUARD_PAGE_SIZE + a); [lia|].
    iSplit!; [done|]. by rewrite Nat.sub_0_r.
Qed.

(*   iAssert () *)
(* iModIntro. *)
(*   iSplitL "Hmem". *)
(*   - iExists _. by iFrame. *)
(*   - iExists _. by iFrame. *)
(* Qed. *)

Lemma i2a_args_nil o rs:
  i2a_args o [] rs ⊣⊢ True.
Proof. done. Qed.

Lemma i2a_args_cons o v vs rs r:
  args_registers !! o = Some r →
  i2a_args o (v::vs) rs ⊣⊢ (∃ av, ⌜rs !! r = Some av⌝ ∗ i2a_val_rel v av) ∗ i2a_args (S o) vs rs.
Proof.
  move => ?. rewrite /i2a_args. setoid_rewrite Nat.add_succ_l. setoid_rewrite <-Nat.add_succ_r => /=.
  f_equiv. setoid_rewrite Nat.add_0_r. iSplit; iIntros!; iSplit!.
Qed.

Lemma i2a_args_mono o vs rs rs':
  map_preserved (drop o args_registers) rs rs' →
  i2a_args o vs rs -∗
  i2a_args o vs rs'.
Proof.
  iIntros (Hpre) "Hargs". iApply (big_sepL_impl with "Hargs").
  iIntros "!>" (???) "[% [% [% [% ?]]]]". iExists _, _. iFrame. iSplit; [done|]. iPureIntro.
  etrans; [symmetry; apply: Hpre|done].
  apply elem_of_list_lookup. setoid_rewrite lookup_drop. naive_solver.
Qed.

(** ** prepost *)
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

Definition imp_to_asm_pre (ins : gset Z) (fns : gset string) (f2i : gmap string Z) (gp : Z)
 (e : asm_event) (s : imp_to_asm_state) :
 prepost (imp_event * imp_to_asm_state) imp_to_asmUR :=
  match e with
  | (i, EAJump pc rs mem) =>
    (* env chooses if this is a function call or return *)
    pp_quant $ λ b : bool,
    pp_prop (i = Incoming) $
    pp_quant $ λ h,
    pp_star (i2a_mem_inv (rs !!! "SP") gp mem ∗ i2a_heap_inv h) $
    if b then
      (* env chooses return address *)
      pp_quant $ λ ret,
      (* env chooses function name *)
      pp_quant $ λ f,
      (* env chooses arguments *)
      pp_quant $ λ vs,
      pp_star (i2a_args 0 vs rs) $
      (* env proves that function name is valid *)
      pp_prop  (f ∈ fns) $
      (* env proves it calls the right address *)
      pp_prop (f2i !! f = Some pc) $
      (* env proves that ret is not in ins *)
      pp_prop (ret ∉ ins) $
      (* env proves that rs corresponds to vs and ret *)
      pp_prop (i2a_regs_call ret rs) $
      (* track the registers and return address (false means ret belongs to env) *)
      pp_end ((i, EICall f vs h), I2A ((I2AI false ret rs)::s.(i2a_calls)) rs)
    else
      (* env chooses return value *)
      pp_quant $ λ v,
      pp_quant $ λ av,
      pp_star (i2a_val_rel v av) $
      (* env chooses old registers *)
      pp_quant $ λ rsold,
      (* env chooses rest of cs *)
      pp_quant $ λ cs',
      (* get registers from stack (true means pc belongs to the program) *)
      pp_prop (s.(i2a_calls) = (I2AI true pc rsold)::cs') $
      (* env proves that rs is updated correctly *)
      pp_prop (i2a_regs_ret rs rsold av) $
      pp_end ((i, EIReturn v h), I2A cs' rs)
  | _ => pp_prop False $ pp_quant $ λ e, pp_end e
  end.

Definition imp_to_asm_post (ins : gset Z) (fns : gset string) (f2i : gmap string Z) (gp : Z)
           (e : imp_event) (s : imp_to_asm_state) : prepost (asm_event * imp_to_asm_state) imp_to_asmUR :=
  pp_prop (e.1 = Outgoing) $
  pp_quant $ λ pc,
  pp_quant $ λ rs,
  pp_quant $ λ mem,
  pp_star (i2a_mem_inv (rs !!! "SP") gp mem ∗ i2a_heap_inv (heap_of_event e.2)) $
  match e with
  | (i, EICall f vs h) =>
      (* program chooses return address *)
      pp_quant $ λ ret,
      (* program chooses new physical blocks *)
      pp_star (i2a_args 0 vs rs) $
      (* program proves that this function is external *)
      pp_prop (f ∉ fns) $
      (* program proves that the address is correct *)
      pp_prop (f2i !! f = Some pc) $
      (* program proves that ret is in ins *)
      pp_prop (ret ∈ ins) $
      (* program proves that rs corresponds to vs and ret  *)
      pp_prop (i2a_regs_call ret rs) $
      (* program proves it only touched a specific set of registers *)
      pp_prop (map_scramble touched_registers s.(i2a_last_regs) rs) $
      (* track the registers and return address (true means ret belongs to program) *)
      pp_end ((Outgoing, EAJump pc rs mem), (I2A ((I2AI true ret rs)::s.(i2a_calls)) s.(i2a_last_regs)))
  | (i, EIReturn v h) =>
      pp_quant $ λ av,
      (* program chooses new physical blocks *)
      pp_star (i2a_val_rel v av) $
      (* program chooses old registers *)
      pp_quant $ λ rsold,
      (* program chooses rest of cs *)
      pp_quant $ λ cs',
      (* get registers from stack (false means pc belongs to the env) *)
      pp_prop (s.(i2a_calls) = (I2AI false pc rsold)::cs') $
      (* prog proves that rs is updated correctly *)
      pp_prop (i2a_regs_ret rs rsold av) $
      (* program proves it only touched a specific set of registers *)
      pp_prop (map_scramble touched_registers s.(i2a_last_regs) rs) $
      pp_end ((Outgoing, EAJump pc rs mem), (I2A cs' s.(i2a_last_regs)))
  end.

Definition imp_to_asm (ins : gset Z) (fns : gset string) (f2i : gmap string Z) (gp : Z)
           (m : module imp_event) : module asm_event :=
  mod_prepost (imp_to_asm_pre ins fns f2i gp) (imp_to_asm_post ins fns f2i gp) m.

Definition initial_imp_to_asm_state (m : module imp_event) (σ : m.(m_state)) :=
  (@SMFilter imp_event, σ, (@PPOutside imp_event asm_event, I2A [] ∅, (True : uPred imp_to_asmUR)%I)).

Lemma imp_to_asm_trefines m m' σ σ' ins fns f2i gp `{!VisNoAll m}:
  trefines (MS m σ) (MS m' σ') →
  trefines (MS (imp_to_asm ins fns f2i gp m) (initial_imp_to_asm_state m σ))
           (MS (imp_to_asm ins fns f2i gp m') (initial_imp_to_asm_state m' σ')).
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
  | |- i2a_regs_call _ _ => eassumption
  | |- i2a_regs_ret _ _ _ => eassumption
  | |- ?P ⊣⊢ _ => is_evar P; reflexivity
  | |- map_scramble ?r ?a ?b =>
      assert_fails (has_evar r); assert_fails (has_evar a); assert_fails (has_evar b); by etrans
  end.
Local Ltac split_tac ::=
  repeat (original_split_tac; try split_solve).

Lemma imp_to_asm_combine ins1 ins2 fns1 fns2 f2i1 f2i2 m1 m2 σ1 σ2 gp `{!VisNoAll m1} `{!VisNoAll m2}:
  ins1 ## ins2 →
  fns1 ## fns2 →
  (∀ f, f ∈ fns1 → ∃ i, i ∈ ins1 ∧ f2i1 !! f = Some i) →
  (∀ f, f ∈ fns2 → ∃ i, i ∈ ins2 ∧ f2i2 !! f = Some i) →
  (∀ f i1 i2, f2i1 !! f = Some i1 → f2i2 !! f = Some i2 → i1 = i2) →
  (∀ f i, f2i1 !! f = Some i → i ∈ ins2 → f ∈ fns2) →
  (∀ f i, f2i2 !! f = Some i → i ∈ ins1 → f ∈ fns1) →
  trefines (MS (asm_prod ins1 ins2 (imp_to_asm ins1 fns1 f2i1 gp m1) (imp_to_asm ins2 fns2 f2i2 gp m2))
               (MLFNone, None, initial_imp_to_asm_state m1 σ1,
                 initial_imp_to_asm_state m2 σ2))
           (MS (imp_to_asm (ins1 ∪ ins2) (fns1 ∪ fns2) (f2i1 ∪ f2i2) gp (imp_prod fns1 fns2 m1 m2))
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
    destruct e as [pc rs mem| | |]; destruct_all?; simplify_eq/=.
    move => b *. apply pp_to_all_forall => ra ya Hra xa Hxa. eexists b.
    move: ra ya Hra xa Hxa. apply: pp_to_all_forall_2. destruct b => /=.
    + move => ret f vs Hin Hf2i /not_elem_of_union[??] ? ??.
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
    destruct e as [pc rs mem| | |]; destruct_all?; simplify_eq/=.
    move => b *. apply pp_to_all_forall => ra ya Hra xa Hxa. eexists b.
    move: ra ya Hra xa Hxa. apply: pp_to_all_forall_2. destruct b => /=.
    + move => ret f vs Hin Hf2i /not_elem_of_union[??] ???.
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


Lemma imp_to_asm_proof ins fns ins_dom fns_dom f2i gp :
  ins_dom = dom _ ins →
  fns_dom = dom _ fns →
  (∀ n i rs mem K f fn vs h cs pc ret rf rc lr,
      rs !! "PC" = Some pc →
      ins !! pc = Some i →
      fns !! f = Some fn →
      f2i !! f = Some pc →
      satisfiable (i2a_mem_inv (rs !!! "SP") gp mem ∗ i2a_heap_inv h ∗ i2a_args 0 vs rs ∗ rf ∗ rc) →
      i2a_regs_call ret rs →
      length vs = length (fd_args fn) →
      map_scramble touched_registers lr rs →
      (* Call *)
      (∀ K' rs' mem' f' es vs pc' ret' h' lr' rf' r',
          Forall2 (λ e v, e = Val v) es vs →
          rs' !! "PC" = Some pc' →
          (ins !! pc' = None ↔ fns !! f' = None) →
          f2i !! f' = Some pc' →
          satisfiable (i2a_mem_inv (rs' !!! "SP") gp mem' ∗ i2a_heap_inv h' ∗
                      i2a_args 0 vs rs' ∗ rf' ∗ r') →
          i2a_regs_call ret' rs' →
          is_Some (ins !! ret') →
          map_scramble touched_registers lr' rs' →
          (∀ rs'' mem'' av v h'' rf'' lr'',
              rs'' !! "PC" = Some ret' →
              satisfiable (i2a_mem_inv (rs'' !!! "SP") gp mem'' ∗ i2a_heap_inv h'' ∗
                           i2a_val_rel v av ∗ rf'' ∗ r') →
              i2a_regs_ret rs'' rs' av →
              map_scramble touched_registers lr'' rs'' →
              AsmState (ARunning []) rs'' mem'' ins ⪯{asm_module, imp_to_asm ins_dom fns_dom f2i gp imp_module, n, true}
               (SMProg, Imp (expr_fill K (expr_fill K' (Val v))) h'' fns, (PPInside, I2A cs lr'', rf''))) →
          AsmState (ARunning []) rs' mem' ins ⪯{asm_module, imp_to_asm ins_dom fns_dom f2i gp imp_module, n, true}
               (SMProg, Imp (expr_fill K (expr_fill K' (imp.Call f' es))) h' fns, (PPInside, I2A cs lr', rf'))) →
      (* Return *)
      (∀ rs' mem' av v h' lr' rf',
          rs' !! "PC" = Some ret →
          satisfiable (i2a_mem_inv (rs' !!! "SP") gp mem' ∗ i2a_heap_inv h' ∗
                      i2a_val_rel v av ∗ rf' ∗ rc) →
          i2a_regs_ret rs' rs av →
          map_scramble touched_registers lr' rs' →
          AsmState (ARunning []) rs' mem' ins ⪯{asm_module, imp_to_asm ins_dom fns_dom f2i gp imp_module, n, true}
               (SMProg, Imp (expr_fill K (Val v)) h' fns, (PPInside, I2A cs lr', rf'))) →
      AsmState (ARunning []) rs mem ins ⪯{asm_module, imp_to_asm ins_dom fns_dom f2i gp imp_module, n, false}
               (SMProg, Imp (expr_fill K (AllocA fn.(fd_vars) $ subst_l fn.(fd_args) vs fn.(fd_body))) h fns, (PPInside, I2A cs lr, rf))
) →
  trefines (MS asm_module (initial_asm_state ins))
           (MS (imp_to_asm ins_dom fns_dom f2i gp imp_module) (initial_imp_to_asm_state imp_module
             (initial_imp_state fns))).
Proof.
  move => ? ? Hf. subst.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember_call.
  { simpl. exact (λ d b '((AsmState i1 rs1 mem1 ins'1), (σfs1, Imp e1 h1 fns'1, (t1, I2A cs1 lr1, r1)))
                        '((AsmState i2 rs2 mem2 ins'2), (σfs2, Imp e2 h2 fns'2, (t2, I2A cs2 lr2, r2))),
      ∃ K, i2 = AWaiting ∧ ins'2 = ins ∧ e2 = expr_fill K (Waiting (bool_decide (d ≠ 0%nat))) ∧ fns'2 = fns ∧
              t2 = PPOutside ∧ σfs2 = SMFilter ∧ (d = 0%nat ↔ cs2 = []) ∧
      if b then
        e2 = e1 ∧
        cs2 = cs1 ∧
        r1 = r2
      else
        True
                 ). }
  { simpl. exact (λ  '(AsmState i1 rs1 mem1 ins'1) '(σfs1, Imp e1 h1 fns'1, (t1, I2A cs1 lr1, r1))
                     '(AsmState i2 rs2 mem2 ins'2) '(σfs2, Imp e2 h2 fns'2, (t2, I2A cs2 lr2, r2)),
    ∃ i K av v pc lr',
      rs2 !! "PC" = Some pc ∧
      ins !! pc = Some i ∧
      satisfiable (i2a_mem_inv (rs2 !!! "SP") gp mem2 ∗ i2a_heap_inv h2 ∗ i2a_val_rel v av ∗ r1 ∗ r2) ∧
      i2a_regs_ret rs2 lr' av ∧
      i2 = ARunning [] ∧
      ins'1 = ins'2 ∧
      σfs2 = SMProg ∧
      e1 = expr_fill K (Waiting true) ∧
      e2 = expr_fill K (Val v) ∧
      fns'1 = fns'2 ∧
      t2 = PPInside ∧
      cs1 = I2AI true pc lr' :: cs2 ∧
      lr2 = rs2
). }
  { move => ??? *. destruct_all?. repeat case_match; naive_solver. }
  { move => /= *. destruct_all?. repeat case_match. naive_solver. }
  { move => /=. eexists []. split!. }
  move => /= n [i rs mem ins'] [[?[???]][[?[cs ?]]r]] d ? ? Hstay Hcall Hret. destruct_all?; simplify_eq/=.
  tstep_i => ??????.
  go_s. split!.
  go_s => -[] ? /=.
  - move => ???? /elem_of_dom[??] ? /not_elem_of_dom ? ???.
    go_s. split!.
    repeat case_bool_decide (_ = _); try by tstep_s.
    (* This inner loop deals with calls inside of the module. We use
    Hf both for calls triggered from inside and outside the module. *)
    unshelve eapply tsim_remember. { exact (λ n '(AsmState i1 rs1 mem1 ins'1) '(σfs1, Imp e1 h1 fns'1, (t1, I2A cs1 lr1, r1)),
       ∃ K' pc i ret f fn vs r',
         rs1 !! "PC" = Some pc ∧
         ins !! pc = Some i ∧
         fns !! f = Some fn ∧
         f2i !! f = Some pc ∧
         ins'1 = ins ∧
         fns'1 = fns ∧
         satisfiable (i2a_mem_inv (rs1 !!! "SP") gp mem1 ∗ i2a_heap_inv h1 ∗
                                   i2a_args 0 vs rs1 ∗ r' ∗ r1) ∧
         i2a_regs_call ret rs1 ∧
         i1 = ARunning [] ∧
         e1 = expr_fill K' (AllocA fn.(fd_vars) $ subst_l fn.(fd_args) vs fn.(fd_body)) ∧
         map_scramble touched_registers lr1 rs1 ∧
         length vs = length (fd_args fn) ∧
         t1 = PPInside ∧
         σfs1 = SMProg ∧
         (∀ rs' mem' av v h' lr' rf',
          rs' !! "PC" = Some ret →
          satisfiable (i2a_mem_inv (rs' !!! "SP") gp mem' ∗ i2a_heap_inv h' ∗
                      i2a_val_rel v av ∗ r' ∗ rf') →
          i2a_regs_ret rs' rs1 av  →
          map_scramble touched_registers lr' rs' →
          AsmState (ARunning []) rs' mem' ins ⪯{asm_module, imp_to_asm (dom _ ins) (dom _ fns) f2i gp imp_module, n, true}
               (SMProg, Imp (expr_fill K' (Val v)) h' fns, (PPInside, I2A cs1 lr', rf'))) ). }
    { eexists (ReturnExtCtx _:: _). split! => //. { iSatMono. iIntros!. iFrame. iAccu. }
      iSatClear. move => *.
      tstep_s.
      tstep_i => ??. simplify_map_eq.
      tstep_s. split!. { iSatMono. iIntros!. iFrame. iAccu. }
      apply Hstay; [done|]. by split!.
    }
    { move => ?? [????] [[?[???]][[?[??]]?]] ??. destruct_all?. split!; [done..|].
      move => *. apply: tsim_mono; [naive_solver|]. etrans; [|done]. apply ti_le_S. }
    iSatClear.
    move => n' /= Hn' IH [i' rs' mem' ins'] [[?[???]][[?[??]]?]] ?. destruct_all?; simplify_eq.
    apply: Hf; [try eassumption..| |].
    { iSatMono. iIntros!. iFrame. iAccu. }
    + iSatClear.
      move => K'' rs'' mem'' f'' es vs'' pc'' ret'' h'' lr rf'' r'' Hall ??????? Hret'.
      have ?: es = Val <$> vs''. { clear -Hall. elim: Hall; naive_solver. } subst.
      destruct (ins !! pc'') eqn:Hi.
      * have [??] : is_Some (fns !! f''). { apply not_eq_None_Some. naive_solver. }
        tstep_s. left. split! => ?/=.
        apply IH; [done|]. split! => //.
        { iSatMono. iIntros!. iFrame. iAccu. }
        iSatClear. move => *.
        rewrite expr_fill_app.
        apply: Hret' => //.
        iSatMono. iIntros!. iFrame.
      * have ?: fns !! f'' = None by naive_solver.
        tstep_i => ??. simplify_map_eq.
        tstep_s. right. split!.
        tstep_s. split!. { by apply not_elem_of_dom. } { by apply elem_of_dom. }
        { iSatMono. iIntros!. iFrame. iAccu. }
        apply Hcall. { etrans; [|done]. apply ti_le_S. } { by split!. }
        iSatClear.
        move => [i2 rs2 mem2 ins'2] [[?[???]][[?[??]]?]].
        move => [i3 rs3 mem3 ins'3] [[?[???]][[?[??]]?]] ??. destruct_all?; simplify_eq.
        repeat match goal with | H : expr_fill _ _ = expr_fill _ _ |- _ => apply expr_fill_Waiting_inj in H end.
        destruct_all?; simplify_eq.
        rewrite !expr_fill_app /=.
        eapply Hret' => //.
        iSatMono. iIntros!. iFrame.
    + iSatClear. move => *.
      apply: H16 => //.
      iSatMono. iIntros!. iFrame.
  - move => *.
    tstep_s. simplify_eq. destruct d; [exfalso; naive_solver|]. split!.
    apply Hret; [done..| |].
    + by split!.
    + split!; [|done..].
      iSatMono. iIntros!. iFrame.
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
  i2a_regs_call ret rs avs →
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
