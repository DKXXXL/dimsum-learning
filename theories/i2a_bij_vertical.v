Require Export iris.algebra.cmra.
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
Require Import refframe.imp_to_asm.
Require Import refframe.imp_heap_bij_own.

Local Open Scope Z_scope.

(** * imp_heap_bij_own.v *)
Program Definition heap_bij_share_big (s : gmap prov prov) (bij : heap_bij)
        (H : ∀ p1 p2, s !! p2 = Some p1 → p1 ∉ hb_provs_i bij) :=
  HeapBij ((HBShared <$> s) ∪ (hb_bij bij)) (hb_priv_i bij) _ _.
Next Obligation.
  move => ?? Hnotin ??.
Admitted.
(*   rewrite !lookup_insert_Some => ?. destruct_all?; simplify_eq/= => //; try naive_solver. *)
(*   - apply eq_None_ne_Some => ??. naive_solver. *)
(*   - by apply: hb_disj. *)
(* Qed. *)
Next Obligation.
Admitted.
(*   move => ??? Hnotin ???. move: Hnotin. rewrite elem_of_hb_provs_i => ?. *)
(*   rewrite !lookup_insert_Some => ??. destruct_all?; simplify_eq/= => //; try naive_solver. *)
(*   by apply: hb_iff. *)
(* Qed. *)

Lemma heap_bij_alloc_big s bij (H : ∀ p1 p2, s !! p2 = Some p1 → p1 ∉ hb_provs_i bij) :
  dom (gset _) s ## dom _ (hb_bij bij) →
  heap_bij_auth bij ==∗
  heap_bij_auth (heap_bij_share_big s bij H) ∗ [∗ map] p2↦p1∈s, heap_bij_shared p1 p2.
Proof.
Admitted.

Lemma heap_bij_update_all bij' bij ho :
  hb_shared bij = hb_shared bij' →
  hb_priv_i bij = hb_priv_i bij' →
  heap_bij_auth bij -∗
  ([∗ map] p↦h∈ hb_priv_s bij ∖ ho, heap_bij_const_s p h) ==∗
  heap_bij_auth bij' ∗
  ([∗ map] p↦h∈ hb_priv_s bij' ∖ ho, heap_bij_const_s p h).
Proof.
  (* iIntros (????) "Hauth Hsh Hho". *)
Admitted.
(* Lemma heap_bij_update_all bij bij' ho : *)
(*   (* ho ⊆ hb_priv_s bij' → *) *)
(*   (* ho ⊆ hb_priv_s bij → *) *)
(*   hb_shared bij ⊆ hb_shared bij' → *)
(*   hb_priv_i bij = hb_priv_i bij' → *)
(*   heap_bij_auth bij -∗ *)
(*   ([∗ map] p2↦p1∈ hb_shared bij, heap_bij_shared p1 p2) -∗ *)
(*   ([∗ map] p↦h∈ hb_priv_s bij ∖ ho, heap_bij_const_s p h) ==∗ *)
(*   heap_bij_auth bij' ∗ *)
(*   ([∗ map] p2↦p1∈ hb_shared bij', heap_bij_shared p1 p2) ∗ *)
(*   ([∗ map] p↦h∈ hb_priv_s bij' ∖ ho, heap_bij_const_s p h). *)
(* Proof. *)
(*   (* iIntros (????) "Hauth Hsh Hho". *) *)
(* Admitted. *)

(** * through bij *)
Definition val_through_bij (bij : heap_bij) (vs : val) : val :=
  match vs with
  | ValLoc l => ValLoc (if hb_bij bij !! l.1 is Some (HBShared p) then p else inhabitant, l.2)
  | _ => vs
  end.

Program Definition heap_through_bij (bij : heap_bij) (h : heap_state) : heap_state :=
  Heap (list_to_map $ omap (OMap:=list_omap) (λ '(l, v), if hb_bij bij !! l.1 is Some (HBShared p) then
         Some ((p, l.2), val_through_bij bij v) else None) (map_to_list (h_heap h)))
       (gset_to_gmap tt $ hb_shared_i bij) _.
Next Obligation.
  move => ??. apply bool_decide_spec. move => ? /elem_of_map[?[?/elem_of_dom]]. subst.
  rewrite dom_gset_to_gmap.
  rewrite list_to_map_lookup_is_Some => -[?]. rewrite elem_of_list_omap => -[[[??]?]]/=[??].
  repeat case_match; simplify_eq. rewrite elem_of_hb_shared_i. naive_solver.
Qed.

Lemma heap_through_bij_provs bij h :
  h_provs (heap_through_bij bij h) = hb_shared_i bij.
Proof. by rewrite /h_provs dom_gset_to_gmap. Qed.

Lemma heap_through_bij_Some bij h pi o vi:
  h_heap (heap_through_bij bij h) !! (pi, o) = Some vi ↔
    ∃ ps vs, hb_bij bij !! ps = Some (HBShared pi) ∧ h_heap h !! (ps, o) = Some vs ∧ vi = val_through_bij bij vs.
Proof.
  simpl. rewrite -elem_of_list_to_map. 2: {
    rewrite list_fmap_omap. apply NoDup_omap_2_strong; [|apply NoDup_map_to_list].
    move => [[??]?] [[??]?] [??] /=.
    move => /elem_of_map_to_list ?/elem_of_map_to_list? /fmap_Some[[??][??]] /fmap_Some[[??][??]].
    by repeat case_match; simplify_eq/=; simplify_bij.
  }
  rewrite elem_of_list_omap.
  split.
  - move => [[[??]?]]. rewrite elem_of_map_to_list => ?. repeat case_match => //; naive_solver.
  - move => ?. destruct_all?. eexists (_,_,_). rewrite elem_of_map_to_list. split; [done|].
    by simplify_option_eq.
Qed.
Opaque heap_through_bij.

Lemma heap_through_bij_is_Some bij h pi o:
  is_Some (h_heap (heap_through_bij bij h) !! (pi, o)) ↔
          ∃ ps, hb_bij bij !! ps = Some (HBShared pi) ∧ is_Some (h_heap h !! (ps, o)).
Proof. rewrite /is_Some. setoid_rewrite heap_through_bij_Some. naive_solver. Qed.

Lemma heap_through_bij_is_Some' bij h pi ps o:
  hb_bij bij !! ps = Some (HBShared pi) →
  is_Some (h_heap (heap_through_bij bij h) !! (pi, o)) ↔ is_Some (h_heap h !! (ps, o)).
Proof.
  move => ?. rewrite heap_through_bij_is_Some. split; [|naive_solver].
  move => [p'[??]]. by simplify_bij.
Qed.

(** combine bij *)
Definition i2a_combine_bij (ih : gmap prov Z) (bij : heap_bij) : gmap prov Z :=
  omap (λ v, if v is HBShared pi then
               if ih !! pi is Some a then
                 Some a
               else
                 None
             else
               None) bij.(hb_bij).

Lemma i2a_combine_bij_lookup_Some ih bij p a:
  i2a_combine_bij ih bij !! p = Some a ↔ ∃ p', hb_bij bij !! p = Some (HBShared p') ∧ ih !! p' = Some a.
Proof.
  rewrite /i2a_combine_bij lookup_omap_Some.
  split => ?; destruct_all?.
  - do 2 case_match => //. simplify_eq. naive_solver.
  - eexists (HBShared _). by simplify_map_eq.
Qed.

Definition i2a_combine_priv_shared (ih : gmap prov Z) (bij : heap_bij) (hb : heap_state) : gmap prov (gmap Z val) :=
  map_imap (λ ps v, if v is HBShared pi then
               if ih !! pi is Some a then
                 None
               else
                 Some (h_block hb ps)
             else
               None) bij.(hb_bij).

Lemma i2a_combine_priv_shared_Some ih bij p b hb:
  i2a_combine_priv_shared ih bij hb !! p = Some b ↔
    ∃ pi, hb_bij bij !! p = Some (HBShared pi) ∧ ih !! pi = None ∧ b = h_block hb p.
Proof.
  rewrite /i2a_combine_priv_shared map_lookup_imap bind_Some.
  split => ?; destruct_all?.
  - repeat case_match => //; simplify_eq. naive_solver.
  - eexists (HBShared _). by simplify_map_eq.
Qed.

Lemma i2a_combine_priv_shared_priv_s_disj ih bij ho :
  i2a_combine_priv_shared ih bij ho ##ₘ hb_priv_s bij.
Proof.
  apply map_disjoint_spec => ???. rewrite i2a_combine_priv_shared_Some hb_priv_s_lookup_Some. naive_solver.
Qed.


Definition i2a_combine_priv (ih : gmap prov Z) (bij : heap_bij) (hb : heap_state) : gmap prov (gmap Z val) :=
  i2a_combine_priv_shared ih bij hb ∪ hb_priv_s bij.

Lemma i2a_combine_priv_Some ih bij p b hb:
  i2a_combine_priv ih bij hb !! p = Some b ↔
    hb_bij bij !! p = Some (HBConstant b) ∨
    ∃ pi, hb_bij bij !! p = Some (HBShared pi) ∧ ih !! pi = None ∧ b = h_block hb p.
Proof.
  rewrite /i2a_combine_priv lookup_union_Some. 2: by apply i2a_combine_priv_shared_priv_s_disj.
  rewrite i2a_combine_priv_shared_Some hb_priv_s_lookup_Some. naive_solver.
Qed.

Lemma i2a_combine_priv_diff ih bij hb ho :
  i2a_combine_priv_shared ih bij hb ⊆ ho →
  i2a_combine_priv ih bij hb ∖ ho = hb_priv_s bij ∖ ho.
Proof.
  move => Hho.
  apply map_eq => ?. apply option_eq => ?.
  rewrite !lookup_difference_Some i2a_combine_priv_Some hb_priv_s_lookup_Some.
  split => ?; destruct_all?; simplify_eq => //.
  - exfalso. revert select (ho !! _ = None). apply not_eq_None_Some. apply: lookup_weaken_is_Some; [|done].
    eexists _. apply i2a_combine_priv_shared_Some. naive_solver.
  - naive_solver.
Qed.

Lemma i2a_combine_bij_priv_disj ih bij h:
  I2AShared <$> i2a_combine_bij ih bij ##ₘ I2AConstant <$> i2a_combine_priv ih bij h.
Proof.
  apply map_disjoint_spec => ???.
  rewrite !lookup_fmap !fmap_Some.
  setoid_rewrite i2a_combine_bij_lookup_Some. setoid_rewrite i2a_combine_priv_Some.
  move => ??. destruct_all?; simplify_eq.
Qed.

Lemma i2a_combine_bij_mono ih bij ih' bij' :
  ih ⊆ ih' →
  hb_shared bij ⊆ hb_shared bij' →
  i2a_combine_bij ih bij ⊆ i2a_combine_bij ih' bij'.
Proof.
  move => Hih Hbij. apply map_subseteq_spec => ??.
  setoid_rewrite i2a_combine_bij_lookup_Some.
  setoid_rewrite <-hb_shared_lookup_Some => -[?[??]].
  split!; by apply: lookup_weaken.
Qed.

Lemma fresh_map_learn ih bijb (X : gset prov) ps pi:
  fresh_map (dom _ (i2a_ih_shared ih) ∖ hb_shared_s bijb) X !! ps = Some pi →
  (∃ a, ih !! ps = Some (I2AShared a) ∧ ∀ pi', hb_bij bijb !! ps ≠ Some (HBShared pi'))
   ∧ pi ∉ X.
Proof.
  move => /(fresh_map_lookup_Some _ _ _ _)[/elem_of_difference[/elem_of_dom[? /i2a_ih_shared_Some ?]]].
  rewrite !elem_of_hb_shared_s. naive_solver.
Qed.
Ltac fresh_map_learn :=
  repeat match goal with
         | H : fresh_map (dom _ (i2a_ih_shared _) ∖ hb_shared_s _) _ !! _ = Some _ |- _ =>
             learn_hyp (fresh_map_learn _ _ _ _ _ H)
         end.

Definition i2a_combine_heap_bij_bij (X : gset prov) (ih : gmap prov imp_to_asm_elem) (bijb : heap_bij)
            :=
  (HBShared <$> (hb_shared bijb ∪ fresh_map ((dom _ (i2a_ih_shared ih)) ∖ hb_shared_s bijb) X)) ∪
  (HBConstant <$> i2a_ih_constant ih).

Lemma i2a_combine_heap_bij_bij_shared X bijb ps pi ih:
  i2a_combine_heap_bij_bij X ih bijb !! ps = Some (HBShared pi) ↔
    hb_bij bijb !! ps = Some (HBShared pi) ∨
    fresh_map ((dom _ (i2a_ih_shared ih)) ∖ hb_shared_s bijb) X !! ps = Some pi.
Proof.
  rewrite /i2a_combine_heap_bij_bij !lookup_union_Some_raw ?lookup_union_None !lookup_fmap.
  rewrite !fmap_None !fmap_Some.
  setoid_rewrite i2a_ih_constant_Some.
  setoid_rewrite lookup_union_Some_raw.
  setoid_rewrite lookup_union_None.
  setoid_rewrite hb_shared_lookup_Some.
  setoid_rewrite hb_shared_lookup_None.
  split => ?; destruct_all?; simplify_eq/=.
  - naive_solver.
  - naive_solver.
  - left. split!. naive_solver.
  - fresh_map_learn. destruct_all?. left. split!. naive_solver.
Qed.

Lemma i2a_combine_heap_bij_bij_priv_s X bijb ps ih h:
  i2a_combine_heap_bij_bij X ih bijb !! ps = Some (HBConstant h) ↔
    ih !! ps = Some (I2AConstant h) ∧ ps ∉ hb_shared_s bijb.
Proof.
  rewrite /i2a_combine_heap_bij_bij !lookup_union_Some_raw ?lookup_union_None !lookup_fmap.
  rewrite elem_of_hb_shared_s.
  rewrite !fmap_None !fmap_Some.
  setoid_rewrite i2a_ih_constant_Some.
  setoid_rewrite lookup_union_Some_raw.
  setoid_rewrite lookup_union_None.
  setoid_rewrite hb_shared_lookup_Some.
  setoid_rewrite hb_shared_lookup_None.
  split => ?; destruct_all?; simplify_eq/=.
  - naive_solver.
  - right. split!. 1: naive_solver. apply fresh_map_lookup_None.
    apply not_elem_of_difference. left. move => /elem_of_dom[? /i2a_ih_shared_Some ?]. naive_solver.
Qed.

Program Definition i2a_combine_heap_bij (X : gset prov) (ih : gmap prov imp_to_asm_elem) (bijb : heap_bij)
 (H1 : hb_provs_i bijb ⊆ X) : heap_bij :=
  HeapBij (i2a_combine_heap_bij_bij X ih bijb) (hb_priv_i bijb) _ _.
Next Obligation.
  move => X ih bijb HX ps pi.
  rewrite !i2a_combine_heap_bij_bij_shared // => -[?|?]; [by apply: hb_disj|].
  apply eq_None_ne_Some => ??.
  have : (pi ∈ hb_provs_i bijb) by rewrite elem_of_hb_provs_i; naive_solver.
  fresh_map_learn. set_solver.
Qed.
Next Obligation.
  move => X ih bijb HX pi ps ps'.
  rewrite !i2a_combine_heap_bij_bij_shared => ??.
  destruct_all?; simplify_bij.
  - done.
  - fresh_map_learn. destruct_all?. move: (HX pi). rewrite elem_of_hb_provs_i. naive_solver.
  - fresh_map_learn. destruct_all?. move: (HX pi). rewrite elem_of_hb_provs_i. naive_solver.
  - by apply: fresh_map_bij.
Qed.

Definition i2a_combine_i2a (X : gset prov) (ih : gmap prov imp_to_asm_elem) (bijb : heap_bij) : gmap prov Z :=
  list_to_map $
   omap (λ '(ps, pi), if ih !! ps is Some (I2AShared a) then Some (pi : prov, a) else None) $
    map_to_list (fresh_map ((dom _ (i2a_ih_shared ih)) ∖ hb_shared_s bijb) X).

Lemma i2a_combine_i2a_Some X ih bijb p a:
  i2a_combine_i2a X ih bijb !! p = Some a ↔
    ∃ ps, fresh_map ((dom _ (i2a_ih_shared ih)) ∖ hb_shared_s bijb) X !! ps = Some p
          ∧ ih !! ps = Some (I2AShared a).
Proof.
  rewrite /i2a_combine_i2a. rewrite -elem_of_list_to_map. 2: {
    rewrite list_fmap_omap. apply: NoDup_omap_2_strong; [|apply NoDup_map_to_list].
    move => [??] [??] ? /elem_of_map_to_list? /elem_of_map_to_list? /= /fmap_Some[?[??]] /fmap_Some[?[??]].
    repeat case_match => //. simplify_eq/=. f_equal. by apply: fresh_map_bij.
  }
  rewrite elem_of_list_omap.
  split => ?; destruct_all?; simplify_eq.
  - repeat case_match => //. simplify_eq/=. revert select (_ ∈ map_to_list _) => /elem_of_map_to_list. naive_solver.
  - eexists (_, _). simplify_option_eq. split!. by apply elem_of_map_to_list.
Qed.

Lemma i2a_combine_extend (X : gset prov) iha bijb ih ho hb :
  i2a_combine_bij (i2a_ih_shared iha) bijb ⊆ i2a_ih_shared ih →
  ho ⊆ i2a_ih_constant ih →
  i2a_combine_priv_shared (i2a_ih_shared iha) bijb hb ⊆ ho →
  dom _ iha ⊆ X →
  hb_provs_i bijb ⊆ X →
  ∃ ih' bijb',
    i2a_ih_shared ih = i2a_combine_bij (ih' ∪ i2a_ih_shared iha) bijb' ∧
    i2a_ih_constant ih = i2a_combine_priv (ih' ∪ i2a_ih_shared iha) bijb' hb ∧
    dom _ ih' ## X ∧
    hb_shared bijb ⊆ hb_shared bijb' ∧
    hb_priv_i bijb = hb_priv_i bijb' ∧
    (* The following is redundant but it makes the proof easier. *)
    (I2AShared <$> ih') ##ₘ iha ∧
    dom (gset prov) (hb_bij bijb') ⊆ dom (gset prov) ih ∧
    (i2a_ih_constant ih ∖ (hb_priv_s bijb' ∖ ho)) = ho
.
Proof.
  move => Hcombine Hho Hpriv HXa HXb.
  have Hdisj : (I2AShared <$> (i2a_combine_i2a X ih bijb)) ##ₘ iha. {
    apply map_disjoint_spec => ???. rewrite lookup_fmap => /fmap_Some [?[/i2a_combine_i2a_Some[?[??]]?]] ?.
    fresh_map_learn. destruct_all?. simplify_eq. revert select (_ ∉ X). apply. apply HXa. by apply elem_of_dom.
  }
  have Hdisj2 : dom (gset _) (i2a_combine_priv_shared (i2a_ih_shared iha) bijb hb) ## dom _ (i2a_ih_shared ih). {
    apply: disjoint_mono; [|by apply: subseteq_dom|done].
    apply: disjoint_mono; [|by apply: subseteq_dom|done].
    apply elem_of_disjoint => ? /elem_of_dom[? /i2a_ih_constant_Some ?] /elem_of_dom[? /i2a_ih_shared_Some ?].
    naive_solver.
  }
  have Hrev: ∀ ps pi b,
      ih !! ps = Some (I2AConstant b) →
      hb_bij bijb !! ps = Some (HBShared pi) →
      i2a_ih_shared iha !! pi = None ∧ b = h_block hb ps. {
    move => ps pi b Hih Hbij.
    destruct (i2a_ih_shared iha !! pi) as [a|] eqn: Hiha.
    - exfalso. have : i2a_ih_shared ih !! ps = Some a.
      { apply: lookup_weaken; [|done]. apply i2a_combine_bij_lookup_Some. naive_solver. }
      rewrite i2a_ih_shared_Some. naive_solver.
    - split!. have : ih !! ps = Some (I2AConstant (h_block hb ps)); [|naive_solver].
      rewrite -i2a_ih_constant_Some. apply: lookup_weaken; [|done]. apply: lookup_weaken; [|done].
      rewrite i2a_combine_priv_shared_Some. naive_solver.
  }

  eexists (i2a_combine_i2a X ih bijb).
  eexists (i2a_combine_heap_bij X ih bijb HXb).
  split_and!.
  - apply map_eq => ps. apply option_eq => a. rewrite i2a_ih_shared_Some.
    rewrite i2a_combine_bij_lookup_Some /=.
    setoid_rewrite i2a_combine_heap_bij_bij_shared.
    setoid_rewrite lookup_union_Some. 2: {
     apply (map_disjoint_fmap I2AShared I2AShared). eapply map_disjoint_weaken_r; [done|].
     apply i2a_ih_shared_fmap_l. }
    setoid_rewrite i2a_combine_i2a_Some.
    setoid_rewrite i2a_ih_shared_Some.
    split => ?.
    + destruct (hb_shared bijb !! ps) as [pi|] eqn:Hps.
      * move: Hps => /hb_shared_lookup_Some Hps. eexists _. split; [by left|].
        split!.
        destruct (i2a_ih_shared iha !! pi) as [a'|] eqn:Heq.
        -- right. have : i2a_ih_shared ih !! ps = Some a'. {
             apply: lookup_weaken; [|done]. apply i2a_combine_bij_lookup_Some. naive_solver.
           }
           rewrite i2a_ih_shared_Some. rewrite i2a_ih_shared_Some in Heq. naive_solver.
        -- exfalso. move: Hdisj2 => /elem_of_disjoint. apply.
           ++ apply elem_of_dom. eexists _. apply i2a_combine_priv_shared_Some. naive_solver.
           ++ apply elem_of_dom. eexists _. by apply i2a_ih_shared_Some.
      * have [??]: is_Some (fresh_map (dom (gset prov) (i2a_ih_shared ih) ∖ hb_shared_s bijb) X !! ps). {
          apply not_eq_None_Some. rewrite fresh_map_lookup_None. apply. apply elem_of_difference.
          split.
          - apply elem_of_dom. eexists _. by apply i2a_ih_shared_Some.
          - rewrite elem_of_hb_shared_s. rewrite hb_shared_lookup_None in Hps. naive_solver.
        }
        eexists _. split; [by right|]. left. naive_solver.
    + destruct_all?; simplify_eq.
      * fresh_map_learn. destruct_all?. exfalso. revert select (_ ∉ X). apply. apply HXb.
        apply elem_of_hb_provs_i. naive_solver.
      * have : ps = ps0; [|naive_solver]. by apply: fresh_map_bij.
      * rewrite -i2a_ih_shared_Some. apply: lookup_weaken; [|done].
        apply i2a_combine_bij_lookup_Some. split!. by apply i2a_ih_shared_Some.
      * fresh_map_learn. destruct_all?. exfalso. revert select (_ ∉ X). apply. apply HXa. by apply elem_of_dom.
  - apply map_eq => ps. apply option_eq => b. rewrite i2a_ih_constant_Some i2a_combine_priv_Some /=.
    setoid_rewrite i2a_combine_heap_bij_bij_priv_s.
    setoid_rewrite i2a_combine_heap_bij_bij_shared.
    setoid_rewrite lookup_union_None.
    split => ?; destruct_all?; simplify_eq.
    + destruct (decide (ps ∈ hb_shared_s bijb)) as [[pi ?]%elem_of_hb_shared_s|]. 2: naive_solver.
      right.
      efeed pose proof Hrev; [done..|]. destruct_all?.
      eexists _. split_and!; [by left | |done|done].
      apply eq_None_ne_Some => ?. rewrite i2a_combine_i2a_Some => ?. destruct_all?.
      fresh_map_learn. destruct_all?. simplify_eq. revert select (_ ∉ X). apply. apply HXb.
      rewrite elem_of_hb_provs_i. naive_solver.
    + naive_solver.
    + rewrite -i2a_ih_constant_Some. apply: lookup_weaken; [|done]. apply: lookup_weaken; [|done].
      rewrite i2a_combine_priv_shared_Some. naive_solver.
    + fresh_map_learn. destruct_all?.
      exfalso. revert select (i2a_combine_i2a _ _ _ !! _ = None). apply not_eq_None_Some.
      eexists _. apply i2a_combine_i2a_Some. naive_solver.
  - apply elem_of_disjoint => ? /elem_of_dom [? /i2a_combine_i2a_Some ?]. destruct_all?.
    fresh_map_learn. naive_solver.
  - apply map_subseteq_spec => ??. rewrite !hb_shared_lookup_Some /= i2a_combine_heap_bij_bij_shared. naive_solver.
  - done.
  - done.
  - move => ps /elem_of_dom /=[][pi|?].
    + move => /i2a_combine_heap_bij_bij_shared[|].
      * move => ?. rewrite -(i2a_ih_shared_constant ih). rewrite dom_union_L !dom_fmap elem_of_union !elem_of_dom.
        destruct (i2a_ih_shared iha !! pi) eqn:Heq.
        -- left. apply: lookup_weaken_is_Some; [|done]. eexists _. apply i2a_combine_bij_lookup_Some. naive_solver.
        -- right. apply: lookup_weaken_is_Some; [|done]. apply: lookup_weaken_is_Some; [|done].
           eexists _. apply i2a_combine_priv_shared_Some. naive_solver.
      * move => ?. fresh_map_learn. destruct_all?. by apply elem_of_dom.
    + move => /i2a_combine_heap_bij_bij_priv_s[??]. by apply elem_of_dom.
  - apply map_eq => ps. apply option_eq => b.
    rewrite lookup_difference_Some lookup_difference_None hb_priv_s_lookup_None i2a_ih_constant_Some /=.
    setoid_rewrite i2a_combine_heap_bij_bij_priv_s.
    split => ?; destruct_all?; simplify_eq.
    + destruct (decide (ps ∈ hb_shared_s bijb)) as [[pi ?]%elem_of_hb_shared_s|]. 2: naive_solver.
      enough (is_Some (ho !! ps)) as [b' ?]. {
        have /i2a_ih_constant_Some : i2a_ih_constant ih !! ps = Some b' by apply: lookup_weaken.
        naive_solver.
      }
      apply: lookup_weaken_is_Some; [|done]. eexists _. apply i2a_combine_priv_shared_Some.
      split!. apply eq_None_ne_Some_2 => a ?.
      enough (i2a_ih_shared ih !! ps = Some a) as ?%i2a_ih_shared_Some by naive_solver.
      apply: lookup_weaken; [|done]. apply i2a_combine_bij_lookup_Some. naive_solver.
    + revert select (is_Some _) => -[b' ?].
      have /i2a_ih_constant_Some : i2a_ih_constant ih !! ps = Some b' by apply: lookup_weaken.
      naive_solver.
    + split; [|naive_solver]. apply i2a_ih_constant_Some. by apply: lookup_weaken.
Qed.

(** * imp_to_asm.v ?! *)
Lemma i2a_mem_update_all1 mem mem' mo :
  mo ⊆ mem →
  mo ⊆ mem' →
  i2a_mem_auth mem' -∗
  i2a_mem_map (mem' ∖ mo) ==∗
  i2a_mem_auth mem ∗ i2a_mem_map (mem ∖ mo).
Proof.
  iIntros (Hsub ?) "Hmem Hconst".
  iMod (i2a_mem_delete_big' with "[$] [$]").
  iMod (i2a_mem_alloc_big' with "[$]") as "[? $]".
  { apply map_disjoint_spec => ???. rewrite !lookup_difference_Some lookup_difference_None /is_Some.
    move => ??. destruct_all?; simplify_eq. } iModIntro.
  rewrite map_difference_id // map_union_comm ?map_difference_union //. apply map_disjoint_difference_l'.
Qed.
(*
Lemma i2a_mem_update_all2 moa mem mo :
  mo ⊆ mem →
  moa ##ₘ mo →
  i2a_mem_auth (moa ∪ mo) -∗
  i2a_mem_map moa ==∗
  i2a_mem_auth mem ∗ i2a_mem_map (mem ∖ mo).
Proof.
  iIntros (Hsub Hdisj) "Hmem Hconst".
  iInduction moa as [|a v moa ?] "IH" using map_ind forall (mem mo Hsub Hdisj). {
    rewrite left_id_L.
    iMod (i2a_mem_alloc_big' with "[$]") as "[? $]". { apply map_disjoint_difference_l'. }
    rewrite map_union_comm. 2: { apply map_disjoint_difference_l'. }
    by rewrite map_difference_union.
  }
  move: Hdisj => /map_disjoint_insert_l [??].
  rewrite {3}/i2a_mem_map big_sepM_insert //. iDestruct "Hconst" as "[Hc Hconst]".
  rewrite -insert_union_l insert_union_r //.
  iMod ("IH" $! (<[a:=v]> mem) with "[%] [%] [$] [$]") as "[Hmem Hconst]".
  { by apply insert_mono. } { by apply map_disjoint_insert_r. }
  rewrite (difference_insert _ _ _ _ _ v) -delete_difference.
  destruct (mem !! a) as [v'|] eqn:?.
  - iMod (i2a_mem_update' v' with "[$]") as "[??]". iModIntro.
    rewrite insert_insert (insert_id _ _ v') //. iFrame.
    iApply big_sepM_delete; [|by iFrame]. by apply lookup_difference_Some.
  - rewrite delete_notin. 2: { apply lookup_difference_None. by left. } iFrame.
    iMod (i2a_mem_delete' with "[$]"). by rewrite delete_insert.
Qed.

Lemma i2a_mem_update_all1 mem mem' mo :
  mo ⊆ mem →
  mo ⊆ mem' →
  i2a_mem_auth mem' -∗
  i2a_mem_map (mem' ∖ mo) ==∗
  i2a_mem_auth mem ∗ i2a_mem_map (mem ∖ mo).
Proof.
  iIntros (Hsub ?) "Hmem Hconst".
  iApply (i2a_mem_update_all2 (mem' ∖ mo) with "[Hmem] [$]").
  { done. } { apply map_disjoint_difference_l'. }
  rewrite map_union_comm. 2: { apply map_disjoint_difference_l'. }
  by rewrite map_difference_union.
Qed.
*)

(*
Lemma i2a_heap_alloc_shared_big'' ih ih' :
  (∀ p a1 a2, ih' !! p = Some a1 → ih !! p = Some a2 → a2 = I2AShared a1) →
  i2a_heap_auth ih -∗
  ([∗ map] p↦a∈i2a_ih_shared ih, i2a_heap_shared p a) ==∗
   i2a_heap_auth ((I2AShared <$> ih') ∪ ih) ∗ [∗ map] p↦a∈ih', i2a_heap_shared p a.
Proof.
  iIntros (Hag) "Hh #Hsh".
  iInduction ih' as [|p a ih' ?] "IH" using map_ind;
    rewrite ->?fmap_empty, ?fmap_insert in *.
  { rewrite left_id big_sepM_empty. by iFrame. }
  iMod ("IH" with "[] [$]") as "[??]".
  { iPureIntro => ????. apply: Hag. apply lookup_insert_Some. naive_solver. }
  rewrite -insert_union_l.
  destruct (ih !! p) eqn: Hp.
  - iModIntro. efeed pose proof Hag; [|done|]. { apply lookup_insert_Some. by left. } simplify_eq.
    rewrite insert_union_r. 2: { by rewrite lookup_fmap fmap_None. }
    rewrite insert_id //. iFrame.
    iApply big_sepM_insert_2; [|done]. iApply (big_sepM_lookup with "Hsh").
    by apply i2a_ih_shared_Some.
  - iMod (i2a_heap_alloc_shared' with "[$]") as "[$ ?]".
    { apply lookup_union_None. split!. rewrite lookup_fmap. by apply fmap_None. }
    rewrite big_sepM_insert //. by iFrame.
Qed.
*)

Lemma i2a_heap_update_all ihs ihc ih hob :
  hob ⊆ i2a_ih_constant ih →
  hob ⊆ ihc →
  i2a_ih_shared ih ⊆ ihs →
  dom (gset _) ihs ## dom _ ihc →
  i2a_heap_auth ih -∗
  ([∗ map] p↦a∈i2a_ih_shared ih, i2a_heap_shared p a) -∗
  ([∗ map] p↦a∈i2a_ih_constant ih ∖ hob, i2a_heap_constant p a) ==∗
  i2a_heap_auth ((I2AShared <$> ihs) ∪ (I2AConstant <$> ihc)) ∗
  ([∗ map] p↦a∈ihs, i2a_heap_shared p a) ∗
  ([∗ map] p↦a∈ihc ∖ hob, i2a_heap_constant p a).
Proof.
  iIntros (Hsub1 Hsub2 Hsh Hdisj) "Hauth #Hsh Hconst".
  iMod (i2a_heap_free_big' with "[$] [$]") as "?".
  iMod (i2a_heap_alloc_shared_big' _ (ihs ∖ i2a_ih_shared ih) with "[$]") as "[??]".
  { apply map_disjoint_spec => ? x y.
    rewrite lookup_fmap fmap_Some !lookup_difference_Some lookup_fmap fmap_None lookup_difference_None.
    setoid_rewrite lookup_difference_Some. unfold is_Some.
    setoid_rewrite i2a_ih_constant_None.
    setoid_rewrite i2a_ih_shared_None.
    move => ??. destruct_all?; simplify_eq.
    - destruct y; naive_solver.
    - have ? := lookup_weaken _ _ _ _ ltac:(done) Hsub2.
      apply: Hdisj; by apply elem_of_dom.
  }
  have -> : ((I2AShared <$> ihs ∖ i2a_ih_shared ih) ∪ ih ∖ (I2AConstant <$> i2a_ih_constant ih ∖ hob)) =
             (I2AShared <$> ihs) ∪ (I2AConstant <$> hob). {
    rewrite - {2}(i2a_ih_shared_constant ih).
    rewrite map_difference_union_distr assoc. f_equal.
    - rewrite (map_difference_disj_id _ (I2AConstant <$> _)).
      2: { admit. }
      rewrite -map_fmap_union map_union_comm ?map_difference_union //.
      apply map_disjoint_difference_l'.
    - have -> : (I2AConstant <$> i2a_ih_constant ih ∖ hob) = (I2AConstant <$> i2a_ih_constant ih) ∖ (I2AConstant <$> hob). by admit.
      apply map_difference_id. by apply map_fmap_mono.
  }
  (* ((I2AShared <$> ihs ∖ i2a_ih_shared ih) ∪ ih) = *)
  (*          (I2AShared <$> ihs) ∪ (I2AConstant <$> i2a_ih_constant ih). { *)
  (*   rewrite - {2}(i2a_ih_shared_constant ih) assoc. f_equal. *)
  (*   rewrite -map_fmap_union map_union_comm ?map_difference_union //. *)
  (*   apply map_disjoint_difference_l'. *)
  (* } *)
  iMod (i2a_heap_alloc_big' with "[$]") as "[? $]".
  { apply map_disjoint_spec => ???.
    rewrite lookup_union_Some_raw !lookup_fmap !fmap_Some !fmap_None.
    setoid_rewrite lookup_difference_Some.
    move => ??. destruct_all?; simplify_eq.
    apply: Hdisj; by apply elem_of_dom.
  } iModIntro.
  iAssert ([∗ map] p↦a ∈ ihs, i2a_heap_shared p a)%I as "#Hsh'". {
    rewrite - {3} (map_difference_union (i2a_ih_shared ih) ihs) //.
    by iApply big_sepM_union_2.
  } iFrame "Hsh'".
  iDestruct (i2a_heap_shared_lookup_big' with "[$] Hsh'") as %Hsub.
  have -> : ((I2AConstant <$> ihc ∖ hob) ∪ ((I2AShared <$> ihs) ∪ (I2AConstant <$> hob))) =
             ((I2AShared <$> ihs) ∪ (I2AConstant <$> ihc)). {
    rewrite assoc_L (map_union_comm _ (I2AShared <$> _)). 2: { admit. }
    rewrite -assoc. f_equal. rewrite -map_fmap_union. rewrite map_union_comm ?map_difference_union //.
    apply map_disjoint_difference_l'.
  }
  (*
  have -> : ((I2AConstant <$> ihc ∖ hob)
         ∪ ((I2AShared <$> ihs) ∪ (I2AConstant <$> i2a_ih_constant ih))
           ∖ (I2AConstant <$> i2a_ih_constant ih ∖ hob)) = ((I2AShared <$> ihs) ∪ (I2AConstant <$> ihc)). {
    apply map_eq => ps. apply option_eq => e.
    rewrite !lookup_union_Some_raw !lookup_fmap !fmap_Some !lookup_difference_Some !fmap_None.
    rewrite !lookup_union_Some_raw !lookup_fmap !fmap_Some !fmap_None !lookup_difference_None /is_Some.
    setoid_rewrite lookup_difference_Some.
    setoid_rewrite i2a_ih_constant_Some.
    setoid_rewrite i2a_ih_constant_None.
    split => ?; destruct_all?; simplify_eq => //; split!.
    - apply eq_None_ne_Some => ??. apply: Hdisj; by apply elem_of_dom.
    - naive_solver.
    - naive_solver.
    - have [??]: is_Some (ihc !! ps); [|naive_solver]. by apply: lookup_weaken_is_Some; [|done].
    - revert select (hob !! _ = Some _) => Hob.
      have := lookup_weaken _ _ _ _ Hob Hsub1.
      have := lookup_weaken _ _ _ _ Hob Hsub2.
      rewrite i2a_ih_constant_Some. naive_solver.
    - left. apply eq_None_ne_Some => ??. apply: Hdisj; by apply elem_of_dom.
    - have := lookup_weaken _ _ _ _ ltac:(done) Hsub.
      rewrite i2a_ih_shared_Some.
      rewrite !lookup_union_Some_raw !lookup_fmap !fmap_Some !lookup_difference_Some !fmap_None.
      rewrite !lookup_union_Some_raw !lookup_fmap !fmap_Some !fmap_None !lookup_difference_None /is_Some.
      setoid_rewrite lookup_difference_Some.
      setoid_rewrite i2a_ih_constant_Some.
      setoid_rewrite i2a_ih_constant_None. move => ?. destruct_all?; simplify_eq/=; naive_solver.
    - destruct (hob !! ps) eqn:Hob.
      + right. split!; [naive_solver| |naive_solver].
        have := lookup_weaken _ _ _ _ Hob Hsub1.
        have := lookup_weaken _ _ _ _ Hob Hsub2.
        rewrite i2a_ih_constant_Some. naive_solver.
      + naive_solver.
  }
   *)
  done.
Admitted.

Lemma i2a_heap_shared_agree_union h1 h2 ih:
  h1 ##ₘ h2 →
  i2a_heap_shared_agree (h1 ∪ h2) ih ⊣⊢ i2a_heap_shared_agree h1 ih ∗ i2a_heap_shared_agree h2 ih.
Proof. apply big_sepM_union. Qed.

Lemma i2a_heap_shared_agree_impl h1 h2 ih1 ih2:
  (∀ l v a, h2 !! l = Some v → ih2 !! l.1 = Some (I2AShared a) →
            h1 !! l = Some v ∧ ih1 !! l.1 = Some (I2AShared a)) →
  i2a_heap_shared_agree h1 ih1 -∗
  i2a_heap_shared_agree h2 ih2.
Proof.
  iIntros (Himpl) "Hag".
  iApply (big_sepM_impl_strong' with "[$]").
  iIntros "!>" (k ?) "H1". iIntros (?). destruct (ih2 !! k.1) as [[]|] eqn:? => //.
  have [??]:= Himpl _ _ _ ltac:(done) ltac:(done). by simplify_map_eq.
Qed.

(** mem_transfer *)
Lemma i2a_mem_transfer mem m1 m2 P1 P2:
  satisfiable (i2a_mem_auth mem ∗ i2a_mem_map m1 ∗ i2a_mem_map m2 ∗ P1) →
  satisfiable (i2a_mem_map (mem ∖ m1) ∗ P2) →
    satisfiable (i2a_mem_auth mem ∗ i2a_mem_map (m2 ∪ m1) ∗ P1) ∧
    satisfiable (i2a_mem_map m2 ∗ i2a_mem_map (mem ∖ (m2 ∪ m1)) ∗ P2).
Proof.
  move => Hs1 Hs2.
  iSatStart Hs1. iIntros "(Hauth&Hm1&Hm2&?)".
  iDestruct (i2a_mem_lookup_big' with "Hauth Hm1") as %?.
  iDestruct (i2a_mem_lookup_big' with "Hauth Hm2") as %?.
  iDestruct (i2a_mem_map_excl with "Hm1 Hm2") as %?.
  iSatStop Hs1. split.
  - iSatMono Hs1. iFrame. rewrite /i2a_mem_map big_sepM_union; [by iFrame|done].
  - iSatMono Hs2. iIntros "(Hmem&$)".
    rewrite -(map_difference_union m2 (mem ∖ m1)). 2: {
      apply map_subseteq_spec => ???. apply lookup_difference_Some.
      split; [by apply: lookup_weaken| by apply: map_disjoint_Some_l].
    }
    rewrite /i2a_mem_map big_sepM_union; [|by apply map_disjoint_difference_r'].
    by rewrite map_difference_difference map_union_comm.
Qed.

(** * pure versions *)
(** ** imp to asm *)
Definition i2a_val_rel_pure (ih : gmap prov prov) (iv : val) (av : Z) : Prop :=
  match iv with
  | ValNum z => av = z
  | ValBool b => av = bool_to_Z b
  | ValLoc l => ∃ z, av = (z + l.2)%Z ∧ ih !! l.1 = Some z
  end.

Lemma i2a_val_rel_to_pure v av ih :
  i2a_heap_auth ih -∗
  i2a_val_rel v av -∗
  ⌜i2a_val_rel_pure (i2a_ih_shared ih) v av⌝.
Proof.
  iIntros "Hh Hv". destruct v => //=. iDestruct!.
  iDestruct (i2a_heap_shared_lookup' with "[$] [$]") as %?.
  iPureIntro. setoid_rewrite i2a_ih_shared_Some. naive_solver.
Qed.

Lemma i2a_val_rel_of_pure ih v av :
  i2a_val_rel_pure ih v av →
  ([∗ map] p↦a ∈ ih, i2a_heap_shared p a) -∗
  i2a_val_rel v av.
Proof.
  iIntros (Hv) "Hsh". destruct v => //=. simplify_eq/=. destruct_all?. simplify_eq.
  iSplit!; [done|]. by iApply (big_sepM_lookup with "[$]").
Qed.

Lemma i2a_val_rel_pure_through_bij iv av ih1 ih2 bij:
  i2a_val_rel_pure ih1 iv av →
  ih1 = i2a_combine_bij ih2 bij →
  i2a_val_rel_pure ih2 (val_through_bij bij iv) av.
Proof.
  move => Hp ?. subst. destruct iv => //; simplify_eq/=.
  move: Hp => [? [? /i2a_combine_bij_lookup_Some[?[??]]]]. simplify_map_eq.
  naive_solver.
Qed.

Definition i2a_args_pure (ih : gmap prov prov) (o : nat) (vs : list val) (rs : gmap string Z) : Prop :=
  ∀ i v, vs !! i = Some v → ∃ r av,
      args_registers !! (o + i)%nat = Some r ∧
      rs !! r = Some av ∧
      i2a_val_rel_pure ih v av.

Lemma i2a_args_to_pure ih o vs rs :
  i2a_heap_auth ih -∗
  i2a_args o vs rs -∗
  ⌜i2a_args_pure (i2a_ih_shared ih) o vs rs⌝.
Proof.
  iIntros "Hh Hargs".
  iInduction vs as [|v vs] "IH" forall (o). { iPureIntro => ? [] //. }
  rewrite /i2a_args /=. iDestruct "Hargs" as "[[% [% [% [% ?]]]]?]".
  iDestruct (i2a_val_rel_to_pure with "[$] [$]") as %?.
  setoid_rewrite <-Nat.add_succ_comm.
  iDestruct ("IH" with "[$] [$]") as %Hp.
  iPureIntro => i ? /lookup_cons_Some[[??]|[? Hv]]; simplify_eq. 1: naive_solver. destruct i; [lia|].
  setoid_rewrite <-Nat.add_succ_comm. apply Hp. rewrite -Hv. f_equal. lia.
Qed.

Lemma i2a_args_of_pure ih o vs rs :
  i2a_args_pure ih o vs rs →
  ([∗ map] p↦a ∈ ih, i2a_heap_shared p a) -∗
  i2a_args o vs rs.
Proof.
  iIntros (Hp) "Hsh".
  iInduction vs as [|v vs] "IH" forall (o Hp). { by rewrite /i2a_args /=. }
  rewrite /i2a_args /=. iSplit.
  - move: (Hp 0%nat v) => []// ?[?[?[??]]]. iSplit!. by iApply i2a_val_rel_of_pure.
  - setoid_rewrite <-Nat.add_succ_comm. iApply ("IH" with "[%] [$]").
    move => ???. setoid_rewrite Nat.add_succ_comm. by apply: Hp.
Qed.

Lemma i2a_args_pure_through_bij o vs rs ih1 ih2 bij:
  i2a_args_pure ih1 o vs rs →
  ih1 = i2a_combine_bij ih2 bij →
  i2a_args_pure ih2 o (val_through_bij bij <$> vs) rs.
Proof.
  move => Hp ?. subst.
  elim: vs o Hp; csimpl. { move => ?? ? []//. }
  move => v ? IH ? Hp i v' /lookup_cons_Some[[??]|[? Hv]]; simplify_eq.
  - move: (Hp 0%nat v) => []// ?[?[?[??]]]. split!. by apply: i2a_val_rel_pure_through_bij.
  - destruct i; [lia|]. setoid_rewrite <-Nat.add_succ_comm. apply IH.
    + move => ???. setoid_rewrite Nat.add_succ_comm. by apply Hp.
    + rewrite -Hv. f_equal. lia.
Qed.

Definition i2a_heap_shared_agree_pure (h : gmap loc val) (ih : gmap prov prov) (mem : gmap Z (option Z)) : Prop :=
  ∃ m2l : gmap Z loc,
  map_Forall (λ l v,
               if ih !! l.1 is Some a then
                 ∃ av, i2a_val_rel_pure ih v av ∧ mem !! (a + l.2) = Some (Some av) ∧ m2l !! (a + l.2) = Some l
               else True
  ) h.


Lemma i2a_heap_shared_agree_to_pure h ih :
  i2a_heap_shared_agree h ih -∗
  i2a_heap_auth ih -∗
  ∃ m, ⌜i2a_heap_shared_agree_pure h (i2a_ih_shared ih) m⌝ ∗ i2a_mem_map m ∗ i2a_heap_auth ih.
Proof.
Admitted.

Lemma i2a_heap_shared_agree_of_pure ih h m :
  i2a_heap_shared_agree_pure h (i2a_ih_shared ih) m →
  ([∗ map] p↦a ∈ i2a_ih_shared ih, i2a_heap_shared p a) -∗
  i2a_mem_map m -∗
  i2a_heap_shared_agree h ih.
Proof.
Admitted.

Lemma i2a_heap_shared_agree_pure_impl f ih1 h1 ih2 h2 m :
  i2a_heap_shared_agree_pure h1 ih1 m →
  (∀ l2 v2 a, h2 !! l2 = Some v2 → ih2 !! l2.1 = Some a →
    ∃ p1 v1, f p1 = Some l2.1 ∧ h1 !! (p1, l2.2) = Some v1 ∧ ih1 !! p1 = Some a ∧
               (∀ av, i2a_val_rel_pure ih1 v1 av → i2a_val_rel_pure ih2 v2 av)) →
  i2a_heap_shared_agree_pure h2 ih2 m.
Proof.
  move => [m2l Hh] Himpl.
  eexists (omap (λ x, (λ y, (y, x.2)) <$> f x.1) m2l). move => l2 v2 ?. case_match => //.
  have [?[?[?[?[? Hvr]]]]]:= Himpl _ _ _ ltac:(done) ltac:(done).
  have := Hh _ _ ltac:(done). simplify_map_eq.
  move => [?[?[??]]]. split!; [by apply: Hvr|].
  simplify_option_eq. by destruct l2.
Qed.

(** ** heap_bij *)
Definition val_in_bij_pure (bij : heap_bij) (v1 v2 : val) : Prop :=
  match v1, v2 with
  | ValNum n1, ValNum n2 => n1 = n2
  | ValBool b1, ValBool b2 => b1 = b2
  | ValLoc l1, ValLoc l2 => l1.2 = l2.2 ∧ hb_bij bij !! l2.1 = Some (HBShared l1.1)
  | _, _ => False
  end.

Lemma val_in_bij_to_pure bij v1 v2 :
  heap_bij_auth bij -∗
  val_in_bij v1 v2 -∗
  ⌜val_in_bij_pure bij v1 v2⌝.
Proof.
  iIntros "Hh Hv". destruct v1, v2 => //=. unfold loc_in_bij. iDestruct!.
  iDestruct (heap_bij_shared_lookup with "[$] [$]") as %?. done.
Qed.

Lemma val_in_bij_to_pure_big bij vs1 vs2 :
  heap_bij_auth bij -∗
  ([∗ list] v1;v2∈vs1;vs2, val_in_bij v1 v2) -∗
  ⌜Forall2 (val_in_bij_pure bij) vs1 vs2⌝.
Proof.
  iIntros "Hh Hv".
  iInduction vs1 as [|v1 vs1] "IH" forall (vs2).
  { iDestruct (big_sepL2_nil_inv_l with "[$]") as %->. iPureIntro. econs. }
  iDestruct (big_sepL2_cons_inv_l with "[$]") as (???) "[??]". subst.
  iDestruct ("IH" with "[$] [$]") as %?.
  iDestruct (val_in_bij_to_pure with "[$] [$]") as %?.
  iPureIntro. by econs.
Qed.

Lemma val_in_bij_of_pure bij v1 v2 :
  val_in_bij_pure bij v1 v2 →
  ([∗ map]p2↦p1∈hb_shared bij, heap_bij_shared p1 p2) -∗
  val_in_bij v1 v2.
Proof.
  iIntros (Hv) "Hsh". destruct v1, v2 => //=. simplify_eq/=. destruct_all?.
  iSplit; [done|]. iApply (big_sepM_lookup with "[$]"). by apply hb_shared_lookup_Some.
Qed.

Definition heap_in_bij_pure (bij : heap_bij) (h h' : heap_state) : Prop :=
  ∀ p1 p2 o,
  hb_bij bij !! p2 = Some (HBShared p1) →

  (is_Some (h.(h_heap) !! (p1, o)) ↔ is_Some (h'.(h_heap) !! (p2, o)))
  ∧
  ∀ v1 v2,
  h.(h_heap)  !! (p1, o) = Some v1 →
  h'.(h_heap) !! (p2, o) = Some v2 →
  val_in_bij_pure bij v1 v2.

Lemma heap_in_bij_to_pure bij h h' :
  heap_bij_auth bij -∗
  heap_in_bij bij h h' -∗
  ⌜heap_in_bij_pure bij h h'⌝.
Proof.
  iIntros "Ha Hh". iIntros (????).
  iDestruct ("Hh" with "[//]") as (?) "Hh".
  iSplit; [done|]. iIntros (????).
  iApply (val_in_bij_to_pure with "[$]"). by iApply "Hh".
Qed.

Lemma heap_in_bij_of_pure bij h h' :
  heap_in_bij_pure bij h h' →
  ([∗ map]p2↦p1∈hb_shared bij, heap_bij_shared p1 p2) -∗
  heap_in_bij bij h h'.
Proof.
  iIntros (Hh) "Hsh". iIntros (p1 p2 o ?).
  move: Hh => /(_ _ _ o ltac:(done))[? {}Hh]. iSplit; [done|].
  iIntros (????). iApply (val_in_bij_of_pure with "[$]"). by apply: Hh.
Qed.

Lemma val_in_through_bij bij v av ih1 ih:
  i2a_val_rel_pure ih1 v av →
  ih1 = i2a_combine_bij ih bij →
  ([∗ map] p2↦p1 ∈ hb_shared bij, heap_bij_shared p1 p2) -∗
  val_in_bij (val_through_bij bij v) v.
Proof.
  iIntros (Hp ?) "Hbij". destruct v => //; simplify_eq/=.
  move: Hp => [?[? /i2a_combine_bij_lookup_Some [?[??]]]]. simplify_map_eq.
  iSplit; [done|]. iApply (big_sepM_lookup with "[$]").
  by apply hb_shared_lookup_Some.
Qed.

Lemma i2a_val_rel_pure_combine ih bij v1 v2 av :
  i2a_val_rel_pure ih v1 av →
  val_in_bij_pure bij v1 v2 →
  i2a_val_rel_pure (i2a_combine_bij ih bij) v2 av.
Proof.
  move => ??. destruct v1, v2; simplify_eq/= => //. destruct_all?. simplify_eq.
  split!; [by f_equal|]. apply i2a_combine_bij_lookup_Some. naive_solver.
Qed.

Lemma i2a_args_pure_combine ih bij o vs1 vs2 rs :
  i2a_args_pure ih o vs1 rs →
  Forall2 (val_in_bij_pure bij) vs1 vs2 →
  i2a_args_pure (i2a_combine_bij ih bij) o vs2 rs.
Proof.
  move => Ha /Forall2_same_length_lookup[? Hl] i ? Hvs2. move: (Hvs2) => /(lookup_lt_Some _ _ _)?.
  have [??]: is_Some (vs1 !! i) by apply lookup_lt_is_Some; lia.
  have [?[?[?[??]]]] := Ha _ _ ltac:(done).
  split!. apply: i2a_val_rel_pure_combine; [done|naive_solver].
Qed.

Definition hb_shared_rev (bij : heap_bij) : gmap prov prov :=
  list_to_map $ (λ x, (x.2, x.1)) <$> map_to_list (hb_shared bij).

Lemma hb_shared_rev_lookup_Some bij ps pi :
  hb_shared_rev bij !! pi = Some ps ↔ hb_bij bij !! ps = Some (HBShared pi).
Proof.
  rewrite /hb_shared_rev -elem_of_list_to_map. 2: {
    rewrite -list_fmap_compose. apply NoDup_fmap_2_strong; [|apply NoDup_map_to_list].
    move => [??][??] /elem_of_map_to_list/hb_shared_lookup_Some? /elem_of_map_to_list /hb_shared_lookup_Some?/= ?.
    by simplify_bij.
  }
  rewrite elem_of_list_fmap -hb_shared_lookup_Some.
  split.
  - move => [[??] /=[? /elem_of_map_to_list ?]]. naive_solver.
  - move => ?. eexists (_, _). rewrite elem_of_map_to_list. naive_solver.
Qed.


Lemma i2a_heap_shared_agree_pure_combine ih bij h1 h2 h m :
  i2a_heap_shared_agree_pure h1 ih m →
  heap_in_bij_pure bij h2 h →
  (∀ l v, h_heap h2 !! l = Some v → l.1 ∈ hb_shared_i bij → h1 !! l = Some v) →
  i2a_heap_shared_agree_pure (h_heap h) (i2a_combine_bij ih bij) m.
Proof.
  move => ? Hbij Hincl.
  apply: (i2a_heap_shared_agree_pure_impl (λ p, hb_shared_rev bij !! p)); [done|].
  move => l2 ??? /i2a_combine_bij_lookup_Some[pi [??]].
  setoid_rewrite hb_shared_rev_lookup_Some.
  have [Hiff Hv]:= Hbij _ _ l2.2 ltac:(done). rewrite -surjective_pairing in Hiff.
  have [??]: is_Some (h_heap h2 !! (pi, l2.2)) by naive_solver.
  split!.
  - apply Hincl; [done|]. apply elem_of_hb_shared_i. naive_solver.
  - move => ??. apply: i2a_val_rel_pure_combine; [done|]. naive_solver.
Qed.

Lemma i2a_bij_vertical m σ `{!VisNoAll m} ins fns f2i gp:
  trefines (MS (imp_to_asm ins fns f2i gp (imp_heap_bij m))
               (initial_imp_to_asm_state (imp_heap_bij m) (initial_imp_heap_bij_state m σ)))
           (MS (imp_to_asm ins fns f2i gp m)
               (initial_imp_to_asm_state m σ))
.
Proof.
  unshelve apply: mod_prepost_combine. {
    exact (λ pl '(I2A csa lra) _ '(I2A cs lr) Pa Pb P,
      csa = cs ∧
      lra = lr ∧
      ∃ mem' moa mo,
        (* mem' = moa ∪ mo ∧ *)
    if pl is Env then
      ∃ iha bijb hob ho hprev mh hb,
        moa = mem' ∖ mo ∧
        hob = i2a_combine_priv (i2a_ih_shared iha) bijb hb ∖ ho ∧
        (P ⊣⊢ i2a_mem_map mo ∗ i2a_mem_map mh ∗
           ([∗ map] p↦a ∈ i2a_combine_bij (i2a_ih_shared iha) bijb, i2a_heap_shared p a) ∗
           ([∗ map] p↦h ∈ ho, i2a_heap_constant p h)) ∧
        satisfiable (Pa ∗
                        i2a_mem_auth mem' ∗ i2a_heap_auth iha ∗
                        i2a_mem_map moa ∗
                        ([∗ map]p↦a ∈ i2a_ih_shared iha, i2a_heap_shared p a)) ∧
        satisfiable (Pb ∗ heap_bij_auth bijb ∗
           ([∗ map] p2↦p1∈ hb_shared bijb, heap_bij_shared p1 p2) ∗
           ([∗ map] p↦h∈ hob, heap_bij_const_s p h) ∗
           heap_in_bij bijb hprev hb
 ) ∧
        mo ⊆ mem' ∧
        ho ⊆ i2a_combine_priv (i2a_ih_shared iha) bijb hb ∧
        hb_provs_i bijb ⊆ h_provs hprev ∧
        dom _ iha ⊆ h_provs hprev ∧
        heap_preserved (i2a_ih_constant iha) hprev ∧
        heap_preserved (hb_priv_i bijb) hprev ∧
        i2a_combine_priv_shared (i2a_ih_shared iha) bijb hb ⊆ ho ∧
        i2a_heap_shared_agree_pure (filter (λ x, x.1.1 ∉ hb_shared_i bijb) (h_heap hprev))
                                   (i2a_ih_shared iha) mh
    else
      ∃ iha bijb ih hob ho hb,
        mo = mem' ∖ moa ∧
        ho = i2a_ih_constant ih ∖ hob ∧
        i2a_ih_shared ih = i2a_combine_bij (i2a_ih_shared iha) bijb ∧
        i2a_ih_constant ih = i2a_combine_priv (i2a_ih_shared iha) bijb hb ∧
        satisfiable (P ∗ i2a_mem_auth mem' ∗ i2a_heap_auth ih ∗ i2a_mem_map mo ∗
                        ([∗ map] p↦a ∈ i2a_ih_shared ih, i2a_heap_shared p a) ∗
                        ([∗ map] p↦h ∈ ho, i2a_heap_constant p h)) ∧
        (Pa ⊣⊢ i2a_mem_map moa ∗ ([∗ map] p↦a ∈ i2a_ih_shared iha, i2a_heap_shared p a)) ∧
        (Pb ⊣⊢ ([∗ map] p2↦p1∈ hb_shared bijb, heap_bij_shared p1 p2) ∗
           ([∗ map] p↦h∈ hob, heap_bij_const_s p h)) ∧
        moa ⊆ mem' ∧
        hob ⊆ i2a_ih_constant ih
). }
  { split!. all: admit. }
  all: move => [csa lra] [] [cs lr] Pa Pb P [? e] ?/=; destruct_all?; simplify_eq.
  - move: e => []//= pc regs mem b ? h. move: b => [] /=.
    + move => i f args ???? P' HP'. eexists true => /=. setoid_subst.
      rename select (satisfiable (Pa ∗ _)) into HPa.
      rename select (satisfiable (Pb ∗ _)) into HPb.
      rename select (heap_preserved (i2a_ih_constant iha) hprev) into Hpreva.
      rename select (heap_preserved (hb_priv_i bijb) hprev) into Hprevb.
      iSatStart HP'. iIntros!.
      iDestruct select (i2a_mem_inv _ _ _) as (?) "(Hgp&Hsp&Hmauth)".
      iDestruct (i2a_mem_lookup_big' mo with "[$] [$]") as %?.
      iDestruct (i2a_mem_uninit_alt1 with "[$]") as (? Hvslen) "Hsp"; [lia|].
      iDestruct select (i2a_heap_inv _) as (ih ??) "[Hsh [Hhag Hh]]".
      iDestruct (i2a_heap_shared_lookup_big' (i2a_combine_bij _ _) with "[$] [$]") as %?.
      iDestruct (i2a_heap_lookup_big' with "[$] [$]") as %?.
      iDestruct (i2a_heap_shared_agree_to_pure with "[$] [$]") as (??) "[? ?]".
      iDestruct (i2a_args_to_pure with "[$] [$]") as %?.
      iSatStop HP'.

      have [| | | | |ih' [bijb' ?]]:= i2a_combine_extend (h_provs hprev) iha bijb ih ho hb => //.
      destruct_all?.
      rename select (i2a_ih_shared ih = _) into Hihs.
      rename select (i2a_ih_constant ih = _) into Hihc.
      rename select (hb_priv_i bijb = hb_priv_i bijb') into Hpriveq.
      rename select (i2a_ih_constant ih ∖ (hb_priv_s bijb' ∖ ho) = ho) into Hhoeq.

      iSatStartBupd HPa. iIntros!.
      iMod (i2a_mem_update_all1 mem with "[$] [$]") as "[Ha Hmo]"; [done..|].
      iMod (i2a_heap_alloc_shared_big' with "[$]") as "[Hih ?]"; [done..|]. iModIntro.
      iSatStop HPa.
      efeed pose proof i2a_mem_transfer as H'.
      2: { iSatMono HPa. iFrame. iAccu. }
      { iSatMono HP'. iFrame. iAccu. }
      clear HPa HP'. move: H' => [HP' HPa].
      efeed pose proof i2a_mem_transfer as H'.
      2: { iSatMono HPa. iIntros!. iFrame. iAccu. }
      { iSatMono HP'. iIntros!. iFrame. iAccu. }
      clear HPa HP'. move: H' => [HP' HPa].
      efeed pose proof i2a_mem_transfer as H'.
      2: { iSatMono HPa. iIntros!. iFrame. iAccu. }
      { iSatMono HP'. iIntros!. iFrame. iAccu. }
      clear HPa HP'. move: H' => [HP' HPa].
      efeed pose proof i2a_mem_transfer as H'.
      2: { iSatMono HPa. iIntros!. iFrame. iAccu. }
      { iSatMono HP'. iIntros!. iFrame. iAccu. }
      clear HPa HP'. move: H' => [HP' HPa].

      iSatStart HP'. iIntros!. iDestruct (i2a_mem_lookup_big' with "[$] [$]") as %?. iSatStop HP'.

      iSatStartBupd HPb. iIntros!.
      have ? : ∀ p1 p2 : prov, (hb_shared bijb' ∖ hb_shared bijb) !! p2 = Some p1 → p1 ∉ hb_provs_i bijb. {
        admit.
      }
      unshelve iMod (heap_bij_alloc_big (hb_shared bijb' ∖ hb_shared bijb) with "[$]") as "[? Hs2]"; [done| |]. {
        admit.
      }
      iDestruct select ([∗ map] _↦_∈hb_shared _, heap_bij_shared _ _)%I as "Hs1".
      iDestruct (big_sepM_union_2 with "Hs1 Hs2") as "Hs". rewrite map_difference_union //.
      iDestruct "Hs" as "#Hs".
      iDestruct select ([∗ map] _↦_∈_, heap_bij_const_s _ _)%I as "Hp".
      iMod (heap_bij_update_all bijb' _ ho with "[$] [Hp]") as "[??]".
      { admit. } { done. } { rewrite i2a_combine_priv_diff //. admit. }
      iModIntro.
      iSatStop HPb.

      split; [done|].
      eexists (heap_merge (heap_restrict (heap_through_bij bijb' h)
                                         (λ p, p ∈ dom (gset _) (ih' ∪ i2a_ih_shared iha)))
                  (heap_restrict hprev
                                 (λ x, x ∉ dom (gset _) (ih' ∪ i2a_ih_shared iha) ∨ x ∉ hb_shared_i bijb'))).
      eexists _, _, (val_through_bij bijb' <$> args).
      split!.
      * iSatMono HPa. iIntros!.
        iAssert ([∗ map] p↦a ∈ i2a_ih_shared ((I2AShared <$> ih') ∪ iha), i2a_heap_shared p a)%I as "#Hsh". {
          rewrite i2a_ih_shared_union // i2a_ih_shared_fmap. by iApply (big_sepM_union_2 with "[$]").
        } iFrame "Hsh".
        iDestruct select (i2a_mem_map (mem ∖ _)) as "$". iFrame.
        rewrite -!(assoc bi_sep). iSplit; [done|].
        iDestruct (i2a_mem_uninit_alt2 with "[$]") as "Huninit". rewrite Hvslen Z2Nat.id; [|lia].
        iFrame "Huninit".
        rewrite !bi.sep_exist_r. iExists _.
        rewrite -!(assoc bi_sep).
        iDestruct select (i2a_heap_auth _) as "$".

        iSplit!.
        -- rewrite heap_merge_provs !heap_restrict_provs dom_union_L heap_through_bij_provs.
           apply union_mono; [|done]. admit. (* provable with maybe tweaks to the result of i2a_combine_extend *)
        -- move => l ?. rewrite i2a_ih_constant_union // i2a_ih_constant_fmap_shared left_id_L.
           move => ? /=.
           have ? : l.1 ∉ dom (gset prov) (ih' ∪ i2a_ih_shared iha). { admit. (* provable by map disjoint *) }
           rewrite lookup_union_r. 2: { apply map_filter_lookup_None. naive_solver. }
           rewrite map_filter_lookup_true; [by apply Hpreva|naive_solver].
        -- iApply i2a_heap_shared_agree_union. {
             apply map_disjoint_spec => -[p o] ?? /map_filter_lookup_Some[/=/heap_through_bij_Some??].
             move => /map_filter_lookup_Some[?[//|]] /=. destruct_all?.
             apply. apply elem_of_hb_shared_i. naive_solver.
           }
           iDestruct select (i2a_mem_map mh) as "Hmh".
           iSplitR "Hmh".
           ++ iApply i2a_heap_shared_agree_of_pure; [|done..].
              apply: (i2a_heap_shared_agree_pure_impl (λ p, hb_shared bijb' !! p)); [done|].
              move => ??? /map_filter_lookup_Some [/heap_through_bij_Some[?[?[?[??]]]] ?] Hsh. simplify_eq/=.
              split!.
              ** by apply hb_shared_lookup_Some.
              ** done.
              ** rewrite Hihs. apply i2a_combine_bij_lookup_Some. split!.
                 by rewrite i2a_ih_shared_union // i2a_ih_shared_fmap in Hsh.
              ** move => ??. apply: i2a_val_rel_pure_through_bij; [done|].
                 by rewrite i2a_ih_shared_union // i2a_ih_shared_fmap.
           ++ iApply i2a_heap_shared_agree_impl.
              2: { iApply (i2a_heap_shared_agree_of_pure with "[] [$]"); [done|].
                   rewrite i2a_ih_shared_union // big_sepM_union //. 2: by apply map_disjoint_omap.
                   by iDestruct!. }
              move => ??? /map_filter_lookup_Some[? Hne] Ha.
              move: Hne => [Hne|Hne]; simplify_eq/=. {
                contradict Hne. apply elem_of_dom.
                move: Ha. rewrite -i2a_ih_shared_Some i2a_ih_shared_union // i2a_ih_shared_fmap. done.
              }
              split.
              ** apply map_filter_lookup_Some => /=. split; [done|].
                 contradict Hne.
                 (* provable from hb_shared bijb ⊆ hb_shared bijb' *)
                 admit.
              ** move: Ha => /lookup_union_Some_raw[?|[??] //].
                 (* Use the fact that the elements in ih' are not in h_provs hprev *)
                 admit.
        -- iApply (i2a_args_of_pure (ih' ∪ i2a_ih_shared iha)).
           ++ by apply: i2a_args_pure_through_bij.
           ++ by iApply (big_sepM_union_2 with "[$]").
      * iSatMono HPb. iIntros!. iFrame "Hs". iFrame. iSplit!.
        -- iExists _. iFrame. repeat iSplit.
           ++ iPureIntro. by etrans.
           ++ iPureIntro. rewrite heap_merge_provs !heap_restrict_provs heap_through_bij_provs.
              move => ? /elem_of_hb_provs_i[[? Hin]|[??]]; apply elem_of_union.
              ** right. revert select (hb_provs_i bijb ⊆ h_provs hprev). apply.
                 apply elem_of_hb_provs_i. rewrite Hpriveq. naive_solver.
              ** left. apply elem_of_hb_shared_i. naive_solver.
           ++ iPureIntro. apply: heap_preserved_mono; [done|]. rewrite Hihc.
              apply map_subseteq_spec => ??. rewrite hb_priv_s_lookup_Some i2a_combine_priv_Some.
              naive_solver.
           ++ iPureIntro. rewrite -Hpriveq.
              move => [p o] ?? /=. rewrite lookup_union_r. 2: {
                apply map_filter_lookup_None. left.
                apply eq_None_not_Some => /heap_through_bij_is_Some[?[/hb_disj]].
                rewrite -Hpriveq. naive_solver.
              }
              rewrite map_filter_lookup_true; [by apply Hprevb|].
              move => ?? /=. right. move => /elem_of_hb_shared_i[??].
              efeed pose proof hb_disj as HNone; [done|]. rewrite -Hpriveq in HNone. naive_solver.
           ++ done.
           ++ iIntros (p1 p2 o ?) => /=.
              destruct (decide (p1 ∈ dom (gset _) (ih' ∪ i2a_ih_shared iha))).
              ** rewrite lookup_union_l'.
                 2: { apply map_filter_lookup_None. right => ?? /=. rewrite elem_of_hb_shared_i. naive_solver. }
                 rewrite map_filter_lookup_true; [|done].
                 iSplit; [iPureIntro; by apply heap_through_bij_is_Some'|].
                 iIntros (??[?[?[?[??]]]]%heap_through_bij_Some ?). simplify_bij.
                 iApply (val_in_through_bij with "[$]"); [|done].
                 admit. (* use i2a_heap_shared_agree_pure (h_heap h) (i2a_ih_shared ih) m0 *)
              ** rewrite lookup_union_r. 2: { apply map_filter_lookup_None. naive_solver. }
                 rewrite map_filter_lookup_true; [|naive_solver].
                 revert select (heap_preserved (i2a_ih_constant ih) h) => Hpre.
                 have -> : h_heap h !! (p2, o) = h_heap hb !! (p2, o). {
                   rewrite -(h_block_lookup hb). apply Hpre.
                   rewrite Hihc /=. apply: lookup_weaken; [|by apply map_union_subseteq_l].
                   apply i2a_combine_priv_shared_Some. split!. by apply not_elem_of_dom. }
                 iDestruct select (heap_in_bij _ _ _) as "Hbij".
                 iApply ("Hbij" $! p1 p2 o). iPureIntro.
                 admit.
        -- rewrite big_sepL2_fmap_l. iApply big_sepL_sepL2_diag.
           iApply big_sepL_intro. iIntros "!>" (???).
           revert select (i2a_args_pure  _ _ _ _) => /(_ _ _ ltac:(done))[?[?[?[??]]]].
           by iApply (val_in_through_bij with "[$]").
      * by rewrite i2a_ih_shared_union // i2a_ih_shared_fmap.
      * rewrite {1}Hihc i2a_ih_shared_union; [|done]. by rewrite i2a_ih_shared_fmap.
      * iSatMono HP'. iIntros!. rewrite Hhoeq. iFrame.
        rewrite !map_difference_id; [by iFrame|done..].
      * by apply map_subseteq_difference_l.
      * rewrite Hihc. apply map_union_subseteq_r';
           [by apply i2a_combine_priv_shared_priv_s_disj|by apply map_subseteq_difference_l].
    + move => v av rs' cs' ?? P' HP'. eexists false => /=. simplify_eq. setoid_subst.
      (*
      rename select (satisfiable (Pa ∗ _)) into HPa.
      rename select (satisfiable (Pb ∗ _)) into HPb.
      rename select (i2a_heap_agree hprev iha) into Hpa.
      iSatStart HP'. iIntros!.
      iDestruct select (i2a_mem_inv _ _ _) as (?) "(Hgp&Hsp&Hmauth)".
      iDestruct (i2a_mem_lookup_big' mo with "[$] [$]") as %?.
      iDestruct (i2a_mem_uninit_alt1 with "[$]") as (? Hvslen) "Hsp"; [lia|].
      iDestruct select (i2a_heap_inv _) as (ih ?) "[Hsh [Hhag Hh]]".
      iDestruct (i2a_heap_shared_lookup_big1 with "[$] [$]") as %?.
      iDestruct (i2a_heap_shared_lookup_big1 (i2a_combine_bij _ _) with "[$] [$]") as %?.
      iDestruct (i2a_heap_lookup_big1 with "[$] [$]") as %?.
      iDestruct (i2a_heap_shared_agree_to_pure with "[$] [$]") as (??) "[? ?]".
      iDestruct (i2a_val_rel_to_pure with "[$] [$]") as %?.
      iSatStop HP'.

      have [//|//|//|//|ih' [bijb' ?]]:= i2a_combine_extend iha bijb ih ho h. destruct_all?.

      iSatStartBupd HPa. iIntros!.
      iMod (i2a_mem_update_all1 mem with "[$] [$]") as "[Ha Hmo]"; [done..|].
      iMod (i2a_heap_alloc_shared_big1 with "[$]") as "[Hih ?]"; [done..|]. iModIntro.
      iSatStop HPa.
      efeed pose proof i2a_mem_transfer as H'.
      2: { iSatMono HPa. iFrame. iAccu. }
      { iSatMono HP'. iFrame. iAccu. }
      clear HPa HP'. move: H' => [HP' HPa].
      efeed pose proof i2a_mem_transfer as H'.
      2: { iSatMono HPa. iIntros!. iFrame. iAccu. }
      { iSatMono HP'. iIntros!. iFrame. iAccu. }
      clear HPa HP'. move: H' => [HP' HPa].
      efeed pose proof i2a_mem_transfer as H'.
      2: { iSatMono HPa. iIntros!. iFrame. iAccu. }
      { iSatMono HP'. iIntros!. iFrame. iAccu. }
      clear HPa HP'. move: H' => [HP' HPa].
      split; [done|].
      eexists (heap_merge (heap_restrict (heap_through_bij bijb' h)
                                         (λ p, p ∈ ih' ∪ i2a_ih_shared iha))
                  (heap_restrict hprev
                                 (λ x, x ∉ ih' ∪ i2a_ih_shared iha ∨ x ∉ hb_shared_i bijb'))).
      eexists (val_through_bij bijb' v).
      split!.
      * done.
      * iSatMono HPa. iIntros!.
        iDestruct select (i2a_mem_map (mem ∖ _)) as "$". iFrame.
        rewrite -!(assoc bi_sep). iSplit; [done|].
        iDestruct (i2a_mem_uninit_alt2 with "[$]") as "Huninit". rewrite Hvslen Z2Nat.id; [|lia].
        iFrame "Huninit".
        rewrite !bi.sep_exist_r. iExists _.
        rewrite -!(assoc bi_sep).
        iDestruct select (i2a_heap_auth _) as "$".
        iAssert ([∗ map] p↦a ∈ i2a_ih_shared ((I2AShared <$> ih') ∪ iha), i2a_heap_shared p a)%I as "#$". {
          admit.
        }

        iSplit!.
        -- split.
           ++ rewrite heap_merge_provs !heap_restrict_provs dom_union_L. admit.
           ++ move => /= ?? /lookup_union_Some_raw. rewrite lookup_fmap.
              move => [/fmap_Some[?[?//]]|[/fmap_None ??]]. rewrite lookup_union_r. 2: {
                apply map_filter_lookup_None. right => ?? /=. admit. }
              rewrite map_filter_lookup_true; [by apply Hpa|].
              admit.
        -- admit. (* TODO, not clear yet *)
        -- iApply (i2a_val_rel_of_pure (ih' ∪ i2a_ih_shared iha)).
           ++ by apply: i2a_val_rel_pure_through_bij.
           ++ by iApply (big_sepM_union_2 with "[$]").
      * iSatMono HPb. iIntros!. iFrame.
        admit.
      * by instantiate (1:= [_]).
      * iSatMono HP'. iIntros!. iFrame.
        admit.
      * by apply map_subseteq_difference_l.
      *)
      admit.
  - move => vs hb' Pb' HPb' ? i rs' mem''.
    destruct e as [fn args h|v h]; simplify_eq/=.
    + move => ret ????? Pa' HPa'. setoid_subst.
      rename select (satisfiable (P ∗ _)) into HP.
      rename select (i2a_ih_shared ih = _) into Hihs.
      rename select (i2a_ih_constant ih = _) into Hihc.

      iSatStart HPb'. iIntros!.
      iDestruct select (heap_bij_inv _ _) as (bijb' ? ? ? ?) "(Hsh&Hh&Hbij)".
      iDestruct (val_in_bij_to_pure_big with "[$] [$]") as %?.
      iDestruct (heap_bij_const_s_lookup_big with "[$] [$]") as %?.
      iDestruct (heap_bij_shared_lookup_big with "[$] [$]") as %?.
      iDestruct (heap_in_bij_to_pure with "[$] [$]") as %?.
      iSatStop HPb'.

      iSatStart HPa'. iIntros!.
      iDestruct select (i2a_mem_inv _ _ _) as (?) "(Hgp&Hsp&Hmauth)".
      iDestruct (i2a_mem_lookup_big' moa with "[$] [$]") as %?.
      iDestruct (i2a_mem_uninit_alt1 with "[$]") as (? Hvslen) "Hsp"; [lia|].
      iDestruct select (i2a_heap_inv _) as (iha' ??) "[Hsh [Hhag Hh]]".
      rewrite -(map_filter_union_complement (λ x, x.1.1 ∈ hb_shared_i bijb') (h_heap hb')).
      rewrite i2a_heap_shared_agree_union. 2: apply map_disjoint_filter_complement.
      iDestruct "Hhag" as "[Hhag1 Hhag2]".
      iDestruct (i2a_heap_shared_agree_to_pure with "Hhag1 [$]") as (mhag1 ?) "[? ?]".
      iDestruct (i2a_heap_shared_agree_to_pure with "Hhag2 [$]") as (mhag2 ?) "[? ?]".
      iDestruct (i2a_heap_shared_lookup_big' with "[$] [$]") as %?.
      iDestruct (i2a_args_to_pure with "[$] [$]") as %?.
      iSatStop HPa'.

      have Hdisj := i2a_combine_bij_priv_disj (i2a_ih_shared iha') bijb' h.

      iSatStartBupd HP. iIntros!.
      iMod (i2a_mem_update_all1 mem'' with "[$] [$]") as "[Ha Hmo]"; [done..|].
      iMod (i2a_heap_update_all
              (i2a_combine_bij (i2a_ih_shared iha') bijb')
              (i2a_combine_priv (i2a_ih_shared iha') bijb' h)
             with "[$] [$] [$]") as "(?&?&?)"; [done| | | |].
      { etrans; [done|]. apply map_union_subseteq_r. apply i2a_combine_priv_shared_priv_s_disj. }
      { rewrite Hihs. by apply i2a_combine_bij_mono. }
      { move: Hdisj => /map_disjoint_dom. by rewrite !dom_fmap. }
      iModIntro.
      iSatStop HP.

      efeed pose proof i2a_mem_transfer as H'.
      2: { iSatMono HP. iFrame. iAccu. }
      { iSatMono HPa'. iFrame. iAccu. }
      clear HPa' HP. move: H' => [HPa' HP].
      efeed pose proof i2a_mem_transfer as H'.
      2: { iSatMono HP. iIntros!. iFrame. iAccu. }
      { iSatMono HPa'. iIntros!. iFrame. iAccu. }
      clear HPa' HP. move: H' => [HPa' HP].
      efeed pose proof i2a_mem_transfer as H'.
      2: { iSatMono HP. iIntros!. iFrame. iAccu. }
      { iSatMono HPa'. iIntros!. iFrame. iAccu. }
      clear HPa' HP. move: H' => [HPa' HP].
      efeed pose proof i2a_mem_transfer as H'.
      2: { iSatMono HP. iIntros!. iFrame. iAccu. }
      { iSatMono HPa'. iIntros!. iFrame. iAccu. }
      clear HPa' HP. move: H' => [HPa' HP].

      split!. 2: {
        iSatMono HPa'. iIntros!.
        iDestruct (i2a_mem_lookup_big' with "[$] [$]") as %?.
        iFrame. by erewrite map_difference_id.
      }
      * iSatMono HP. iIntros!.
        iDestruct select (i2a_mem_map (mem'' ∖ _)) as "$".
        iDestruct select (i2a_mem_map mhag2) as "$".
        iDestruct select ([∗ map] _↦_ ∈ _, i2a_heap_shared _ _)%I as "#Hsh". iFrame. iFrame "Hsh".
        rewrite -!(assoc bi_sep).
        iSplit; [done|].
        iDestruct (i2a_mem_uninit_alt2 with "[$]") as "Hsp". rewrite Hvslen Z2Nat.id; [|lia]. iFrame.
        iSplitL.
        -- iExists _. iFrame. repeat iSplit.
           ++ iPureIntro. etrans; [|done]. rewrite dom_union_L !dom_fmap_L. apply union_least.
              ** move => ? /elem_of_dom[?/i2a_combine_bij_lookup_Some?]. apply elem_of_dom. naive_solver.
              ** move => ? /elem_of_dom[?/i2a_combine_priv_Some?]. apply elem_of_dom. naive_solver.
           ++ iPureIntro. rewrite i2a_ih_constant_union // i2a_ih_constant_fmap_shared left_id_L.
              rewrite i2a_ih_constant_fmap.
              move => ?? /i2a_combine_priv_Some[?|?].
              ** revert select (heap_preserved (hb_priv_s bijb') h). apply. by apply hb_priv_s_lookup_Some.
              ** destruct_all?; simplify_eq. by rewrite h_block_lookup -surjective_pairing.
           ++ by rewrite i2a_ih_shared_union // i2a_ih_shared_fmap i2a_ih_shared_fmap_constant right_id_L.
           ++ iApply (i2a_heap_shared_agree_of_pure with "[] [$]").
              all: rewrite i2a_ih_shared_union // i2a_ih_shared_fmap i2a_ih_shared_fmap_constant right_id_L //.
              apply: i2a_heap_shared_agree_pure_combine; [done..|].
              move => ????. by apply map_filter_lookup_Some.
        -- iSplit; [|done]. iApply (i2a_args_of_pure with "Hsh"). by apply: i2a_args_pure_combine.
      * iSatMono HPb'. iFrame.
        erewrite map_difference_id; [by iFrame|].
        etrans; [done|]. apply map_union_subseteq_r. apply i2a_combine_priv_shared_priv_s_disj.
      * by apply map_subseteq_difference_l.
      * by apply map_subseteq_difference_l.
      * rewrite /i2a_combine_priv map_difference_union_distr. apply map_union_subseteq_l'.
        rewrite map_difference_disj_id //. apply: map_disjoint_weaken_r; [|done].
        apply i2a_combine_priv_shared_priv_s_disj.
      * done.
    + move => av lr' cs' ??? Pa' HPa'. simplify_eq/=. setoid_subst.
      (* split!. *)
      admit.
Admitted.
