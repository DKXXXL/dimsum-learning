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
Lemma heap_bij_update_all bij bij' ho :
  ho ⊆ hb_priv_s bij' →
  ho ⊆ hb_priv_s bij →
  hb_shared bij' ⊆ hb_shared bij →
  hb_priv_i bij' = hb_priv_i bij →
  heap_bij_auth bij' -∗
  ([∗ map] p2↦p1∈ hb_shared bij', heap_bij_shared p1 p2) -∗
  ([∗ map] p↦h∈ hb_priv_s bij' ∖ ho, heap_bij_const_s p h) ==∗
  heap_bij_auth bij ∗
  ([∗ map] p2↦p1∈ hb_shared bij, heap_bij_shared p1 p2) ∗
  ([∗ map] p↦h∈ hb_priv_s bij ∖ ho, heap_bij_const_s p h).
Proof.
  iIntros (????) "Hauth Hsh Hho".
Admitted.

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

Definition i2a_combine_priv (ih : gmap prov Z) (bij : heap_bij) : gset prov :=
  dom _ $
      omap (λ v, if v is HBShared pi then
               if ih !! pi is Some a then
                 None
               else
                 Some tt
             else
               None) bij.(hb_bij).

Lemma i2a_combine_priv_elem_of ih bij p:
  p ∈ i2a_combine_priv ih bij ↔ ∃ pi, hb_bij bij !! p = Some (HBShared pi) ∧ ih !! pi = None.
Proof.
  rewrite /i2a_combine_priv elem_of_dom /is_Some. setoid_rewrite lookup_omap_Some.
  split => ?; destruct_all?.
  - do 2 case_match => //. simplify_eq. naive_solver.
  - eexists tt, (HBShared _). by simplify_map_eq.
Qed.

(* Lemma i2a_combine_extend iha bijb ih ho h : *)
(*   i2a_combine_bij (i2a_ih_shared iha) bijb ⊆ i2a_ih_shared ih → *)
(*   ho ⊆ hb_priv_s bijb → *)
(*   ho ⊆ i2a_ih_constant ih → *)
(*   i2a_heap_agree h ih → *)
(*   ∃ ih' bijb', *)
(*     i2a_ih_shared ih = i2a_combine_bij (ih' ∪ i2a_ih_shared iha) bijb' ∧ *)
(*     (I2AShared <$> ih') ##ₘ iha ∧ *)
(*     hb_priv_s bijb' = i2a_ih_constant ih ∧ *)
(*     ho ⊆ hb_priv_s bijb' ∧ *)
(*     heap_preserved (hb_priv_s bijb') h ∧ *)
(*     hb_shared bijb ⊆ hb_shared bijb' ∧ *)
(*     hb_priv_i bijb = hb_priv_i bijb' *)
(* . *)
(* Proof. Admitted. *)

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
           (ho : gmap prov (gmap loc val)) :=
  (HBShared <$> (hb_shared bijb ∪ fresh_map ((dom _ (i2a_ih_shared ih)) ∖ hb_shared_s bijb) X)) ∪
  (* (HBConstant <$> ho) ∪ *)
  (HBConstant <$> i2a_ih_constant ih).

Lemma i2a_combine_heap_bij_bij_shared X bijb ps pi ih ho:
  i2a_combine_heap_bij_bij X ih bijb ho !! ps = Some (HBShared pi) ↔
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
  - left.
    (* left. *)
    split!. naive_solver.
  - fresh_map_learn. destruct_all?.
    (* left.  *)
    left. split!. naive_solver.
Qed.

Lemma i2a_combine_heap_bij_bij_priv_s X bijb ps ih ho h:
  i2a_combine_heap_bij_bij X ih bijb ho !! ps = Some (HBConstant h) ↔
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

Program Definition i2a_combine_heap_bij (X : gset prov) (ih : gmap prov imp_to_asm_elem) (bijb : heap_bij) ho
 (H1 : hb_provs_i bijb ⊆ X) : heap_bij :=
  HeapBij (i2a_combine_heap_bij_bij X ih bijb ho) (hb_priv_i bijb) _ _.
Next Obligation.
  move => X ih bijb ho HX ps pi.
  rewrite !i2a_combine_heap_bij_bij_shared // => -[?|?]; [by apply: hb_disj|].
  apply eq_None_ne_Some => ??.
  have : (pi ∈ hb_provs_i bijb) by rewrite elem_of_hb_provs_i; naive_solver.
  fresh_map_learn. set_solver.
Qed.
Next Obligation.
  move => X ih bijb ho HX pi ps ps'.
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

Lemma i2a_combine_extend (X : gset prov) iha bijb ih ho :
  i2a_combine_bij (i2a_ih_shared iha) bijb ⊆ i2a_ih_shared ih →
  ho ⊆ i2a_ih_constant ih →
  i2a_combine_priv (i2a_ih_shared iha) bijb ⊆ dom _ ho →
  ho ⊆ hb_priv_s bijb →
  dom _ iha ⊆ X →
  hb_provs_i bijb ⊆ X →
  (* ho ⊆ hb_priv_s bijb → *)
  (* ho ⊆ i2a_ih_constant ih → *)
  (* i2a_heap_agree h ih → *)
  ∃ ih' bijb',
    i2a_ih_shared ih = i2a_combine_bij (ih' ∪ i2a_ih_shared iha) bijb' ∧
    (I2AShared <$> ih') ##ₘ iha ∧
    hb_priv_s bijb' ⊆ i2a_ih_constant ih ∧
    ho ⊆ hb_priv_s bijb' ∧
    (* heap_preserved (hb_priv_s bijb') h ∧ *)
    hb_shared bijb ⊆ hb_shared bijb' ∧
    hb_priv_i bijb = hb_priv_i bijb'
.
Proof.
  move => Hcombine Hho Hpriv Hhob HXa HXb.
  have Hdisj : (I2AShared <$> (i2a_combine_i2a X ih bijb)) ##ₘ iha. {
    apply map_disjoint_spec => ???. rewrite lookup_fmap => /fmap_Some [?[/i2a_combine_i2a_Some[?[??]]?]] ?.
    fresh_map_learn. destruct_all?. simplify_eq. revert select (_ ∉ X). apply. apply HXa. by apply elem_of_dom.
  }
  have Hdisj2 : i2a_combine_priv (i2a_ih_shared iha) bijb ## dom _ (i2a_ih_shared ih). {
    apply elem_of_disjoint => ? /Hpriv.
    admit.
  }

  eexists (i2a_combine_i2a X ih bijb).
  eexists (i2a_combine_heap_bij X ih bijb ho HXb).
  split_and!.
  - apply map_eq => ps. apply option_eq => a. rewrite i2a_ih_shared_Some.
    rewrite i2a_combine_bij_lookup_Some /=.
    setoid_rewrite i2a_combine_heap_bij_bij_shared.
    setoid_rewrite lookup_union_Some. 2: {
     apply (map_disjoint_fmap I2AShared I2AShared). eapply map_disjoint_weaken_r; [done|]. admit.
    }
    setoid_rewrite i2a_combine_i2a_Some.
    setoid_rewrite i2a_ih_shared_Some.
    split => ?.
    + destruct (hb_shared bijb !! ps) as [pi|] eqn:Hps.
      * move: Hps => /hb_shared_lookup_Some Hps. eexists _. split; [by left|].
        split!.
        destruct (i2a_ih_shared iha !! pi) as [a'|] eqn:?.
        -- right. (* via Hcombine *) admit.
        -- exfalso. move: Hdisj2 => /elem_of_disjoint. apply.
           ++ apply i2a_combine_priv_elem_of. naive_solver.
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
      * (* via Hcombine *) admit.
      * fresh_map_learn. destruct_all?. exfalso. revert select (_ ∉ X). apply. apply HXa. by apply elem_of_dom.
  - done.
  - apply map_subseteq_spec => p h. rewrite hb_priv_s_lookup_Some /=.
    rewrite i2a_combine_heap_bij_bij_priv_s i2a_ih_constant_Some. naive_solver.
  - admit.
  - apply map_subseteq_spec => ??. rewrite !hb_shared_lookup_Some /= i2a_combine_heap_bij_bij_shared. naive_solver.
  - done.
Admitted.

(** * imp_to_asm.v ?! *)
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
      ∃ iha bijb hob ho hprev mh,
        moa = mem' ∖ mo ∧
        hob = hb_priv_s bijb ∖ ho ∧
        (P ⊣⊢ i2a_mem_map mo ∗ i2a_mem_map mh ∗
           ([∗ map] p↦a ∈ i2a_combine_bij (i2a_ih_shared iha) bijb, i2a_heap_shared p a) ∗
           ([∗ map] p↦h ∈ ho, i2a_heap_constant p h)) ∧
        satisfiable (Pa ∗
                        i2a_mem_auth mem' ∗ i2a_heap_auth iha ∗
                        i2a_mem_map moa ∗
                        ([∗ map]p↦a ∈ i2a_ih_shared iha, i2a_heap_shared p a)) ∧
        satisfiable (Pb ∗ heap_bij_auth bijb ∗
           ([∗ map] p2↦p1∈ hb_shared bijb, heap_bij_shared p1 p2) ∗
           ([∗ map] p↦h∈ hob, heap_bij_const_s p h)) ∧
        mo ⊆ mem' ∧
        ho ⊆ hb_priv_s bijb ∧
        hb_provs_i bijb ⊆ h_provs hprev ∧
        dom _ iha ⊆ h_provs hprev ∧
        heap_preserved (i2a_ih_constant iha) hprev ∧
        heap_preserved (hb_priv_i bijb) hprev ∧
        i2a_combine_priv (i2a_ih_shared iha) bijb ⊆ dom (gset prov) ho ∧
        i2a_heap_shared_agree_pure (filter (λ x, x.1.1 ∉ hb_shared_i bijb) (h_heap hprev))
                                   (i2a_ih_shared iha) mh
    else
      ∃ iha bijb ih hob ho,
        mo = mem' ∖ moa ∧
        ho = hb_priv_s bijb ∖ hob ∧
        i2a_ih_shared ih = i2a_combine_bij (i2a_ih_shared iha) bijb ∧
        satisfiable (P ∗ i2a_mem_auth mem' ∗ i2a_heap_auth ih ∗ i2a_mem_map mo ∗
                        ([∗ map] p↦a ∈ i2a_ih_shared ih, i2a_heap_shared p a) ∗
                        ([∗ map] p↦h ∈ ho, i2a_heap_constant p h)) ∧
        (Pa ⊣⊢ i2a_mem_map moa ∗ ([∗ map] p↦a ∈ i2a_ih_shared iha, i2a_heap_shared p a)) ∧
        (Pb ⊣⊢ ([∗ map] p2↦p1∈ hb_shared bijb, heap_bij_shared p1 p2) ∗
           ([∗ map] p↦h∈ hob, heap_bij_const_s p h)) ∧
        (* hb_priv_s bijb = i2a_ih_constant ih ∧ *)
        moa ⊆ mem' ∧
        hob ⊆ hb_priv_s bijb
). }
  { split!. all: admit. }
  all: move => [csa lra] [] [cs lr] Pa Pb P [? e] ?/=; destruct_all?; simplify_eq.
  - move: e => []//= pc regs mem b ? h. move: b => [] /=.
    + move => i f args ???? P' HP'. eexists true => /=. setoid_subst.
      rename select (satisfiable (Pa ∗ _)) into HPa.
      rename select (satisfiable (Pb ∗ _)) into HPb.
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

      have [| | | | | |ih' [bijb' ?]]:= i2a_combine_extend (h_provs hprev) iha bijb ih ho => //.
      destruct_all?.
      rename select (i2a_ih_shared ih = _) into Hih.

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
      iMod (heap_bij_update_all bijb' with "[$] [$] [$]") as "(Ha&#Hsh&Hho)"; [done..|]. iModIntro.
      iSatStop HPb.

      split; [done|].
      eexists (heap_merge (heap_restrict (heap_through_bij bijb' h)
                                         (λ p, p ∈ dom (gset _) (ih' ∪ i2a_ih_shared iha)))
                  (heap_restrict hprev
                                 (λ x, x ∉ dom (gset _) (ih' ∪ i2a_ih_shared iha) ∨ x ∉ hb_shared_i bijb'))).
      eexists _, _, (val_through_bij bijb' <$> args).
      split!.
      * iSatMono HPa. iIntros!.
        iAssert ([∗ map] p↦a ∈ i2a_ih_shared ((I2AShared <$> ih') ∪ iha), i2a_heap_shared p a)%I as "#$". {
          rewrite i2a_ih_shared_union // i2a_ih_shared_fmap. by iApply (big_sepM_union_2 with "[$]").
        }
        iDestruct select (i2a_mem_map (mem ∖ _)) as "$". iFrame.
        rewrite -!(assoc bi_sep). iSplit; [done|].
        iDestruct (i2a_mem_uninit_alt2 with "[$]") as "Huninit". rewrite Hvslen Z2Nat.id; [|lia].
        iFrame "Huninit".
        rewrite !bi.sep_exist_r. iExists _.
        rewrite -!(assoc bi_sep).
        iDestruct select (i2a_heap_auth _) as "$".

        iSplit!.
        -- rewrite heap_merge_provs !heap_restrict_provs dom_union_L heap_through_bij_provs. admit.
        -- admit.
(* move => /= ?? /lookup_union_Some_raw. rewrite lookup_fmap. *)
              (* move => [/fmap_Some[?[?//]]|[/fmap_None ??]]. rewrite lookup_union_r. 2: { *)
                (* apply map_filter_lookup_None. right => ?? /=. admit. } *)
              (* rewrite map_filter_lookup_true; [by apply Hpreva|]. *)
              (* admit. *)
        -- iApply i2a_heap_shared_agree_union. { admit. }
           iDestruct select (i2a_mem_map mh) as "Hmh".
           iSplitR "Hmh".
           ++ iApply i2a_heap_shared_agree_of_pure; [|done..].
              apply: (i2a_heap_shared_agree_pure_impl (λ p, hb_shared bijb' !! p)); [done|].
              move => ??? /map_filter_lookup_Some [/heap_through_bij_Some[?[?[?[??]]]] ?] Hsh. simplify_eq/=.
              split!.
              ** by apply hb_shared_lookup_Some.
              ** done.
              ** rewrite Hih. apply i2a_combine_bij_lookup_Some. split!.
                 by rewrite i2a_ih_shared_union // i2a_ih_shared_fmap in Hsh.
              ** move => ??. apply: i2a_val_rel_pure_through_bij; [done|].
                 by rewrite i2a_ih_shared_union // i2a_ih_shared_fmap.
           ++ iApply i2a_heap_shared_agree_impl.
              2: { iApply (i2a_heap_shared_agree_of_pure with "[] [$]"); [done|]. admit. }
              move => ??? /map_filter_lookup_Some[? Hne] Ha.
              move: Hne => [Hne|Hne]; simplify_eq/=.
              { contradict Hne. apply elem_of_dom. admit. }
              split.
              ** apply map_filter_lookup_Some => /=. split; [done|].
                 (* provable from hb_shared bijb ⊆ hb_shared bijb' *)
                 admit.
              ** move: Ha => /lookup_union_Some_raw[?|[??] //]. contradict Hne.
                 admit.
        -- iApply (i2a_args_of_pure (ih' ∪ i2a_ih_shared iha)).
           ++ by apply: i2a_args_pure_through_bij.
           ++ by iApply (big_sepM_union_2 with "[$]").
      * iSatMono HPb. iIntros!. iFrame. iSplit!.
        -- iExists _. iFrame. repeat iSplit.
           ++ iPureIntro. etrans; [|done]. admit.
           ++ iPureIntro. rewrite heap_merge_provs !heap_restrict_provs heap_through_bij_provs.
              admit.
           ++ iPureIntro. apply: heap_preserved_mono; [done|]. done.
           ++ iPureIntro. rename select (hb_priv_i bijb = hb_priv_i bijb') into Heq. rewrite -Heq.
              move => ??? /=. rewrite lookup_union_r. 2: {
                apply map_filter_lookup_None. right => ?? /=. admit. }
              rewrite map_filter_lookup_true; [by apply Hprevb|].
              move => ?? /=. right. move => /elem_of_hb_shared_i[??].
              efeed pose proof hb_disj as HNone; [done|]. rewrite -Heq in HNone. naive_solver.
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
                 (* TODO: use ho to add a heap_in_bij to the invariant *)
                 admit. (* tricky *)
        -- rewrite big_sepL2_fmap_l. iApply big_sepL_sepL2_diag.
           iDestruct "Hsh" as "#Hsh".
           iApply big_sepL_intro. iIntros "!>" (???).
           revert select (i2a_args_pure  _ _ _ _) => /(_ _ _ ltac:(done))[?[?[?[??]]]].
           by iApply (val_in_through_bij with "[$]").
        -- done.
      * by rewrite i2a_ih_shared_union // i2a_ih_shared_fmap.
      * iSatMono HP'. iIntros!. iFrame.
        rewrite !map_difference_id; [by iFrame|done..].
      (* * done. *)
      * by apply map_subseteq_difference_l.
      * by apply map_subseteq_difference_l.
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
      rename select (i2a_ih_shared ih = _) into Hih.
      iSatStart HPa'. iIntros!.
      iDestruct select (i2a_mem_inv _ _ _) as (?) "(Hgp&Hsp&Hmauth)".
      iDestruct (i2a_mem_lookup_big' moa with "[$] [$]") as %?.
      iDestruct (i2a_mem_uninit_alt1 with "[$]") as (? Hvslen) "Hsp"; [lia|].
      iDestruct select (i2a_heap_inv _) as (iha' ??) "[Hsh [Hhag Hh]]".
      (* iDestruct (i2a_heap_shared_lookup_big1 with "[$] [$]") as %?. *)
      (* iDestruct (i2a_heap_shared_lookup_big1 (i2a_combine_bij _ _) with "[$] [$]") as %?. *)
      (* iDestruct (i2a_heap_lookup_big1 with "[$] [$]") as %?. *)
      iDestruct (i2a_heap_shared_agree_to_pure with "[$] [$]") as (mhs ?) "[? ?]".
      iDestruct (i2a_args_to_pure with "[$] [$]") as %?.
      iSatStop HPa'.

      iSatStart HPb'. iIntros!.
      iDestruct select (heap_bij_inv _ _) as (bijb' ? ? ? ?) "(Hsh&Hh&Hbij)".
      iSatStop HPb'.

      iSatStartBupd HP. iIntros!.
      iMod (i2a_mem_update_all1 mem'' with "[$] [$]") as "[Ha Hmo]"; [done..|].
      (* iMod (i2a_heap_alloc_shared_big1 with "[$]") as "[Hih ?]"; [done..|]. iModIntro. *)
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

      split!. 2: {
        iSatMono HPa'. iIntros!.
        iDestruct (i2a_mem_lookup_big' with "[$] [$]") as %?.
        iFrame. by erewrite map_difference_id.
      } 2: {
        iSatMono HPb'. iFrame. erewrite map_difference_id; [by iFrame|]. admit. (* easy with sep logic lookup lemma *)
      }
      * iSatMono HP. iIntros!.
        iDestruct select (i2a_mem_map (mem'' ∖ _)) as "$".
        iDestruct select (i2a_mem_map mhs) as "$".
        rewrite Hih.
(*
Lemma i2a_heap_update_all1 ih ih' :
  mo ⊆ mem →
  mo ⊆ mem' →
  i2a_heap_auth ih' -∗
  [∗ map] p↦h0 ∈ ( ∖ hob), i2a_heap_constant p h0 ==∗
  i2a_mem_auth mem ∗ i2a_mem_map (mem ∖ mo).
Proof.
  _ : i2a_heap_auth ih
  _ : [∗ map] p↦a ∈ i2a_ih_shared ih, i2a_heap_shared p a
  _ :
*)
        admit.
      * by apply map_subseteq_difference_l.
      * by apply map_subseteq_difference_l.
      * admit.
      * admit. (* tricky *)
    + move => av lr' cs' ??? Pa' HPa'. simplify_eq/=. setoid_subst.
      (* split!. *)
      admit.
Admitted.
