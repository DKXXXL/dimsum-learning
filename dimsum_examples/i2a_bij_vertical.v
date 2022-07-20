From dimsum.core Require Export proof_techniques.
From dimsum.core Require Import prepost.
From dimsum.examples Require Import imp asm imp_to_asm imp_heap_bij.

Local Open Scope Z_scope.

(** * Vertical compositionality of [imp_to_asm] and [imp_heap_bij] *)
(** Overview of the structure of the proof:

There are three heaps / memories involved:
- the inner heap, seen by the inner module [m],
- the middle heap, after applying [imp_heap_bij], but before [imp_to_asm]
- the outer memory, after applying both [imp_heap_bij] and [imp_to_asm]

Additionally, there are the following translations:
- [ih : gmap prov imp_to_asm_elem] : inner heap ↔ asm memory
- [iha : gmap prov imp_to_asm_elem] : middle heap ↔ asm memory
- [bijb : heap_bij] : inner heap ↔ middle heap

There are allow the following private states:
- [ho] : private locations of the program in the inner heap
- [hob] : private locations of the environment in the inner heap


They are related as depicted by the following diagram:

  memory              middle heap                inner heap
    -----------------------|-------------------------|------------------------
    |    i2a_shared iha    |                         | i2a_shared ih         |
    -----------------------|     hb_shared bijb      |------------------------
        |                  |                         | i2a_constant ih (ho)  |
        | i2a_constant iha |--------------------------------------------------
        |                  |                |
    -----------------------| hb_priv_i bijb |
    |   i2a_shared iha     |                |
    --------------------------------------------------------------------------
                                    |                | i2a_constant ih (ho)  |
                                    | hb_priv_s bijb |------------------------
                                    |                | i2a_constant ih (hob) |
                                    ------------------------------------------
*)


(** * through bij *)
Definition val_through_bij (bij : heap_bij) (vs : val) : val :=
  match vs with
  | ValLoc l => ValLoc (if hb_bij bij !! l.1 is Some (HBShared p) then p else inhabitant, l.2)
  | _ => vs
  end.

Program Definition heap_through_bij (bij : heap_bij) (h : heap_state) : heap_state :=
  Heap (list_to_map $ omap (OMap:=list_omap) (λ '(l, v), if hb_bij bij !! l.1 is Some (HBShared p) then
         Some ((p, l.2), val_through_bij bij v) else None) (map_to_list (h_heap h)))
       (hb_shared_i bij) _.
Next Obligation.
  move => ???. rewrite list_to_map_lookup_is_Some => -[?]. rewrite elem_of_list_omap => -[[[??]?]]/=[??].
  repeat case_match; simplify_eq. rewrite elem_of_hb_shared_i. naive_solver.
Qed.

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
  - move => ?. destruct!. eexists (_,_,_). rewrite elem_of_map_to_list. split; [done|].
    by simplify_option_eq.
Qed.
Opaque heap_through_bij.

Lemma heap_through_bij_is_Some bij h pi o:
  is_Some (h_heap (heap_through_bij bij h) !! (pi, o)) ↔
          ∃ ps, hb_bij bij !! ps = Some (HBShared pi) ∧ is_Some (h_heap h !! (ps, o)).
Proof. rewrite /is_Some. setoid_rewrite heap_through_bij_Some. naive_solver. Qed.

Lemma heap_through_bij_is_Some1 bij h pi ps o:
  hb_bij bij !! ps = Some (HBShared pi) →
  is_Some (h_heap (heap_through_bij bij h) !! (pi, o)) ↔ is_Some (h_heap h !! (ps, o)).
Proof.
  move => ?. rewrite heap_through_bij_is_Some. split; [|naive_solver].
  move => [p'[??]]. by simplify_bij.
Qed.

(** * combine bij *)
(** ** i2a_combine_bij *)
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
  split => ?; destruct!.
  - do 2 case_match => //. simplify_eq. naive_solver.
  - eexists (HBShared _). by simplify_map_eq.
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

(** ** i2a_combine_priv_shared *)
Definition i2a_combine_priv_shared (ih : gmap prov Z) (bij : heap_bij) (hb : heap_state)
  : gmap prov (gmap Z val) :=
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
  split => ?; destruct!.
  - repeat case_match => //; simplify_eq. naive_solver.
  - eexists (HBShared _). by simplify_map_eq.
Qed.

Lemma i2a_combine_priv_shared_priv_s_disj ih bij ho :
  i2a_combine_priv_shared ih bij ho ##ₘ hb_priv_s bij.
Proof.
  apply map_disjoint_spec => ???. rewrite i2a_combine_priv_shared_Some hb_priv_s_lookup_Some. naive_solver.
Qed.


(** ** i2a_combine_priv *)
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

(** ** combine lemmas *)
Lemma i2a_combine_priv_diff ih bij hb ho :
  i2a_combine_priv_shared ih bij hb ⊆ ho →
  i2a_combine_priv ih bij hb ∖ ho = hb_priv_s bij ∖ ho.
Proof.
  move => Hho.
  apply map_eq => ?. apply option_eq => ?.
  rewrite !lookup_difference_Some i2a_combine_priv_Some hb_priv_s_lookup_Some.
  split => ?; destruct! => //.
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
  move => ??. destruct!.
Qed.

(** ** i2a_combine_extend *)
Lemma fresh_map_learn ih bijb (X : gset prov) ps pi:
  fresh_map (dom (i2a_ih_shared ih) ∖ hb_shared_s bijb) X !! ps = Some pi →
  (∃ a, ih !! ps = Some (I2AShared a) ∧ ∀ pi', hb_bij bijb !! ps ≠ Some (HBShared pi'))
   ∧ pi ∉ X.
Proof.
  move => /(fresh_map_lookup_Some _ _ _ _)[/elem_of_difference[/elem_of_dom[? /i2a_ih_shared_Some ?]]].
  rewrite !elem_of_hb_shared_s. naive_solver.
Qed.
Ltac fresh_map_learn :=
  repeat match goal with
         | H : fresh_map (dom (i2a_ih_shared _) ∖ hb_shared_s _) _ !! _ = Some _ |- _ =>
             learn_hyp (fresh_map_learn _ _ _ _ _ H)
         end.

Definition i2a_combine_heap_bij_bij (X : gset prov) (ih : gmap prov imp_to_asm_elem) (bijb : heap_bij) :=
  (HBShared <$> (hb_shared bijb ∪ fresh_map ((dom (i2a_ih_shared ih)) ∖ hb_shared_s bijb) X)) ∪
  (HBConstant <$> i2a_ih_constant ih).

Lemma i2a_combine_heap_bij_bij_shared X bijb ps pi ih:
  i2a_combine_heap_bij_bij X ih bijb !! ps = Some (HBShared pi) ↔
    hb_bij bijb !! ps = Some (HBShared pi) ∨
    fresh_map ((dom (i2a_ih_shared ih)) ∖ hb_shared_s bijb) X !! ps = Some pi.
Proof.
  rewrite /i2a_combine_heap_bij_bij !lookup_union_Some_raw ?lookup_union_None !lookup_fmap.
  rewrite !fmap_None !fmap_Some.
  setoid_rewrite i2a_ih_constant_Some.
  setoid_rewrite lookup_union_Some_raw.
  setoid_rewrite lookup_union_None.
  setoid_rewrite hb_shared_lookup_Some.
  setoid_rewrite hb_shared_lookup_None.
  split => ?; destruct!/=.
  - naive_solver.
  - naive_solver.
  - left. split!. naive_solver.
  - fresh_map_learn. destruct!. left. split!. naive_solver.
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
  split => ?; destruct!/=.
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
  destruct!; simplify_bij.
  - done.
  - fresh_map_learn. destruct!. move: (HX pi). rewrite elem_of_hb_provs_i. naive_solver.
  - fresh_map_learn. destruct!. move: (HX pi). rewrite elem_of_hb_provs_i. naive_solver.
  - by apply: fresh_map_bij.
Qed.

Definition i2a_combine_i2a (X : gset prov) (ih : gmap prov imp_to_asm_elem) (bijb : heap_bij) : gmap prov Z :=
  list_to_map $
   omap (λ '(ps, pi), if ih !! ps is Some (I2AShared a) then Some (pi : prov, a) else None) $
    map_to_list (fresh_map ((dom (i2a_ih_shared ih)) ∖ hb_shared_s bijb) X).

Lemma i2a_combine_i2a_Some X ih bijb p a:
  i2a_combine_i2a X ih bijb !! p = Some a ↔
    ∃ ps, fresh_map ((dom (i2a_ih_shared ih)) ∖ hb_shared_s bijb) X !! ps = Some p
          ∧ ih !! ps = Some (I2AShared a).
Proof.
  rewrite /i2a_combine_i2a. rewrite -elem_of_list_to_map. 2: {
    rewrite list_fmap_omap. apply: NoDup_omap_2_strong; [|apply NoDup_map_to_list].
    move => [??] [??] ? /elem_of_map_to_list? /elem_of_map_to_list? /= /fmap_Some[?[??]] /fmap_Some[?[??]].
    repeat case_match => //. simplify_eq/=. f_equal. by apply: fresh_map_bij.
  }
  rewrite elem_of_list_omap.
  split => ?; destruct!.
  - repeat case_match => //. simplify_eq/=. revert select (_ ∈ map_to_list _) => /elem_of_map_to_list. naive_solver.
  - eexists (_, _). simplify_option_eq. split!. by apply elem_of_map_to_list.
Qed.

Lemma i2a_combine_extend (X : gset prov) iha bijb ih ho hb :
  i2a_combine_bij (i2a_ih_shared iha) bijb ⊆ i2a_ih_shared ih →
  ho ⊆ i2a_ih_constant ih →
  ho ⊆ i2a_combine_priv (i2a_ih_shared iha) bijb hb →
  i2a_combine_priv_shared (i2a_ih_shared iha) bijb hb ⊆ ho →
  dom iha ⊆ X →
  hb_provs_i bijb ⊆ X →
  ∃ ih' bijb',
    i2a_ih_shared ih = i2a_combine_bij (ih' ∪ i2a_ih_shared iha) bijb' ∧
    i2a_ih_constant ih = i2a_combine_priv (ih' ∪ i2a_ih_shared iha) bijb' hb ∧
    dom ih' ## X ∧
    hb_shared bijb ⊆ hb_shared bijb' ∧
    hb_priv_i bijb = hb_priv_i bijb' ∧
    (* The following is a random collection of semi-redundant
    properties that are used by the later proof. TODO: clean this up *)
    (I2AShared <$> ih') ##ₘ iha ∧
    dom (hb_bij bijb') ⊆ dom ih ∧
    (i2a_ih_constant ih ∖ (hb_priv_s bijb' ∖ ho)) = ho ∧
    ho ∖ (ho ∖ hb_priv_s bijb) ⊆ hb_priv_s bijb' ∧
    (hb_priv_s bijb' ∖ (ho ∖ (ho ∖ hb_priv_s bijb))) = hb_priv_s bijb' ∖ ho ∧
    dom ih' ⊆ hb_shared_i bijb' ∧
    (∀ p2 p1, hb_bij bijb' !! p2 = Some (HBShared p1) →
              p1 ∉ dom (ih' ∪ i2a_ih_shared iha) →
              hb_bij bijb !! p2 = Some (HBShared p1))
.
Proof.
  move => Hcombine Hho Hho2 Hpriv HXa HXb.
  have Hdisj : (I2AShared <$> (i2a_combine_i2a X ih bijb)) ##ₘ iha. {
    apply map_disjoint_spec => ???. rewrite lookup_fmap => /fmap_Some [?[/i2a_combine_i2a_Some[?[??]]?]] ?.
    fresh_map_learn. destruct!. simplify_eq. revert select (_ ∉ X). apply. apply HXa. by apply elem_of_dom.
  }
  have Hdisj2 : dom (i2a_combine_priv_shared (i2a_ih_shared iha) bijb hb) ## dom (i2a_ih_shared ih). {
    apply: disjoint_mono; [|by apply: subseteq_dom|done].
    apply: disjoint_mono; [|by apply: subseteq_dom; apply Hho|done].
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
      * have [??]: is_Some (fresh_map (dom (i2a_ih_shared ih) ∖ hb_shared_s bijb) X !! ps). {
          apply not_eq_None_Some. rewrite fresh_map_lookup_None. apply. apply elem_of_difference.
          split.
          - apply elem_of_dom. eexists _. by apply i2a_ih_shared_Some.
          - rewrite elem_of_hb_shared_s. rewrite hb_shared_lookup_None in Hps. naive_solver.
        }
        eexists _. split; [by right|]. left. naive_solver.
    + destruct!.
      * fresh_map_learn. destruct!. exfalso. revert select (_ ∉ X). apply. apply HXb.
        apply elem_of_hb_provs_i. naive_solver.
      * have : ps = ps0; [|naive_solver]. by apply: fresh_map_bij.
      * rewrite -i2a_ih_shared_Some. apply: lookup_weaken; [|done].
        apply i2a_combine_bij_lookup_Some. split!. by apply i2a_ih_shared_Some.
      * fresh_map_learn. destruct!. exfalso. revert select (_ ∉ X). apply. apply HXa. by apply elem_of_dom.
  - apply map_eq => ps. apply option_eq => b. rewrite i2a_ih_constant_Some i2a_combine_priv_Some /=.
    setoid_rewrite i2a_combine_heap_bij_bij_priv_s.
    setoid_rewrite i2a_combine_heap_bij_bij_shared.
    setoid_rewrite lookup_union_None.
    split => ?; destruct!.
    + destruct (decide (ps ∈ hb_shared_s bijb)) as [[pi ?]%elem_of_hb_shared_s|]. 2: naive_solver.
      right.
      efeed pose proof Hrev; [done..|]. destruct!.
      eexists _. split_and!; [by left | |done|done].
      apply eq_None_ne_Some => ?. rewrite i2a_combine_i2a_Some => ?. destruct!.
      fresh_map_learn. destruct!. simplify_eq. revert select (_ ∉ X). apply. apply HXb.
      rewrite elem_of_hb_provs_i. naive_solver.
    + naive_solver.
    + rewrite -i2a_ih_constant_Some. apply: lookup_weaken; [|done]. apply: lookup_weaken; [|done].
      rewrite i2a_combine_priv_shared_Some. naive_solver.
    + fresh_map_learn. destruct!.
      exfalso. revert select (i2a_combine_i2a _ _ _ !! _ = None). apply not_eq_None_Some.
      eexists _. apply i2a_combine_i2a_Some. naive_solver.
  - apply elem_of_disjoint => ? /elem_of_dom [? /i2a_combine_i2a_Some ?]. destruct!.
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
      * move => ?. fresh_map_learn. destruct!. by apply elem_of_dom.
    + move => /i2a_combine_heap_bij_bij_priv_s[??]. by apply elem_of_dom.
  - apply map_eq => ps. apply option_eq => b.
    rewrite lookup_difference_Some lookup_difference_None hb_priv_s_lookup_None i2a_ih_constant_Some /=.
    setoid_rewrite i2a_combine_heap_bij_bij_priv_s.
    split => ?; destruct!.
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
  - apply map_subseteq_spec => ??.
    rewrite hb_priv_s_lookup_Some /= i2a_combine_heap_bij_bij_priv_s.
    rewrite lookup_difference_Some lookup_difference_None /is_Some.
    setoid_rewrite hb_priv_s_lookup_Some. rewrite elem_of_hb_shared_s.
    move => ?. destruct!. split; [|naive_solver].
    rewrite -i2a_ih_constant_Some. by apply: lookup_weaken.
  - apply map_eq => i. apply option_eq => ?.
    rewrite !(lookup_difference_Some, lookup_difference_None, hb_priv_s_lookup_Some) /= /is_Some.
    rewrite !i2a_combine_heap_bij_bij_priv_s elem_of_hb_shared_s.
    setoid_rewrite lookup_difference_Some.
    setoid_rewrite hb_priv_s_lookup_None.
    split => ?; destruct!.
    + done.
    + have [?]: is_Some (i2a_combine_priv (i2a_ih_shared iha) bijb hb !! i) by apply: lookup_weaken_is_Some.
      rewrite i2a_combine_priv_Some. naive_solver.
    + naive_solver.
  - move => ? /elem_of_dom[? /i2a_combine_i2a_Some[??]]. apply elem_of_hb_shared_i => /=.
    eexists _. apply i2a_combine_heap_bij_bij_shared. naive_solver.
  - move => ?? /= /i2a_combine_heap_bij_bij_shared[//|?] Hnotin. exfalso. apply Hnotin.
    rewrite dom_union_L elem_of_union !elem_of_dom /is_Some.
    setoid_rewrite i2a_combine_i2a_Some. fresh_map_learn. naive_solver.
Qed.

(** * mem_transfer *)
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

Ltac i2a_mem_transfer Hfrom Hto :=
  let H := fresh in
  efeed pose proof i2a_mem_transfer as H;
  [ | iSatMono Hto; iIntros!; iFrame; by iAccu |];
  [ iSatMono Hfrom; iIntros!; iFrame; by iAccu | ];
  clear Hfrom Hto; destruct H as [Hfrom Hto].

(** * pure versions *)
(** ** imp to asm *)
(** *** i2a_val_rel_pure *)
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
  iIntros (Hv) "Hsh". destruct v => //=. simplify_eq/=. destruct!.
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

Lemma i2a_val_rel_big_to_pure vs avs ih :
  i2a_heap_auth ih -∗
  ([∗ list] v;av∈vs;avs, i2a_val_rel v av) -∗
  ⌜Forall2 (i2a_val_rel_pure (i2a_ih_shared ih)) vs avs⌝.
Proof.
  iIntros "Hh Hv".
  iDestruct (big_sepL2_length with "[$]") as %?.
  iApply bi.pure_mono; [by apply Forall2_same_length_lookup_2|].
  iIntros (?????). iApply (i2a_val_rel_to_pure with "[$]").
  by iApply (big_sepL2_lookup with "Hv").
Qed.

Lemma i2a_val_rel_big_of_pure ih vs avs :
  Forall2 (i2a_val_rel_pure ih) vs avs →
  ([∗ map] p↦a ∈ ih, i2a_heap_shared p a) -∗
  ([∗ list] v;av∈vs;avs, i2a_val_rel v av).
Proof.
  iIntros (Hall) "#Hsh". iInduction Hall as [] "IH"; [done|].
  iFrame "#". by iApply i2a_val_rel_of_pure.
Qed.

Lemma i2a_val_rel_big_through_bij vs avs ih1 ih2 bij :
  Forall2 (i2a_val_rel_pure ih1) vs avs →
  ih1 = i2a_combine_bij ih2 bij →
  ([∗ map] p↦a ∈ ih2, i2a_heap_shared p a) -∗
  [∗ list] v;av ∈ (val_through_bij bij <$> vs);avs, i2a_val_rel v av.
Proof.
  iIntros (Hall ?) "#Hih2". subst.
  rewrite big_sepL2_fmap_l. iApply big_sepL2_intro. { by apply: Forall2_length. }
  iIntros "!>" (? v ???).
  iApply (i2a_val_rel_of_pure with "Hih2"). apply: i2a_val_rel_pure_through_bij; [|done].
  by apply: Forall2_lookup_lr.
Qed.

(** *** i2a_heap_shared_agree_pure *)
Definition i2a_heap_shared_agree_pure (h : gmap loc val) (ih : gmap prov Z) (mem : gmap Z (option Z)) : Prop :=
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
  iIntros "Hag Hauth".
  iInduction h as [|l v h ?] "IH" using map_ind.
  { iExists ∅. iFrame. rewrite /i2a_mem_map big_sepM_empty. iSplit!. eexists ∅ => ?? //. }
  rewrite /i2a_heap_shared_agree big_sepM_insert //. iDestruct "Hag" as "[??]".
  iDestruct ("IH" with "[$] [$]") as (? [m2l Hag]) "[Hm Hauth]". iClear "IH".
  destruct ((i2a_ih_shared ih) !! l.1) as [a|] eqn: Hl. 2: {
    iExists _. iFrame. iPureIntro. eexists m2l.
    move => ?? /lookup_insert_Some[[??]|[??]]; simplify_option_eq => //. by apply Hag.
  }
  move: Hl => /i2a_ih_shared_Some Hl. simplify_option_eq.
  iDestruct!. iDestruct (i2a_val_rel_to_pure with "[$] [$]") as %?.
  iDestruct (i2a_mem_map_constant_excl with "[$] [$]") as %?.
  iExists (<[a + l.2 := Some av]>m). rewrite /i2a_mem_map big_sepM_insert //. iFrame. iPureIntro.
  eexists (<[a + l.2 := l]>m2l). move => ?? /lookup_insert_Some[[??]|[??]]; simplify_eq.
  + move: Hl => /i2a_ih_shared_Some ->. split!; simplify_map_eq; done.
  + case_match => //. have := Hag _ _ ltac:(done). simplify_option_eq => ?. destruct!.
    rewrite !lookup_insert_ne; [|move => Heq; rewrite ->Heq in *; naive_solver..]. naive_solver.
Qed.

Lemma i2a_heap_shared_agree_of_pure ih h m :
  i2a_heap_shared_agree_pure h (i2a_ih_shared ih) m →
  ([∗ map] p↦a ∈ i2a_ih_shared ih, i2a_heap_shared p a) -∗
  i2a_mem_map m -∗
  i2a_heap_shared_agree h ih.
Proof.
  iIntros (Hag) "#Hsh Hm".
  iInduction h as [|l v h Hl] "IH" using map_ind forall (m Hag). { by iApply big_sepM_empty. }
  move: Hag => [m2l /map_Forall_insert [//|? Hag]].
  iApply big_sepM_insert; [done|].
  case_match as Heq; destruct!; rewrite ?i2a_ih_shared_Some ?i2a_ih_shared_None in Heq; simplify_option_eq.
  - erewrite <-(insert_delete m); [|done].
    iDestruct (big_sepM_insert with "Hm") as "[Ha Hm]". { by simplify_map_eq. }
    iSplitL "Ha".
    + iSplit!; [|done]. by iApply i2a_val_rel_of_pure.
    + iApply ("IH" with "[] Hm"). iPureIntro. eexists m2l. move => l' v' Hl'.
      have := (Hag l' v' ltac:(done)). case_match => // ?. destruct!. split!; [done|].
      apply lookup_delete_Some. split!. move => Hx. rewrite <-Hx in *. simplify_option_eq.
      by rewrite Hl in Hl'.
  - iSplitR.
    + do 2 case_match => //. naive_solver.
    + iApply ("IH" with "[%] Hm"). by eexists _.
Qed.

Lemma i2a_heap_shared_agree_pure_lookup l v ih h m :
  i2a_heap_shared_agree_pure h ih m →
  h !! l = Some v →
  is_Some (ih !! l.1) →
  ∃ a, i2a_val_rel_pure ih v a.
Proof. move => [? Hag] Hl [??]. have := Hag _ _ ltac:(done). simplify_option_eq. naive_solver. Qed.

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
(** *** val_in_bij_pure *)
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
  iIntros (Hv) "Hsh". destruct v1, v2 => //=. simplify_eq/=. destruct!.
  iSplit; [done|]. iApply (big_sepM_lookup with "[$]"). by apply hb_shared_lookup_Some.
Qed.

(** *** heap_in_bij_pure *)
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

(** ** combining *)
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
  move => ??. destruct v1, v2; simplify_eq/= => //. destruct!.
  split!; [by f_equal|]. apply i2a_combine_bij_lookup_Some. naive_solver.
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

(** * Main vertical compositionality theorem:  *)

Lemma i2a_bij_vertical m σ moinit `{!VisNoAll m} ins fns f2i:
  trefines (MS (imp_to_asm ins fns f2i (imp_heap_bij m))
               (initial_imp_to_asm_state moinit (imp_heap_bij m) (initial_imp_heap_bij_state m σ)))
           (MS (imp_to_asm ins fns f2i m)
               (initial_imp_to_asm_state moinit m σ))
.
Proof.
  unshelve apply: mod_prepost_combine. {
    exact (λ pl '(I2A csa lra) _ '(I2A cs lr) Pa Pb P,
      csa = cs ∧
      lra = lr ∧
      ∃ mem' moa mo,
        if pl is Env then
          ∃ iha bijb hob ho hprev mh hb,
          moa = mem' ∖ mo ∧
          hob = i2a_combine_priv (i2a_ih_shared iha) bijb hb ∖ ho ∧
          (P ⊣⊢ i2a_mem_map mo ∗ i2a_mem_map mh ∗
             ([∗ map] p↦a ∈ i2a_combine_bij (i2a_ih_shared iha) bijb, i2a_heap_shared p a) ∗
             ([∗ map] p↦h ∈ ho, i2a_heap_constant p h)) ∧
          satisfiable (Pa ∗ i2a_mem_auth mem' ∗ i2a_heap_auth iha ∗
                          i2a_mem_map moa ∗
                          ([∗ map]p↦a ∈ i2a_ih_shared iha, i2a_heap_shared p a)) ∧
          satisfiable (Pb ∗ heap_bij_auth bijb ∗
             ([∗ map] p2↦p1∈ hb_shared bijb, heap_bij_shared p1 p2) ∗
             ([∗ map] p↦h∈ hob, heap_bij_const_s p h) ∗
             heap_in_bij bijb hprev hb) ∧
          mo ⊆ mem' ∧
          ho ⊆ i2a_combine_priv (i2a_ih_shared iha) bijb hb ∧
          hb_provs_i bijb ⊆ h_provs hprev ∧
          dom iha ⊆ h_provs hprev ∧
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
  { simpl. split_and!; [done..|].
    eexists moinit, ∅, moinit, ∅, ∅, ∅, ∅, ∅, ∅, ∅. split!.
    - by rewrite map_difference_diag.
    - rewrite map_difference_empty. compute_done.
    - iSplit; iIntros!; [|done]. iFrame.
      rewrite /i2a_mem_map i2a_ih_shared_empty /i2a_combine_bij omap_empty !big_sepM_empty. done.
    - apply: satisfiable_mono; [apply i2a_res_init|]. iIntros!. iFrame.
      rewrite i2a_ih_shared_empty /i2a_mem_map !big_sepM_empty. iSplit; [|done].
      iDestruct select (i2a_heap_inv _) as (ih Hsub ?) "(?&?&?)".
      have -> : ih = ∅; [|done]. apply map_eq => i. apply option_eq => ?. split => // ?.
      have : i ∈ h_provs ∅; [|done]. apply Hsub. by apply elem_of_dom.
    - apply: satisfiable_mono; [apply heap_bij_init|]. iIntros "$".
      rewrite /hb_shared omap_empty !big_sepM_empty. iSplit!.
      iIntros (????). done.
    - eexists ∅. move => ?? /map_filter_lookup_Some. naive_solver.
  }
  all: move => [csa lra] [] [cs lr] Pa Pb P [? e] ?/=; destruct!.
  - move: e => []//= regs mem b ? h ? vs avs.
    apply pp_to_all_forall => -[e' [??]] P'x Hx P' HP'. simplify_eq/=. setoid_subst. eexists b.
    rename select (satisfiable (Pa ∗ _)) into HPa.
    rename select (satisfiable (Pb ∗ _)) into HPb.
    rename select (heap_preserved (i2a_ih_constant iha) hprev) into Hpreva.
    rename select (heap_preserved (hb_priv_i bijb) hprev) into Hprevb.
    iSatStart HP'. iIntros!.
    iDestruct select (i2a_mem_inv _ _ _) as "((Hgp&Hsp)&Hmauth)".
    iDestruct (i2a_mem_lookup_big' mo with "[$] [$]") as %?.
    iDestruct (i2a_mem_uninit_alt1 with "[$]") as (? Hvslen) "Hsp"; [lia|].
    iDestruct select (i2a_heap_inv _) as (ih ??) "[Hsh [Hhag Hh]]".
    iDestruct (i2a_heap_shared_lookup_big' (i2a_combine_bij _ _) with "[$] [$]") as %?.
    iDestruct (i2a_heap_lookup_big' with "[$] [$]") as %?.
    iDestruct (i2a_heap_shared_agree_to_pure with "[$] [$]") as (??) "[? ?]".
    iDestruct (i2a_val_rel_big_to_pure with "[$] [$]") as %Hvs.
    iSatStop HP'.

    have [| | | | | |ih' [bijb' ?]]:= i2a_combine_extend (h_provs hprev) iha bijb ih ho hb => //.
    destruct!.
    rename select (i2a_ih_shared ih = _) into Hihs.
    rename select (i2a_ih_constant ih = _) into Hihc.
    rename select (hb_priv_i bijb = hb_priv_i bijb') into Hpriveq.
    rename select (i2a_ih_constant ih ∖ (hb_priv_s bijb' ∖ ho) = ho) into Hhoeq.
    rename select (hb_priv_s bijb' ∖ (ho ∖ (ho ∖ hb_priv_s bijb)) = hb_priv_s bijb' ∖ ho) into Hhoeq2.

    iSatStartBupd HPa. iIntros!.
    iMod (i2a_mem_update_all mem with "[$] [$]") as "[Ha Hmo]"; [done..|].
    iMod (i2a_heap_alloc_shared_big' with "[$]") as "[Hih ?]"; [done..|]. iModIntro.
    iSatStop HPa.

    repeat i2a_mem_transfer HP' HPa.

    iSatStart HP'. iIntros!. iDestruct (i2a_mem_lookup_big' with "[$] [$]") as %?. iSatStop HP'.

    iSatStartBupd HPb. iIntros!.
    rewrite i2a_combine_priv_diff // (map_difference_difference_add (hb_priv_s bijb)).

    iMod (heap_bij_update_all bijb' with "[$] [$] [$]") as "[?[#Hs ?]]". {
      apply map_difference_difference_subseteq. move => j x1 x2 Hho.
      have : i2a_combine_priv (i2a_ih_shared iha) bijb hb !! j = Some x1 by apply: lookup_weaken.
      move => /i2a_combine_priv_Some ? /hb_priv_s_lookup_Some. naive_solver.
    } { done. } { done. } { done. }
    rewrite Hhoeq2.
    iModIntro.
    iSatStop HPb.

    split; [done|].
    set (h' := (heap_merge (heap_restrict (heap_through_bij bijb' h)
                              (λ p, p ∈ dom (ih' ∪ i2a_ih_shared iha)))
                  (heap_restrict hprev
                                 (λ x, x ∉ dom (ih' ∪ i2a_ih_shared iha) ∨ x ∉ hb_shared_i bijb')))).
    set (vs' := (val_through_bij bijb' <$> vs)).
    eexists h', _, vs', avs. apply pp_to_ex_exists.
    eexists ((e'.1, event_set_vals_heap e'.2 vs' h'), I2A _ _), True%I. unfold vs' in *.
    split!.
    + iSatMono HPa. iIntros!.
      iAssert ([∗ map] p↦a ∈ i2a_ih_shared ((I2AShared <$> ih') ∪ iha), i2a_heap_shared p a)%I as "#Hsh". {
        rewrite i2a_ih_shared_union // i2a_ih_shared_fmap. by iApply (big_sepM_union_2 with "[$]").
      } iFrame "Hsh".
      iDestruct select (i2a_mem_map (mem ∖ _)) as "$". iFrame.
      iDestruct (i2a_mem_uninit_alt2 with "[$]") as "Huninit". rewrite Hvslen Z2Nat.id; [|lia].
      iFrame "Huninit".
      rewrite !bi.sep_exist_r. iExists _.
      rewrite -!(assoc bi_sep).
      iDestruct select (i2a_heap_auth _) as "$".

      iSplit!.
      * rewrite dom_union_L. apply union_mono; [|done]. by rewrite dom_fmap_L.
      * move => l ?. rewrite i2a_ih_constant_union // i2a_ih_constant_fmap_shared left_id_L.
        move => Hih /=.
        have ? : l.1 ∉ dom (ih' ∪ i2a_ih_shared iha). {
          move: Hih => /i2a_ih_constant_Some?.
          rewrite dom_union. apply not_elem_of_union. split.
          - revert select (dom ih' ## h_provs hprev) => Hih'.
            symmetry in Hih'. apply: Hih'.
            revert select (dom iha ⊆ h_provs hprev). apply.
            by apply elem_of_dom.
          - apply not_elem_of_dom. apply i2a_ih_shared_None. naive_solver.
        }
        rewrite lookup_union_r. 2: { apply map_filter_lookup_None. naive_solver. }
        rewrite map_filter_lookup_true; [by apply Hpreva|naive_solver].
      * iApply i2a_heap_shared_agree_union. {
          apply map_disjoint_spec => -[p o] ?? /map_filter_lookup_Some[/=/heap_through_bij_Some??].
          move => /map_filter_lookup_Some[?[//|]] /=. destruct!.
          apply. apply elem_of_hb_shared_i. naive_solver.
        }
        iDestruct select (i2a_mem_map mh) as "Hmh".
        iSplitR "Hmh".
        -- iApply i2a_heap_shared_agree_of_pure; [|done..].
           apply: (i2a_heap_shared_agree_pure_impl (λ p, hb_shared bijb' !! p)); [done|].
           move => ??? /map_filter_lookup_Some [/heap_through_bij_Some[?[?[?[??]]]] ?] Hsh. simplify_eq/=.
           split!.
           ++ by apply hb_shared_lookup_Some.
           ++ done.
           ++ rewrite Hihs. apply i2a_combine_bij_lookup_Some. split!.
              by rewrite i2a_ih_shared_union // i2a_ih_shared_fmap in Hsh.
           ++ move => ??. apply: i2a_val_rel_pure_through_bij; [done|].
              by rewrite i2a_ih_shared_union // i2a_ih_shared_fmap.
        -- iApply i2a_heap_shared_agree_impl.
           2: { iApply (i2a_heap_shared_agree_of_pure with "[] [$]"); [done|].
                rewrite i2a_ih_shared_union // big_sepM_union //. 2: by apply map_disjoint_omap.
                by iDestruct!. }
           move => l ?? /map_filter_lookup_Some[? Hne] Ha.
           move: Hne => [Hne|Hne]; simplify_eq/=. {
             contradict Hne. apply elem_of_dom.
             move: Ha. rewrite -i2a_ih_shared_Some i2a_ih_shared_union // i2a_ih_shared_fmap. done.
           }
           split.
           ++ apply map_filter_lookup_Some => /=. split; [done|].
              contradict Hne. move: Hne => /elem_of_hb_shared_i[?]. rewrite -hb_shared_lookup_Some => ?.
              apply elem_of_hb_shared_i. eexists _. rewrite -hb_shared_lookup_Some.
              by apply: lookup_weaken.
           ++ move: Ha => /lookup_union_Some_raw[|[??] //]. rewrite lookup_fmap => /fmap_Some[?[??]].
              exfalso. revert select (dom ih' ## h_provs hprev). apply.
              ** by apply elem_of_dom.
              ** by apply heap_wf.
      * iApply (i2a_val_rel_big_through_bij with "Hsh"); [done|].
        by rewrite i2a_ih_shared_union // i2a_ih_shared_fmap.
    + iSatMono HPb. iIntros!. rewrite heap_of_event_event_set_vals_heap vals_of_event_event_set_vals_heap.
      2: { rewrite fmap_length. destruct b; simplify_eq/=; destruct!/=; done. }
      iFrame "Hs". iFrame. iSplit!.
      * iExists _. iFrame. repeat iSplit.
        -- iPureIntro. by etrans.
        -- iPureIntro. move => ? /elem_of_hb_provs_i[[? Hin]|[??]]; apply elem_of_union.
           ++ right. revert select (hb_provs_i bijb ⊆ h_provs hprev). apply.
              apply elem_of_hb_provs_i. rewrite Hpriveq. naive_solver.
           ++ left. apply elem_of_hb_shared_i. naive_solver.
        -- iPureIntro. apply: heap_preserved_mono; [done|]. rewrite Hihc.
           apply map_subseteq_spec => ??. rewrite hb_priv_s_lookup_Some i2a_combine_priv_Some.
           naive_solver.
        -- iPureIntro. rewrite -Hpriveq.
           move => [p o] ?? /=. rewrite lookup_union_r. 2: {
             apply map_filter_lookup_None. left.
             apply eq_None_not_Some => /heap_through_bij_is_Some[?[/hb_disj]].
             rewrite -Hpriveq. naive_solver.
           }
           rewrite map_filter_lookup_true; [by apply Hprevb|].
           move => ?? /=. right. move => /elem_of_hb_shared_i[??].
           efeed pose proof hb_disj as HNone; [done|]. rewrite -Hpriveq in HNone. naive_solver.
        -- done.
        -- iIntros (p1 p2 o ?) => /=.
           destruct (decide (p1 ∈ dom (ih' ∪ i2a_ih_shared iha))) as [Hin|].
           ++ rewrite lookup_union_l'.
              2: { apply map_filter_lookup_None. right => ?? /=. rewrite elem_of_hb_shared_i. naive_solver. }
              rewrite map_filter_lookup_true; [|done].
              iSplit; [iPureIntro; by apply heap_through_bij_is_Some1|].
              iIntros (??[?[?[?[??]]]]%heap_through_bij_Some ?). simplify_bij.
              have [|??]:= i2a_heap_shared_agree_pure_lookup _ _ _ _ _ ltac:(done) ltac:(done) => /=. {
                move: Hin => /elem_of_dom[??]. rewrite Hihs. eexists _. apply i2a_combine_bij_lookup_Some.
                naive_solver.
              }
              by iApply (val_in_through_bij with "[$]").
           ++ rewrite lookup_union_r. 2: { apply map_filter_lookup_None. naive_solver. }
              rewrite map_filter_lookup_true; [|naive_solver].
              revert select (heap_preserved (i2a_ih_constant ih) h) => Hpre.
              have -> : h_heap h !! (p2, o) = h_heap hb !! (p2, o). {
                rewrite -(h_block_lookup hb). apply Hpre.
                rewrite Hihc /=. apply: lookup_weaken; [|by apply map_union_subseteq_l].
                apply i2a_combine_priv_shared_Some. split!. by apply not_elem_of_dom. }
              iDestruct select (heap_in_bij _ _ _) as "Hbij".
              iApply ("Hbij" $! p1 p2 o). iPureIntro.
              naive_solver.
      * rewrite big_sepL2_fmap_l. iApply big_sepL_sepL2_diag.
        iApply big_sepL_intro. iIntros "!>" (???).
        move: Hvs => /(Forall2_lookup_l _ _ _ _ _). move => /(_ _ _ ltac:(done))[?[??]].
        by iApply (val_in_through_bij with "[$]"); [|done].
    + destruct b; simplify_eq/=; destruct!/=; done.
    + by rewrite i2a_ih_shared_union // i2a_ih_shared_fmap.
    + rewrite {1}Hihc i2a_ih_shared_union; [|done]. by rewrite i2a_ih_shared_fmap.
    + iSatMono HP'. iIntros!. rewrite Hhoeq. iFrame.
      rewrite !map_difference_id; [by iFrame|done..].
    + by apply map_subseteq_difference_l.
    + rewrite Hihc. apply map_union_subseteq_r';
           [by apply i2a_combine_priv_shared_priv_s_disj|by apply map_subseteq_difference_l].
    + destruct b; simplify_eq/=; destruct!/=; split!.
  - move => vs hb' Pb' HPb' ? rs' mem'' ? avs.
    apply pp_to_all_forall => -[e' [??]] ? Hx Pa' HPa'. setoid_subst.
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
    rewrite heap_of_event_event_set_vals_heap vals_of_event_event_set_vals_heap.
    2: { destruct e; simplify_eq/=; destruct!/=; solve_length. }
    iDestruct select (i2a_mem_inv _ _ _) as "((Hgp&Hsp)&Hmauth)".
    iDestruct (i2a_mem_lookup_big' moa with "[$] [$]") as %?.
    iDestruct (i2a_mem_uninit_alt1 with "[$]") as (? Hvslen) "Hsp"; [lia|].
    iDestruct select (i2a_heap_inv _) as (iha' ??) "[Hsh [Hhag Hh]]".
    rewrite -(map_filter_union_complement (λ x, x.1.1 ∈ hb_shared_i bijb') (h_heap hb')).
    rewrite i2a_heap_shared_agree_union. 2: apply map_disjoint_filter_complement.
    iDestruct "Hhag" as "[Hhag1 Hhag2]".
    iDestruct (i2a_heap_shared_agree_to_pure with "Hhag1 [$]") as (mhag1 ?) "[? ?]".
    iDestruct (i2a_heap_shared_agree_to_pure with "Hhag2 [$]") as (mhag2 ?) "[? ?]".
    iDestruct (i2a_heap_shared_lookup_big' with "[$] [$]") as %?.
    iDestruct (i2a_val_rel_big_to_pure with "[$] [$]") as %Hvs.
    iSatStop HPa'.

    have Hdisj := i2a_combine_bij_priv_disj (i2a_ih_shared iha') bijb' (heap_of_event e).

    iSatStartBupd HP. iIntros!.
    iMod (i2a_mem_update_all mem'' with "[$] [$]") as "[Ha Hmo]"; [done..|].
    iMod (i2a_heap_update_all
            (i2a_combine_bij (i2a_ih_shared iha') bijb')
            (i2a_combine_priv (i2a_ih_shared iha') bijb' (heap_of_event e))
           with "[$] [$] [$]") as "(?&?&?)"; [done| | | |].
    { etrans; [done|]. apply map_union_subseteq_r. apply i2a_combine_priv_shared_priv_s_disj. }
    { rewrite Hihs. by apply i2a_combine_bij_mono. }
    { move: Hdisj => /map_disjoint_dom. by rewrite !dom_fmap. }
    iModIntro.
    iSatStop HP.

    repeat i2a_mem_transfer HPa' HP.

    split; [done|]. eexists  _, _, _, avs.
    apply pp_to_ex_exists. eexists (_, I2A _ _), True%I. split!. 2: {
      iSatMono HPa'. iIntros!.
      iDestruct (i2a_mem_lookup_big' with "[$] [$]") as %?.
      iFrame. by erewrite map_difference_id.
    }
    + iSatMono HP. iIntros!.
      iDestruct select (i2a_mem_map (mem'' ∖ _)) as "$".
      iDestruct select (i2a_mem_map mhag2) as "$".
      iDestruct select ([∗ map] _↦_ ∈ _, i2a_heap_shared _ _)%I as "#Hsh". iFrame. iFrame "Hsh".
      iDestruct (i2a_mem_uninit_alt2 with "[$]") as "Hsp". rewrite Hvslen Z2Nat.id; [|lia]. iFrame.
      iSplitL.
      * iExists _. iFrame. repeat iSplit.
        -- iPureIntro. etrans; [|done]. rewrite dom_union_L !dom_fmap_L. apply union_least.
           ++ move => ? /elem_of_dom[?/i2a_combine_bij_lookup_Some?]. apply elem_of_dom. naive_solver.
           ++ move => ? /elem_of_dom[?/i2a_combine_priv_Some?]. apply elem_of_dom. naive_solver.
        -- iPureIntro. rewrite i2a_ih_constant_union // i2a_ih_constant_fmap_shared left_id_L.
           rewrite i2a_ih_constant_fmap.
           move => ?? /i2a_combine_priv_Some[?|?].
           ++ revert select (heap_preserved (hb_priv_s bijb') (heap_of_event e)).
              apply. by apply hb_priv_s_lookup_Some.
           ++ destruct!. by rewrite h_block_lookup -surjective_pairing.
        -- by rewrite i2a_ih_shared_union // i2a_ih_shared_fmap i2a_ih_shared_fmap_constant right_id_L.
        -- iApply (i2a_heap_shared_agree_of_pure with "[] [$]").
           all: rewrite i2a_ih_shared_union // i2a_ih_shared_fmap i2a_ih_shared_fmap_constant right_id_L //.
           apply: i2a_heap_shared_agree_pure_combine; [done..|].
           move => ????. by apply map_filter_lookup_Some.
      * iApply (i2a_val_rel_big_of_pure with "Hsh").
        apply Forall2_same_length_lookup. split; [solve_length|].
        move => ?????. move: Hvs => /(Forall2_lookup_r _ _ _ _ _). move => /(_ _ _ ltac:(done))[?[??]].
        revert select (Forall2 _ _ _) => /(Forall2_lookup_lr _ _ _ _ _ _)?.
        apply: i2a_val_rel_pure_combine; naive_solver.
    + iSatMono HPb'. iFrame.
      erewrite map_difference_id; [by iFrame|].
      etrans; [done|]. apply map_union_subseteq_r. apply i2a_combine_priv_shared_priv_s_disj.
    + by apply map_subseteq_difference_l.
    + by apply map_subseteq_difference_l.
    + done.
    + done.
    + done.
    + done.
    + rewrite /i2a_combine_priv map_difference_union_distr. apply map_union_subseteq_l'.
      rewrite map_difference_disj_id //. apply: map_disjoint_weaken_r; [|done].
      apply i2a_combine_priv_shared_priv_s_disj.
    + done.
    + destruct e; simplify_eq/=; destruct!/=; split!.
Qed.

(* Print Assumptions i2a_bij_vertical. *)

Lemma i2a_bij_vertical_N m σ moinit `{!VisNoAll m} ins fns f2i n:
  trefines (MS (imp_to_asm ins fns f2i (imp_heap_bij_N n m))
               (initial_imp_to_asm_state moinit (imp_heap_bij_N n m) (initial_imp_heap_bij_state_N n m σ)))
           (MS (imp_to_asm ins fns f2i m)
               (initial_imp_to_asm_state moinit m σ))
.
Proof. elim: n => //= ??. etrans; [by apply: i2a_bij_vertical|done]. Qed.