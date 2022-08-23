From dimsum.core Require Export proof_techniques.
From dimsum.core Require Import itree axioms.
From dimsum.examples Require Import lam.

Local Open Scope Z_scope.

Local Ltac go :=
  clear_itree.
Local Ltac go_s :=
  tstep_s; go.
Local Ltac go_i :=
  tstep_i; go.

Definition nb_itree: itree (moduleE lam_event unit) unit:= TNb.
Lemma ub_itree_refines_everything s:
  trefines (itree_mod nb_itree ()) s.
Proof.
  apply tsim_implies_trefines=>n. unfold nb_itree.
  go_i. auto.
Qed.

(* ** Various Lam programs to test the TStepS and TStepI instances*)

(* ** free variable*)
Definition free_var_lam: fndef :={|
fd_args := [];
fd_body := Var "x";
fd_static := I
|}.
Definition free_var_prog : gmap fid fndef :=
  <[("free_var",None) := free_var_lam]> $ ∅.
Definition free_var_mod := lam_mod free_var_prog.

Definition free_var_itree : itree (moduleE lam_event unit) unit:=
  h← TExist _;;;
  TVis (Incoming, ELCall ("free_var",None) [] h);;;;
  TUb.

Lemma free_var_itree_refines_free_var_lam:
  trefines (itree_mod free_var_itree ()) free_var_mod.
Proof.
  apply tsim_implies_trefines => n /=. unfold free_var_itree, free_var_prog. 
  go_i. intros. go. go_i. go_s. left. eexists _,_,_. split!.
  go_s. eexists _,_. split!. eauto. intros. auto.
  unfold free_var_lam. simpl. go_s. auto. 
Qed.


(* ** Simple binary operation*)
Definition add_lam: fndef :={|
fd_args := ["x";"y"];
fd_body := BinOp (Var "x") AddOp (Var "y");
fd_static := I
|}.
Definition add_prog : gmap fid fndef :=
  <[("add",None) := add_lam]> $ ∅.
Definition add_mod := lam_mod add_prog.

Definition add_itree : itree (moduleE lam_event unit) unit :=
        '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ELCall f vs h));;;
        TAssume (f= ("add",None));;;;
        x ← TAll _;;;
        y ← TAll _;;; 
        TAssume (vs = [ValNum x;ValNum y]);;;;
        TVis (Outgoing, ELReturn (ValNum (x+y)) h);;;;
        TUb.
Lemma add_prog_refines_add_itree :
  trefines add_mod (itree_mod add_itree ()).
Proof.
  apply tsim_implies_trefines => n. 
  go_i. split!. intros. go_s. eexists (f, vs, h'). go.
  go_s. split!. go. go_s. intros. go. go_s. intros. go.
  go_s. intros. go. go_s. intros. go.
  go_i. split!. unfold add_prog in *.  intros. 
  rewrite lookup_insert_Some in H2.   destruct!. split!. go_i. go_i.
  go_s. split!. go. go_s.  auto.
  intros.
  subst. rewrite lookup_insert_None in H2. destruct!.
  intros. destruct!.
Qed.

Definition add_repeat_itree : itree (moduleE lam_event unit) unit :=
        ITree.forever(
          '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ELCall f vs h));;;
          TAssume (f= ("add",None));;;;
          x ← TAll _;;;
          y ← TAll _;;; 
          TAssume (vs = [ValNum x;ValNum y]);;;;
          TVis (Outgoing, ELReturn (ValNum (x+y)) h)
        ) .
Lemma add_prog_refines_add_repeat_itree :
  trefines add_mod (itree_mod add_repeat_itree ()).
Proof.
  apply tsim_implies_trefines => n.
  unshelve eapply tsim_remember.
  { simpl. exact (λ _ σa '(t, _),
  t ≈ add_repeat_itree ∧
  ∃h, σa= Lam Waiting [] h add_prog). } 
  {simpl. naive_solver. }
  { simpl. eauto. }
  { simpl. intros ???[????][??][??]. destruct!. 
  go_i. split!. intros. go_s. go_s. rewrite -/add_repeat_itree. eexists (f, vs, h'). go.
  go_s. intros. split. naive_solver. go. go_s. intros. go. go_s. intros.
  go. go_s. intros. go. go_s. intros. go. go_i. split.
  intros. unfold add_prog. rewrite lookup_insert_Some in H5. destruct!/=; subst.
  split!. go_i. go_i. go_s. split!. go. 
  eapply H0; auto. split!. naive_solver.
  intros. destruct!. }
Qed. 

Definition add_wrong_lam: fndef :={|
fd_args := [];
fd_body := BinOp (Val (ValNum 0)) AddOp (Val (ValBool true));
fd_static := I
|}.
Definition add_wrong_prog : gmap fid fndef :=
  <[("add_wrong",None) := add_wrong_lam]> $ ∅.
Definition add_wrong_mod := lam_mod add_wrong_prog.
Definition add_wrong_itree : itree (moduleE lam_event unit) unit:=
  h← TExist _;;;
  TVis (Incoming, ELCall ("add_wrong",None) [] h);;;;
  TUb.

Lemma add_wrong_itree_refines_add_wrong_lam:
  trefines (itree_mod  add_wrong_itree ()) add_wrong_mod.
Proof.
  apply tsim_implies_trefines => n.
  go_i. intros. go. go_i. 
  go_s. left.
  eexists ("add_wrong", None),[],x.
  split!. 
  go_s. eexists _,_. split!. rewrite lookup_insert_Some. left. auto. intros.
  auto. go_s. intros. inversion H1.
Qed.  

(* ** newrefs *)
Definition newref_lam: fndef :={|
fd_args := ["x";"y"];
fd_body := NewRef (Var "x") (Var "y");
fd_static := I
|}.
Definition newref_prog : gmap fid fndef :=
  <[("newref",None) := newref_lam]> $ ∅.
Definition newref_mod := lam_mod newref_prog.

Definition newref_itree : itree (moduleE lam_event unit) unit :=
    ITree.forever(
      '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ELCall f vs h));;;
      TAssume (f= ("newref",None));;;;
      x ← TAll _;;;
      y ← TAll _;;; 
      TAssume (vs = [ValNum x;ValNum y]);;;;
      TAssume (y>0);;;;
      l ← TExist _;;;
      h' ← TExist _;;;
      TVis (Outgoing, ELReturn (ValLoc l) h');;;;
      (* ** add assertions*)
      TAssert( h'.(h_heap)!!l = Some (ValNum x))
    ) .
Lemma newref_prog_refines_newref_itree :
  trefines newref_mod (itree_mod newref_itree ()).
Proof.
  apply tsim_implies_trefines => n.
  unshelve eapply tsim_remember.
  { simpl. exact (λ _ σa '(t, _),
  t ≈ newref_itree ∧
  ∃h, σa= Lam Waiting [] h newref_prog). }
  {naive_solver. }
  {naive_solver. }
  intros ???[????][??][?[??]]. inversion H2; subst.
  go_i. split!.
  - intros. go_s. go_s. exists (f, vs, h'). go. go_s. split!. go.
  go_s. intros. go. go_s. intros. go. go_s. intros. go. go_s. intros. destruct!. go. go_s. intros. go.
  go_i. split!. intros. rewrite lookup_insert_Some in H4. destruct!. split!. 
  (* ** newref part *)
  go_i. intros. split!.
  go_s. exists l. go. go_s. exists h'0. go. go_i. go_s. split!.
  go. go_s.
  split!. unfold heap_alloc_prop in H4. destruct!. inversion H2. apply heap_alloc_h_lookup. lia. lia.
  rewrite -/newref_itree. go. apply H0. auto. split!. 
  - intros. destruct!.
Qed.
   
Definition newref_nonnum_lam: fndef :={|
fd_args := [];
fd_body := NewRef (Val (ValNum 0)) (Val(ValBool true));
fd_static := I
|}.
Definition newref_nonnum_prog : gmap fid fndef :=
  <[("newref_nonnum",None) := newref_nonnum_lam]> $ ∅.
Definition newref_nonnum_mod := lam_mod newref_nonnum_prog.

Definition newref_nonnum_itree : itree (moduleE lam_event unit) unit :=
  h← TExist _;;;
  TVis (Incoming, ELCall ("newref_nonnum",None) [] h);;;;
  TUb.
Lemma newref_nonnum_itree_refines_newref_nonnum_lam:
  trefines (itree_mod newref_nonnum_itree ()) newref_nonnum_mod.
Proof.
  apply tsim_implies_trefines => n.
  go_i. intros. go. go_i. 
  go_s. left.
  eexists ("newref_nonnum", None),[],x.
  split!. 
  go_s. eexists _,_. split!. rewrite lookup_insert_Some. left. auto. intros.
  auto. go_s. exists (0,0). exists ∅.  
  split!. 
Qed.

Definition newref_zero_lam: fndef :={|
fd_args := [];
fd_body := NewRef (Val (ValNum 0)) (Val (ValNum 0));
fd_static := I
|}.
Definition newref_zero_prog : gmap fid fndef :=
  <[("newref_zero",None) := newref_zero_lam]> $ ∅.
Definition newref_zero_mod := lam_mod newref_zero_prog.

Definition newref_zero_itree : itree (moduleE lam_event unit) unit :=
  h← TExist _;;;
  TVis (Incoming, ELCall ("newref_zero",None) [] h);;;;
  TUb.
Lemma newref_zero_itree_refines_newref_zero_lam:
  trefines (itree_mod newref_zero_itree ()) newref_zero_mod.
Proof.
  apply tsim_implies_trefines => n.
  go_i. intros. go. go_i. go_s. left.
  eexists ("newref_zero", None),[],x.
  split!. 
  go_s. split!. rewrite lookup_insert_Some. left. auto. 
  auto. intros. go_s.
  eexists (0,0),∅. intros. destruct!.  split!. left. reflexivity.
Qed. 


(* ** identity function*)
Definition id_lam: fndef := {|
  fd_args := [];
  fd_body := FixE "" ["x"] (Var "x");
  fd_static := I
|}.
Definition id_prog : gmap fid fndef :=
  <[("id",None) := id_lam]> $ ∅.
Definition id_mod := lam_mod id_prog.

(* ** identity specification*)
Definition id_simple_itree : itree (moduleE lam_event (list fid)) unit :=
        '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ELCall f vs h));;;
        fid_list ← TGet ;;;
        TAssume (f = ("id",None));;;;
        TAssume (vs = []);;;;
        newfid ← TExist fid;;;
        TPut (newfid::fid_list);;;;
        TVis (Outgoing, ELReturn (ValFid newfid) h);;;;
        '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ELCall f vs h));;;
        fid_list ← TGet ;;;
        TAssume (f ∈ fid_list);;;;
        z ← TAll Z;;;
        TAssume (vs = [ValNum z]);;;;
        TVis (Outgoing, ELReturn (ValNum z) h);;;;
        TUb.

Lemma id_prog_refines_id_simple_itree :
  trefines id_mod (itree_mod id_simple_itree []).
Proof.
    apply tsim_implies_trefines => n0 /=. unfold id_prog.
    tstep_i;  split; intros.
    - go_s. exists (f,vs,h'). go. go_s. split!. go. go_s. go_s. intros. go.
    go_s. intros. go. go_i. split!.
      { intros. split!. subst. rewrite lookup_insert_Some in H2. destruct!. reflexivity.
      rewrite lookup_insert_Some in H2. destruct!. go_i. intros. split!.
      go_s. exists ("id", Some n). go. go_s. go_i. go_s. split!.
      go. go_i. split;intros. 
        - go_s. exists (f, vs, h'0). go. go_s. split!. go. go_s.
        go_s. intros. go. go_s. intros. go. go_s. intros. go.
        go_i. split.
        *  intros. rewrite elem_of_cons in H2. destruct!. rewrite lookup_insert_Some in H4. destruct!.
        split!. go_i. go_s. split!. go. go_s. auto. apply elem_of_nil in H2. inversion H2. 
        * intros. rewrite lookup_insert_None in H4. destruct!. rewrite elem_of_cons in H2. destruct!.
        apply elem_of_nil in H2. inversion H2. 
        - destruct!.  
      }
      {intros.  rewrite lookup_insert_None in H2. destruct!. } 
    - destruct!. 
    Unshelve. auto.
Qed.

Definition id_loop_itree : itree (moduleE lam_event (list fid)) unit :=
  ITree.forever(
        '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ELCall f vs h));;;
        fid_list ← TGet ;;;
        if (bool_decide(f = ("id",None)))
          then 
          TAssume (vs = []);;;;
          newfid ← TExist fid;;;
          TPut (newfid::fid_list);;;;
          TVis (Outgoing, ELReturn (ValFid newfid) h)
        else if (bool_decide(f∈fid_list))
          then 
          z ← TAll Z;;;
          TAssume (vs = [ValNum z]);;;;
          TVis (Outgoing, ELReturn (ValNum z) h)
        else TUb
  ).

Fixpoint fns_add_list fns l entry:=
  match l with 
    | [] => fns 
    | hd::tl => fns_add (fns_add_list fns tl entry) hd entry
    end.  

Lemma lookup_add_list_None m l entry f: fns_add_list m l entry !! f= None → m !! f = None.
Proof.
  induction l.
  auto.
  simpl. intros. rewrite lookup_insert_None in H. destruct!. auto.
Qed.

Lemma lookup_add_list_in m l entry f: f∈l→fns_add_list m l entry !! f= Some entry .
Proof.
  induction l.
  auto.
  simpl. intros. apply elem_of_nil in H. inversion H. 
  intros. apply elem_of_cons in H. destruct!. simpl.
  rewrite lookup_insert_Some . split!. simpl.
  rewrite lookup_insert_Some. destruct (bool_decide(a=f)) eqn:K.
  case_bool_decide. left. auto. inversion K. case_bool_decide. inversion K.
  right. naive_solver. 
Qed.

Lemma lookup_add_list_not_in m l entry f: f∉l→fns_add_list m l entry !! f= m !! f .
Proof.
  induction l.
  auto.
  simpl. intros. rewrite not_elem_of_cons in H. destruct!.
  apply IHl in H1. rewrite -H1. rewrite lookup_insert_ne. reflexivity. intro. subst. contradiction. 
Qed.

Lemma id_prog_refines_id_loop_itree :
  trefines id_mod (itree_mod id_loop_itree []).
Proof.
  apply tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember.
  {simpl. exact (λ _ σa '(t, l),
  t ≈ id_loop_itree ∧
  ∃h id_prog', σa= Lam Waiting [] h id_prog'/\ 
  id_prog' = fns_add_list id_prog l (Build_fndef ["x"] (Var "x") I) /\ 
  ("id",None)∉l). }
  {simpl. split!. reflexivity. intro. apply elem_of_nil in H. auto. }
  {simpl. intros. destruct!. split!. }
  {simpl. intros. destruct!.

  go_i. split!;[|intros;destruct!]. intros. go_s. go_s. exists (f,vs,h'). go.
  go_s. split!. go. go_s. case_bool_decide. 
  - (* f = ("id", None)*)
   go_s. intros. go. 
   go_i. split!.
   * intros. 
   rewrite lookup_add_list_not_in in H6; [|naive_solver]. rewrite lookup_insert_Some in H6.
   destruct!. split!.
   go_i. intros. exists I. go_i. go_s. exists ("id", Some n). go.
   go_s. go_s. split!.  rewrite -/id_loop_itree. go. apply H0. auto. split!.
   rewrite not_elem_of_cons. split!.
   * intros.  apply lookup_add_list_None in H6. rewrite lookup_insert_None in H6. destruct!.
  - case_bool_decide.
   * (* f = ("id", Some n)*)
    go_s. intros. go. go_s. intros. go.  go_i. split!.
    + intros. rewrite lookup_add_list_in in H7; auto. inversion H7. split!. naive_solver. subst.
    go_i. go_s. rewrite -/id_loop_itree. split!. go. apply H0. auto.
    split!. 
    + intros. apply (lookup_add_list_in id_prog l (Build_fndef ["x"] (Var "x") I)) in H4.
    rewrite H4 in H7. inversion H7. 
   * go_s. auto.  
  }
  Qed. 

(* ** recursive identity function*)
Definition rec_id_lam: fndef := {|
  fd_args := [];
  fd_body := FixE "f" ["x"] (
    If (BinOp (Var "x") EqOp (Val 0)) 
    (Val 0)
    (BinOp (Val 1) AddOp (App (Var "f") ([BinOp (Var "x") AddOp (Val (-1))])))
  );
  fd_static := I
|}.
Definition rec_id_prog : gmap fid fndef :=
  <[("rec_id",None) := rec_id_lam]> $ ∅.
Definition rec_id_mod := lam_mod rec_id_prog.

Definition rec_id_loop_itree : itree (moduleE lam_event (gmap fid unit)) unit :=
  ITree.forever(
        '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ELCall f vs h));;;
        fid_map ← TGet ;;;
        if (bool_decide(f = ("rec_id",None)))
          then 
          TAssume (vs = []);;;;
          newfid ← TExist fid;;;
          TPut (insert newfid () fid_map);;;;
          TVis (Outgoing, ELReturn (ValFid newfid) h)
        else if (bool_decide(f∈dom fid_map))
          then 
          z ← TAll Z;;;
          TAssume (vs = [ValNum z]);;;;
          TAssume (z>=0);;;;
          TVis (Outgoing, ELReturn (ValNum z) h)
        else TUb
  ).

Program Definition rec_id_prop elem key := 
  match elem with 
  | Some e => 
    e = Build_fndef ["x"] 
    (If (BinOp (Var "x") EqOp (Val 0)) 
    (Val 0)
    (BinOp (Val 1) AddOp (App (Val (ValFid key)) ([BinOp (Var "x") AddOp (Val (-1))])))) 
    _
  | _ => False
  end
.
Next Obligation. intros. simpl. destruct key. destruct o; auto.
Qed.


Lemma rec_id_map_forall_neq k (m:gmap _ unit) entry p: k ∉dom m → map_Forall
(λ (key : fid) (_ : ()), rec_id_prop (p !! key) key) m →
map_Forall (λ (key : fid) (_ : ()), rec_id_prop 
(fns_add p k entry !! key) key) m.
Proof.
  intros.
  assert (map_Forall (λ (key : fid) (_ : ()), k≠key/\rec_id_prop (p !! key) key) m).
  apply map_Forall_lookup_2.
  intros.
  split!.
  intro; subst. rewrite not_elem_of_dom in H. rewrite H1 in H. inversion H.
  rewrite  map_Forall_lookup in H0.
  eapply H0. exact H1.
  eapply map_Forall_impl.
  exact H1.
  simpl.
  intros.
  rewrite lookup_insert_ne; by destruct!.
Qed.
  
Lemma rec_id_fundamental_lemma x prog f n' Ks h': 
  0<=x→
  prog !! f =
  Some
    (Build_fndef ["x"]
       (If (BinOp (Var "x") EqOp (Val 0)) (Val 0)
          (BinOp (Val 1) AddOp
             (App (Val (ValFid f)) [BinOp (Var "x") AddOp (Val (-1))])))
       (rec_id_prop_obligation_1 f))→
  Lam
  (expr_fill Ks
     (If (BinOp (Val x) EqOp (Val 0)) (Val 0)
        (BinOp (Val 1) AddOp
           (App (Val (ValFid f)) [BinOp (Val x) AddOp (Val (-1))])))) [f.1]
  h' prog ⪯{lam_trans, lam_trans, n', true} 
  Lam
  (expr_fill Ks  (Val x)) [f.1]
  h' prog 
.
Proof.
  intros.
  generalize dependent Ks.
  remember (λ x,∀ Ks,
  Lam(expr_fill Ks
     (If (BinOp (Val x) EqOp (Val 0)) (Val 0)
        (BinOp (Val 1) AddOp
           (App (Val (ValFid f)) [BinOp (Val x) AddOp (Val (-1))])))) [f.1]
  h' prog ⪯{lam_trans, lam_trans, n', true} 
  Lam (expr_fill Ks  (Val x)) [f.1] h' prog ).
  remember (natlike_rec P).
  clear Heqp. subst.
  apply p; auto.
  - intros. go_i. split!. go_i. apply trefines_implies_tsim. reflexivity. (* reflexive*)
  - intros. go_i. split!. go_i. case_bool_decide. assert (~0 ≤ x0) by lia. contradiction.
    go_i. 
    assert (Z.succ x0 + -1 = x0) by lia.
    rewrite H4.
    go_i.
    split!.
    intros. rewrite H0 in H5. inversion H5. split!.
    assert (∀e, expr_fill Ks (BinOp (Val 1) AddOp e) = expr_fill ((BinOpRCtx 1 AddOp)::Ks) e) by auto.
    rewrite H6.
    apply trefines_implies_tsim.
    admit. (*transitive*)
  intros.
  rewrite H5 in H0.
  inversion H0.
Admitted.


Lemma rec_id_prog_refines_rec_id_loop_itree :
  trefines rec_id_mod (itree_mod rec_id_loop_itree ∅).
Proof.
  apply tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember.
  {simpl. 
  exact (λ _ σa '(t, m),
  t ≈ rec_id_loop_itree ∧
  ∃h rec_id_prog', σa= Lam Waiting [] h rec_id_prog'/\ 
  map_Forall (λ key _, rec_id_prop (rec_id_prog' !! key ) key)  m/\ 
  ("rec_id",None)∉ dom m/\ 
  rec_id_prog!!("rec_id",None)=rec_id_prog'!!("rec_id",None)). }
  {simpl. split!. reflexivity.  intro. intros. rewrite lookup_empty in H. inversion H. auto.  }
  {simpl. intros. destruct!. split!. }
  {simpl. intros. destruct!.

  go_i. split!;[|intros;destruct!]. intros. go_s. go_s. exists (f,vs,h'). go.
  go_s. split!. go. go_s. case_bool_decide.
  - (* f = ("rec_id", None)*)
   go_s. intros. go. 
   go_i. split!.
   * intros.  subst. rewrite -H6 in H8. rewrite lookup_insert_Some in H8. destruct!.
   split!. go_i. intros. exists I. go_i. go_s. rewrite -/rec_id_loop_itree. exists ("rec_id", Some n).
   go. go_s. go_s. split!. go. apply H0; auto. split!.  apply map_Forall_insert_2.
    + (*prove rec_id_prop*) rewrite lookup_insert. split!. f_equal. apply AxProofIrrelevance . 
    + apply rec_id_map_forall_neq; auto. 
    intro. rewrite map_Forall_lookup in H3. rewrite elem_of_dom in H7. unfold is_Some in H7. destruct!.
    apply H3 in H7. unfold rec_id_prop in H7. rewrite H5 in H7. auto.
    + rewrite not_elem_of_dom. rewrite lookup_insert_None; split!. by rewrite - not_elem_of_dom.
    +  rewrite (lookup_insert_ne _ ("rec_id", Some n)). auto. auto. 
   * intros. subst. rewrite -H6 in H8.   rewrite lookup_insert_None in H8. destruct!.
  - case_bool_decide.
   * (* f = ("rec_id", Some n)*)
    go_s. intros. go. go_s. intros. go.  go_i. split!.
    + intros. rewrite elem_of_dom in H7. destruct H7. rewrite map_Forall_lookup in H3.
    apply H3 in H7. rewrite H9 in H7. unfold rec_id_prop in H7. subst. split!. 
    go_s. intros. rewrite -/rec_id_loop_itree. go.

    (* ** main theorem!!*)
    assert (∀e, ReturnExt e = expr_fill [ReturnExtCtx] e).
    auto.
    rewrite H8.
    
    admit.
    + intros. rewrite elem_of_dom in H1. destruct H1. rewrite H9 in H1. inversion H1. 
   * go_s. auto.  
  }
  Admitted.
  

(* ** closure add*)
Definition clos_add_lam: fndef :={|
fd_args := [];
fd_body := 
  FixE "" ["x"] (
    FixE "" ["y"] (
      BinOp (Var "x") AddOp (Var "y")
    )
);
fd_static := I
|}.
Definition clos_add_prog : gmap fid fndef :=
  <[("clos_add",None) := clos_add_lam]> $ ∅.
Definition clos_add_mod := lam_mod clos_add_prog.

Inductive clos_add_ctype:=
  | Main
  | Initial 
  | Final (z:Z).

Definition clos_add_loop_itree : itree (moduleE lam_event (gmap fid clos_add_ctype)) unit :=
  ITree.forever(
        '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ELCall f vs h));;;
        fid_map ← TGet ;;;
        match fid_map !! f with 
          | Some Main => 
            TAssume (vs = []);;;;
            newfid ← TExist fid;;;
            TPut (insert newfid Initial fid_map);;;;
            TVis (Outgoing, ELReturn (ValFid newfid) h)
          | Some Initial => 
            x ← TAll _;;;
            TAssume (vs = [ValNum x]);;;;
            newfid ← TExist fid;;;
            TPut (insert newfid (Final x) fid_map);;;;
            TVis (Outgoing, ELReturn (ValFid newfid) h)
          | Some (Final x) =>  
            y ← TAll _;;;
            TAssume (vs = [ValNum y]);;;;
            TVis (Outgoing, ELReturn (ValNum (x+y)) h)
          | None => TUb 
        end
  ).

Definition clos_add_fns_m_prop (fns:gmap fid fndef) (m:gmap fid clos_add_ctype):Prop:= 
  ∀ f:fid, 
  (fns!!f = Some clos_add_lam ↔ m!!f = Some Main)/\ 
  (fns!!f = Some {|
    fd_args := ["x"];
    fd_body := 
      FixE "" ["y"] (
        BinOp (Var "x") AddOp (Var "y")
      )
    ;
    fd_static := I
    |} ↔ m!!f = Some Initial)/\ 
    (∀n, fns!!f = Some {|
    fd_args := ["y"];
    fd_body := 
      BinOp (Val (ValNum n)) AddOp (Var "y")
    ;
    fd_static := I
    |} ↔ m!!f = Some (Final n))
  .

Lemma clos_add_prog_refines_clos_add_loop_itree :
  trefines clos_add_mod (itree_mod clos_add_loop_itree (insert ("clos_add",None) Main ∅)).
Proof.
  apply tsim_implies_trefines. intros.
  unshelve eapply tsim_remember.
  {simpl. exact (λ n s '(t,m),
    t ≈ clos_add_loop_itree ∧
    ∃h fns, s= Lam Waiting [] h fns ∧
    clos_add_fns_m_prop fns m
    ). }
  {simpl. split!. reflexivity. unfold clos_add_fns_m_prop. intros. split!; split; intros;
   rewrite lookup_insert_Some in H;rewrite lookup_insert_Some;naive_solver. }
  {simpl. intros. auto. }
  {simpl. intros. destruct!. go_i. split!.
   {intros. go_s. go_s. rewrite -/clos_add_loop_itree. exists (f, vs, h'). go. go_s. split!. go. go_s.
    destruct (m!!f) eqn:V.  unfold clos_add_fns_m_prop in H4. remember (H4 f). destruct!. clear Heqa.
    - destruct c eqn:V'.
      + (* main case*) go_s. intros. go. go_i. split!; intros. 
        * rewrite- H3 in V. rewrite H8 in V. inversion V. subst. split!.
          go_i. intros. exists I. go_i. go_s. exists (f.1, Some n0). go. go_s. go_s. split!. go.
          apply H0. auto. split!.  
          unfold clos_add_fns_m_prop. 
          intros;split!; split;intros; 
          rewrite lookup_insert_Some in H9; rewrite lookup_insert_Some; naive_solver.
        * rewrite -H3 in V. rewrite H8 in V. inversion V.   
      + (* Initial case*)  go_s. intros. go. go_s. intros. go. go_i. split!; intros. 
        * rewrite -H6 in V. rewrite H8 in V. inversion V. subst. split!. 
        go_i. intros. exists I. go_i. go_s. exists (f.1, Some n0). go. go_s. go_s. split!. go. apply H0.
        auto. split!.
        unfold clos_add_fns_m_prop. 
        intros;split!; split;intros; 
        rewrite lookup_insert_Some in H9; rewrite lookup_insert_Some; naive_solver.
        * rewrite -H6 in V. rewrite H8 in V. inversion V.  
      + (* Final case*) go_s. intros. go. go_s. intros. go. go_i. split!; intros. 
        * rewrite -H7 in V. rewrite H8 in V. inversion V. subst. split!.
          go_i. go_i. go_s. split!. go. apply H0. auto. split!. 
        * rewrite -H7 in V. rewrite H8 in V. inversion V.  
    - go_s. auto. 
   } 
   {intros. destruct!. }
  }
Qed.


Definition main_lam: fndef := {|
  fd_args := ["input"];
  fd_body := App (Val $ ValFid ("id",None)) [Var "input"];
  fd_static := I
|}.

Definition main_prog: gmap fid fndef := 
    <[("main",None) := main_lam]> $ ∅.
