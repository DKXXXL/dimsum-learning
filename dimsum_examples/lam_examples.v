From dimsum.core Require Export proof_techniques.
From dimsum.core Require Import spec_mod.
From dimsum.core Require Import axioms.
From dimsum.examples Require Import lam.

Local Open Scope Z_scope.

Local Ltac go :=
  clear_spec.
Local Ltac go_s :=
  tstep_s; go.
Local Ltac go_i :=
  tstep_i; go.

Definition nb_spec: spec  lam_event unit void:= TNb.
Lemma ub_spec_refines_everything s:
  trefines (spec_mod nb_spec ()) s.
Proof.
  apply tsim_implies_trefines=>n. unfold nb_spec.
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

Definition free_var_spec : spec  lam_event unit void:=
  h← TExist _;
  TVis (Incoming, ELCall ("free_var",None) [] h);;
  TUb.

Lemma free_var_spec_refines_free_var_lam:
  trefines (spec_mod free_var_spec ()) free_var_mod.
Proof.
  apply tsim_implies_trefines => n /=. unfold free_var_spec, free_var_prog. 
  go_i. intros. go. go_i. go_s. left. eexists _,_,_. split!.
  go_s. split!. eauto. intros. auto.
  unfold free_var_lam in H. rewrite lookup_insert_Some in H. destruct!. simpl. go_s. auto. 
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

Definition add_spec : spec lam_event unit void :=
        '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ELCall f vs h));
        TAssume (f= ("add",None));;
        x ← TAll _;
        y ← TAll _; 
        TAssume (vs = [ValNum x;ValNum y]);;
        TVis (Outgoing, ELReturn (ValNum (x+y)) h);;
        TUb.
Lemma add_prog_refines_add_spec :
  trefines add_mod (spec_mod add_spec ()).
Proof.
  apply tsim_implies_trefines => n. 
  go_i. split!. intros. go_s. eexists (f, vs, h'). go.
  go_s. split!. go. go_s. intros. go. go_s. intros. go.
  go_s. intros. go. go_s. intros. go.
  go_i. split!. intros. split!. unfold add_prog in *.  
  rewrite lookup_insert_Some. split!.   destruct!. auto. subst.  go_i. go_i. go_i.
  go_s. split!. go. go_s.  auto.
  intros. destruct!.
Qed.

Definition add_repeat_spec : spec  lam_event unit void :=
        Spec.forever(
          '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ELCall f vs h));
          TAssume (f= ("add",None));;
          x ← TAll _;
          y ← TAll _; 
          TAssume (vs = [ValNum x;ValNum y]);;
          TVis (Outgoing, ELReturn (ValNum (x+y)) h)
        ) .
Lemma add_prog_refines_add_repeat_spec :
  trefines add_mod (spec_mod add_repeat_spec ()).
Proof.
  apply tsim_implies_trefines => n.
  unshelve eapply tsim_remember.
  { simpl. exact (λ _ σa '(t, _),
  t ≡ add_repeat_spec ∧
  ∃h, σa= Lam Waiting [] h add_prog). } 
  {simpl. naive_solver. }
  { simpl. eauto. }
  { simpl. intros ???[????][??][??]. destruct!. 
  go_i. split!. intros. go_s. go_s. rewrite -/add_repeat_spec. eexists (f, vs, h'). go.
  go_s. intros. split. naive_solver. go. go_s. intros. go. go_s. intros.
  go. go_s. intros. go. go_s. intros. go. go_i. split.
  intros. unfold add_prog. split!. rewrite lookup_insert_Some. destruct!/=; subst.
  split!. by subst. subst. go_i. go_i. go_i. go_s. split!. go. 
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
Definition add_wrong_spec : spec lam_event unit void:=
  h← TExist _;
  TVis (Incoming, ELCall ("add_wrong",None) [] h);;
  TUb.

Lemma add_wrong_spec_refines_add_wrong_lam:
  trefines (spec_mod  add_wrong_spec ()) add_wrong_mod.
Proof.
  apply tsim_implies_trefines => n.
  go_i. intros. go. go_i. 
  go_s. left.
  eexists ("add_wrong", None),[],x.
  split!. 
  go_s. left. split!. intros. rewrite lookup_insert_Some in H. destruct!. 
  go_s. intros. inversion H1.
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

Definition newref_spec : spec  lam_event unit void:=
    Spec.forever(
      '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ELCall f vs h));
      TAssume (f= ("newref",None));;
      x ← TAll _;
      y ← TAll _; 
      TAssume (vs = [ValNum x;ValNum y]);;
      TAssume (y>0);;
      l ← TExist _;
      h' ← TExist _;
      TVis (Outgoing, ELReturn (ValLoc l) h');;
      (* ** add assertions*)
      TAssert( h'.(h_heap)!!l = Some (ValNum x))
    ) .
Lemma newref_prog_refines_newref_spec :
  trefines newref_mod (spec_mod newref_spec ()).
Proof.
  apply tsim_implies_trefines => n.
  unshelve eapply tsim_remember.
  { simpl. exact (λ _ σa '(t, _),
  t ≡ newref_spec ∧
  ∃h, σa= Lam Waiting [] h newref_prog). }
  {naive_solver. }
  {naive_solver. }
  intros ???[????][??][?[??]]. inversion H2; subst.
  go_i. split!.
  - intros. go_s. go_s. exists (f, vs, h'). go. go_s. split!. go.
  go_s. intros. go. go_s. intros. go. go_s. intros. go. go_s. intros. destruct!. go. go_s. intros. go.
  go_i. split!. intros. split!. rewrite lookup_insert_Some . left;done. auto. 
  (* ** newref part *)
  go_i. intros. split!.
  go_s. exists l. go. go_s. exists h'0. go. go_i. go_i. go_s. split!.
  go. go_s.
  split!. unfold heap_alloc_prop in H4. destruct!. inversion H1. apply heap_alloc_h_lookup. lia. lia.
  rewrite -/newref_spec. go. apply H0. auto. split!. 
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

Definition newref_nonnum_spec : spec  lam_event unit void :=
  h← TExist _;
  TVis (Incoming, ELCall ("newref_nonnum",None) [] h);;
  TUb.
Lemma newref_nonnum_spec_refines_newref_nonnum_lam:
  trefines (spec_mod newref_nonnum_spec ()) newref_nonnum_mod.
Proof.
  apply tsim_implies_trefines => n.
  go_i. intros. go. go_i. 
  go_s. left.
  eexists ("newref_nonnum", None),[],x.
  split!. 
  go_s. left. split!. intros. rewrite lookup_insert_Some in H. destruct!. 
  go_s. exists (0,0). exists ∅.  
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

Definition newref_zero_spec : spec  lam_event unit void :=
  h← TExist _;
  TVis (Incoming, ELCall ("newref_zero",None) [] h);;
  TUb.
Lemma newref_zero_spec_refines_newref_zero_lam:
  trefines (spec_mod newref_zero_spec ()) newref_zero_mod.
Proof.
  apply tsim_implies_trefines => n.
  go_i. intros. go. go_i. go_s. left.
  eexists ("newref_zero", None),[],x.
  split!. 
  go_s. split!. intros. rewrite lookup_insert_Some in H. destruct!. 
  go_s.
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
Definition id_simple_spec : spec  lam_event (list fid) void :=
        '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ELCall f vs h));
        fid_list ← TGet ;
        TAssume (f = ("id",None));;
        TAssume (vs = []);;
        newfid ← TExist fid;
        TPut (newfid::fid_list);;
        TVis (Outgoing, ELReturn (ValFid newfid) h);;
        '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ELCall f vs h));
        fid_list ← TGet ;
        TAssume (f ∈ fid_list);;
        z ← TAll Z;
        TAssume (vs = [ValNum z]);;
        TVis (Outgoing, ELReturn (ValNum z) h);;
        TUb.

Lemma id_prog_refines_id_simple_spec :
  trefines id_mod (spec_mod id_simple_spec []).
Proof.
    apply tsim_implies_trefines => n0 /=. unfold id_prog.
    tstep_i;  split; intros.
    - go_s. exists (f,vs,h'). go. go_s. split!. go. go_s. go_s. intros. go.
    go_s. intros. go. go_i. split!.
      { intros. split!.  rewrite lookup_insert_Some . split!. subst. auto. 
      go_i. intros. split!.
      go_s. exists ("id", Some n). go. go_s. go_i. go_i. go_s. split!. subst. done.
      go. go_i. split;intros.  
        - go_s. eexists (_,_,_). go. go_s. split!. go. go_s.
        go_s. intros. go. go_s. intros. go. go_s. intros. go.
        go_i. split.
        *  intros. split!.  rewrite lookup_insert_Some. left. split!. rewrite elem_of_cons in H5. destruct!.
        auto. apply elem_of_nil in H5. done. subst. auto.
        subst. go_i. go_i. go_s. split!. go. go_s. auto. 
        * intros. rewrite lookup_insert_None in H3. destruct!.
        - destruct!.  
      }
      
    - destruct!. 
    Unshelve. auto.
Qed.

Definition id_loop_spec : spec  lam_event (list fid) void :=
  Spec.forever(
        '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ELCall f vs h));
        fid_list ← TGet ;
        if (bool_decide(f = ("id",None)))
          then 
          TAssume (vs = []);;
          newfid ← TExist fid;
          TPut (newfid::fid_list);;
          TVis (Outgoing, ELReturn (ValFid newfid) h)
        else if (bool_decide(f∈fid_list))
          then 
          z ← TAll Z;
          TAssume (vs = [ValNum z]);;
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

Lemma id_prog_refines_id_loop_spec :
  trefines id_mod (spec_mod id_loop_spec []).
Proof.
  apply tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember.
  {simpl. exact (λ _ σa '(t, l),
  t ≡ id_loop_spec ∧
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
   * intros. split!. 
   rewrite lookup_add_list_not_in; [|naive_solver]. rewrite lookup_insert_Some. left.
   split!. by subst.
   go_i. intros. exists I. go_i. go_i. go_s. exists ("id", Some n). go.
   go_s. go_s. split!. by subst.  rewrite -/id_loop_spec. go. apply H0. auto. split!. by subst.
   rewrite not_elem_of_cons. split!.
  - case_bool_decide.
   * (* f = ("id", Some n)*)
    go_s. intros. go. go_s. intros. go.  go_i. split!.
    + intros. split!. rewrite lookup_add_list_in; auto. subst;auto. subst. 
    go_i. go_i. go_s. rewrite -/id_loop_spec. split!. go. apply H0. auto.
    split!. 
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

Definition rec_id_loop_spec : spec  lam_event (gmap fid unit) void :=
  Spec.forever(
        '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ELCall f vs h));
        fid_map ← TGet ;
        if (bool_decide(f = ("rec_id",None)))
          then 
          TAssume (vs = []);;
          newfid ← TExist fid;
          TPut (insert newfid () fid_map);;
          TVis (Outgoing, ELReturn (ValFid newfid) h)
        else if (bool_decide(f∈dom fid_map))
          then 
          z ← TAll Z;
          TAssume (vs = [ValNum z]);;
          TAssume (z>=0);;
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
  
(* to remove*)
(*
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
*)

(* ** TODO *)
Lemma rec_id_prog_refines_rec_id_loop_spec :
  trefines rec_id_mod (spec_mod rec_id_loop_spec ∅).
Proof.
  apply tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember.
  {simpl. 
  exact (λ _ σa '(t, m),
  t ≡ rec_id_loop_spec ∧
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
   * intros.  subst. split!. rewrite -H6. rewrite lookup_insert_Some. left. split!. auto. 
   go_i. intros. exists I. go_i. go_s. rewrite -/rec_id_loop_spec. exists ("rec_id", Some n).
   go. go_i. go_s. go_s. split!. go. apply H0; auto. split!.  apply map_Forall_insert_2.
    + (*prove rec_id_prop*) rewrite lookup_insert. split!. f_equal. apply AxProofIrrelevance . 
    + apply rec_id_map_forall_neq; auto. 
    intro. rewrite map_Forall_lookup in H3. rewrite elem_of_dom in H5. unfold is_Some in H5. destruct!.
    apply H3 in H5. unfold rec_id_prop in H5. rewrite H2 in H5. auto.
    + rewrite not_elem_of_dom. rewrite lookup_insert_None; split!. by rewrite - not_elem_of_dom.
    +  rewrite (lookup_insert_ne _ ("rec_id", Some n)). auto. auto. 
  - case_bool_decide.
   * (* f = ("rec_id", Some n)*)
    go_s. intros. go. go_s. intros. go. go_s. intros. rewrite -/rec_id_loop_spec. go. 
    simplify_eq/=.  rewrite elem_of_dom in H5. destruct H5. rewrite map_Forall_lookup in H3. 
    apply H3 in H5. unfold rec_id_prop in H5. case_match; try done. 
    unshelve eapply tsim_remember.
    {simpl. exact (λ n σa '(t,m),
    ∀n', 
    n' ⊆ n → 
    t ≡(TVis (Outgoing, ELReturn x h');; rec_id_loop_spec)%spec /\ 
    ∃ e Ks e' s x', 
    x'>=0 /\
    LamExprFill e Ks e' /\ 
    σa = Lam e s h' rec_id_prog' /\ 
    e' = App (Val (ValFid f)) [Val (ValNum x')] /\ 
    Lam (expr_fill Ks (Val(ValNum x'))) s h' rec_id_prog' ⪯{lam_trans, spec_trans lam_event (gmap fid ()), n', true} 
    (t, m)
    ). } { simpl. intros.  split!. done.  apply _. tstep_i. tstep_s. split!. go. apply H0; auto. split!. } {
      simpl. intros. destruct!. intros. 
      assert (n'1 ⊆ n). apply o_lt_impl_le in H9. eapply transitivity. done. done.
      apply H10 in H11.  destruct!.  split!. all:try done. }
    simpl.
    intros n'' ineq Hloop.
    intros. destruct!.
    remember (H9 n'').
    assert (n''⊆ n'') by auto.
    apply a in H5. destruct!.

    tstep_i. split!.
    intros. split!.
    destruct (x'=?0) eqn:?; try done.  rewrite Z.eqb_eq in Heqb; subst.
    -- (* 0 *) tstep_i. split!. tstep_i. go_i. done.
    -- rewrite Z.eqb_neq in Heqb. tstep_i. split!. case_bool_decide; try done. tstep_i. tstep_i. apply Hloop. auto.
    intros. split!. assert(x'+-1>=0) by lia. exact H16. apply _. simpl. tstep_i. tstep_i. 
    assert (1 + (x' + -1) = x') by lia. rewrite H16. 
    eapply tsim_mono; done.
    (* ** main theorem!!*)
  
   * go_s. auto.  
  }
Qed.
  

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

Definition clos_add_loop_spec : spec  lam_event (gmap fid clos_add_ctype) void :=
  Spec.forever(
        '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ELCall f vs h));
        fid_map ← TGet ;
        match fid_map !! f with 
          | Some Main => 
            TAssume (vs = []);;
            newfid ← TExist fid;
            TPut (insert newfid Initial fid_map);;
            TVis (Outgoing, ELReturn (ValFid newfid) h)
          | Some Initial => 
            x ← TAll _;
            TAssume (vs = [ValNum x]);;
            newfid ← TExist fid;
            TPut (insert newfid (Final x) fid_map);;
            TVis (Outgoing, ELReturn (ValFid newfid) h)
          | Some (Final x) =>  
            y ← TAll _;
            TAssume (vs = [ValNum y]);;
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

Lemma clos_add_prog_refines_clos_add_loop_spec :
  trefines clos_add_mod (spec_mod clos_add_loop_spec (insert ("clos_add",None) Main ∅)).
Proof.
  apply tsim_implies_trefines. intros.
  unshelve eapply tsim_remember.
  {simpl. exact (λ n s '(t,m),
    t ≡ clos_add_loop_spec ∧
    ∃h fns, s= Lam Waiting [] h fns ∧
    clos_add_fns_m_prop fns m
    ). }
  {simpl. split!. reflexivity. unfold clos_add_fns_m_prop. intros. split!; split; intros;
   rewrite lookup_insert_Some in H;rewrite lookup_insert_Some;naive_solver. }
  {simpl. intros. auto. }
  {simpl. intros. destruct!. go_i. split!.
   {intros. go_s. go_s. rewrite -/clos_add_loop_spec. exists (f, vs, h'). go. go_s. split!. go.  go_s.
   unfold clos_add_fns_m_prop in H4. remember (H4 f). destruct!. clear Heqa.
   repeat case_match.
    - (* main case*) go_s. intros. go.  go_i. split!; intros.
      split!. by erewrite H2. subst. auto.  go_i. intros. exists I. go_i. go_i. go_s. exists (f.1, Some n0). go.
      go_s. go_s. split!. go. apply H0; try done. split!. 
      unfold clos_add_fns_m_prop, fns_add;intros;split!;split;intros H11;
      rewrite lookup_insert_Some in H11; rewrite lookup_insert_Some; naive_solver.
    - (* initial*) tstep_s. intros;go. tstep_s. intros; go. tstep_i. split!. intros. split!.
      naive_solver. naive_solver. tstep_i. subst. tstep_i. intros. exists I. intros.
      split!. done. tstep_i. tstep_i. tstep_s. exists (f.1, Some n0). go. tstep_s. go. tstep_s.
      split!. go. apply H0; try done. split!. unfold clos_add_fns_m_prop.
      intros;split!; split; unfold fns_add;rewrite !lookup_insert_Some;intros; naive_solver.
    - (* final *) go_s. intros;go. tstep_s. intros;go. tstep_i. split!. intros. split!.
      naive_solver. naive_solver. tstep_i. subst. tstep_i. intros. split!;try done.
      tstep_i. tstep_i. tstep_s. split!. go. apply H0; try done. split!.
    - (* none*) by tstep_s.

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
