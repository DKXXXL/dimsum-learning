From dimsum.core.itree Require Export upstream events.
From dimsum.core Require Import universes module axioms itree_mod.
From dimsum.examples Require Import rec.

Local Open Scope Z_scope.

(** ** Operational semantics *)
Definition get_rec_heap {E} `{!stateE rec_state -< E} : itree E heap_state :=
  (σ ← get_state; Ret σ.(st_heap))%itree.
Definition set_rec_heap {E} `{!stateE rec_state -< E} (h : heap_state) : itree E unit :=
  (σ ← get_state; set_state (Rec σ.(st_expr) h σ.(st_fns));; Ret tt)%itree.
Definition get_rec_fns {E} `{!stateE rec_state -< E} : itree E (gmap string fndef) :=
  (σ ← get_state; Ret σ.(st_fns))%itree.

Definition rec_expr_itree (e : expr) : itree (callE expr val +' moduleE rec_event rec_state) val :=
  match e with
  | Val v => Ret v
  | BinOp e1 op e2 =>
      v1 ← call e1;
      v2 ← call e2;
      v ← eval_binop op v1 v2?;
      Ret v
  | Load e1 =>
      v1 ← call e1;
      l ← val_to_loc v1?;
      h ← get_rec_heap;
      v ← (h.(h_heap) !! l)?;
      Ret v
  | Store e1 e2 =>
      v1 ← call e1;
      v2 ← call e2;
      l ← val_to_loc v1?;
      h ← get_rec_heap;
      assume (heap_alive h l);;
      set_rec_heap (heap_update h l v2);;
      Ret v2
  | If e1 e2 e3 =>
      v1 ← call e1;
      b ← val_to_bool v1?;
      if b then
        call e2
      else
        call e3
  | LetE x e1 e2 =>
      v1 ← call e1;
      call (subst x v1 e2)
  | AllocA xs e =>
      assume (Forall (λ x, 0 < x) xs.*2);;
      h ← get_rec_heap;
      ls ← demonic _;
      h' ← demonic _;
      assert (heap_alloc_list xs.*2 ls h h');;
      set_rec_heap h';;
      v ← call (subst_l xs.*1 (ValLoc <$> ls) e);
      he ← get_rec_heap;
      he' ← angelic _;
      assume (heap_free_list (zip ls xs.*2) he he');;
      set_rec_heap he';;
      Ret v
  | Call f es =>
      vs ← ITree.flat_map call es;
      fns ← get_rec_fns;
      if fns !! f is Some fn then
        assume (length vs = length fn.(fd_args));;
        call (AllocA fn.(fd_vars) (subst_l fn.(fd_args) vs fn.(fd_body)))
      else
        h ← get_rec_heap;
        visible (Outgoing, ERCall f vs h);;
        call (Waiting true)
  | Waiting b =>
      c ← demonic bool;
      if c then
        fns ← get_rec_fns;
        f ← demonic _;
        vs ← demonic _;
        h ← demonic _;
        fn ← (fns !! f)!;
        set_rec_heap h;;
        visible (Incoming, ERCall f vs h);;
        v ← call (Call f (Val <$> vs));
        h ← get_rec_heap;
        visible (Outgoing, ERReturn v h);;
        call (Waiting b)
      else
        assert (b = true);;
        v ← demonic _;
        h ← demonic _;
        set_rec_heap h;;
        visible (Incoming, ERReturn v h);;
        Ret v
  | _ =>
      UB
  end%itree.

Definition rec_itree : itree (moduleE rec_event rec_state) void :=
  ITree.bind (rec' rec_expr_itree (Waiting false)) (λ _, NB).

Local Ltac go :=
  clear_itree; repeat itree_step.
Local Ltac go_s :=
  tstep_s; go.
Local Ltac go_i :=
  tstep_i; go.

(** ** rec_itree_expr_inv

    [rec_itree_expr_inv] is a version of [is_static_expr] for proving
    the equivalence.

    TODO: Define a version of is_static_expr that takes a predicate on
    the head of the expression and lifts it to the whole expression. *)
Local Fixpoint rec_itree_expr_inv (e : expr) : bool :=
  match e with
  | Var v => true
  | Val v => true
  | BinOp e1 o e2 => rec_itree_expr_inv e1 && rec_itree_expr_inv e2
  | Load e1 => rec_itree_expr_inv e1
  | Store e1 e2 => rec_itree_expr_inv e1 && rec_itree_expr_inv e2
  | If e e1 e2 => rec_itree_expr_inv e && rec_itree_expr_inv e1 && rec_itree_expr_inv e2
  | LetE v e1 e2 => rec_itree_expr_inv e1 && rec_itree_expr_inv e2
  | Call f args => forallb rec_itree_expr_inv args
  | AllocA _ e => rec_itree_expr_inv e
  | FreeA _ e => false
  | ReturnExt can_return_further e => false
  | Waiting can_return => true
  end.

Local Lemma rec_itree_expr_inv_forallb vs:
  forallb rec_itree_expr_inv (Val <$> vs).
Proof. by apply forallb_True, Forall_fmap, Forall_true. Qed.

Local Lemma rec_itree_expr_inv_subst x v e:
  rec_itree_expr_inv e →
  rec_itree_expr_inv (subst x v e).
Proof.
  elim: e => //= *; try naive_solver.
  - by case_bool_decide.
  - case_bool_decide; naive_solver.
  - apply forallb_True, Forall_forall => ? /elem_of_list_fmap[?[??]]. subst.
    revert select (Forall _ _) => /Forall_forall.
    revert select (Is_true (forallb _ _)) => /forallb_True/Forall_forall. naive_solver.
Qed.

Local Lemma rec_itree_expr_inv_subst_l xs vs e:
  rec_itree_expr_inv e →
  rec_itree_expr_inv (subst_l xs vs e).
Proof.
  elim: xs vs e. { by case. }
  move => ?? IH [//|??] /=??. apply IH.
  by apply rec_itree_expr_inv_subst.
Qed.

Local Lemma is_static_expr_rec_itree_expr_inv e:
  is_static_expr false e →
  rec_itree_expr_inv e.
Proof.
  elim: e => //=; try naive_solver.
  move => ?? IH /forallb_True.
  elim: IH => // *. decompose_Forall_hyps; naive_solver.
Qed.

(** ** equivalence proof *)
Lemma rec_itree_refines_rec_call t e h fns k K f args b n:
  t ⊒ ↓ᵢ (ITree.bind (interp (recursive' rec_expr_itree) (ITree.flat_map call args)) k) →
  (∀ t' e' h' K' a k,
      a ∈ args →
      t' ⊒ ↓ᵢ (Tau (ITree.bind (rec' rec_expr_itree a) k)) →
      (∀ t'' e'' h'' v,
          t'' ⊒ ↓ᵢ (k v) →
          (t'', Rec e'' h'' fns) ⪯{itree_trans rec_event rec_state, rec_trans, n, b}
            Rec (expr_fill K' (Val v)) h'' fns) →
      (t', Rec e' h' fns) ⪯{itree_trans rec_event rec_state, rec_trans, n, b}
        Rec (expr_fill K' a) h' fns) →
  (∀ t' e' h' argsv,
      t' ⊒ ↓ᵢ (k argsv) →
      (t', Rec e' h' fns) ⪯{itree_trans rec_event rec_state, rec_trans, n, b}
        Rec (expr_fill K (Call f (Val <$> argsv))) h' fns) →
  (t, Rec e h fns) ⪯{itree_trans rec_event rec_state, rec_trans, n, b}
    Rec (expr_fill K (Call f args)) h fns.
Proof.
  move => Ht Hargs Hret. move: Ht Hargs.
  change args with ((Val <$> []) ++ args) at 3.
  change k with (λ x, k ([] ++ x)).
  move: (@nil val) => argsv.
  elim: args argsv h e t.
  { move => argsv h e t /= Ht ?. go. move: Ht. rewrite !app_nil_r. naive_solver. }
  move => /= arg args IH argsv h e t Ht Ha.
  go_i. change (Call _ _) with (expr_fill ([CallCtx f argsv args]) arg).
  rewrite -expr_fill_app. eapply Ha; [set_solver|done|].
  move => ??? /=??. rewrite cons_middle app_assoc -fmap_snoc.
  apply IH; [|set_solver].
  etrans; [done|].
  rewrite interp_bind bind_bind. setoid_rewrite interp_ret.
  setoid_rewrite bind_ret_l. do 2 f_equiv. move => ?. by rewrite <-app_assoc.
Qed.

Lemma rec_itree_refines_rec fns :
  trefines (itree_mod rec_itree (rec_init fns)) (rec_mod fns).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  rewrite /rec_itree.
  unshelve eapply tsim_remember. { simpl. exact (λ n '(t, Rec _ hi fnsi) '(Rec es hs fnss),
    ∃ K e k,
    t ⊒ ↓ᵢ (ITree.bind (rec' rec_expr_itree e) k) ∧
    RecExprFill es K e ∧ hi = hs ∧ fnsi = fns ∧ fnss = fns ∧
    rec_itree_expr_inv e ∧
    ∀ v t' ei h' b, t' ⊒ ↓ᵢ (k v) → (t', Rec ei h' fns) ⪯{itree_trans rec_event rec_state, rec_trans, n, b} Rec (expr_fill K (Val v)) h' fns). }
  { exists []. split!; [done|apply _|done|]. move => ??????/=. by go_i. } {
    move => ?? [?[???]] [???] ? /= ?. destruct!. split!; [done..|]. move => *. apply: tsim_mono; naive_solver. }
  move => n /= ? Hloop [?[???]] [???] [? [e ?]]. destruct!/=.
  rename H6 into Hret. go_i.
  revert select (RecExprFill _ _ _) => -[?].
  destruct e; simplify_eq/=.
  - by tstep_s.
  - go_i. by apply Hret.
  - go_i. go_i.
    apply Hloop; [done|]. split!; [done|apply _|naive_solver|].
    move => /= *. go.
    go_i. go_i.
    apply Hloop; [done|]. split!; [done|apply _|naive_solver|].
    move => /= *. go.
    go_s => ??.
    go_i. split!. go.
    by apply Hret.
  - go_i. go_i.
    apply Hloop; [done|]. split!; [done|apply _|naive_solver|].
    move => /= *. go.
    go_s => *. simplify_eq/=.
    go_i. go_i. split!. go.
    by apply Hret.
  - go. go_i. go_i.
    apply Hloop; [done|]. split!; [done|apply _|naive_solver|].
    move => /= *. go.
    go_i. go_i.
    apply Hloop; [done|]. split!; [done|apply _|naive_solver|].
    move => /= *. go.
    go_s => *. simplify_eq/=. go.
    go_i. go_i. split!. go. go_i. go_i.
    by apply Hret.
  - go. go_i. go_i.
    apply Hloop; [done|]. split!; [done|apply _|naive_solver|].
    move => /= *. go.
    go_s => b *. simplify_eq/=. go_i.
    destruct b; go_i; go_i.
    all: apply Hloop; [done|]; split!; [done|apply _|naive_solver|done].
  - go. go_i. go_i.
    apply Hloop; [done|]. split!; [done|apply _|naive_solver|].
    move => /= *. go.
    go_s.
    go_i. go_i.
    apply Hloop; [done|].
    split!; [done|apply _|apply rec_itree_expr_inv_subst; naive_solver|done].
  - go. revert select (Is_true (forallb _ _)) => /forallb_True/Forall_forall?.
    apply: rec_itree_refines_rec_call; [done|..]. {
      move => ???????? Hret2. go_i. apply Hloop; [done|].
      split!; [done|apply _|naive_solver| ].
      move => /= *. apply tsim_mono_b_false. naive_solver.
    }
    move => /= ?????. go_i.
    case_match.
    + go_s. split!. move => ?. go_i. split!. go. go_i. go_i.
      apply Hloop; [done|].
      split!; [done|apply _| |done].
      cbn. apply rec_itree_expr_inv_subst_l.
      apply is_static_expr_rec_itree_expr_inv. apply fd_static.
    + go_i. go_i. go_s. split!. go_i. go_i.
      apply Hloop; [done|]. split!; [done|apply _|done|done].
  - go.
    destruct (decide (Forall (λ x : Z, 0 < x) ls.*2)).
    2: { go_s. exploit (heap_alloc_list_fresh ls.*2 ∅) => -[??]. by split!. }
    go_i. split!. go. go_i.
    go_i => ?. go.
    go_i => ?. go.
    go_i => ?. go.
    go_i. go_i. go_i. go_i.
    go_s. split!; [done|]. move => ?.
    apply Hloop; [done|]. split!; [done|apply _| |].
    { move => *. apply rec_itree_expr_inv_subst_l. naive_solver. }
    move => /= *. go.
    go_s => ??.
    go_i. go_i. split!. go. go_i. split!; [done|]. go.
    go_i. go_i.
    by apply Hret.
  - done.
  - done.
  - go_i => b. go.
    destruct b.
    + go_i. go_i => ?. go. go_i => ?. go. go_i => ?. go.
      go_i => ??. go. go_i. go_i. go_i.
      go_s. split!. go_i. go_i.
      apply Hloop; [done|]. split!; [done|apply _| |].
      { move => /=. apply rec_itree_expr_inv_forallb. }
      move => /= *. go.
      go_i. go_i.
      go_s. split!.
      go_i. go_i.
      apply Hloop; [done|]. split!; [done|apply _|done|done].
    + go_i => ?. go. simplify_eq. go_i => ?. go. go_i => ?. go. go_i. go_i.
      go_i. go_s. split!.
      by apply Hret.
Qed.

Lemma rec_refines_rec_itree_call t e h fns k K f args b n:
  t ⊒ ↓ᵢ (ITree.bind (interp (recursive' rec_expr_itree) (ITree.flat_map call args)) k) →
  (∀ t' e' h' K' a k,
      a ∈ args →
      t' ⊒ ↓ᵢ (Tau (ITree.bind (rec' rec_expr_itree a) k)) →
      (∀ t'' e'' h'' v,
          t'' ⊒ ↓ᵢ (k v) →
           (Rec (expr_fill K' (Val v)) h'' fns) ⪯{rec_trans, itree_trans rec_event rec_state, n, b}
            (t'', Rec e'' h'' fns)) →
       Rec (expr_fill K' a) h' fns ⪯{rec_trans, itree_trans rec_event rec_state, n, b}
        (t', Rec e' h' fns)) →
  (∀ t' e' h' argsv,
      t' ⊒ ↓ᵢ (k argsv) →
      (Rec (expr_fill K (Call f (Val <$> argsv))) h' fns)
        ⪯{rec_trans, itree_trans rec_event rec_state, n, b}
        (t', Rec e' h' fns)) →
  (Rec (expr_fill K (Call f args)) h fns) ⪯{rec_trans, itree_trans rec_event rec_state, n, b}
    (t, Rec e h fns).
Proof.
  move => Ht Hargs Hret. move: Ht Hargs.
  change args with ((Val <$> []) ++ args) at 3.
  change k with (λ x, k ([] ++ x)).
  move: (@nil val) => argsv.
  elim: args argsv h e t.
  { move => argsv h e t /= Ht ?. go. move: Ht. rewrite !app_nil_r. naive_solver. }
  move => /= arg args IH argsv h e t Ht Ha.
  go_s. change (Call _ _) with (expr_fill ([CallCtx f argsv args]) arg).
  rewrite -expr_fill_app. eapply Ha; [set_solver|done|].
  move => ??? /=??. rewrite cons_middle app_assoc -fmap_snoc.
  apply IH; [|set_solver].
  etrans; [done|].
  rewrite interp_bind bind_bind. setoid_rewrite interp_ret.
  setoid_rewrite bind_ret_l. do 2 f_equiv. move => ?. by rewrite <-app_assoc.
Qed.

Lemma rec_refines_rec_itree fns :
  trefines (rec_mod fns) (itree_mod rec_itree (rec_init fns)).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  rewrite /rec_itree.
  unshelve eapply tsim_remember. { simpl. exact (λ n '(Rec ei hi fnsi) '(t, Rec _ hs fnss),
    ∃ K e k,
    t ⊒ ↓ᵢ (ITree.bind (rec' rec_expr_itree e) k) ∧
    RecExprFill ei K e ∧ hi = hs ∧ fnsi = fns ∧ fnss = fns ∧
    rec_itree_expr_inv e ∧
    ∀ v t' ei h' b, t' ⊒ ↓ᵢ (k v) → Rec (expr_fill K (Val v)) h' fns ⪯{rec_trans, itree_trans rec_event rec_state, n, b} (t', Rec ei h' fns)). }
  { exists []. split!; [done|apply _|done|]. move => ??????/=. by go_i. } {
    move => ?? [???] [?[???]] ? /= ?. destruct!. split!; [done..|]. move => *. apply: tsim_mono; naive_solver. }
  move => n /= ? Hloop [ei hi fnsi] [t [es hs fnss]] [K [e]].
  elim/rec_expr_depth_ind: e ei hi fnsi t es hs fnss K.
  move => e IHe *. destruct!/=.
  rename H6 into Hret. revert select (RecExprFill _ _ _) => -[?]. subst.
  destruct e; simplify_eq/=.
  - go_s. by go_s.
  - go_s. by apply Hret.
  - go_s. go_s. go_s.
    eapply IHe; [|split!; [done|apply _|naive_solver|]]; [lia|].
    move => /= *. go_s. go_s.
    apply tsim_mono_b_false.
    eapply IHe; [|split!; [done|apply _|naive_solver|]]; [lia|].
    move => /= *. go_s => ??. go.
    go_i. split!. by apply Hret.
  - go_s. go_s. go_s.
    eapply IHe; [|split!; [done|apply _|naive_solver|]]; [lia|].
    move => /= v *. go_s => ??. go. go_s. go_s => ??. go.
    destruct v => //; simplify_eq/=.
    go_i. split!. by apply Hret.
  - go_s. go_s. go_s.
    eapply IHe; [|split!; [done|apply _|naive_solver|]]; [lia|].
    move => /= v *. go_s. go_s.
    apply tsim_mono_b_false.
    eapply IHe; [|split!; [done|apply _|naive_solver|]]; [lia|].
    move => /= *. go_s => ??. go. go_s. go_s => ?. go. go_s. go_s.
    destruct v => //; simplify_eq/=.
    go_i. split!. by apply Hret.
  - go_s. go_s. go_s.
    eapply IHe; [|split!; [done|apply _|naive_solver|]]; [lia|].
    move => /= v *. go_s => b ?. go.
    destruct v; simplify_eq/=. destruct b; go_s; go_s.
    + go_i. apply tsim_mono_b_false.
      eapply IHe; [|split!; [done|apply _|naive_solver|]]; [lia|done].
    + go_i. apply tsim_mono_b_false.
      eapply IHe; [|split!; [done|apply _|naive_solver|]]; [lia|done].
  - go_s. go_s. go_s.
    eapply IHe; [|split!; [done|apply _|naive_solver|]]; [lia|].
    move => /= *. go_s. go_s. go_i.
    apply tsim_mono_b_false.
    eapply IHe; [|split!; [done|apply _| |done]].
    + rewrite rec_expr_depth_subst. lia.
    + apply rec_itree_expr_inv_subst. naive_solver.
  - revert select (Is_true (forallb _ _)) => /forallb_True/Forall_forall?.
    go_s. apply: rec_refines_rec_itree_call; [done|..]. {
      move => ???? a ??? Hret2. go_s.
      eapply IHe; [|split!; [done|apply _|naive_solver|]].
      { exploit (max_list_elem_of_le (rec_expr_depth a) (rec_expr_depth <$> args)); [|lia].
        apply elem_of_list_fmap. naive_solver. }
      move => /= *. apply tsim_mono_b_false. naive_solver.
    }
    move => /= *. go_s. tstep_both. split => *; simplify_option_eq.
    + go_s => ?. go. tend. split!. go_s. go_s.
      apply Hloop; [done|]. split!; [done|apply _| |done].
      cbn. apply rec_itree_expr_inv_subst_l.
      apply is_static_expr_rec_itree_expr_inv. apply fd_static.
    + go_s. go_s. split!; [done|]. go. tend. go_s. go_s.
      apply Hloop; [done|]. split!; [done|apply _|done|done].
  - go_s. go_s => ?. go. go_i => *. split!.
    go_s. go_s. eexists _. go. go_s. eexists _. go. go_s. split!; [done|]. go.
    go_s. go_s. go_s. go_s.
    apply Hloop; [done|]. split!; [done|apply _|apply rec_itree_expr_inv_subst_l; naive_solver |].
    move => /= *. go_s. go_s => ?. go. go_s => ?. go. go_s. go_s.
    go_i. split!; [done|].
    by apply Hret.
  - done.
  - done.
  - go_i. split.
    + move => *. go_s. go_s. eexists true. go. go_s. go_s. eexists _. go.
      go_s. eexists _. go. go_s. eexists _. go. go_s. split!; [done|]. go.
      go_s. go_s. go_s. split!. go. go_s. go_s.
      apply Hloop; [done|]. split!; [done|apply _|apply rec_itree_expr_inv_forallb|].
      move => /= *. go_s.
      go_i. go_s. split!. go. go_s. go_s.
      apply Hloop; [done|]. split!; [done|apply _|done|done].
    + move => ???. go_s. go_s. eexists false. go. go_s. split!; [by destruct can_return|]. go.
      go_s. eexists _. go. go_s. eexists _. go. go_s. go_s. go_s. split!. go.
      by apply Hret.
Qed.
