From dimsum.core.itree Require Export upstream events.
From dimsum.core Require Import universes module axioms.
From dimsum.examples Require Import rec.
Import ITreeStdppNotations.

Notation moduleE EV S := (choiceE +' visibleE EV +' stateE S).

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
      v1 ← trigger (Recursion.Call e1);
      v2 ← trigger (Recursion.Call e2);
      v ← eval_binop op v1 v2?;
      Ret v
  | Load e1 =>
      v1 ← trigger (Recursion.Call e1);
      l ← val_to_loc v1?;
      h ← get_rec_heap;
      v ← (h.(h_heap) !! l)?;
      Ret v
  | Store e1 e2 =>
      v1 ← trigger (Recursion.Call e1);
      v2 ← trigger (Recursion.Call e2);
      l ← val_to_loc v1?;
      h ← get_rec_heap;
      assume (heap_alive h l);;
      set_rec_heap (heap_update h l v2);;
      Ret v2
  | If e1 e2 e3 =>
      v1 ← trigger (Recursion.Call e1);
      b ← val_to_bool v1?;
      if b then
        trigger (Recursion.Call e2)
      else
        trigger (Recursion.Call e3)
  | LetE x e1 e2 =>
      v1 ← trigger (Recursion.Call e1);
      trigger (Recursion.Call (subst x v1 e2))
  | AllocA xs e =>
      assume (Forall (λ x, 0 < x) xs.*2);;
      h ← get_rec_heap;
      ls ← demonic _;
      h' ← demonic _;
      assert (heap_alloc_list xs.*2 ls h h');;
      set_rec_heap h';;
      v ← trigger (Recursion.Call (subst_l xs.*1 (ValLoc <$> ls) e));
      he ← get_rec_heap;
      he' ← angelic _;
      assume (heap_free_list (zip ls xs.*2) he he');;
      set_rec_heap he';;
      Ret v
  | Call f es =>
      vs ← ITree.flat_map (λ e, trigger (Recursion.Call e)) es;
      fns ← get_rec_fns;
      if fns !! f is Some fn then
        assume (length vs = length fn.(fd_args));;
        trigger (Recursion.Call (AllocA fn.(fd_vars) (subst_l fn.(fd_args) vs fn.(fd_body))))
      else
        h ← get_rec_heap;
        visible (Outgoing, ERCall f vs h);;
        trigger (Recursion.Call (Waiting true))
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
        v ← trigger (Recursion.Call (Call f (Val <$> vs)));
        h ← get_rec_heap;
        visible (Outgoing, ERReturn v h);;
        trigger (Recursion.Call (Waiting b))
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
  ITree.bind (rec rec_expr_itree (Waiting false)) (λ _, NB).
