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
      vs ← ITree.flat_map (λ e, trigger (Recursion.Call e)) es;
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
  clear_itree.
Local Ltac go_s :=
  tstep_s; go.
Local Ltac go_i :=
  tstep_i; go.

Lemma itree_tstep_bind_tau {E R} A h (x : itree _ A) cont:
  ITreeTStep (E:=E) (R:=R) cont (ITree.bind (Tau x) h) (Tau (ITree.bind x h)).
Proof. constructor. by rewrite unfold_bind. Qed.
Global Hint Resolve itree_tstep_bind_tau : typeclass_instances.

Lemma itree_tstep_interp_ret {E} {R A B S} f x cont (h : S → _):
  ITreeTStep (E:=E) (R:=R) cont (ITree.bind (interp (recursive' (A:=A) (B:=B) f) (Ret x)) h) (ITree.bind (Ret x) h).
Proof. constructor. by rewrite interp_ret. Qed.
Global Hint Resolve itree_tstep_interp_ret : typeclass_instances.

Lemma itree_tstep_interp_bind {E} {R A B S} f g1 (g2 : B → _) cont (h : S → _):
  ITreeTStep (E:=E) (R:=R) cont
    (ITree.bind (interp (recursive' (A:=A) (B:=B) f) (ITree.bind g1 g2)) h)
    (ITree.bind (interp (recursive' f) g1) (λ x,
         ITree.bind (interp (recursive' f) (g2 x)) h)).
Proof. constructor. by rewrite interp_bind bind_bind. Qed.
Global Hint Resolve itree_tstep_interp_bind : typeclass_instances.

Lemma itree_tstep_interp_rec'_call {E} {R A B} f x (h : B → _):
  ITreeTStep (E:=E) (R:=R) false
    (ITree.bind (interp (recursive' (A:=A) (B:=B) f) (call x)) h)
    (ITree.bind (Tau (rec' f x)) h).
Proof.
  constructor. rewrite interp_recursive'_call_eq.
  do 3 f_equiv. setoid_rewrite tau_euttge. by rewrite bind_ret_r.
Qed.
Global Hint Resolve itree_tstep_interp_rec'_call : typeclass_instances.

Class ITreeToTranslate {E1 E2 R} (i : itree E1 R) (H : E2 -< E1) (o : itree E2 R) := {
    itree_to_translate : i ≅ translate (@resum _ _ _ _ H) o
}.
Global Hint Mode ITreeToTranslate + + + ! + - : typeclass_instances.

Lemma itree_tstep_interp_rec'_inr {E} {R A B} f (g : itree (callE A B +' E) _)
  (g' : itree E _) (h : B → _) cont :
  ITreeToTranslate g _ g' →
  ITreeTStep (E:=E) (R:=R) cont
    (ITree.bind (interp (recursive' (A:=A) (B:=B) f) g) h)
    (ITree.bind g' h).
Proof.
  move => [Heq]. constructor.
  by rewrite Heq /= interp_translate /recursive' interp_trigger_h_ge.
Qed.
Global Hint Resolve itree_tstep_interp_rec'_inr : typeclass_instances.

Global Instance ITreeToTranslate_assume_option E1 E2 R (o : option R) {HE1 : choiceE -< E1} (Hin : E1 -< E2) {HE2 : choiceE -< E2} :
  (∀ T, TCEq (HE2 T) (cat (@resum _ _ _ _ HE1) (@resum _ _ _ _ Hin) T)) →
  ITreeToTranslate (assume_option o) Hin (assume_option o).
Proof.
  move => /(_ void)/TCEq_eq Heq.
  constructor. destruct o => //=.
  - by rewrite translate_ret.
  - rewrite /UB translate_bind /angelic translate_trigger_eq.
    f_equiv; [|done]. by rewrite /subevent/resum/= Heq.
Qed.


Lemma itree_tstep_rec' {E} {R A B} f x  (h : B → _):
  ITreeTStep (E:=E) (R:=R) false (ITree.bind (rec' (A:=A) (B:=B) f x) h) (ITree.bind (interp (recursive' f) (f x)) h).
Proof. constructor. by rewrite rec'_as_interp_eq. Qed.
Global Hint Resolve itree_tstep_rec' : typeclass_instances.


Lemma rec_itree_refines_rec fns :
  trefines (itree_mod rec_itree (rec_init fns)) (rec_mod fns).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  rewrite /rec_itree.
  unshelve eapply tsim_remember. { simpl. exact (λ n '(t, Rec _ hi fnsi) '(Rec es hs fnss),
    ∃ K e k,
    t ⊒ ↓ᵢ (ITree.bind (rec' rec_expr_itree e) k) ∧
    RecExprFill es K e ∧ hi = hs ∧ fnsi = fns ∧ fnss = fns ∧
    ∀ v t' ei h', t' ⊒ ↓ᵢ (k v) → (t', Rec ei h' fns) ⪯{itree_trans rec_event rec_state, rec_trans, n, false} Rec (expr_fill K (Val v)) h' fns). }
  { exists []. split!; [done|apply _|]. move => ?????/=. by go_i. } {
    move => ?? [?[???]] [???] ? /= ?. destruct!. split!; [done..|]. move => *. apply: tsim_mono; naive_solver. }
  move => n /= ? Hloop [?[???]] [???] [? [e ?]]. destruct!/=. go_i.
  revert select (RecExprFill _ _ _) => -[?].
  destruct e; simplify_eq/=.
  - by tstep_s.
  - go_i. by apply H5.
  - go_i. go_i.
    apply Hloop; [done|]. split!; [done|apply _|].
    move => /= *.
    go_i. go_i.
    apply Hloop; [done|]. split!; [done|apply _|].
    move => /= *.
    go_s => ??.
    go_i. split!. go.
    go_i. by apply H5.
  - go_i. go_i.
    apply Hloop; [done|]. split!; [done|apply _|].
    move => /= *.
    go_s => *. simplify_eq/=.
    go_i.
Abort.
