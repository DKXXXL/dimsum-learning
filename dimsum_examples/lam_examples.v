From dimsum.core Require Export proof_techniques.
From dimsum.core Require Import itree.
From dimsum.examples Require Import lam.

Local Open Scope Z_scope.

Local Ltac go :=
  clear_itree.
Local Ltac go_s :=
  tstep_s; go.
Local Ltac go_i :=
  tstep_i; go.


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
Definition id_itree : itree (moduleE lam_event (list fid)) unit :=
    ITree.forever (
        '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ELCall f vs h));;;
        fid_list ← TGet ;;;
        if bool_decide (f = ("id",None)) then
          newfid ← TExist fid;;;
          TPut (newfid::fid_list);;;;
          TVis (Outgoing, ELReturn (ValFid newfid) h)
        else if bool_decide (f ∈ fid_list) then
          z ← TAll Z;;;
          TAssume (vs = [ValNum z]);;;;
          TVis (Outgoing, ELReturn (ValNum z) h)
        else
          TNb).

Lemma id_prog_refines_id_itree :
  trefines id_mod (itree_mod id_itree []).
Proof.
    apply tsim_implies_trefines => n0 /=. unfold id_prog.
    tstep_i;  split; intros.
    - admit. 
    - admit.

Admitted.




    unshelve eapply tsim_remember. 
    { simpl. exact (λ _ σa '(t, _),
    t ≈ id_itree ∧
    σa.(asm_cur_instr) = AWaiting ∧
    σa.(asm_instrs) = print_asm).  }

Definition main_lam: fndef := {|
  fd_args := ["input"];
  fd_body := App (Val $ ValFid ("id",None)) [Var "input"];
  fd_static := I
|}.

Definition main_prog: gmap fid fndef := 
    <[("main",None) := main_lam]> $ ∅.
