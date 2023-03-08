From dimsum.core.itree Require Export upstream.
From stdpp Require Import prelude.
From dimsum.core Require Import universes.
Import ITreeStdppNotations.

(** * state events *)
Inductive stateE (S : TypeBelowState) : TypeBelowState → TypeState :=
| EGetState : stateE S S
| ESetState (x : S) : stateE S unit
| EYield : stateE S unit.
Arguments EGetState {_}.
Arguments ESetState {_} _.
Arguments EYield {_}.

Definition get_state {E S} `{!stateE S -< E} : itree E S :=
  (trigger EGetState)%itree.
Definition set_state {E S} `{!stateE S -< E} (s : S) : itree E unit :=
  (trigger (ESetState s))%itree.
Definition yield {E S} `{!stateE S -< E} : itree E unit :=
  (trigger EYield)%itree.

Global Typeclasses Opaque get_state set_state yield.

(** * choice events *)
Inductive choiceE : TypeBelowState → TypeState :=
| EDemonic (X : TypeBelowState) : choiceE X
| EAngelic (X : TypeBelowState) : choiceE X.

Definition angelic {E} `{!choiceE -< E} R : itree E R :=
  (trigger (EAngelic R))%itree.
Definition demonic {E} `{!choiceE -< E} R : itree E R :=
  (trigger (EDemonic R))%itree.

Definition assume {E} `{!choiceE -< E} (P : Prop) : itree E unit :=
  (angelic P;; Ret tt)%itree.
Definition assert {E} `{!choiceE -< E} (P : Prop) : itree E unit :=
  (demonic P;; Ret tt)%itree.

Definition UB {E R} `{!choiceE -< E} : itree E R :=
  (x ← angelic void; match x : void with end)%itree.
Definition NB {E R} `{!choiceE -< E} : itree E R :=
  (x ← demonic void; match x : void with end)%itree.

Definition assume_option {E R} `{!choiceE -< E} (o : option R) : itree E R :=
  (match o with | Some x => Ret x | None => UB end)%itree.
Definition assert_option {E R} `{!choiceE -< E} (o : option R) : itree E R :=
  (match o with | Some x => Ret x | None => NB end)%itree.

Notation "x ?" := (assume_option x) (at level 10, format "x ?") : itree_scope.
Notation "x !" := (assert_option x) (at level 10, format "x !") : itree_scope.

Global Typeclasses Opaque angelic demonic assume assert UB NB assume_option assert_option.

(** * visible events *)
Inductive visibleE (EV : TypeState) : TypeBelowState → TypeState :=
| EVisible (e : EV) : visibleE EV unit.
Arguments EVisible {_} _.

Definition visible {E EV} `{!visibleE EV  -< E} (e : EV) : itree E unit :=
  (trigger (EVisible e))%itree.

Global Typeclasses Opaque visible.

(** * [moduleE] *)
Notation moduleE EV S := (choiceE +' visibleE EV +' stateE S).

Section moduleE_eq_itree_inv.

  Context {EV S R : Type}.

  Notation moduleE_eq_itree_ t1_ t2_ :=
    match observe t1_, observe t2_ with
    | RetF r1, RetF r2 => r1 = r2
    | TauF t1, TauF t2 => t1 ≅ t2
    | VisF e1 t1, VisF e2 t2 =>
        match e1, e2 with
        | inl1 e1, inl1 e2 =>
            match e1 in choiceE X return (X → itree _ _) → _ with
            | EDemonic X1 => λ t1,
                  match e2 in choiceE X return (X → itree _ _) → _ with
                  | EDemonic X2 => λ t2,
                        ∃ p : @eq Type X1 X2, pweqeq (eq_itree eq) p t1 t2
                  | _ => λ _, False
                  end t2
            | EAngelic X1 => λ t1,
                  match e2 in choiceE X return (X → itree _ _) → _ with
                  | EAngelic X2 => λ t2,
                        ∃ p : @eq Type X1 X2, pweqeq (eq_itree eq) p t1 t2
                  | _ => λ _, False
                  end t2
            end t1
        | inr1 (inl1 e1), inr1 (inl1 e2) =>
            match e1 in visibleE _ X return (X → itree _ _) → _ with
            | EVisible e1 => λ t1,
                  match e2 in visibleE _ X return (X → itree _ _) → _ with
                  | EVisible e2 => λ t2,
                        e1 = e2 ∧ t1 () ≅ t2 ()
                  end t2
            end t1
        | inr1 (inr1 e1), inr1 (inr1 e2) =>
            match e1 in stateE _ X return (X → itree _ _) → _ with
            | EGetState => λ t1,
                  match e2 in stateE _ X return (X → itree _ _) → _ with
                  | EGetState => λ t2,
                        ∀ s, t1 s ≅ t2 s
                  | _ => λ _, False
                  end t2
            | ESetState s1 => λ t1,
                  match e2 in stateE _ X return (X → itree _ _) → _ with
                  | ESetState s2 => λ t2,
                        s1 = s2 ∧ t1 () ≅ t2 ()
                  | _ => λ _, False
                  end t2
            | EYield => λ t1,
                  match e2 in stateE _ X return (X → itree _ _) → _ with
                  | EYield => λ t2,
                        t1 () ≅ t2 ()
                  | _ => λ _, False
                  end t2
            end t1
        | _, _ => False
        end
    | _, _ => False
    end.

  Lemma moduleE_eq_itree_inv (t1 t2 : itree (moduleE EV S) R) :
    t1 ≅ t2 -> moduleE_eq_itree_ t1 t2.
  Proof using Type*.
    intros Heq%eqit_inv. unfold observe.
    destruct (_observe t1), (_observe t2); try done.
    destruct Heq as [? [Heq1 Heq2]]. simplify_eq/=.
    repeat case_match; simplify_eq/=.
    - exists eq_refl. done.
    - exists eq_refl. done.
    - naive_solver.
    - naive_solver.
    - naive_solver.
    - naive_solver.
  Qed.

End moduleE_eq_itree_inv.


(** * tests *)
Definition step : itree (moduleE nat nat) unit :=
  (demonic nat;;
   n ← angelic nat;
   set_state n;;
   n ← get_state;
   yield;;
   '(m, _) ← angelic (nat * nat);
   Some 10?;;
   (None : option nat)!;;
   x ← Some 10?;
   y ← (None : option nat)!;
   UB (R:=void);;
   NB (R:=void);;
   visible x;;
   ret ())%itree.
