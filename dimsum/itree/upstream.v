From ITree Require Export ITree ITreeFacts.

(* TODO: upstream *)
Module ITreeStdppNotations.
Notation "m ≫= f" := (ITree.bind f m) (at level 60, right associativity) : itree_scope.
Notation "x ← y ; z" := (ITree.bind y (fun x : _ => z))
  (at level 20, y at level 100, z at level 200,
  format "x  ←  y ;  '/' z") : itree_scope.
Notation "' x ← y ; z" := (ITree.bind y (fun x_ : _ => match x_ with x => z end))
  (at level 20, x pattern, y at level 100, z at level 200,
  format "' x  ←  y ;  '/' z") : itree_scope.
Notation "x ;; z" := (ITree.bind x (fun _ => z))
  (at level 100, z at level 200, right associativity) : itree_scope.
End ITreeStdppNotations.

Module ITree.
  Import ITreeStdppNotations.
  Fixpoint flat_map {A E R} (f : A -> itree E R) (xs : list A) : itree E (list R) :=
    match xs with
    | nil => Ret nil
    | cons y ys =>
        r ← f y;
        rs ← flat_map f ys;
        Ret (cons r rs)
        end%itree.
End ITree.

Definition Tau_maybe {E R} (b : bool) (t : itree E R) :=
  if b then Tau t else t.
Notation "'Tau?' b t" := (Tau_maybe b t)
  (at level 20, b at level 9, t at level 20, right associativity, format "'Tau?' b  t").
