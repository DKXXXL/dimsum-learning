From dimsum.core.itree.program_logic Require Export language.
From dimsum.core.itree Require Export upstream events small_itree.
From dimsum.core Require Import universes.

Export ITreeStdppNotations.

Section itree_lang.
  Context {S : TypeBelowState} {EV : TypeState}.
  Inductive itree_expr :=
  | IExpr (e : itree (moduleE EV S) void) | IHalted.

  Definition to_val (e : itree_expr) : option unit :=
    match e with
    | IExpr _ => None
    | IHalted => Some tt
    end.

  Definition of_val (v : unit) : itree_expr := IHalted.

  Inductive itree_step : itree_expr → S → list EV → itree_expr → S → list itree_expr → bool → Prop :=
  | ITauS t t' s:
    t ≅ (Tau t') →
    itree_step (IExpr t) s [] (IExpr t') s [] false
  | IAngelicS T t t' s x :
    t ≅ (Vis (inl1 (EAngelic T)) t') →
    itree_step (IExpr t) s [] (IExpr (t' x)) s [] false
  | IDemonicS T t t' s x :
    t ≅ (Vis (inl1 (EDemonic T)) t') →
    itree_step (IExpr t) s [] (IExpr (t' x)) s [] false
  | IDemonicS_fail T t t' s :
    t ≅ (Vis (inl1 (EDemonic T)) t') →
    itree_step (IExpr t) s [] IHalted s [] false
  | IVisS t t' s e :
    t ≅ (Vis (inr1 (inl1 (EVisible e))) t') →
    itree_step (IExpr t) s [e] (IExpr (t' tt)) s [] false
  | IGetS t t' s :
    t ≅ (Vis (inr1 (inr1 EGetState)) t') →
    itree_step (IExpr t) s [] (IExpr (t' s)) s [] false
  | ISetS t t' s s':
    t ≅ (Vis (inr1 (inr1 (ESetState s'))) t') →
    itree_step (IExpr t) s [] (IExpr (t' tt)) s' [] false
  | IYieldS t t' s :
    t ≅ (Vis (inr1 (inr1 EYield)) t') →
    itree_step (IExpr t) s [] (IExpr (t' tt)) s [] true.

  Lemma itree_lang_mixin : LanguageMixin of_val to_val itree_step.
  Proof.
    split => //=.
    - by case.
    - by case.
    - move => ??????? Hstep. by inversion Hstep; simplify_eq/=.
  Qed.
  Canonical Structure itree_lang := Language itree_lang_mixin.
End itree_lang.
