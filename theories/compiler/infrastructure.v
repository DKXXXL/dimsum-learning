Require Import refframe.base.
Require Import refframe.trefines.

Record compiler_pass {EV A B E} := Pass {
  pass_compile : A → B + E;
  pass_source_module : module EV;
  pass_target_module : module EV;
  pass_source_state : A → pass_source_module.(m_state);
  pass_target_state : B → pass_target_module.(m_state);
  pass_pre : A → B → Prop;
  pass_post : A → B → Prop;
  pass_refines a b :
    pass_compile a = inl b →
    pass_pre a b →
    trefines (MS pass_target_module (pass_target_state b))
             (MS pass_source_module (pass_source_state a));
  pass_post_holds a b :
    pass_compile a = inl b →
    pass_pre a b →
    pass_post a b
}.
Arguments compiler_pass : clear implicits.

Program Definition pass_compose {EV A B C E1 E2} (p1 : compiler_pass EV A B E1) (p2 : compiler_pass EV B C E2)
  : compiler_pass EV A C (E1 + E2) := {|
  pass_compile a :=
    match p1.(pass_compile) a with
    | inl b => match p2.(pass_compile) b with
              | inl c => inl c
              | inr e2 => inr (inr e2)
              end
    | inr e1 => inr (inl e1)
    end;
  pass_source_module := p1.(pass_source_module);
  pass_target_module := p2.(pass_target_module);
  pass_source_state := p1.(pass_source_state);
  pass_target_state := p2.(pass_target_state);
  pass_pre a c :=
    p1.(pass_target_module) = p2.(pass_source_module) ∧
    p1.(pass_target_state) = p2.(pass_source_state) ∧
    ∀ b, p1.(pass_pre) a b ∧ (p1.(pass_post) a b → p1.(pass_post) b c)
|}.
Next Obligation.
  move => /= ?????? p1 p2 ???. repeat case_match => //; simplify_eq.
  etrans; [by apply (pass_refines p2)|].
  apply (pass_refines p1).

; [by apply (pass_refines p1)|].  apply pass_refines.
