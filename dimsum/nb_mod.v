From dimsum.core Require Export module trefines.

Definition nb_step EV (_ : unit) (_ : option EV) (_ : unit → Prop) : Prop := False.
Definition nb_trans EV : mod_trans EV := ModTrans (nb_step EV).
Definition nb_mod EV : module EV := Mod (nb_trans EV) tt.

Lemma nb_trans_has_trace EV σ κ Pσ :
  σ ~{ nb_trans EV, option_trace κ }~>ₜ Pσ →
  κ = None ∧ Pσ tt.
Proof.
  move => Ht. destruct κ, σ.
  - apply thas_trace_cons_inv in Ht.
    apply thas_trace_nil_inv in Ht. inv Ht => //. destruct!.
    inv_all @m_step.
  - apply thas_trace_nil_inv in Ht. by inv Ht.
Qed.
