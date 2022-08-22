From dimsum.core Require Export base universes.

(** * Definition of [module] *)

(**
Naming scheme:

|                     | Type      | naming    | example       |
| event               | Type      | ..._event | product_event |
| case                | Type      | ..._case  | product_case  | (e.g. seq_product_case)
| state               | Type      | ..._state | product_state |
| step relation       | ...       | ..._step  | product_step  |
| state + step        | mod_trans | ..._trans | product_trans |
| initial state       | ...       | ..._init  | product_init  |
| init + state + step | module    | ..._mod   | product_mod   |
 *)

Record mod_trans (EV : TypeEvent) : Type := ModTrans {
  m_state : TypeState;
  m_step : m_state → option EV → (m_state → Prop) → Prop;
}.
Arguments m_state {_}.
Arguments m_step {_}.
Arguments ModTrans {_ _}.
Add Printing Constructor mod_trans.

Record module (EV : TypeEvent) : Type := Mod {
  m_trans : mod_trans EV;
  m_init : m_trans.(m_state);
}.
Arguments Mod {_}.
Arguments m_trans {_}.
Arguments m_init {_}.
Add Printing Constructor module.

(* Coercion m_trans : module >-> mod_trans. *)

(** [VisNoAng m] encodes that the mod_trans [m] only does trivial angelic choices
on visible events. *)
Class VisNoAng {EV} (m : mod_trans EV) : Prop :=
  vis_no_all σ κ Pσ : m.(m_step) σ (Some κ) Pσ → ∃ σ', ∀ σ'', Pσ σ'' ↔ σ'' = σ'.

(** * Auxiliary definitions *)

Inductive io_type : Set :=
| Incoming | Outgoing.

Definition io_event (EV : TypeEvent) : TypeEvent := io_type * EV.

Inductive player :=
| Prog | Env.
Global Instance player_eq_dec : EqDecision player.
Proof. solve_decision. Qed.

Definition opponent (p : player) : player :=
  match p with
  | Prog => Env
  | Env => Prog
  end.

(* Inductive player3 := *)
(* | PLeft | PRight | PEnv. *)
(* Global Instance player3_eq_dec : EqDecision player3. *)
(* Proof. solve_decision. Qed. *)
(* Global Instance player3_inhabited : Inhabited player3 := populate PEnv. *)
