From dimsum.core Require Export base.

(** * Definition of [module] *)

(*
Idea for naming scheme:

|                     | Type      | naming    | example       |
| event               | Type      | ..._event | product_event |
| case                | Type      | ..._case  | product_case  | (e.g. currently seq_product_state)
| state               | Type      | ..._state | product_state |
| step relation       | ...       | ..._step  | product_step  |
| state + step        | mod_trans | ..._trans | product_trans |
| initial state       | ...       | ..._init  | product_init  |
| init + state + step | module    | ..._mod   | product_mod   |

 *)

Record module (EV : Type) : Type := Mod {
  m_state : Type;
  m_step : m_state → option EV → (m_state → Prop) → Prop;
}.
Arguments m_state {_}.
Arguments m_step {_}.
Arguments Mod {_ _}.
Add Printing Constructor module.

Record mod_state EV := MS {
  ms_module : module EV;
  ms_state : ms_module.(m_state);
}.
Arguments MS {_}.
Arguments ms_module {_}.
Arguments ms_state {_}.
Add Printing Constructor mod_state.

Coercion ms_module : mod_state >-> module.

(** [VisNoAll m] encodes that the module [m] only does trivial angelic choices
on visible events. *)
Class VisNoAll {EV} (m : module EV) : Prop :=
  vis_no_all σ κ Pσ : m.(m_step) σ (Some κ) Pσ → ∃ σ', ∀ σ'', Pσ σ'' ↔ σ'' = σ'.

(** * Auxiliary definitions *)

Inductive io_type : Set :=
| Incoming | Outgoing.

Definition io_event (EV : Type) : Type := io_type * EV.

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
