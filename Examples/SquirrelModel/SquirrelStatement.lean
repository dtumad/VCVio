/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Examples.SquirrelModel.Execution
public import Examples.SquirrelModel.ChainSecrecy

/-!
# The paper's forward-secrecy statement, as a corollary

The paper proves forward secrecy of its hash chain in Squirrel's form
(`motivating-example.sp`, `forward_secrecy`):

  `[happens(t, t')] → [safe t] → frame@t' ⊬ ck@t`.

The trace is fixed, the attacker computes each input from the frame, and secrecy means no
attacker computes the key from the final frame. This file builds exactly that attacker from
`Execution.lean`'s fixed-schedule program `ofSchedule`, and reads off the statement at
`t = init` from the adaptive theorem `chainAdv_le`:

* `toChain` answers the actions of `Execution.lean`'s `ChainAct` (updates, corruptions,
  random-oracle queries) with the chain's oracles;
* `scheduleAdversary σ att f` is Squirrel's attacker: the trace `σ`, the messages `att` computes
  from the frame, and the final guess `f` of the frame;
* `squirrel_forward_secrecy`: for every trace, attacker and guess,
  `Pr[f(frame) = ck@init] ≤ (|σ| + 1) / |K|`.

Messages are pairs in `K × M`: updates and corruptions read the second component, random-oracle
queries hash the pair. `att` and `f` are pure functions, so the bound holds for any of them,
however expensive; a randomized attacker is a mixture of these.
-/

public section

open OracleComp OracleSpec ENNReal PFunctor

namespace SquirrelModel.Chain

variable {K M : Type} [Inhabited K] [Inhabited M]

/-- The chain's oracles answering the actions of the paper's chain. An update sends the message's
second component, a corruption does the same and returns the leaked key, and a random-oracle
query hashes the message. Every condition holds, so every answer is `some`. -/
@[expose] def toChain (n : ℕ) :
    Handler (OracleComp (advSpec K M)) (iface (ChainAct n) (K × M)) := fun
  | (.upd _, (_, x)) =>
      (fun _ => some (default, default)) <$> (advSpec K M).query (.inr (.inl x))
  | (.corrupt, (_, u)) => (fun k => some (k, default)) <$> (advSpec K M).query (.inr (.inr u))
  | (.rom _, (k, x)) => (fun h => some (h, default)) <$> (advSpec K M).query (.inl (.inr (k, x)))

/-- Squirrel's attacker against the chain: the fixed trace `σ`, the messages `att` computes from
the frame, and the final guess `f` of the frame. -/
@[expose] def scheduleAdversary {n : ℕ} (σ : List (ChainAct n))
    (att : Frame (K × M) → K × M) (f : Frame (K × M) → K) : OracleComp (advSpec K M) K :=
  f <$> (ofSchedule att σ []).liftM (toChain n)

/-- Running a query node through a handler runs the handler, then the continuation. -/
private theorem liftM_liftBind {P : PFunctor} {m : Type → Type} [Monad m] {α : Type}
    (h : (a : P.A) → m (P.B a)) (a : P.A) (k : P.B a → FreeM P α) :
    (FreeM.liftBind a k).liftM h = h a >>= fun o => (k o).liftM h := rfl

/-- Each action of the trace costs one charged query. -/
theorem isQueryBoundP_liftM_ofSchedule {n : ℕ} (att : Frame (K × M) → K × M)
    (σ : List (ChainAct n)) (fr : Frame (K × M)) :
    IsQueryBoundP ((ofSchedule att σ fr).liftM (toChain n)) (fun t => isCoin t = false)
      σ.length := by
  induction σ generalizing fr with
  | nil => exact isQueryBoundP_pure _ _ _
  | cons a σ ih =>
    rw [ofSchedule, liftM_liftBind, List.length_cons, Nat.add_comm]
    refine isQueryBoundP_bind (n := 1) ?_ fun o _ => ih (o :: fr)
    rcases a with _ | _ | _ <;>
      exact (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)

variable [DecidableEq K] [DecidableEq M] [SampleableType K]

/-- **The paper's forward secrecy, at the initial key.** For every fixed trace `σ`, attacker
`att` and final guess `f`, Squirrel's attacker outputs the initial key with probability at most
`(|σ| + 1) / |K|`. This is `frame@t' ⊬ ck@init` with the trace ending at `t'`, made concrete; the
trace may corrupt at any point and any number of times. -/
theorem squirrel_forward_secrecy [Fintype K] {n : ℕ} (σ : List (ChainAct n))
    (att : Frame (K × M) → K × M) (f : Frame (K × M) → K) :
    chainAdv (scheduleAdversary σ att f) ≤ (σ.length + 1) * (Fintype.card K : ℝ≥0∞)⁻¹ :=
  chainAdv_le _ ((isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_liftM_ofSchedule att σ []))

end SquirrelModel.Chain
