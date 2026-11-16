/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Examples.SquirrelModel.SquirrelStatement
public import Examples.SquirrelModel.TracePrice
public import Examples.SquirrelModel.Asymptotic
public import VCVio.CryptoFoundations.Asymptotics.Negligible

/-!
# Random tapes and constant-length traces

**Translation.** Squirrel's attacker functions read a shared random tape `ρ_a`, sampled once at
the start of the execution. Here a tape is a value `ρ : Tape` drawn from a distribution
`D : ProbComp Tape` and then fixed; the attacker is the family of pure attackers `att ρ`, and the
final guess may read the same tape (`f ρ`). Squirrel's security parameter `η` is the index of a
family of handlers, programs and events, and "negligible" is VCVio's `negligible`. A Squirrel
trace is a fixed list of actions, so its length `n` does not depend on `η`.

This file closes two gaps between Squirrel's statements and the pure, fixed-parameter statements
of the other files.

* **Tapes.** A tape drawn once and then fixed is a mixture of pure attackers, so a bound proved for
  every pure attacker holds for the mixture (`prEvent_bind_tape_le`). For the hash chain the tape
  can be drawn by the attacker itself from its coins, which the chain's bound does not charge:
  `Chain.squirrel_forward_secrecy_tape` bounds the attacker that draws `ρ ← D` and then runs
  `scheduleAdversary σ (att ρ) (f ρ)` by `(|σ| + 1) / |K|`, as for pure attackers.
* **Constant-length traces.** For a fixed number `n` of actions, if every one of the `|Act| ^ n`
  traces of length `n` gives its guided attacker negligible success, then the adaptive program's
  success is negligible (`negligible_prEvent_run_of_forall_trace`). It is the sum of finitely many
  negligible functions, by `prEvent_run_eq_sum_guided`. The exponential loss of `ladder` in
  `TracePrice.lean` therefore matters only when the number of actions grows with `η`, which a
  Squirrel trace never does.
* **Growing traces.** The fixed `n` is needed. With `η + 1` actions, every guided attacker of the
  ladder succeeds with probability at most `2⁻¹ ^ η`, negligible even for traces chosen depending
  on `η` (`negligible_prEvent_ladder_guided`), while the adaptive attacker always succeeds
  (`not_negligible_prEvent_ladder_ladderAttacker`).
-/

public section

open OracleComp OracleSpec ENNReal PFunctor

namespace SquirrelModel

/-! ## Random tapes -/

/-- **A tape drawn once is a mixture of pure attackers.** If the game against the pure attacker
`att ρ` produces the event with probability at most `ε` for every tape `ρ`, then so does the game
whose tape is drawn once from any distribution `D` and then fixed. This is
`prEvent_bind_le_of_forall_le` read for tapes. -/
theorem prEvent_bind_tape_le {Tape Att β : Type} (D : ProbComp Tape) (att : Tape → Att)
    (game : Att → ProbComp β) (E : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ ρ, Pr{let z ← game (att ρ)}[E z] ≤ ε) :
    Pr{let ρ ← D; let z ← game (att ρ)}[E z] ≤ ε := by
  simpa only [prEvent_norm] using prEvent_bind_le_of_forall_le D (fun ρ => game (att ρ)) E h

namespace Chain

variable {K M : Type}

/-- A probabilistic computation lifted into the chain's oracles queries only coins, which the
chain's bound does not charge. -/
theorem isQueryBoundP_liftComp_coin {Tape : Type} (D : ProbComp Tape) :
    IsQueryBoundP (liftComp D (advSpec K M)) (fun t => isCoin t = false) 0 := by
  induction D using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [liftComp_bind, liftComp_query]
    exact isQueryBoundP_bind_zero _ _ ((isQueryBoundP_map_iff _ _ _).2
      ((isQueryBoundP_query_iff _ (.inl (.inl t) : (advSpec K M).Domain) 0).2
        (by simp [isCoin]))) ih

variable [Inhabited K] [Inhabited M] [DecidableEq K] [DecidableEq M] [SampleableType K]

/-- **The paper's forward secrecy, with a random tape.** An attacker that draws a tape `ρ` once
from any distribution `D`, with its own coins, and then runs Squirrel's attacker
`scheduleAdversary σ (att ρ) (f ρ)`, whose messages and final guess both read `ρ`, outputs the
initial key with probability at most `(|σ| + 1) / |K|`, the bound of `squirrel_forward_secrecy`
for pure attackers. The tape is drawn inside the attacker, as an oracle computation. -/
theorem squirrel_forward_secrecy_tape [Fintype K] {Tape : Type} (D : ProbComp Tape) {n : ℕ}
    (σ : List (ChainAct n)) (att : Tape → Frame (K × M) → K × M)
    (f : Tape → Frame (K × M) → K) :
    chainAdv (liftComp D (advSpec K M) >>= fun ρ => scheduleAdversary σ (att ρ) (f ρ) :
        OracleComp (advSpec K M) K) ≤
      (σ.length + 1) * (Fintype.card K : ℝ≥0∞)⁻¹ := by
  have hA : IsQueryBoundP
      (liftComp D (advSpec K M) >>= fun ρ => scheduleAdversary σ (att ρ) (f ρ))
      (fun t => isCoin t = false) (0 + σ.length) :=
    isQueryBoundP_bind (isQueryBoundP_liftComp_coin D) fun ρ _ =>
      (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_liftM_ofSchedule (att ρ) σ [])
  rw [zero_add] at hA
  exact chainAdv_le _ hA

end Chain

/-! ## Constant-length traces -/

/-- **Constant-length traces lose nothing asymptotically.** Take, for each security parameter `η`,
a stateful handler `h η`, a program `p η` all of whose paths make exactly `n` queries, a start
state and an event; the number of actions `n` and the action set `Act` do not depend on `η`. If
for every trace `σ` of length `n` the guided attacker `guided (p η) σ`, a Squirrel attacker by
`isNonAdaptive_guided`, reproduces the event with negligible probability, then the adaptive
program produces it with negligible probability. The loss is the constant factor of `|Act| ^ n`
traces; `not_negligible_prEvent_ladder_ladderAttacker` shows that it is not negligible once `n`
grows with `η`, which a Squirrel trace never does. -/
theorem negligible_prEvent_run_of_forall_trace {Act : Type} {Msg α T : ℕ → Type}
    [Finite Act] [DecidableEq Act] [∀ η, Inhabited (Msg η)]
    {m : Type → Type} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    (h : ∀ η, Handler.Stateful m (T η) (iface Act (Msg η))) (n : ℕ)
    (p : ∀ η, FreeM (iface Act (Msg η)) (α η))
    (hp : ∀ η (path : FreeM.Path (p η)), FreeM.Path.length (p η) path = n) (s₀ : ∀ η, T η)
    (E : ∀ η, α η × T η → Prop)
    (hσ : ∀ σ : List Act, σ.length = n → negligible fun η =>
      Pr{let z ← (h η).run (guided (p η) σ) (s₀ η)}[∃ a, z.1 = some a ∧ E η (a, z.2)]) :
    negligible fun η => Pr{let z ← (h η).run (p η) (s₀ η)}[E η z] := by
  have := Fintype.ofFinite Act
  simp_rw [fun η => prEvent_run_eq_sum_guided (h η) n (p η) (hp η) (s₀ η) (E η)]
  exact negligible_sum fun σ _ => hσ _ List.length_ofFn

/-! ## Growing traces -/

/-- A constant one is not negligible. -/
private theorem not_negligible_one : ¬negligible fun _ : ℕ => (1 : ℝ≥0∞) := by
  intro h
  have h0 := h 0
  simp only [pow_zero, one_mul] at h0
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h0)

/-- With `η + 1` actions, every guided attacker of `ladderAttacker (η + 1) false` succeeds with
probability at most `2⁻¹ ^ η`, so negligibly, even when its trace `σ η` depends on `η`. -/
theorem negligible_prEvent_ladder_guided (σ : ℕ → List Bool) :
    negligible fun η =>
      Pr{let z ← (ladder.handler.run (guided (ladderAttacker (η + 1) false) (σ η))
        (ladder.init, true))}[∃ a, z.1 = some a ∧ η + 1 ≤ z.2.1.2] := by
  refine negligible_of_le (fun η => ?_) Asymptotic.negligible_inv_two_pow
  refine (prEvent_mono _ _ _ fun _ ⟨_, _, hz⟩ => hz).trans
    ((prEvent_ladder_le_of_isNonAdaptive η (σ η) _ (isNonAdaptive_guided _ _)).trans ?_)
  rw [ENNReal.inv_pow]

/-- **The number of actions must stay fixed.** With `η + 1` actions the guided attackers of the
ladder all succeed negligibly (`negligible_prEvent_ladder_guided`), but the adaptive attacker
succeeds with probability one, which is not negligible. So
`negligible_prEvent_run_of_forall_trace` fails once the number of actions grows with `η`. -/
theorem not_negligible_prEvent_ladder_ladderAttacker :
    ¬negligible fun η =>
      Pr{let z ← ladder.handler.run (ladderAttacker (η + 1) false) (ladder.init, true)}[
        η + 1 ≤ z.2.1.2] := by
  simp only [prEvent_ladder_ladderAttacker]
  exact not_negligible_one

end SquirrelModel
