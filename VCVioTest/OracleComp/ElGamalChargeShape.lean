/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# The prefix and suffix bounds of the generic multi-query ElGamal reduction, through charges

The suffix of the generic ElGamal reduction answers group operations by one target operation,
private coins by a coin query, and a left/right query by a cache lookup that makes no operation,
followed on a miss by an encryption of three operations. A program with at most `qₒ` operations
and `q` left/right queries therefore runs with at most `qₒ + 3 * q` target operations.

With charges the induction disappears: the two source budgets form one pair budget
(`isChargeBound_prod_iff`), which a monotone additive map weighs into the scalar charge
`op + 3 * leftRight` (`IsChargeBound.map`), and the stateful transfer `IsChargeBound.run_liftM`
moves that budget through the implementation once each call is within its weighted charge from
every state. `toyImpl` recreates the three branches with a list cache.

The prefix pauses at the first fresh left/right query once `k` encryptions are spent, which is not
a simulation through a handler. PolyFun's `PFunctor.FreeM.runUntil` is that pausing runner, and
`IsChargeBound.runUntil` is its amortized budget with a decreasing potential; `toyPrefix` with the
potential `3 * (k - count)` gives the prefix bound `3 * (k - count) + qₒ`.
-/

public section

open OracleComp OracleSpec PFunctor

namespace VCVioTest.OracleComp.ElGamalChargeShape

/-! ## The generic two-budget transfer -/

variable {ι ι' σ α : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}

/-- Weigh a pair of counts into `a + w * b`. -/
@[expose] def weigh (w : ℕ) : ℕ × ℕ →+o ℕ :=
  ⟨⟨⟨fun v => v.1 + w * v.2, by simp⟩, fun a b => by simp only [Prod.fst_add, Prod.snd_add]; ring⟩,
    fun _ _ h => add_le_add h.1 (Nat.mul_le_mul_left w h.2)⟩

@[simp] theorem weigh_apply (w : ℕ) (v : ℕ × ℕ) : weigh w v = v.1 + w * v.2 := rfl

/-- Two predicate budgets on the source transfer to a weighted target budget through a stateful
implementation whose step at `t` makes at most `[p₁ t] + w * [p₂ t]` target `q'`-queries from every
state. -/
theorem isQueryBoundP_run_simulateQ_of_two_budgets {p₁ p₂ : ι → Prop} [DecidablePred p₁]
    [DecidablePred p₂] {q' : ι' → Prop} [DecidablePred q'] (w : ℕ)
    (impl : QueryImpl spec (StateT σ (OracleComp spec')))
    (hstep : ∀ t s, IsQueryBoundP ((impl t).run s) q'
      ((if p₁ t then 1 else 0) + w * (if p₂ t then 1 else 0)))
    {oa : OracleComp spec α} {n₁ n₂ : ℕ} (h₁ : IsQueryBoundP oa p₁ n₁)
    (h₂ : IsQueryBoundP oa p₂ n₂) (s : σ) :
    IsQueryBoundP ((simulateQ impl oa).run s) q' (n₁ + w * n₂) := by
  simp only [isQueryBoundP_iff_isChargeBound] at *
  have hpair := (FreeM.isChargeBound_prod_iff (s₁ := 0) (s₂ := 0)).2 ⟨h₁, h₂⟩
  have hw := hpair.map (weigh w)
  simp only [Function.comp_def, weigh_apply, mul_zero, add_zero] at hw
  exact hw.run_liftM impl (fun t s => by simpa using hstep t s) s

/-! ## A toy suffix with the three branches -/

/-- Group operations (`.inl ()`), private coins and left/right queries. -/
abbrev srcSpec : OracleSpec (Unit ⊕ (ℕ ⊕ ℕ)) := (Unit →ₒ Unit) + (unifSpec + (ℕ →ₒ ℕ))

/-- Group operations and coins. -/
abbrev tgtSpec : OracleSpec (Unit ⊕ ℕ) := (Unit →ₒ Unit) + unifSpec

/-- Whether a source query is a group operation. -/
abbrev isOp : Unit ⊕ (ℕ ⊕ ℕ) → Prop := (· matches .inl _)

/-- Whether a source query is a left/right query. -/
abbrev isLR : Unit ⊕ (ℕ ⊕ ℕ) → Prop := (· matches .inr (.inr _))

/-- Whether a target query is a group operation. -/
abbrev isOp' : Unit ⊕ ℕ → Prop := (· matches .inl _)

/-- One group operation. -/
def groupOp : OracleComp tgtSpec Unit := tgtSpec.query (.inl ())

/-- The suffix implementation: a group operation is one target operation, a coin is forwarded,
and a left/right query is free on a cache hit and three operations on a miss. -/
def toyImpl : QueryImpl srcSpec (StateT (List ℕ) (OracleComp tgtSpec))
  | .inl () => fun st => do let u ← groupOp; pure (u, st)
  | .inr (.inl n) => fun st => do let u ← tgtSpec.query (.inr n); pure (u, st)
  | .inr (.inr m) => fun st =>
      if m ∈ st then pure (m, st) else do
        groupOp; groupOp; groupOp
        pure (m, m :: st)

/-- From every cache, each call stays within its weighted charge `[op] + 3 * [left/right]`. -/
theorem toyImpl_step (t : Unit ⊕ (ℕ ⊕ ℕ)) (st : List ℕ) :
    IsQueryBoundP ((toyImpl t).run st) isOp'
      ((if isOp t then 1 else 0) + 3 * (if isLR t then 1 else 0)) := by
  rcases t with _ | n | m
  · simp [toyImpl, groupOp, StateT.run, isOp, isLR, isOp']
  · simp [toyImpl, StateT.run, isOp, isLR, isOp']
  · by_cases hm : m ∈ st
    · simp [toyImpl, StateT.run, hm, isOp, isLR]
    · simp [toyImpl, groupOp, StateT.run, hm, isOp, isLR, isOp']

/-- The suffix bound: `qₒ` operations and `q` left/right queries run with `qₒ + 3 * q`
operations. -/
theorem suffix_bound {A : OracleComp srcSpec Bool} {qₒ q : ℕ} (hₒ : IsQueryBoundP A isOp qₒ)
    (hq : IsQueryBoundP A isLR q) (st : List ℕ) :
    IsQueryBoundP ((simulateQ toyImpl A).run st) isOp' (qₒ + 3 * q) :=
  isQueryBoundP_run_simulateQ_of_two_budgets 3 toyImpl toyImpl_step hₒ hq st


/-! ## Pausing prefixes with a potential

The prefix of the reduction pauses at the first fresh left/right query once `k` encryptions are
spent, returning the query and the continuation. PolyFun's `runUntil` is that runner: each call
is either answered, with a new state, or pauses the run. A decreasing potential `Φ` on the state
pays for the steps: if from every state a call at `t` stays, along every prefix of its run, within
what the caller can afford, and ends with `spent + Φ next ≤ spent₀ + Φ now + c t`, then a source
budget `B` gives the target budget `Φ σ₀ + B`. -/

section Prefix

/-- A toy prefix: encrypt a fresh left/right query while fewer than `k` were encrypted, and pause
at the first fresh one after that. The state is the number of encryptions and the cache. -/
@[expose] def toyPrefix (k : ℕ) :
    (t : Unit ⊕ (ℕ ⊕ ℕ)) → ℕ × List ℕ → OracleComp tgtSpec (Option (srcSpec.Range t × (ℕ × List ℕ)))
  | .inl (), st => do let u ← groupOp; pure (some (u, st))
  | .inr (.inl n), st => do let u ← tgtSpec.query (.inr n); pure (some (u, st))
  | .inr (.inr m), st =>
      if m ∈ st.2 then pure (some (m, st))
      else if st.1 < k then do
        groupOp; groupOp; groupOp
        pure (some (m, (st.1 + 1, m :: st.2)))
      else pure none

/-- The prefix bound: `qₒ` operations run with at most `qₒ + 3 * (k - count)` operations. -/
theorem prefix_bound (k : ℕ) {A : OracleComp srcSpec Bool} {qₒ : ℕ}
    (hₒ : IsQueryBoundP A isOp qₒ) (st : ℕ × List ℕ) :
    FreeM.IsChargeBound (FreeM.runUntil (toyPrefix k) A st) (fun t => if isOp' t then 1 else 0)
      (3 * (k - st.1) + qₒ) := by
  rw [isQueryBoundP_iff_isChargeBound] at hₒ
  refine hₒ.runUntil (fun st => 3 * (k - st.1)) (fun _ => Nat.zero_le _) (fun t st e he => ?_)
    (by omega)
  rcases t with _ | n | m
  · simp [toyPrefix, groupOp, Option.elim, OracleComp.liftM_def, OracleSpec.query_def] at he ⊢
    omega
  · simp [toyPrefix, Option.elim, OracleComp.liftM_def, OracleSpec.query_def, OracleQuery.mk,
      PFunctor.Obj.mk] at he ⊢
    omega
  · simp only [isOp, reduceCtorEq, ite_false, add_zero] at he
    by_cases hm : m ∈ st.2
    · simp [toyPrefix, hm, Option.elim]
    by_cases hk : st.1 < k
    · simp [toyPrefix, hm, hk, groupOp, Option.elim, OracleComp.liftM_def, OracleSpec.query_def,
        OracleQuery.mk, PFunctor.Obj.mk, FreeM.wpFold_bind]
      omega
    · simp [toyPrefix, hm, hk, Option.elim]

end Prefix

end VCVioTest.OracleComp.ElGamalChargeShape
