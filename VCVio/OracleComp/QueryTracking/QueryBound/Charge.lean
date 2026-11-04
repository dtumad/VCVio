/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import PolyFun.PFunctor.Free.Cost
public import Mathlib.Algebra.Order.Sub.Prod
public import Mathlib.Algebra.Order.Monoid.Prod

/-!
# Query bounds as charge bounds

Each structural query bound is PolyFun's charge bound `PFunctor.FreeM.IsChargeBound` for a charge
on the oracle indices: every query at `t` costs `c t`, and the bound is a budget on the amount
spent.

* `IsTotalQueryBound` is the unit charge (`isTotalQueryBound_iff_isChargeBound`).
* `IsQueryBoundP` is the indicator charge of the predicate (`isQueryBoundP_iff_isChargeBound`),
  and `AllQueriesSatisfy` is the zero budget for the indicator of the excluded queries
  (`allQueriesSatisfy_iff_isChargeBound`).
* `IsPerIndexQueryBound` is the vector charge `Pi.single t 1`
  (`isPerIndexQueryBound_iff_isChargeBound`); one coordinate at a time it is the family of
  indicator bounds (`isPerIndexQueryBound_iff_forall_isQueryBoundP`).
* A weighted budget `IsQueryBound oa n (fun t b => w t ≤ b) (fun t b => b - w t)` is the charge
  `w` (`isQueryBound_weighted_iff_isChargeBound`).

The charge-bound laws then apply to the query bounds: budgets add under sequencing, push forward
along monotone additive maps, and transfer through handlers whose implementations stay within the
charge of their query. `QueryBound.Batch` states the same bridges for the online round and point
budgets.
-/

public section

open OracleSpec

universe u

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α : Type u}

/-- A total query bound is the unit-charge bound. -/
theorem isTotalQueryBound_iff_isChargeBound (oa : OracleComp spec α) (n : ℕ) :
    IsTotalQueryBound oa n ↔ PFunctor.FreeM.IsChargeBound oa (fun _ : ι => (1 : ℕ)) n :=
  (PFunctor.FreeM.isChargeBound_one_iff_isTotalRollBound oa n).symm

/-- A weighted query budget, which subtracts the weight of each query from what remains, is the
charge bound with the weight as charge. -/
theorem isQueryBound_weighted_iff_isChargeBound (oa : OracleComp spec α) (w : ι → ℕ) (n : ℕ) :
    IsQueryBound oa n (fun t b => w t ≤ b) (fun t b => b - w t) ↔
      PFunctor.FreeM.IsChargeBound oa w n :=
  (PFunctor.FreeM.isChargeBound_iff_isRollBound_nat oa w n).symm

/-- A predicate-targeted query bound is the bound with the indicator of the predicate as
charge. -/
theorem isQueryBoundP_iff_isChargeBound (oa : OracleComp spec α) (p : ι → Prop)
    [DecidablePred p] (n : ℕ) :
    IsQueryBoundP oa p n ↔
      PFunctor.FreeM.IsChargeBound oa (fun t => if p t then (1 : ℕ) else 0) n := by
  rw [← isQueryBound_weighted_iff_isChargeBound]
  refine isQueryBound_congr (fun t b => ?_) (fun t b => ?_)
  · by_cases hp : p t <;> simp [hp, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  · by_cases hp : p t <;> simp [hp]

/-- A predicate-only bound is the zero budget for the indicator of the excluded queries. -/
theorem allQueriesSatisfy_iff_isChargeBound (oa : OracleComp spec α) (P : ι → Prop)
    [DecidablePred P] :
    AllQueriesSatisfy oa P ↔
      PFunctor.FreeM.IsChargeBound oa (fun t => if P t then (0 : ℕ) else 1) 0 := by
  rw [← isQueryBoundP_zero_iff, isQueryBoundP_iff_isChargeBound]
  simp only [ite_not]

section PerIndex

variable [DecidableEq ι]

/-- A per-index query bound is the bound with the vector charge `Pi.single t 1`. -/
theorem isPerIndexQueryBound_iff_isChargeBound (oa : OracleComp spec α) (qb : ι → ℕ) :
    IsPerIndexQueryBound oa qb ↔
      PFunctor.FreeM.IsChargeBound oa (fun t => Pi.single t (1 : ℕ)) qb := by
  rw [PFunctor.FreeM.isChargeBound_iff_isRollBound_orderedSub, tsub_zero]
  simp only [zero_le, true_and]
  refine PFunctor.FreeM.isRollBound_congr (fun t b => ⟨fun h j => ?_, fun h => ?_⟩) fun t b => ?_
  · by_cases hj : j = t
    · subst hj; simpa [Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero] using h
    · simp [hj]
  · simpa [Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero] using h t
  · funext j
    by_cases hj : j = t
    · subst hj; simp
    · simp [hj]

/-- A per-index query bound is, one index at a time, the predicate-targeted bound for that
index. -/
theorem isPerIndexQueryBound_iff_forall_isQueryBoundP (oa : OracleComp spec α) (qb : ι → ℕ) :
    IsPerIndexQueryBound oa qb ↔ ∀ i, IsQueryBoundP oa (· = i) (qb i) := by
  rw [isPerIndexQueryBound_iff_isChargeBound, PFunctor.FreeM.isChargeBound_pi_iff]
  refine forall_congr' fun i => ?_
  rw [isQueryBoundP_iff_isChargeBound]
  simp only [Pi.single_apply, eq_comm (a := i)]
  rfl

end PerIndex

end OracleComp
