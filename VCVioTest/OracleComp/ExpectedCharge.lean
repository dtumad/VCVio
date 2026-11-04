/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.ExpectedCharge

/-!
# Expected charged-query counts as expected charges

The expected charged-query count of a stateful simulation is the expected charge of the indicator
of the charged indices, so its bind law and its bound by `IsQueryBoundP` follow from the
corresponding laws of `expectedSimulatedCharge`. The total-count budget of a simulated program
bounds the expected number of target queries of its run when each call's implementation makes at
most one target query in expectation.
-/

public section

open MeasureTheory OracleComp OracleSpec
open scoped ENNReal

namespace VCVioTest.OracleComp.ExpectedCharge

variable {ι : Type} {spec : OracleSpec ι} {α β σ : Type} {m : Type → Type} [Monad m]
  [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
  (so : QueryImpl spec (StateT σ m)) (charged : spec.Domain → Prop) [DecidablePred charged]

/-- `expectedSimulatedQueryCount_le_of_isQueryBoundP`, from the charge budget. -/
example (oa : OracleComp spec α) (s : σ) (q : ℕ) (hq : oa.IsQueryBoundP charged q) :
    expectedSimulatedQueryCount so charged oa s ≤ q := by
  rw [isQueryBoundP_iff_isChargeBound,
    ← PFunctor.FreeM.isChargeBound_comp_iff (Nat.castAddMonoidHom ℝ≥0∞) fun _ _ => Nat.cast_le]
    at hq
  rw [expectedSimulatedQueryCount_eq]
  simpa [Function.comp_def, apply_ite] using
    expectedSimulatedCharge_le_of_isChargeBound so _ hq s

/-- `expectedSimulatedQueryCount_bind`, from the tower law of the expected charge. -/
example (oa : OracleComp spec α) (ob : α → OracleComp spec β) (s : σ) :
    expectedSimulatedQueryCount so charged (oa >>= ob) s =
      expectedSimulatedQueryCount so charged oa s +
        ∫⁻ r, r ∂𝒟[(fun z => expectedSimulatedQueryCount so charged (ob z.1) z.2) <$>
          (simulateQ so oa).run s] := by
  simp only [expectedSimulatedQueryCount_eq]
  exact expectedSimulatedCharge_bind so _ oa ob s

/-- A total query budget `n` on the source bounds the expected number of target queries of the
run by `n`, when from every state each call's implementation makes at most one target query in
expectation. -/
example {ι' : Type} {spec' : OracleSpec ι'} [AnswerMeasure spec']
    (impl : QueryImpl spec (StateT σ (OracleComp spec')))
    (hstep : ∀ t s, expectedCharge (fun _ => 1) ((impl t).run s) ≤ 1)
    {oa : OracleComp spec α} {n : ℕ} (h : IsTotalQueryBound oa n) (s : σ) :
    expectedCharge (fun _ => 1) ((simulateQ impl oa).run s) ≤ n := by
  rw [isTotalQueryBound_iff_isChargeBound,
    ← PFunctor.FreeM.isChargeBound_comp_iff (Nat.castAddMonoidHom ℝ≥0∞) fun _ _ => Nat.cast_le]
    at h
  simp only [Function.comp_def, Nat.coe_castAddMonoidHom, Nat.cast_one, Nat.cast_zero] at h
  exact expectedCharge_run_simulateQ_le_of_isChargeBound impl hstep h s

end VCVioTest.OracleComp.ExpectedCharge
