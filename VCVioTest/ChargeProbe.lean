/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation
public import VCVio.OracleComp.CanReturn
public import PolyFun.PFunctor.Handler.Charge
public import PolyFun.PFunctor.Free.Cost.Tactic

/-!
# Subsumption probe: VCVio query bounds as PolyFun charge bounds

Each VCVio query-bound predicate is a PolyFun `FreeM.IsChargeBound` for some charge, and the
VCVio transfer theorems are corollaries of the generic ones. Exploratory; not for merge.
-/

public section

open PFunctor OracleSpec

namespace OracleComp.ChargeProbe

universe u

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α β : Type u}

/-! ## The predicates as instances -/

/-- `IsTotalQueryBound` is the unit-charge bound. -/
theorem isTotalQueryBound_iff (oa : OracleComp spec α) (n : ℕ) :
    IsTotalQueryBound oa n ↔ FreeM.IsChargeBound oa (fun _ => (1 : ℕ)) n :=
  (FreeM.isChargeBound_one_iff_isTotalRollBound oa n).symm

/-- The weighted budgets of VCVio #942 are charge bounds with the weight as charge. -/
theorem isQueryBound_weighted_iff (oa : OracleComp spec α) (w : ι → ℕ) (W : ℕ) :
    IsQueryBound oa W (fun t b => w t ≤ b) (fun t b => b - w t) ↔ FreeM.IsChargeBound oa w W :=
  (FreeM.isChargeBound_iff_isRollBound_nat oa w W).symm

/-- `IsQueryBoundP` is the indicator-charge bound. -/
theorem isQueryBoundP_iff (oa : OracleComp spec α) (p : ι → Prop) [DecidablePred p] (n : ℕ) :
    IsQueryBoundP oa p n ↔ FreeM.IsChargeBound oa (fun t => if p t then 1 else 0) n := by
  rw [FreeM.isChargeBound_iff_isRollBound_nat]
  refine FreeM.isRollBound_congr (fun t b => ?_) (fun t b => ?_)
  · by_cases hp : p t <;> simp [hp, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  · by_cases hp : p t <;> simp [hp]

/-- `AllQueriesSatisfy` is the zero budget for the indicator of the excluded queries. -/
theorem allQueriesSatisfy_iff (oa : OracleComp spec α) (P : ι → Prop) [DecidablePred P] :
    AllQueriesSatisfy oa P ↔ FreeM.IsChargeBound oa (fun t => if P t then 0 else 1) 0 := by
  rw [← isQueryBoundP_zero_iff, isQueryBoundP_iff]
  simp only [ite_not]

/-! ## The theorems as corollaries -/

/-- `isTotalQueryBound_bind`. -/
example {oa : OracleComp spec α} {ob : α → OracleComp spec β} {n m : ℕ}
    (h₁ : IsTotalQueryBound oa n) (h₂ : ∀ x, IsTotalQueryBound (ob x) m) :
    IsTotalQueryBound (oa >>= ob) (n + m) := by
  simp only [isTotalQueryBound_iff] at *
  exact h₁.bind h₂

/-- `IsQueryBoundP.mono`. -/
example {oa : OracleComp spec α} {p : ι → Prop} [DecidablePred p] {n m : ℕ}
    (h : IsQueryBoundP oa p n) (hnm : n ≤ m) : IsQueryBoundP oa p m := by
  simp only [isQueryBoundP_iff] at *
  exact h.mono hnm

/-- Multiplication by a constant, as a monotone additive map. -/
def mulRight (k : ℕ) : ℕ →+o ℕ where
  toFun n := n * k
  map_zero' := Nat.zero_mul k
  map_add' a b := Nat.add_mul a b k
  monotone' _ _ h := Nat.mul_le_mul_right k h

/-- `IsTotalQueryBound.simulateQ_of_step_le`. -/
example {ι' : Type u} {spec' : OracleSpec.{u, u} ι'} {impl : QueryImpl spec (OracleComp spec')}
    {oa : OracleComp spec α} {n step : ℕ} (h : IsTotalQueryBound oa n)
    (hstep : ∀ t, IsTotalQueryBound (impl t) step) :
    IsTotalQueryBound (simulateQ impl oa) (n * step) := by
  simp only [isTotalQueryBound_iff] at *
  have h' := h.map (mulRight step)
  rw [map_zero] at h'
  exact (h'.mono_charge fun _ => (Nat.one_mul step).ge).liftM impl hstep

/-- VCVio #942 `IsQueryBound.simulateQ_run_weighted`. -/
example {ι' : Type u} {spec' : OracleSpec.{u, u} ι'} {σ : Type u}
    {impl : QueryImpl spec (StateT σ (OracleComp spec'))} {w : ι → ℕ} {W : ℕ}
    {q : ι' → Prop} [DecidablePred q] {oa : OracleComp spec α}
    (h : IsQueryBound oa W (fun t b => w t ≤ b) (fun t b => b - w t))
    (hstep : ∀ t s, IsQueryBoundP ((impl t).run s) q (w t)) (s : σ) :
    IsQueryBoundP ((simulateQ impl oa).run s) q W := by
  rw [isQueryBound_weighted_iff] at h
  simp only [isQueryBoundP_iff] at hstep ⊢
  exact h.run_liftM impl hstep s

/-- VCVio #942 `isQueryBound_weighted_of_per_kind`: per-kind bounds weigh into one bound. -/
example {K : Type} [Fintype K] [DecidableEq K] (κ : ι → K) (c n : K → ℕ)
    {oa : OracleComp spec α} (h : ∀ k, IsQueryBoundP oa (κ · = k) (n k)) :
    IsQueryBound oa (∑ k, c k * n k) (fun t b => c (κ t) ≤ b) (fun t b => b - c (κ t)) := by
  rw [isQueryBound_weighted_iff]
  have hvec : FreeM.IsChargeBound oa (fun t k => if κ t = k then 1 else 0) n (0 : K → ℕ) :=
    FreeM.isChargeBound_pi_iff.2 fun k => (isQueryBoundP_iff oa _ (n k)).1 (h k)
  let φ : (K → ℕ) →+o ℕ :=
    { toFun := fun v => ∑ k, c k * v k
      map_zero' := by simp
      map_add' := fun v w => by simp [mul_add, Finset.sum_add_distrib]
      monotone' := fun v w hvw => Finset.sum_le_sum fun k _ => Nat.mul_le_mul_left _ (hvw k) }
  have := hvec.map φ
  simp only [map_zero] at this
  refine this.mono_charge fun t => ?_
  change c (κ t) ≤ ∑ k, c k * (if κ t = k then 1 else 0)
  simp

/-- `IsQueryBoundP.cost_le_of_mem_support_run_simulateQ` (and the GroupModel table growth of
VCVio #930), as resource growth. -/
example {ι' : Type u} {spec' : OracleSpec.{u, u} ι'} {σ : Type u} {p : ι → Prop}
    [DecidablePred p] {impl : QueryImpl spec (StateT σ (OracleComp spec'))} (f : σ → ℕ)
    (hstep_p : ∀ t, p t → ∀ s, ∀ z ∈ support ((impl t).run s), f z.2 ≤ f s + 1)
    (hstep_np : ∀ t, ¬ p t → ∀ s, ∀ z ∈ support ((impl t).run s), f z.2 ≤ f s)
    {oa : OracleComp spec α} {n : ℕ} (h : IsQueryBoundP oa p n) (s : σ) :
    ∀ z ∈ support ((simulateQ impl oa).run s), f z.2 ≤ f s + n := by
  intro z hz
  unfold simulateQ at hz
  have hx := ((isQueryBoundP_iff oa p n).1 h).add_left (f s)
  rw [add_zero] at hx
  refine hx.le_of_canReturn_run_liftM impl f (fun t σ₁ z' hz' => ?_) le_rfl
    ((canReturn_iff_mem_support _ _).2 hz)
  rw [canReturn_iff_mem_support] at hz'
  by_cases hp : p t
  · simpa [hp] using hstep_p t hp σ₁ z' hz'
  · simpa [hp] using hstep_np t hp σ₁ z' hz'

/-- VCVio #1016 `IsTotalQueryBound.mapLens`. -/
example {ι' : Type u} {spec' : OracleSpec.{u, u} ι'}
    (l : PFunctor.Lens spec.toPFunctor spec'.toPFunctor) {oa : OracleComp spec α} {n : ℕ}
    (h : IsTotalQueryBound oa n) : IsTotalQueryBound (PFunctor.FreeM.mapLens l oa) n := by
  simp only [isTotalQueryBound_iff] at *
  exact h.mapLens l

/-! ## Automation on oracle programs -/

/-- Two coin flips, then a third when the first is heads. -/
def flips : OracleComp coinSpec Bool := do
  let b ← coinSpec.query ()
  if b then coinSpec.query () else pure false

example : IsTotalQueryBound flips 2 := by
  rw [isTotalQueryBound_iff]
  cost_bound [flips, OracleComp.liftM_def]

example : ¬ IsTotalQueryBound flips 1 := by
  rw [isTotalQueryBound_iff]
  cost_bound [flips, OracleComp.liftM_def, OracleSpec.query_def, OracleQuery.mk]
  -- `PFunctor.Obj.mk` projections are not simp-normalized; the residue is `id b = b`.
  exact fun _ => rfl

end OracleComp.ChargeProbe
