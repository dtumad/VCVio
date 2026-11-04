/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import VCVio.OracleComp.QueryTracking.QueryBound.Charge
public import VCVio.OracleComp.QueryTracking.QueryCost
public import PolyFun.PFunctor.Free.Path.Charge
public import PolyFun.PFunctor.Free.Cost.Event

/-!
# Cost Models for Oracle Computations

This file defines a general cost model for oracle computations, parametric over any
`AddCommMonoid` cost type. This supports natural numbers, extended non-negative reals,
per-oracle cost vectors, signed weights, and custom multi-dimensional cost structures. An upper
bound uses the declared cost order: signed refunds may cancel earlier charges, and reversing the
order changes what an upper bound means. Idempotent addition (such as maximum) or saturating
accumulation may record arbitrarily many unit charges as one; nonnegativity and canonical order
alone do not make the model a counter. These weighted bounds are operation counts only with a
separately justified counting arithmetic and charge table, such as ordinary natural-number vectors
with unit charges in the designated coordinates. Even a nonnegative model may deliberately omit
work or charge zero for an instruction; its accounting boundary must be stated.

Uses `AddWriterT` (defined in `ToMathlib.Control.WriterT`) for additive cost accumulation.

## Main Definitions

- `instrumentedRun oa cm`: `oa` interpreted in the canonical free runtime with additive cost
  tracking.
- `addCostOracle costFn`: the corresponding one-query instrumented oracle implementation.
- `CostModel spec ω`: Assigns cost `queryCost t : ω` to each oracle query `t`.
- `costDist oa cm`: Joint distribution of `(output, totalCost)`.
- `expectedCost oa cm val`: Expected total cost `E[val(cost)]`, computed by Lebesgue integration.
- `WorstCaseCostBound`, `ExpectedCostBound`: Cost bound predicates.

## Key Results

- `fst_map_costDist`: Cost instrumentation doesn't change the output distribution.
- `costDist_pure`, `costDist_bind`, `costDist_query`, `costDist_map`: Instrumentation equations.
- `worstCaseCostBound_map_iff`: Pure observations preserve and reflect query-cost bounds.
- `support_costDist_eq_range_charge`: the support of the cost distribution is the output and the
  PolyFun path charge `PFunctor.FreeM.Path.charge` of each completed path, so
  `WorstCaseCostBound` bounds the charge of every completed path
  (`worstCaseCostBound_iff_forall_charge_le`) and is implied by a charge budget
  (`worstCaseCostBound_of_isChargeBound`).
- `expectedCost_pure`: Expected cost of a pure computation is `0`.
- `prEvent_costDist_gt_le_expectedCost_div`: Markov's inequality for cost distributions.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal

/-! ## Cost Model, Cost Oracle, Cost Distribution

All definitions below operate at `Type` (= `Type 0`), matching the program logic and structural
support API.
-/

variable {ι : Type} {spec : OracleSpec ι} {α β : Type} {ω : Type}

/-- Oracle that tracks additive cost. Wraps `costOracle` with `Multiplicative`
to get additive accumulation through the existing `WriterT` infrastructure. -/
def addCostOracle [AddCommMonoid ω] (costFn : spec.Domain → ω) :
    QueryImpl spec (AddWriterT ω (OracleComp spec)) :=
  (QueryImpl.ofLift spec (OracleComp spec)).withAddCost costFn

@[simp]
lemma fst_map_run_simulateQ_addCostOracle [AddCommMonoid ω] (costFn : spec.Domain → ω)
    (oa : OracleComp spec α) :
    Prod.fst <$> (simulateQ (addCostOracle costFn) oa).run = oa := by
  simp [addCostOracle, QueryImpl.withAddCost, QueryImpl.fst_map_run_withCost]

/-- A cost model assigns a cost in `ω` to each oracle query.
The cost type `ω` can be `ℕ`, `ℝ≥0∞`, `ι → ℕ` (per-oracle), or any `AddCommMonoid`. -/
structure CostModel (spec : OracleSpec ι) (ω : Type) [AddCommMonoid ω] where
  /-- The cost charged for one query on input `t`; costs of successive queries add up. -/
  queryCost : spec.Domain → ω

namespace CostModel

/-- The zero cost model: every query is free. -/
def zero [AddCommMonoid ω] : CostModel spec ω where
  queryCost _ := 0

end CostModel

/-- Run `oa` in the canonical free `OracleComp` runtime instrumented by `cm`'s additive
query-cost function. This is the semantic core of `CostModel`. -/
abbrev instrumentedRun [AddCommMonoid ω] (oa : OracleComp spec α) (cm : CostModel spec ω) :
    AddWriterT ω (OracleComp spec) α :=
  simulateQ ((QueryImpl.ofLift spec (OracleComp spec)).withAddCost cm.queryCost) oa

/-- The joint distribution of `(output, totalCost)` obtained by running `oa` with
additive cost tracking. Cost accumulates via `+` through `AddWriterT`.

Since `Multiplicative ω` and `ω` are definitionally equal, the second component
of the product can be used directly as `ω`. -/
def costDist [AddCommMonoid ω] (oa : OracleComp spec α) (cm : CostModel spec ω) :=
  (instrumentedRun oa cm).run

/-- A pure computation records zero query cost. -/
@[simp] theorem costDist_pure [AddCommMonoid ω] (value : α) (cm : CostModel spec ω) :
    costDist (pure value) cm = pure (value, 1) := by
  simp only [costDist, instrumentedRun, simulateQ_pure, WriterT.run_pure]

/-- Instrumented sequencing retains the two results' actual charges and adds them. -/
theorem costDist_bind [AddCommMonoid ω] (first : OracleComp spec α)
    (next : α → OracleComp spec β) (cm : CostModel spec ω) :
    costDist (first >>= next) cm = (do
      let left ← costDist first cm
      let right ← costDist (next left.1) cm
      return (right.1, left.2 * right.2)) := by
  simp only [costDist, instrumentedRun, simulateQ_bind, WriterT.run_bind]
  apply bind_congr
  intro left
  rw [map_eq_bind_pure_comp]
  rfl

/-- A single query records its designated charge and retains the response. -/
theorem costDist_query [AddCommMonoid ω] (query : spec.Domain) (cm : CostModel spec ω) :
    costDist (spec.query query : OracleComp spec (spec.Range query)) cm = (do
      let response ← (spec.query query : OracleComp spec (spec.Range query))
      return (response, Multiplicative.ofAdd (cm.queryCost query))) := by
  simp [costDist, instrumentedRun, QueryImpl.withAddCost, WriterT.run_bind]

/-- A pure result observation preserves all accumulated query charges. -/
theorem costDist_map [AddCommMonoid ω] (program : OracleComp spec α) (f : α → β)
    (cm : CostModel spec ω) :
    costDist (f <$> program) cm =
      (fun result => (f result.1, result.2)) <$> costDist program cm := by
  simp [costDist, instrumentedRun, WriterT.run_map]

/-- Cost instrumentation does not change the output distribution. -/
@[simp]
theorem fst_map_costDist [AddCommMonoid ω] (oa : OracleComp spec α) (cm : CostModel spec ω) :
    Prod.fst <$> costDist oa cm = oa :=
  fst_map_run_simulateQ_addCostOracle cm.queryCost oa


/-! ## Expected Cost -/

section ExpectedCost

variable [AddCommMonoid ω] [MeasurableSpace ω]
variable [AnswerMeasure spec]

/-- The expected total cost of `oa` under cost model `cm`, valued by `val : ω → ℝ≥0∞`.
Computed as the Lebesgue integral `∫⁻ (x, c), val c ∂𝒟[costDist oa cm]`.

The valuation `val` maps the abstract cost type to `ℝ≥0∞` for expectation computation.
For `ω = ℕ`, use `(↑·)`. For `ω = ℝ≥0∞`, use `id`. For multi-dimensional cost,
choose which dimension to analyze. -/
noncomputable def expectedCost (oa : OracleComp spec α) (cm : CostModel spec ω)
    (val : ω → ℝ≥0∞) : ℝ≥0∞ :=
  AddWriterT.expectedCost (instrumentedRun oa cm) val

/-- Convenience: expected cost for `ℕ`-valued cost models. -/
noncomputable abbrev expectedCostNat (oa : OracleComp spec α)
    (cm : CostModel spec ℕ) : ℝ≥0∞ :=
  expectedCost oa cm (fun n => ↑n)

/-- The `CostModel.expectedCost` facade is the Lebesgue integral of the cost projection of the
instrumented joint distribution. -/
theorem expectedCost_eq_lintegral_costDist [MeasurableSpace α]
    (oa : OracleComp spec α) (cm : CostModel spec ω)
    (val : ω → ℝ≥0∞) (hval : Measurable val) :
    expectedCost oa cm val =
      ∫⁻ z, val (Multiplicative.toAdd z.2) ∂𝒟[costDist oa cm] :=
  AddWriterT.expectedCost_eq_lintegral_run _ val hval

@[simp]
theorem expectedCost_pure (x : α) (cm : CostModel spec ω)
    (val : ω → ℝ≥0∞) (hvalMeas : Measurable val) (hval : val 0 = 0) :
    expectedCost (spec := spec) (pure x) cm val = 0 := by
  simpa only [expectedCost, instrumentedRun, simulateQ_pure] using
    (AddWriterT.expectedCost_pure x val hvalMeas).trans hval

/-- If `val z.2 ≤ c` for all `z` in the support of `costDist`, then `expectedCost ≤ c`.
This is the key bridge from worst-case (support) bounds to expected bounds. -/
theorem expectedCost_le_of_support_bound (oa : OracleComp spec α) (cm : CostModel spec ω)
    (val : ω → ℝ≥0∞) (c : ℝ≥0∞) (hval : Measurable val)
    (h : ∀ z ∈ support (costDist oa cm), val (Multiplicative.toAdd z.2) ≤ c) :
    expectedCost oa cm val ≤ c := by
  apply AddWriterT.expectedCost_le_of_ae_le
  apply evalDist.ae_of_forall_mem_support _ _ (measurableSet_le hval measurable_const)
  intro w hw
  rw [AddWriterT.costs_def, support_map] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  exact h z hz

end ExpectedCost

/-! ## Worst-Case Cost Bounds -/

/-- Every execution path of `oa` under `cm` has total cost at most `bound`. -/
def WorstCaseCostBound [AddCommMonoid ω] [Preorder ω]
    (oa : OracleComp spec α) (cm : CostModel spec ω) (bound : ω) : Prop :=
  AddWriterT.PathwiseCostAtMost (instrumentedRun oa cm) bound

/-- `WorstCaseCostBound` is equivalently a support bound over `costDist`. -/
theorem worstCaseCostBound_iff_support_bound [AddCommMonoid ω] [Preorder ω]
    (oa : OracleComp spec α) (cm : CostModel spec ω) (bound : ω) :
    WorstCaseCostBound oa cm bound ↔
      ∀ z ∈ support (costDist oa cm), Multiplicative.toAdd z.2 ≤ bound := by
  unfold WorstCaseCostBound costDist instrumentedRun AddWriterT.PathwiseCostAtMost
  rfl

/-- A pure result observation preserves and reflects a complete-path query-cost bound. -/
theorem worstCaseCostBound_map_iff [AddCommMonoid ω] [Preorder ω]
    (program : OracleComp spec α) (f : α → β) (cm : CostModel spec ω) (budget : ω) :
    WorstCaseCostBound (f <$> program) cm budget ↔ WorstCaseCostBound program cm budget := by
  simp only [worstCaseCostBound_iff_support_bound, costDist_map, support_map, Set.mem_image]
  constructor
  · intro h result member
    exact h (f result.1, result.2) ⟨result, member, rfl⟩
  · intro h result member
    obtain ⟨original, member, rfl⟩ := member
    exact h original member

/-- Every completed response of a single query has its designated charge. -/
theorem worstCaseCostBound_query [AddCommMonoid ω] [Preorder ω] (query : spec.Domain)
    (cm : CostModel spec ω) :
    WorstCaseCostBound (spec.query query : OracleComp spec (spec.Range query)) cm
      (cm.queryCost query) := by
  intro result member
  change result ∈ support (costDist (spec.query query : OracleComp spec _) cm) at member
  rw [costDist_query] at member
  rcases (mem_support_bind_iff _ _ _).mp member with ⟨response, _, member⟩
  rw [mem_support_pure_iff] at member
  subst result
  exact le_rfl

/-- The actual instrumented query charges its key before the continuation. -/
theorem costDist_query_bind [AddCommMonoid ω]
    (t : spec.Domain) (k : spec.Range t → OracleComp spec α) (cm : CostModel spec ω) :
    costDist ((spec.query t : OracleComp spec (spec.Range t)) >>= k) cm =
      (spec.query t : OracleComp spec (spec.Range t)) >>= fun u =>
        (fun z => (z.1, Multiplicative.ofAdd (cm.queryCost t + Multiplicative.toAdd z.2))) <$>
          costDist (k u) cm := by
  simp [costDist, instrumentedRun, simulateQ_query,
    QueryImpl.withAddCost, WriterT.run_bind, bind_assoc]

/-- A pure computation has zero pathwise cost. -/
@[simp] theorem worstCaseCostBound_pure [AddCommMonoid ω] [Preorder ω]
    (a : α) (cm : CostModel spec ω) (B : ω) :
    WorstCaseCostBound (pure a) cm B ↔ 0 ≤ B := by
  simp [worstCaseCostBound_iff_support_bound, costDist, instrumentedRun]

/-- A query budget bounds the key charge plus every supported continuation cost. -/
theorem worstCaseCostBound_query_bind_iff [AddCommMonoid ω] [Preorder ω]
    (t : spec.Domain) (k : spec.Range t → OracleComp spec α) (cm : CostModel spec ω) (B : ω) :
    WorstCaseCostBound ((spec.query t : OracleComp spec (spec.Range t)) >>= k) cm B ↔
      ∀ u z, z ∈ support (costDist (k u) cm) →
        cm.queryCost t + Multiplicative.toAdd z.2 ≤ B := by
  rw [worstCaseCostBound_iff_support_bound, costDist_query_bind]
  simp only [support_bind, support_liftM_query, Set.mem_iUnion, Set.mem_univ,
    support_map, Set.mem_image]
  constructor
  · intro h u z hz
    exact h _ ⟨u, trivial, z, hz, rfl⟩
  · intro h z hz
    obtain ⟨u, _, w, hw, rfl⟩ := hz
    exact h u w hw

/-- Pathwise budgets add under sequencing of the actual instrumented computations. -/
theorem WorstCaseCostBound.bind [AddCommMonoid ω] [Preorder ω] [IsOrderedAddMonoid ω]
    {oa : OracleComp spec α} {k : α → OracleComp spec β} {cm : CostModel spec ω} {A B : ω}
    (ha : WorstCaseCostBound oa cm A) (hb : ∀ a, WorstCaseCostBound (k a) cm B) :
    WorstCaseCostBound (oa >>= k) cm (A + B) := by
  unfold WorstCaseCostBound instrumentedRun at *
  rw [simulateQ_bind]
  exact AddWriterT.pathwiseCostAtMost_bind ha hb


/-! ## Worst-case bounds as path charges -/

/-- The support of the cost distribution is, for each completed path, its output together with the
path's charge under the cost model. -/
theorem support_costDist_eq_range_charge [AddCommMonoid ω] (oa : OracleComp spec α)
    (cm : CostModel spec ω) :
    support (costDist oa cm) = Set.range fun p : PFunctor.FreeM.Path oa =>
      (PFunctor.FreeM.output oa p,
        Multiplicative.ofAdd (PFunctor.FreeM.Path.charge cm.queryCost oa p)) := by
  induction oa using PFunctor.FreeM.rec with
  | pure a =>
    ext z
    change z ∈ support (costDist (pure a : OracleComp spec α) cm) ↔ _
    rw [costDist_pure, support_pure, Set.mem_singleton_iff]
    exact ⟨fun h => ⟨⟨⟩, h.symm⟩, fun ⟨_, h⟩ => h.symm⟩
  | liftBind t k ih =>
    change support (costDist ((spec.query t : OracleComp spec _) >>= k) cm) = _
    rw [costDist_query_bind]
    ext z
    simp only [support_bind, support_query, Set.mem_iUnion, Set.mem_univ, exists_true_left,
      support_map, ih, Set.mem_image, Set.mem_range, exists_exists_eq_and]
    exact ⟨fun ⟨u, p, h⟩ => ⟨⟨u, p⟩, h⟩, fun ⟨⟨u, p⟩, h⟩ => ⟨u, p, h⟩⟩

/-- A worst-case cost bound bounds the charge of every completed path. -/
theorem worstCaseCostBound_iff_forall_charge_le [AddCommMonoid ω] [Preorder ω]
    (oa : OracleComp spec α) (cm : CostModel spec ω) (B : ω) :
    WorstCaseCostBound oa cm B ↔
      ∀ p : PFunctor.FreeM.Path oa, PFunctor.FreeM.Path.charge cm.queryCost oa p ≤ B := by
  rw [worstCaseCostBound_iff_support_bound, support_costDist_eq_range_charge, Set.forall_mem_range]
  rfl

/-- A charge budget gives a worst-case cost bound. -/
theorem worstCaseCostBound_of_isChargeBound [AddCommMonoid ω] [PartialOrder ω]
    {oa : OracleComp spec α} {cm : CostModel spec ω} {B : ω}
    (h : PFunctor.FreeM.IsChargeBound oa cm.queryCost B) : WorstCaseCostBound oa cm B :=
  (worstCaseCostBound_iff_forall_charge_le oa cm B).2 fun p =>
    (zero_add _).symm.trans_le (PFunctor.FreeM.Path.charge_le_of_isChargeBound h p)

/-- When every query has an answer, a worst-case cost bound in a canonically ordered cost type is
a charge budget. -/
theorem worstCaseCostBound_iff_isChargeBound [AddCommMonoid ω] [PartialOrder ω]
    [CanonicallyOrderedAdd ω] [∀ t, Nonempty (spec.Range t)] (oa : OracleComp spec α)
    (cm : CostModel spec ω) (B : ω) :
    WorstCaseCostBound oa cm B ↔ PFunctor.FreeM.IsChargeBound oa cm.queryCost B := by
  refine ⟨fun h => ?_, worstCaseCostBound_of_isChargeBound⟩
  rw [worstCaseCostBound_iff_forall_charge_le] at h
  exact PFunctor.FreeM.Path.isChargeBound_of_forall_charge_le
    (PFunctor.FreeM.programProgress_of_nonempty oa) fun p => (zero_add _).trans_le (h p)


/-! ## Cost Bounds -/

section CostBounds

variable [AddCommMonoid ω] [MeasurableSpace ω]
variable [AnswerMeasure spec]

/-- The expected cost of `oa` under `cm` (valued by `val`) is at most `bound`. -/
def ExpectedCostBound (oa : OracleComp spec α) (cm : CostModel spec ω)
    (val : ω → ℝ≥0∞) (bound : ℝ≥0∞) : Prop :=
  expectedCost oa cm val ≤ bound

/-- A strict cost bound implies an expected cost bound, provided the valuation `val`
is monotone with respect to `≤` on `ω`. -/
theorem WorstCaseCostBound.toExpectedCostBound [Preorder ω]
    {oa : OracleComp spec α} {cm : CostModel spec ω} {bound : ω}
    (hstrict : WorstCaseCostBound oa cm bound)
    {val : ω → ℝ≥0∞} (hval_mono : Monotone val) (hval : Measurable val) :
    ExpectedCostBound oa cm val (val bound) :=
  AddWriterT.expectedCost_le_of_pathwiseCostAtMost hstrict hval_mono hval

/-- **Markov's inequality for cost distributions** (multiplication form).
The probability that the valued cost exceeds `t`, times `t`, is at most `expectedCost`. -/
theorem prEvent_costDist_gt_mul_le_expectedCost
    (oa : OracleComp spec α) (cm : CostModel spec ω)
    (val : ω → ℝ≥0∞) (hval : Measurable val) (t : ℝ≥0∞) :
    Pr{let z ← costDist oa cm}[t < val (Multiplicative.toAdd z.2)] * t ≤
      expectedCost oa cm val := by
  simpa only [AddWriterT.prEvent_costs, expectedCost, costDist] using
    AddWriterT.prEvent_cost_gt_mul_le_expectedCost (instrumentedRun oa cm) hval t

/-- **Markov's inequality for cost distributions** (division form). -/
theorem prEvent_costDist_gt_le_expectedCost_div
    (oa : OracleComp spec α) (cm : CostModel spec ω) (val : ω → ℝ≥0∞) (hval : Measurable val)
    (t : ℝ≥0∞) (ht : 0 < t) (ht' : t ≠ ⊤) :
    Pr{let z ← costDist oa cm}[t < val (Multiplicative.toAdd z.2)] ≤
      expectedCost oa cm val / t :=
  (ENNReal.le_div_iff_mul_le (.inl ht.ne') (.inl ht')).mpr
    (prEvent_costDist_gt_mul_le_expectedCost oa cm val hval t)

end CostBounds

/-! ## Standard Cost Models -/

namespace CostModel

/-- Unit cost model: every oracle query costs 1.
Total cost under this model equals total query count. -/
def unit : CostModel spec ℕ where
  queryCost _ := 1

end CostModel

section UnitCostBridge

/-- A strict bound under the unit cost model yields a uniform per-index query bound:
if every execution uses at most `bound` total unit-cost steps, then each oracle index
is queried at most `bound` times. -/
theorem WorstCaseCostBound.toIsPerIndexQueryBound_unit
    [DecidableEq ι] [∀ t, Nonempty (spec.Range t)]
    {oa : OracleComp spec α} {bound : ℕ}
    (h : WorstCaseCostBound oa CostModel.unit bound) :
    IsPerIndexQueryBound oa (fun _ => bound) := by
  rw [worstCaseCostBound_iff_isChargeBound] at h
  rw [isPerIndexQueryBound_iff_isChargeBound]
  have := h.map (⟨⟨⟨fun n _ => n, rfl⟩, fun _ _ => rfl⟩, fun _ _ h _ => h⟩ : ℕ →+o (ι → ℕ))
  refine this.mono_charge fun t i => ?_
  by_cases hi : i = t
  · subst hi; simp only [Pi.single_eq_same]; exact le_rfl
  · simp [hi]

/-- If `main` makes at most `qb i` queries to each oracle `i`, then its total query count
(under the unit cost model) is at most `∑ i, qb i` on every execution path. -/
theorem IsPerIndexQueryBound.toWorstCaseCostBound_unit_sum
    [DecidableEq ι] [Fintype ι]
    {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) :
    WorstCaseCostBound oa CostModel.unit (∑ i, qb i) := by
  rw [isPerIndexQueryBound_iff_isChargeBound] at h
  rw [worstCaseCostBound_iff_forall_charge_le]
  intro p
  have hp := (zero_add _).symm.trans_le (PFunctor.FreeM.Path.charge_le_of_isChargeBound h p)
  have hsum := PFunctor.FreeM.Path.charge_map_addMonoidHom
    (∑ i, Pi.evalAddMonoidHom (fun _ : ι => ℕ) i) oa p (c := fun t => Pi.single t 1)
  have hc : (⇑(∑ i, Pi.evalAddMonoidHom (fun _ : ι => ℕ) i) ∘ fun t => Pi.single t (1 : ℕ)) =
      (CostModel.unit (spec := spec)).queryCost := by
    funext t; simp [CostModel.unit]
  rw [← hc, hsum]
  simpa using Finset.sum_le_sum fun i _ => hp i

/-- Corollary: the expected total query count is also at most `∑ i, qb i`. Follows from the
worst-case bound `toWorstCaseCostBound_unit_sum`. -/
theorem IsPerIndexQueryBound.toExpectedCostBound_unit_sum
    [DecidableEq ι] [Fintype ι]
    [AnswerMeasure spec]
    {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) :
    ExpectedCostBound oa CostModel.unit (fun n => (n : ENNReal)) (∑ i, qb i) := by
  simpa using (toWorstCaseCostBound_unit_sum h).toExpectedCostBound
    Nat.mono_cast Measurable.of_discrete

end UnitCostBridge

namespace OracleComp

/-- Run a `ProbComp` with unit-cost instrumentation: each call to the uniform-selection oracle
is counted as cost 1. -/
abbrev probCompUnitQueryRun {β : Type} (oa : ProbComp β) :
    AddWriterT ℕ ProbComp β :=
  simulateQ ((QueryImpl.ofLift unifSpec ProbComp).withUnitCost) oa

end OracleComp
