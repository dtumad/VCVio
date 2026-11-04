/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.PFunctorMeasure.Core
public import PolyFun.PFunctor.Free.Path.Bounded
public import PolyFun.PFunctor.Free.Path.Charge
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Measure semantics of typed interaction paths

Every `FreeM` program is a fully syntactic tree of typed interactions. PolyFun's `withPath`
instrumentation retains the dependent root-to-leaf path selected by the answers, while
`withPathLength` projects that syntax to a plain natural number before any probability semantics
is chosen.

This module denotes those instrumented programs directly as Mathlib measures. The canonical
complexity observer is `queryCountMeasure : Measure ℕ`, which needs no measurable-space choice
for the dependent path type. A full `pathMeasure` remains available when a caller supplies that
choice explicitly; no global measurable-space instance on paths is installed.

`chargeMeasure c` is the distribution of the PolyFun path charge `Path.charge c` of a completed
path, for a charge `c` in `ℝ≥0∞`, and `expectedCharge c` is its expectation. It generalizes the
expected query count, which is the unit charge (`expectedQueryCount_eq_expectedCharge`), is
bounded by every charge budget (`expectedCharge_le_of_isChargeBound`), and satisfies the fold
equation `expectedCharge_liftBind`: a call costs its price plus the expected charge of the
continuation.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

universe u v uA

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, u}} [∀ a, MeasurableSpace (P.B a)] [P.AnswerMeasure]
  [∀ a, DiscreteMeasurableSpace (P.B a)] {α : Type v}

/-! ## Observable measures -/

/-- The measure of fully typed paths through `program` for an explicitly selected measurable
space on its dependent path type. -/
noncomputable def pathMeasure (program : FreeM P α)
    [MeasurableSpace (Path program)] : Measure (Path program) :=
  denote (withPath program)

/-- The distribution of the number of interactions on a completed typed path.

The length projection happens in syntax, before denotation, so this canonical observer does not
need a measurable-space instance on `Path program`. -/
noncomputable def queryCountMeasure (program : FreeM P α) : Measure ℕ :=
  denote (withPathLength program)

instance pathMeasure.instIsProbabilityMeasure (program : FreeM P α)
    [MeasurableSpace (Path program)] : IsProbabilityMeasure (pathMeasure program) :=
  inferInstanceAs (IsProbabilityMeasure (denote (withPath program)))

instance queryCountMeasure.instIsProbabilityMeasure (program : FreeM P α) :
    IsProbabilityMeasure (queryCountMeasure program) :=
  inferInstanceAs (IsProbabilityMeasure (denote (withPathLength program)))

/-- The expected number of interactions on a completed typed path. -/
noncomputable def expectedQueryCount (program : FreeM P α) : ℝ≥0∞ :=
  ∫⁻ count, (count : ℝ≥0∞) ∂queryCountMeasure program

/-- The distribution of the charge of a completed typed path. The charge is computed in syntax,
before denotation, so it needs no measurable-space instance on `Path program`. -/
noncomputable def chargeMeasure (c : P.A → ℝ≥0∞) (program : FreeM P α) : Measure ℝ≥0∞ :=
  denote (FreeM.map (Path.charge c program) (withPath program))

/-- The expected charge of a completed typed path. -/
noncomputable def expectedCharge (c : P.A → ℝ≥0∞) (program : FreeM P α) : ℝ≥0∞ :=
  ∫⁻ x, x ∂chargeMeasure c program

/-! ## Marginals and projections -/

/-- Pushing the full path measure through path length gives the canonical query-count measure. -/
theorem map_length_pathMeasure (program : FreeM P α)
    [MeasurableSpace (Path program)] [DiscreteMeasurableSpace (Path program)] :
    (pathMeasure program).map (Path.length program) = queryCountMeasure program := by
  rw [pathMeasure, queryCountMeasure, withPathLength, denote_map_of_discrete]

/-- Forgetting the path while retaining its selected leaf recovers the program denotation. -/
theorem map_output_pathMeasure [MeasurableSpace α] (program : FreeM P α)
    [MeasurableSpace (Path program)] [DiscreteMeasurableSpace (Path program)] :
    (pathMeasure program).map (output program) = denote program := by
  unfold pathMeasure
  calc
    (denote (withPath program)).map (output program) =
        denote (FreeM.map (output program) (withPath program)) :=
      (denote_map_of_discrete (withPath program) (output program)).symm
    _ = denote program := congrArg denote (map_output_withPath program)

/-- Pushing the full path measure through the path charge gives the charge measure. -/
theorem map_charge_pathMeasure (c : P.A → ℝ≥0∞) (program : FreeM P α)
    [MeasurableSpace (Path program)] [DiscreteMeasurableSpace (Path program)] :
    (pathMeasure program).map (Path.charge c program) = chargeMeasure c program := by
  rw [pathMeasure, chargeMeasure, denote_map_of_discrete]

/-- The expected charge is the integral of the path charge against the full path measure. -/
theorem expectedCharge_eq_lintegral_pathMeasure (c : P.A → ℝ≥0∞) (program : FreeM P α)
    [MeasurableSpace (Path program)] [DiscreteMeasurableSpace (Path program)] :
    expectedCharge c program = ∫⁻ p, Path.charge c program p ∂pathMeasure program := by
  rw [expectedCharge, ← map_charge_pathMeasure,
    lintegral_map (f := fun x => x) measurable_id Measurable.of_discrete]

/-- The expected query count is the expected unit charge. -/
theorem expectedQueryCount_eq_expectedCharge (program : FreeM P α) :
    expectedQueryCount program = expectedCharge (fun _ => 1) program := by
  let _ : MeasurableSpace (Path program) := ⊤
  rw [expectedQueryCount, ← map_length_pathMeasure,
    lintegral_map Measurable.of_discrete Measurable.of_discrete,
    expectedCharge_eq_lintegral_pathMeasure]
  refine lintegral_congr fun p => ?_
  rw [Path.length_eq_charge_one]
  convert (Path.charge_map_addMonoidHom (c := fun _ => (1 : ℕ)) (Nat.castAddMonoidHom ℝ≥0∞)
    program p).symm using 2
  · simp
  · funext x; simp

/-- The expected charge of a call is its price plus the expected charge of the continuation. -/
theorem expectedCharge_liftBind (c : P.A → ℝ≥0∞) (a : P.A) (r : P.B a → FreeM P α) :
    expectedCharge c (FreeM.liftBind a r) =
      c a + ∫⁻ b, expectedCharge c (r b) ∂AnswerMeasure.toMeasure a := by
  have key : FreeM.map (Path.charge c (FreeM.liftBind a r)) (withPath (FreeM.liftBind a r)) =
      FreeM.liftBind a fun b =>
        FreeM.map (c a + ·) (FreeM.map (Path.charge c (r b)) (withPath (r b))) := by
    rw [withPath_liftBind]
    refine congrArg (FreeM.liftBind a) (funext fun b => ?_)
    rw [← FreeM.comp_map, ← FreeM.comp_map]
    rfl
  rw [expectedCharge, chargeMeasure, key, denote_liftBind _ _ Measurable.of_discrete.aemeasurable,
    Measure.lintegral_bind (f := fun x => x) Measurable.of_discrete.aemeasurable
      measurable_id.aemeasurable]
  simp only [denote_map_of_measurable _ _ (measurable_const_add (c a)),
    lintegral_map (f := fun x => x) measurable_id (measurable_const_add (c a)),
    lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  rfl

/-! ## Exact and worst-case path lengths -/

/-- If every typed path has length `count`, then the query-count measure is the Dirac measure at
`count`. The proof uses the full path measure only under a local discrete measurable space. -/
theorem queryCountMeasure_eq_dirac_of_length_eq (program : FreeM P α) (count : ℕ)
    (hlength : ∀ path : Path program, Path.length program path = count) :
    queryCountMeasure program = Measure.dirac count := by
  let _ : MeasurableSpace (Path program) := ⊤
  rw [← map_length_pathMeasure]
  have hfun : Path.length program = fun _ ↦ count := funext hlength
  rw [hfun, Measure.map_const]
  simp

/-- A pointwise constant typed-path length has that exact expectation. -/
theorem expectedQueryCount_eq_of_length_eq (program : FreeM P α) (count : ℕ)
    (hlength : ∀ path : Path program, Path.length program path = count) :
    expectedQueryCount program = (count : ℝ≥0∞) := by
  rw [expectedQueryCount, queryCountMeasure_eq_dirac_of_length_eq program count hlength]
  simp

/-- A charge budget bounds the expected charge. -/
theorem expectedCharge_le_of_isChargeBound {c : P.A → ℝ≥0∞} {program : FreeM P α} {B : ℝ≥0∞}
    (h : program.IsChargeBound c B) : expectedCharge c program ≤ B := by
  let _ : MeasurableSpace (Path program) := ⊤
  rw [expectedCharge_eq_lintegral_pathMeasure]
  refine (lintegral_mono (g := fun _ => B) fun p => ?_).trans_eq (by simp)
  simpa using Path.charge_le_of_isChargeBound h p

/-- A branchwise syntactic roll bound bounds expected query count.

It is the unit-charge instance of `expectedCharge_le_of_isChargeBound`, not an independent
expected-cost assumption. -/
theorem expectedQueryCount_le_of_isTotalRollBound (program : FreeM P α) {bound : ℕ}
    (hbound : program.IsTotalRollBound bound) :
    expectedQueryCount program ≤ (bound : ℝ≥0∞) := by
  rw [expectedQueryCount_eq_expectedCharge]
  refine expectedCharge_le_of_isChargeBound ?_
  have := (isChargeBound_comp_iff (Nat.castAddMonoidHom ℝ≥0∞) fun _ _ => Nat.cast_le).2
    ((isChargeBound_one_iff_isTotalRollBound program bound).2 hbound)
  simpa [Function.comp_def] using this

end PFunctor.FreeM
