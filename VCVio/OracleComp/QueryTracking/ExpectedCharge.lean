/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.ExpectedQueryCount
public import VCVio.OracleComp.QueryTracking.QueryBound.Charge
public import VCVio.EvalDist.PFunctorPath
public import PolyFun.PFunctor.Free.WP

/-!
# Expected charges

Two expectations of a charge `c : spec.Domain → ℝ≥0∞` on the calls of an oracle program, both
folds over the program in the sense of PolyFun's `PFunctor.FreeM.wpFold`.

* `expectedCharge c oa` is the expected charge of `oa` under its answer measures: each call is
  charged when it is made, and the continuation is averaged over the call's answer. The fold is
  linear in its continuation (`wpFold_expectedChargeSpec_eq`), which gives the tower law
  `expectedCharge_bind`. It is the expected path charge `PFunctor.FreeM.expectedCharge` of the
  underlying free program (`expectedCharge_eq_freeM_expectedCharge`).
* `expectedSimulatedCharge so c oa s` is the expected charge of `oa` when its calls are answered
  by a stateful implementation `so` started from `s`. It generalizes
  `expectedSimulatedQueryCount`, which is the indicator charge (`expectedSimulatedQueryCount_eq`),
  satisfies the same tower law (`expectedSimulatedCharge_bind`), and is bounded by any charge
  budget (`expectedSimulatedCharge_le_of_isChargeBound`).

## Transfer through an implementation

If, from every state, the implementation of each call at `t` has expected target charge at most
`c t` (`hstep`), then the expected target charge of the whole run is at most the expected source
charge under the implementation (`expectedCharge_run_simulateQ_le`), and hence at most any charge
budget of the source program (`expectedCharge_run_simulateQ_le_of_isChargeBound`). The bound per
call must hold for every call argument and every handler state: a bound that holds only on average
over states fails once later calls depend on earlier answers. For an implementation without state
this is an instance of PolyFun's transfer principle `PFunctor.FreeM.wpFold_liftM_le`
(`expectedCharge_simulateQ_le`), whose hypothesis is discharged by the linearity of the
expectation.
-/

public section

open MeasureTheory OracleSpec
open scoped ENNReal

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α β σ : Type}

/-! ## Expected charge under the answer measures -/

section AnswerMeasure

variable [AnswerMeasure spec]

/-- The per-call specification of the expected charge with a final value: a call at `t` costs
`c t`, and its continuation is averaged over the call's answer. -/
@[expose] noncomputable def expectedChargeSpec (c : spec.Domain → ℝ≥0∞) :
    PFunctor.OpSpec spec.toPFunctor ℝ≥0∞ :=
  fun t k => c t + ∫⁻ r, r ∂𝒟[k <$> (liftM (spec.query t) : OracleComp spec (spec.Range t))]

/-- The expected charge of `oa` under its answer measures. -/
@[expose] noncomputable def expectedCharge (c : spec.Domain → ℝ≥0∞) (oa : OracleComp spec α) :
    ℝ≥0∞ :=
  PFunctor.FreeM.wpFold (expectedChargeSpec c) oa fun _ => 0

@[simp]
theorem expectedCharge_pure (c : spec.Domain → ℝ≥0∞) (x : α) :
    expectedCharge c (pure x : OracleComp spec α) = 0 :=
  rfl

theorem expectedCharge_query_bind (c : spec.Domain → ℝ≥0∞) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α) :
    expectedCharge c (liftM (spec.query t) >>= k) =
      c t + ∫⁻ r, r ∂𝒟[(fun u => expectedCharge c (k u)) <$>
        (liftM (spec.query t) : OracleComp spec (spec.Range t))] :=
  rfl

/-- The expectation fold is linear in its final value: it is the expected charge plus the expected
final value. -/
theorem wpFold_expectedChargeSpec_eq (c : spec.Domain → ℝ≥0∞) (oa : OracleComp spec α)
    (post : α → ℝ≥0∞) :
    PFunctor.FreeM.wpFold (expectedChargeSpec c) oa post =
      expectedCharge c oa + ∫⁻ r, r ∂𝒟[post <$> oa] := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [expectedCharge]
  | query_bind t k ih =>
    change expectedChargeSpec c t (fun u => PFunctor.FreeM.wpFold (expectedChargeSpec c) (k u) post)
      = expectedCharge c (liftM (spec.query t) >>= k) + _
    rw [expectedCharge_query_bind, expectedChargeSpec, lintegral_id_evalDist_map_bind]
    simp only [ih]
    rw [lintegral_id_evalDist_map_add, add_assoc]

/-- **Tower law.** The expected charge of a bind is the expected charge of its head plus the
expectation of the continuation's expected charge. -/
theorem expectedCharge_bind (c : spec.Domain → ℝ≥0∞) (oa : OracleComp spec α)
    (f : α → OracleComp spec β) :
    expectedCharge c (oa >>= f) =
      expectedCharge c oa + ∫⁻ r, r ∂𝒟[(fun x => expectedCharge c (f x)) <$> oa] := by
  rw [expectedCharge, PFunctor.FreeM.wpFold_bind]
  exact wpFold_expectedChargeSpec_eq c oa _

/-- The expected charge is the expected path charge of the underlying free program. -/
theorem expectedCharge_eq_freeM_expectedCharge (c : spec.Domain → ℝ≥0∞) (oa : OracleComp spec α) :
    expectedCharge c oa = @PFunctor.FreeM.expectedCharge spec.toPFunctor (fun _ ↦ ⊤) _ α c oa := by
  let : ∀ a, MeasurableSpace (spec.toPFunctor.B a) := fun _ ↦ ⊤
  let : ∀ a, DiscreteMeasurableSpace (spec.toPFunctor.B a) := fun _ ↦
    inferInstanceAs (@DiscreteMeasurableSpace _ ⊤)
  induction oa using OracleComp.inductionOn with
  | pure x => simp [PFunctor.FreeM.expectedCharge, PFunctor.FreeM.chargeMeasure]
  | query_bind t k ih =>
    rw [expectedCharge_query_bind]
    change _ = PFunctor.FreeM.expectedCharge c (PFunctor.FreeM.liftBind (P := spec.toPFunctor) t k)
    rw [PFunctor.FreeM.expectedCharge_liftBind]
    congr 1
    let : MeasurableSpace (spec.Range t) := ⊤
    rw [lintegral_id_evalDist_map, evalDist_liftM_query, MeasureTheory.trim_eq_self]
    simp only [ih]

/-- A charge budget bounds the expected charge. -/
theorem expectedCharge_le_of_isChargeBound {c : spec.Domain → ℝ≥0∞} {oa : OracleComp spec α}
    {B s : ℝ≥0∞} (h : PFunctor.FreeM.IsChargeBound oa c B s) : s + expectedCharge c oa ≤ B := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simpa using h
  | query_bind t k ih =>
    rw [expectedCharge_query_bind, ← add_assoc]
    by_cases htop : s + c t = ⊤
    · exact (top_le_iff.1 (htop ▸ h.1)).symm ▸ le_top
    calc s + c t + ∫⁻ r, r ∂𝒟[(fun u => expectedCharge c (k u)) <$>
          (liftM (spec.query t) : OracleComp spec (spec.Range t))]
        ≤ s + c t + (B - (s + c t)) := add_le_add le_rfl
          (lintegral_id_evalDist_map_le_of_le _ fun u =>
            ENNReal.le_sub_of_add_le_left htop (ih u (h.2 u)))
      _ = B := add_tsub_cancel_of_le h.1

end AnswerMeasure

/-! ## Expected charge through a stateful implementation -/

section Simulated

variable {m : Type → Type*} [Monad m] [EvalDistSemantics m]

/-- The per-call specification of the expected charge through `so`: a call at `t` from state `s`
costs `c t`, and its continuation is averaged over the implementation's step. -/
@[expose] noncomputable def simulatedChargeSpec (so : QueryImpl spec (StateT σ m))
    (c : spec.Domain → ℝ≥0∞) : PFunctor.OpSpec spec.toPFunctor (σ → ℝ≥0∞) :=
  fun t k s => c t + ∫⁻ r, r ∂𝒟[(fun z => k z.1 z.2) <$> (so t).run s]

/-- The expected charge of `oa` when it is interpreted by the stateful implementation `so` started
from state `s`. -/
@[expose] noncomputable def expectedSimulatedCharge (so : QueryImpl spec (StateT σ m))
    (c : spec.Domain → ℝ≥0∞) (oa : OracleComp spec α) (s : σ) : ℝ≥0∞ :=
  PFunctor.FreeM.wpFold (simulatedChargeSpec so c) oa (fun _ _ => 0) s

variable (so : QueryImpl spec (StateT σ m)) (c : spec.Domain → ℝ≥0∞)

@[simp]
theorem expectedSimulatedCharge_pure (x : α) (s : σ) :
    expectedSimulatedCharge so c (pure x : OracleComp spec α) s = 0 :=
  rfl

theorem expectedSimulatedCharge_query_bind (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α) (s : σ) :
    expectedSimulatedCharge so c (liftM (spec.query t) >>= k) s =
      c t + ∫⁻ r, r ∂𝒟[(fun z => expectedSimulatedCharge so c (k z.1) z.2) <$> (so t).run s] :=
  rfl

/-- The expected charged-query count is the expected charge of the indicator of the charged
indices. -/
theorem expectedSimulatedQueryCount_eq (charged : spec.Domain → Prop) [DecidablePred charged]
    (oa : OracleComp spec α) (s : σ) :
    expectedSimulatedQueryCount so charged oa s =
      expectedSimulatedCharge so (fun t => if charged t then 1 else 0) oa s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => rfl
  | query_bind t k ih =>
    rw [expectedSimulatedQueryCount_query_bind, expectedSimulatedCharge_query_bind]
    simp only [ih]

variable [LawfulMonad m] [LawfulEvalDistSemantics m]

/-- **Tower law.** The expected charge of a bind is the expected charge of its head plus the
expectation, over the head's interpreted run, of the continuation's expected charge. -/
theorem expectedSimulatedCharge_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (s : σ) :
    expectedSimulatedCharge so c (oa >>= ob) s =
      expectedSimulatedCharge so c oa s +
        ∫⁻ r, r ∂𝒟[(fun z => expectedSimulatedCharge so c (ob z.1) z.2) <$>
          (simulateQ so oa).run s] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    rw [bind_assoc, expectedSimulatedCharge_query_bind, expectedSimulatedCharge_query_bind,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind, lintegral_id_evalDist_map_bind]
    simp only [ih]
    rw [lintegral_id_evalDist_map_add, add_assoc]

/-- A charge budget bounds the expected charge under every stateful implementation, from every
initial state. -/
theorem expectedSimulatedCharge_le_of_isChargeBound {oa : OracleComp spec α} {B t : ℝ≥0∞}
    (h : PFunctor.FreeM.IsChargeBound oa c B t) (s : σ) :
    t + expectedSimulatedCharge so c oa s ≤ B := by
  induction oa using OracleComp.inductionOn generalizing s t with
  | pure x => simpa using h
  | query_bind a k ih =>
    rw [expectedSimulatedCharge_query_bind, ← add_assoc]
    by_cases htop : t + c a = ⊤
    · exact (top_le_iff.1 (htop ▸ h.1)).symm ▸ le_top
    calc t + c a + ∫⁻ r, r ∂𝒟[(fun z => expectedSimulatedCharge so c (k z.1) z.2) <$>
          (so a).run s]
        ≤ t + c a + (B - (t + c a)) := add_le_add le_rfl
          (lintegral_id_evalDist_map_le_of_le _ fun z =>
            ENNReal.le_sub_of_add_le_left htop (ih z.1 (h.2 z.1) z.2))
      _ = B := add_tsub_cancel_of_le h.1

end Simulated

/-! ## Transfer of expected charges through an implementation -/

section Transfer

variable {ι' : Type} {spec' : OracleSpec ι'} [AnswerMeasure spec']

/-- **Expected-charge transfer.** If, from every state, the implementation of each call at `t` has
expected target charge at most `c t`, then the expected target charge of the run is at most the
expected source charge under the implementation. -/
theorem expectedCharge_run_simulateQ_le (so : QueryImpl spec (StateT σ (OracleComp spec')))
    (c : spec.Domain → ℝ≥0∞) (d : spec'.Domain → ℝ≥0∞)
    (hstep : ∀ t s, expectedCharge d ((so t).run s) ≤ c t) (oa : OracleComp spec α) (s : σ) :
    expectedCharge d ((simulateQ so oa).run s) ≤ expectedSimulatedCharge so c oa s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => exact le_of_eq rfl
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, expectedCharge_bind,
      expectedSimulatedCharge_query_bind]
    exact add_le_add (hstep t s) (lintegral_id_evalDist_map_mono _ fun z => ih z.1 z.2)

/-- The expected target charge of a run is at most a charge budget of the source program, when
from every state each call's implementation has expected target charge at most its source
charge. -/
theorem expectedCharge_run_simulateQ_le_of_isChargeBound
    (so : QueryImpl spec (StateT σ (OracleComp spec'))) {c : spec.Domain → ℝ≥0∞}
    {d : spec'.Domain → ℝ≥0∞} (hstep : ∀ t s, expectedCharge d ((so t).run s) ≤ c t)
    {oa : OracleComp spec α} {B : ℝ≥0∞} (h : PFunctor.FreeM.IsChargeBound oa c B) (s : σ) :
    expectedCharge d ((simulateQ so oa).run s) ≤ B :=
  (expectedCharge_run_simulateQ_le so c d hstep oa s).trans
    ((zero_add _).symm.trans_le (expectedSimulatedCharge_le_of_isChargeBound so c h s))

/-- **Stateless transfer through `wpFold_liftM_le`.** With an implementation without state, the
expected target charge of the simulation is bounded by the fold of the source program whose call
at `t` costs `c t` and averages its continuation over the implementation of `t`. -/
theorem expectedCharge_simulateQ_le (route : QueryImpl spec (OracleComp spec'))
    (c : spec.Domain → ℝ≥0∞) (d : spec'.Domain → ℝ≥0∞)
    (hstep : ∀ t, expectedCharge d (route t) ≤ c t) (oa : OracleComp spec α) :
    expectedCharge d (simulateQ route oa) ≤
      PFunctor.FreeM.wpFold (P := spec.toPFunctor)
        (fun t k => c t + ∫⁻ r, r ∂𝒟[k <$> route t]) oa fun _ => 0 :=
  PFunctor.FreeM.wpFold_liftM_le (P := spec.toPFunctor) (Q := spec'.toPFunctor) route
    (Ψ := expectedChargeSpec d)
    (Φ := fun (t : spec.Domain) (k : spec.Range t → ℝ≥0∞) => c t + ∫⁻ r, r ∂𝒟[k <$> route t])
    (fun t _ _ hk => add_le_add le_rfl (lintegral_id_evalDist_map_mono (route t) hk))
    (fun t k => (wpFold_expectedChargeSpec_eq d (route t) k).trans_le
      (add_le_add (hstep t) le_rfl)) oa _

end Transfer

end OracleComp
