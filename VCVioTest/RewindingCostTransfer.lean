/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.CryptoFoundations.Rewinding.Cost
import VCVio.OracleComp.MapLens
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import PolyFun.PFunctor.Free.Measure.StatefulExpectedCharge

/-!
# Expected cost of fixed-table reruns

A single simulation tracks the accumulated charge and the number of reruns. Its two projections
recover the charged runs, and its private state records the inequality between the counters.
PolyFun's stateful transfer theorem puts both terminal observations under the same joint law.
-/

open Rewinding OracleComp OracleSpec MeasureTheory PFunctor PFunctor.FreeM
open scoped ENNReal

namespace VCVioTest.RewindingCostTransfer

section Observation

local instance (n : unifSpec.toPFunctor.A) : MeasurableSpace (unifSpec.toPFunctor.B n) := ⊤
local instance (n : unifSpec.toPFunctor.A) : DiscreteMeasurableSpace (unifSpec.toPFunctor.B n) :=
  inferInstanceAs (@DiscreteMeasurableSpace _ ⊤)

noncomputable abbrev coinLaw (n : unifSpec.toPFunctor.A) :=
  OracleSpec.AnswerMeasure.toMeasure (spec := unifSpec) n

variable {P : PFunctor.{0, 0}} [∀ a, MeasurableSpace (P.B a)]
  [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
  {S β : Type} [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- Compare the two terminal prices against the stateful handler's joint terminal law. -/
theorem expectedCalls_map_le (h : Handler.Stateful ProbComp S P) (alg : FreeM P β) (s : S)
    (price count : S → ℕ) (c : ℕ) (hc : ∀ t, price t ≤ c * count t) :
    expectedCalls (Prod.map id price <$> h.run alg s) ≤
      c * expectedCalls (Prod.map id count <$> h.run alg s) := by
  let : MeasurableSpace β := ⊤
  have project (p : S → ℕ) : expectedCalls (Prod.map id p <$> h.run alg s) =
      ∫⁻ z : β × S, (p z.2 : ℝ≥0∞) ∂runKernel (h.toKernelHandler coinLaw
        (fun _ => Measurable.of_discrete)) alg s := by
    rw [expectedCalls_eq_lintegral_counter, Functor.map_map]
    change (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂𝒟[(fun z : β × S => p z.2) <$> h.run alg s]) = _
    rw [lintegral_evalDist_map (h.run alg s) (f := fun z => p z.2)
      (g := fun n : ℕ => (n : ℝ≥0∞)) (Measurable.of_discrete.comp measurable_snd)
      Measurable.of_discrete]
    rw [← measureFold_run_eq_runKernel coinLaw h (fun _ => Measurable.of_discrete) alg s]
    rfl
  rw [project, project, ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top c)]
  exact lintegral_mono fun z => by exact_mod_cast hc z.2

end Observation

abbrev Counters (c : ℕ) := {p : ℕ × ℕ // p.1 ≤ c * p.2}

def advance {c : ℕ} (s : Counters c) (k : ℕ) (hk : k ≤ c) : Counters c :=
  ⟨(s.val.1 + k, s.val.2 + 1), by
    simpa only [Nat.mul_add, Nat.mul_one] using Nat.add_le_add s.property hk⟩

def jointHandler {Q : Type} {c : ℕ} (cost : Q → ℕ) (hc : ∀ q, cost q ≤ c) :
    QueryImpl (unifSpec + rerunSpec Q Unit) (StateT (Counters c) ProbComp) :=
  coins (S := Counters c) + (fun q => StateT.mk fun s => pure ((), advance s (cost q) (hc q)) :
    QueryImpl (rerunSpec Q Unit) (StateT (Counters c) ProbComp))

theorem project_run {Q β : Type} {c : ℕ} (alg : OracleComp (unifSpec + rerunSpec Q Unit) β)
    (cost : Q → ℕ) (hc : ∀ q, cost q ≤ c)
    (proj : Counters c → ℕ) (price : Q → ℕ)
    (commute : ∀ s q, proj (advance s (cost q) (hc q)) = proj s + price q) (s : Counters c) :
    Prod.map id proj <$> (simulateQ (jointHandler cost hc) alg).run s =
      runCharged alg (fun _ => ()) price (proj s) := by
  apply map_run_simulateQ_eq_of_query_map_eq _ (coins + charged (fun _ => ()) price)
  intro query state
  rcases query with n | q
  · simp [jointHandler, coins, Functor.map_map]
  · simp [jointHandler, charged, commute]

/-- Each rerun has one possible reply in a fixed table. Supply that reply to the original
continuation and leave the answers to coin queries intact. -/
def fixedTableLens {Q α : Type} (f : Q → α) :
    Lens (unifSpec + rerunSpec Q α).toPFunctor (unifSpec + rerunSpec Q Unit).toPFunctor where
  toFunA := id
  toFunB
    | .inl _ => id
    | .inr q => fun _ => f q

theorem runCharged_mapLens_fixedTable {Q α β : Type}
    (alg : OracleComp (unifSpec + rerunSpec Q α) β) (f : Q → α)
    (cost : Q → ℕ) (s : ℕ) :
    runCharged (alg.mapLens (fixedTableLens f)) (fun _ => ()) cost s =
      runCharged alg f cost s := by
  unfold runCharged
  rw [OracleComp.simulateQ_mapLens]
  congr 2
  funext t
  rcases t with n | q
  · change id <$> coins n = coins n
    simp
  · change (fun _ : Unit => f q) <$> charged (fun _ => ()) cost q = charged f cost q
    simp [charged]

abbrev Calls (Q : Type) := (unifSpec + rerunSpec Q Unit).toPFunctor

local instance {Q : Type} (a : (Calls Q).A) : MeasurableSpace ((Calls Q).B a) := ⊤
local instance {Q : Type} (a : (Calls Q).A) : Countable ((Calls Q).B a) := by
  cases a with
  | inl n => exact inferInstanceAs (Countable (Fin (n + 1)))
  | inr _ => exact inferInstanceAs (Countable Unit)

/-- A fixed answer table whose reruns each cost at most `c` costs at most `c` times the
expected unit-charge counter, including any initial counters satisfying the same bound. -/
public theorem expectedCalls_runCharged_le {Q α β : Type}
    (alg : OracleComp (unifSpec + rerunSpec Q α) β) (f : Q → α) (cost : Q → ℕ) (c : ℕ)
    (hc : ∀ q, cost q ≤ c) (s₁ s₂ : ℕ) (hs : s₁ ≤ c * s₂) :
    expectedCalls (runCharged alg f cost s₁) ≤
      c * expectedCalls (runCharged alg f (fun _ => 1) s₂) := by
  rw [← runCharged_mapLens_fixedTable alg f cost,
    ← runCharged_mapLens_fixedTable alg f (fun _ => 1)]
  let client := alg.mapLens (fixedTableLens f)
  let s : Counters c := ⟨(s₁, s₂), hs⟩
  let : MeasurableSpace (Counters c) := ⊤
  have lower := project_run client cost hc (fun p => p.val.1) cost (fun _ _ => rfl) s
  have upper := project_run client cost hc (fun p => p.val.2) (fun _ => 1) (fun _ _ => rfl) s
  rw [← lower, ← upper]
  exact expectedCalls_map_le (P := Calls Q) (jointHandler cost hc) client s
    (fun p => p.val.1) (fun p => p.val.2) c (fun p => p.property)

end VCVioTest.RewindingCostTransfer
