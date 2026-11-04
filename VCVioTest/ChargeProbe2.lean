/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVioTest.ChargeProbe
public import VCVio.OracleComp.QueryTracking.ExpectedQueryCount
public import VCVio.OracleComp.QueryTracking.CachingOracle
public import PolyFun.PFunctor.Free.Cost.Support
public import Mathlib.Basic.ENNReal.Operations
public import VCVio.ProgramLogic.Unary.HandlerSpecs

/-!
# Subsumption probe, part 2: the hard cases

Exploratory; not for merge. Re-derives with the generic PolyFun API:

* deterministic runs (VCVio #1014 `DeterminedCost`, ArkLib `profileArithmetic`);
* the support-restricted bind of `IsQueryBoundP`;
* ℝ≥0∞-weighted round costs (ArkLib `queryBound_round_cost`), in value form;
* completed-path transfer through a stateless handler (VCVio #1013);
* an expected charge for stateful handlers as a fold, generalizing
  `expectedSimulatedQueryCount`, with its tower law and its bound by the structural budget.
-/

public section

open PFunctor OracleSpec ENNReal

namespace OracleComp.ChargeProbe2

universe u

/-! ## ℝ≥0∞ distributes addition over nonempty suprema -/

instance : PFunctor.AddSupDistrib ℝ≥0∞ where
  add_sSup_le _ _ hs := (ENNReal.add_sSup hs).le

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}

/-! ## Deterministic runs -/

/-- An instrumented run through a deterministic handler is the output and charge of the one path
the handler picks (VCVio #1014 `run_withAddCost_mem_support_costDist`, exact form). -/
example (answer : QueryImpl spec Id) (c : spec.Domain → ℕ) (oa : OracleComp spec α) (s : ℕ) :
    ((simulateQ (PFunctor.Handler.withCharge (P := spec.toPFunctor) answer c :
      QueryImpl spec (StateT ℕ Id)) oa).run s).run =
      (FreeM.output oa (FreeM.Path.ofHandler (fun t => (answer t).run) oa),
        s + FreeM.Path.charge c oa (FreeM.Path.ofHandler (fun t => (answer t).run) oa)) :=
  PFunctor.Handler.run_liftM_withCharge_id answer c oa s

/-! ## Restricted bind -/

/-- `isQueryBoundP_bind` with the continuation bounded only on the support. -/
example {oa : OracleComp spec α} {ob : α → OracleComp spec β} {p : ι → Prop} [DecidablePred p]
    {n m : ℕ} (h₁ : IsQueryBoundP oa p n) (h₂ : ∀ x ∈ support oa, IsQueryBoundP (ob x) p m) :
    IsQueryBoundP (oa >>= ob) p (n + m) := by
  rw [ChargeProbe.isQueryBoundP_iff]
  exact ((ChargeProbe.isQueryBoundP_iff oa p n).1 h₁).bind_supp fun x hx =>
    (ChargeProbe.isQueryBoundP_iff (ob x) p m).1 (h₂ x hx)

/-! ## ℝ≥0∞ weights -/

/-- Multiply a natural number by a weight in `ℝ≥0∞`, as a monotone additive map. -/
noncomputable def scale (M : ℝ≥0∞) : ℕ →+o ℝ≥0∞ where
  toFun n := n * M
  map_zero' := by simp
  map_add' a b := by push_cast; ring
  monotone' a b h := by dsimp only; gcongr

/-- ArkLib `queryBound_round_cost`: a total query bound `Q` and weights at most `M` give
worst-case weighted cost at most `Q * M`. -/
example (w : ι → ℝ≥0∞) (M : ℝ≥0∞) (hw : ∀ t, w t ≤ M) {oa : OracleComp spec α} {Q : ℕ}
    (h : IsTotalQueryBound oa Q) : FreeM.cost w oa ≤ Q * M := by
  rw [ChargeProbe.isTotalQueryBound_iff] at h
  have hM := h.map (scale M)
  rw [map_zero] at hM
  have hw' := hM.mono_charge (c' := w) fun t => by
    change w t ≤ ((1 : ℕ) : ℝ≥0∞) * M
    simpa using hw t
  have := FreeM.cost_le_of_isChargeBound hw'
  rw [zero_add] at this
  exact this

/-! ## Completed-path transfer (VCVio #1013) -/

example {ι' : Type} {spec' : OracleSpec.{0, 0} ι'} (route : QueryImpl spec (OracleComp spec'))
    (sourceCost : ι → ℕ) (targetCost : ι' → ℕ)
    (hstep : ∀ t (r : FreeM.Path (route t)), FreeM.Path.charge targetCost (route t) r ≤ sourceCost t)
    {program : OracleComp spec α} {B : ℕ}
    (hprogram : ∀ p : FreeM.Path program, FreeM.Path.charge sourceCost program p ≤ B)
    (q : FreeM.Path (simulateQ route program)) :
    FreeM.Path.charge targetCost (simulateQ route program) q ≤ B :=
  FreeM.Path.charge_liftM_le_of_forall route hstep hprogram q

/-! ## Expected charge through a stateful handler -/

variable {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m]

/-- The expected charge of `oa` interpreted by `so` from state `s`: each call is charged when it
is made, and the continuation is averaged over the handler's step. It is the fold of a per-call
spec over the source program. -/
noncomputable def expectedCharge (so : QueryImpl spec (StateT σ m)) (c : spec.Domain → ℝ≥0∞)
    (oa : OracleComp spec α) (s : σ) : ℝ≥0∞ :=
  FreeM.wpFold (P := spec.toPFunctor)
    (fun (t : spec.Domain) (k : spec.Range t → σ → ℝ≥0∞) (s' : σ) =>
      c t + ∫⁻ r, r ∂𝒟[(fun z => k z.1 z.2) <$> (so t).run s']) oa (fun _ _ => 0) s

/-- VCVio's expected charged-query count is the expected charge of the indicator. -/
theorem expectedSimulatedQueryCount_eq (so : QueryImpl spec (StateT σ m))
    (charged : spec.Domain → Prop) [DecidablePred charged] (oa : OracleComp spec α) (s : σ) :
    expectedSimulatedQueryCount so charged oa s =
      expectedCharge so (fun t => if charged t then 1 else 0) oa s := by
  induction oa using FreeM.rec generalizing s with
  | pure a => rfl
  | liftBind t k ih =>
    exact congrArg ((if charged t then 1 else 0) + ·)
      (congrArg (fun g => ∫⁻ r, r ∂𝒟[g <$> (so t).run s]) (funext fun z => ih z.1 z.2))

/-- The tower law, exactly. -/
theorem expectedCharge_bind (so : QueryImpl spec (StateT σ m)) (c : spec.Domain → ℝ≥0∞)
    (oa : OracleComp spec α) (f : α → OracleComp spec β) (s : σ) :
    expectedCharge so c (oa >>= f) s =
      FreeM.wpFold (P := spec.toPFunctor)
        (fun (t : spec.Domain) (k : spec.Range t → σ → ℝ≥0∞) (s' : σ) =>
          c t + ∫⁻ r, r ∂𝒟[(fun z => k z.1 z.2) <$> (so t).run s']) oa
        (fun a s' => expectedCharge so c (f a) s') s := by
  unfold expectedCharge
  exact congrFun (FreeM.wpFold_bind' _ oa f _) s

/-- The structural budget bounds the expected charge under every stateful handler. -/
theorem expectedCharge_le_of_isChargeBound (so : QueryImpl spec (StateT σ m))
    (c : spec.Domain → ℝ≥0∞) {oa : OracleComp spec α} {B t : ℝ≥0∞}
    (h : FreeM.IsChargeBound oa c B t) (s : σ) : t + expectedCharge so c oa s ≤ B := by
  induction oa using FreeM.rec generalizing s t with
  | pure a =>
    change t + 0 ≤ B
    simpa using h
  | liftBind a k ih =>
    change t + (c a + ∫⁻ r, r ∂𝒟[(fun z => expectedCharge so c (k z.1) z.2) <$> (so a).run s])
      ≤ B
    rw [← add_assoc]
    by_cases htop : t + c a = ⊤
    · have hB : B = ⊤ := top_le_iff.1 (by rw [← htop]; exact h.1)
      rw [hB]
      exact le_top
    calc t + c a + ∫⁻ r, r ∂𝒟[(fun z => expectedCharge so c (k z.1) z.2) <$> (so a).run s]
        ≤ t + c a + (B - (t + c a)) := add_le_add le_rfl
          (lintegral_id_evalDist_map_le_of_le _ fun z =>
            ENNReal.le_sub_of_add_le_left htop (ih z.1 (h.2 z.1) z.2))
      _ = B := add_tsub_cancel_of_le h.1

/-- So does the unit-charge budget, recovering `expectedSimulatedQueryCount_le_of_isQueryBoundP`
for the total count. -/
example (so : QueryImpl spec (StateT σ m)) {oa : OracleComp spec α} {Q : ℕ}
    (h : IsTotalQueryBound oa Q) (s : σ) :
    expectedCharge so (fun _ => 1) oa s ≤ Q := by
  rw [ChargeProbe.isTotalQueryBound_iff] at h
  let castHom : ℕ →+o ℝ≥0∞ := { Nat.castAddMonoidHom ℝ≥0∞ with monotone' := Nat.mono_cast }
  have hQ := h.map castHom
  simp only [map_zero] at hQ
  have := expectedCharge_le_of_isChargeBound so _ hQ s
  rw [zero_add, show (castHom ∘ fun _ : spec.Domain => (1 : ℕ)) = fun _ => (1 : ℝ≥0∞) from
    funext fun _ => Nat.cast_one] at this
  exact this

end OracleComp.ChargeProbe2

namespace OracleComp.ChargeProbe2

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}

open Std.WP OracleComp
open scoped OracleComp.Necessary WriterT.MonoidWP

set_option experimental.vcgen true

/-- One counted call raises the counter by its charge. -/
theorem countingOracle_budget_step [DecidableEq ι] (t : spec.Domain) (s : QueryCount ι) :
    ⦃ fun qc => Multiplicative.toAdd qc ≤ s ⦄
      (countingOracle t : AddWriterT (QueryCount ι) (OracleComp spec) (spec.Range t))
    ⦃ fun _ qc => Multiplicative.toAdd qc ≤ s + QueryCount.single t ⦄ := by
  vcgen [countingOracle_apply, AddWriterT.addTell]
  all_goals
    simp only [toAdd_mul, toAdd_ofAdd]
    exact add_le_add (by assumption) le_rfl

/-- W3: a budget on `oa` bounds the counter of `countingOracle` (in `AddWriterT`), as a core
triple, from the per-call `countingOracle_triple` through the spent-amount ranked triple. -/
example [DecidableEq ι] (oa : OracleComp spec α) (B : QueryCount ι)
    (hoa : FreeM.IsChargeBound oa (fun t => QueryCount.single t) B) :
    ⦃ fun qc => Multiplicative.toAdd qc = 0 ⦄
      (simulateQ countingOracle oa : AddWriterT (QueryCount ι) (OracleComp spec) α)
    ⦃ fun _ qc => Multiplicative.toAdd qc ≤ B ⦄ := by
  refine ⟨(PFunctor.FreeM.triple_liftM_of_isChargeBound countingOracle
    (fun s qc => Multiplicative.toAdd qc ≤ s) (fun qc => Multiplicative.toAdd qc ≤ B) _
    (fun t s _ => countingOracle_budget_step t s) (fun s hs qc hqc => hqc.trans hs) oa 0
    hoa).entails_wp_of_pre ?_⟩
  intro qc hqc
  exact hqc.le

end OracleComp.ChargeProbe2
