/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.MeasuredProgram.FreeM

/-!
# Measured-program composition through PolyFun

The composition results of `OracleComp.MeasuredProgram` follow from PolyFun's
`PFunctor.FreeM.MeasuredProgram` results through the translation `MeasuredProgram.toFreeM`, the
run agreement `run_comp_eq_toFreeM` and the cost transport `costAtMost_comp_of_toFreeM`.
-/

public section

open OracleComp PFunctor

namespace VCVioTest.OracleComp.MeasuredProgramFreeM

variable {A B C ω : Type}

/-- `MeasuredProgram.run_comp`, from PolyFun's `run_comp`. -/
example (outer : MeasuredProgram B C ω) (inner : MeasuredProgram A B ω) (input : A) :
    (outer.comp inner).run input = outer.run (inner.run input) :=
  (MeasuredProgram.run_comp_eq_toFreeM outer inner input).trans
    (FreeM.MeasuredProgram.run_comp _ _ input)

/-- `MeasuredProgram.Realizes.comp`, from PolyFun's `Realizes.comp`. -/
example {outer : MeasuredProgram B C ω} {inner : MeasuredProgram A B ω} {f : A → B} {g : B → C}
    (hg : outer.Realizes g) (hf : inner.Realizes f) : (outer.comp inner).Realizes (g ∘ f) :=
  fun input => (FreeM.MeasuredProgram.Realizes.comp (outer := outer.toFreeM)
    (inner := inner.toFreeM) hg hf input).trans
      (MeasuredProgram.run_comp_eq_toFreeM outer inner input).symm

/-- `MeasuredProgram.CostAtMost.comp`, from PolyFun's `CostAtMost.comp`. -/
example [AddCommMonoid ω] [Preorder ω] [IsOrderedAddMonoid ω] {outer : MeasuredProgram B C ω}
    {inner : MeasuredProgram A B ω} {outerBudget innerBudget : ω}
    (ho : outer.CostAtMost outerBudget) (hi : inner.CostAtMost innerBudget) :
    (outer.comp inner).CostAtMost (innerBudget + outerBudget) :=
  MeasuredProgram.costAtMost_comp_of_toFreeM <| FreeM.MeasuredProgram.CostAtMost.comp
    ((MeasuredProgram.costAtMost_toFreeM_iff _ _).2 ho)
    ((MeasuredProgram.costAtMost_toFreeM_iff _ _).2 hi)

/-- `MeasuredProgram.costAtMost_ofFun`, from the path-charge reading. -/
example [AddCommMonoid ω] [Preorder ω] (f : A → B) :
    (MeasuredProgram.ofFun f (ω := ω)).CostAtMost 0 :=
  (MeasuredProgram.costAtMost_toFreeM_iff _ _).1 fun _ _ => le_rfl

end VCVioTest.OracleComp.MeasuredProgramFreeM
