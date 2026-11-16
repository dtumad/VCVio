/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.OracleComp.Constructions.SampleableType.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.EvalDist.Measure

/-!
# Updating a coordinate of a uniform product

`prEvent_uniformSample_update`: overwriting one coordinate of a uniform sample of a dependent
product with an independent uniform value leaves it uniform. The map
`(c, ρ) ↦ (Function.update ρ i₀ c, ρ i₀)` is a bijection, so the pair is uniform on the product
times the coordinate, and the old coordinate is then marginalized away.

This is the coupling behind encryption rules: a reduction that receives a key or coins from its
game and draws every other coordinate itself sees a uniform tape. Nothing here mentions Squirrel.
It is local to this library until a second consumer needs it.
-/

public section

namespace SquirrelLogic

/-- **Coupling.** Overwriting one coordinate of a uniform dependent product with an independent
uniform value leaves the product uniform. -/
theorem prEvent_uniformSample_update {ι : Type} [DecidableEq ι] {α : ι → Type}
    [SampleableType (∀ i, α i)] (i₀ : ι) [SampleableType (α i₀)] (p : (∀ i, α i) → Prop) :
    Pr{let c ← $ᵗ (α i₀); let ρ ← $ᵗ (∀ i, α i)}[p (Function.update ρ i₀ c)] =
      Pr{let ρ ← $ᵗ (∀ i, α i)}[p ρ] := by
  have hg : Function.Bijective (Function.uncurry
      fun (c : α i₀) (ρ : ∀ i, α i) => (Function.update ρ i₀ c, ρ i₀)) := by
    refine ⟨fun ⟨c, ρ⟩ ⟨c', ρ'⟩ h => ?_, fun ⟨ρ, c⟩ => ⟨(ρ i₀, Function.update ρ i₀ c), ?_⟩⟩
    · simp only [Function.uncurry_apply_pair, Prod.mk.injEq] at h
      obtain ⟨h₁, h₂⟩ := h
      have hc : c = c' := by simpa using congrFun h₁ i₀
      subst hc
      refine Prod.ext rfl (funext fun i => ?_)
      by_cases hi : i = i₀
      · rw [hi]
        exact h₂
      · simpa [Function.update_of_ne hi] using congrFun h₁ i
    · simp
  refine Eq.trans ?_ ((SampleableType.prEvent_uniformSample_pair_of_bijective hg
    fun z => p z.1).trans ?_)
  · rfl
  · refine (SampleableType.prEvent_uniformSample_pair_of_bijective
      (g := fun (y : α i₀) (x : ∀ i, α i) => (x, y)) (Equiv.prodComm _ _).bijective
      fun z => p z.1).symm.trans ?_
    have h := OracleComp.prEvent_bind_const ($ᵗ (α i₀) : ProbComp (α i₀))
      (do let y ← $ᵗ (∀ i, α i); pure (p y))
    simpa only [prEvent_norm] using h

end SquirrelLogic
