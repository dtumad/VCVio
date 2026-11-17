/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.EvalDist.EvalDistEq
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.EvalDist.Measure

/-!
# Updating a coordinate of a uniform product

`prEvent_uniformSample_update`: overwriting one coordinate of a uniform sample of a dependent
product with an independent uniform value leaves it uniform. The map
`(c, ρ) ↦ (Function.update ρ i₀ c, ρ i₀)` is a bijection, so the pair is uniform on the product
times the coordinate, and the old coordinate is then marginalized away.

`prEvent_uniformSample_update_update` overwrites two coordinates, the first before and the second
after drawing the product, which also has an extra component. This is the coupling behind the
encryption rule (`Valid.equiv_enc`): a reduction that receives a key and coins from its game and
draws every other coordinate itself, and the attacker tape, sees a uniform tape.
`prEvent_uniformSample_prod_update` overwrites one coordinate of a product with an extra
component, with the coin drawn first; it is the coupling behind FreshR
(`SquirrelLogic.Rules.Fresh`). Nothing here mentions Squirrel. It is local to this library until a
second consumer needs it.
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

/-- `prEvent_uniformSample_update` in distribution. -/
theorem update_uniformSample_evalDistEq {ι : Type} [DecidableEq ι] {α : ι → Type}
    [SampleableType (∀ i, α i)] (i₀ : ι) [SampleableType (α i₀)] :
    (do
        let c ← $ᵗ (α i₀)
        let ρ ← $ᵗ (∀ i, α i)
        pure (Function.update ρ i₀ c) : ProbComp (∀ i, α i)) =ᵈ
      ($ᵗ (∀ i, α i) : ProbComp (∀ i, α i)) := EvalDistEq.of_forall_prEvent_eq fun p => by
  simpa only [prEvent_norm] using prEvent_uniformSample_update (α := α) i₀ p

/-- Overwriting two coordinates of a uniform product, after drawing the rest, leaves it uniform. -/
private theorem update_update_uniformSample_evalDistEq {ι : Type} [DecidableEq ι]
    {α : ι → Type} [SampleableType (∀ i, α i)] (i₀ i₁ : ι) [SampleableType (α i₀)]
    [SampleableType (α i₁)] :
    (do
        let ρ ← $ᵗ (∀ i, α i)
        let c₀ ← $ᵗ (α i₀)
        let c₁ ← $ᵗ (α i₁)
        pure (Function.update (Function.update ρ i₀ c₀) i₁ c₁) : ProbComp (∀ i, α i)) =ᵈ
      ($ᵗ (∀ i, α i) : ProbComp (∀ i, α i)) := by
  calc (do
          let ρ ← $ᵗ (∀ i, α i)
          let c₀ ← $ᵗ (α i₀)
          let c₁ ← $ᵗ (α i₁)
          pure (Function.update (Function.update ρ i₀ c₀) i₁ c₁) : ProbComp (∀ i, α i))
      =ᵈ (do
          let c₀ ← $ᵗ (α i₀)
          let ρ ← $ᵗ (∀ i, α i)
          let c₁ ← $ᵗ (α i₁)
          pure (Function.update (Function.update ρ i₀ c₀) i₁ c₁) : ProbComp (∀ i, α i)) :=
        OracleComp.EvalDistEq.bind_bind_swap _ _ _
    _ = (do
          let ρ ← (do
            let c₀ ← $ᵗ (α i₀)
            let ρ ← $ᵗ (∀ i, α i)
            pure (Function.update ρ i₀ c₀))
          let c₁ ← $ᵗ (α i₁)
          pure (Function.update ρ i₁ c₁) : ProbComp (∀ i, α i)) := by
        simp only [bind_assoc, pure_bind]
    _ =ᵈ (do
          let ρ ← $ᵗ (∀ i, α i)
          let c₁ ← $ᵗ (α i₁)
          pure (Function.update ρ i₁ c₁) : ProbComp (∀ i, α i)) :=
        (update_uniformSample_evalDistEq i₀).bind_left _
    _ =ᵈ (do
          let c₁ ← $ᵗ (α i₁)
          let ρ ← $ᵗ (∀ i, α i)
          pure (Function.update ρ i₁ c₁) : ProbComp (∀ i, α i)) :=
        OracleComp.EvalDistEq.bind_bind_swap _ _ _
    _ =ᵈ ($ᵗ (∀ i, α i) : ProbComp (∀ i, α i)) := update_uniformSample_evalDistEq i₁

/-- **Coupling at two coordinates.** Draw a coin for the coordinate `i₀`, then a uniform pair of
an extra component and a dependent product, then a coin for `i₁`; overwrite the two coordinates
with the coins. The pair is uniform. This is the order in which the one-time IND-CPA game draws a
key, the reduction's own tapes, and the encryption coins. -/
theorem prEvent_uniformSample_update_update {β ι : Type} [DecidableEq ι] {α : ι → Type}
    [SampleableType β] [SampleableType (∀ i, α i)] (i₀ i₁ : ι) [SampleableType (α i₀)]
    [SampleableType (α i₁)] (p : β × (∀ i, α i) → Prop) :
    Pr{let c₀ ← $ᵗ (α i₀); let ρ ← $ᵗ (β × ∀ i, α i); let c₁ ← $ᵗ (α i₁)}[
        p (ρ.1, Function.update (Function.update ρ.2 i₀ c₀) i₁ c₁)] =
      Pr{let ρ ← $ᵗ (β × ∀ i, α i)}[p ρ] := by
  have h : (do
        let c₀ ← $ᵗ (α i₀)
        let ρ ← $ᵗ (β × ∀ i, α i)
        let c₁ ← $ᵗ (α i₁)
        pure (ρ.1, Function.update (Function.update ρ.2 i₀ c₀) i₁ c₁) :
        ProbComp (β × ∀ i, α i)) =ᵈ ($ᵗ (β × ∀ i, α i) : ProbComp (β × ∀ i, α i)) := by
    calc (do
            let c₀ ← $ᵗ (α i₀)
            let ρ ← $ᵗ (β × ∀ i, α i)
            let c₁ ← $ᵗ (α i₁)
            pure (ρ.1, Function.update (Function.update ρ.2 i₀ c₀) i₁ c₁) :
            ProbComp (β × ∀ i, α i))
        =ᵈ (do
            let ρ ← $ᵗ (β × ∀ i, α i)
            let c₀ ← $ᵗ (α i₀)
            let c₁ ← $ᵗ (α i₁)
            pure (ρ.1, Function.update (Function.update ρ.2 i₀ c₀) i₁ c₁) :
            ProbComp (β × ∀ i, α i)) :=
          OracleComp.EvalDistEq.bind_bind_swap _ _ _
      _ = (do
            let b ← $ᵗ β
            Prod.mk b <$> (do
              let ρ ← $ᵗ (∀ i, α i)
              let c₀ ← $ᵗ (α i₀)
              let c₁ ← $ᵗ (α i₁)
              pure (Function.update (Function.update ρ i₀ c₀) i₁ c₁)) :
            ProbComp (β × ∀ i, α i)) := by
          simp [SampleableType.uniformSample_prod_eq_bind, bind_assoc, map_eq_bind_pure_comp]
      _ =ᵈ (do
            let b ← $ᵗ β
            Prod.mk b <$> ($ᵗ (∀ i, α i) : ProbComp (∀ i, α i)) : ProbComp (β × ∀ i, α i)) :=
          EvalDistEq.bind_right _ fun _ => (update_update_uniformSample_evalDistEq i₀ i₁).map _
      _ = ($ᵗ (β × ∀ i, α i) : ProbComp (β × ∀ i, α i)) := by
          simp [SampleableType.uniformSample_prod_eq_bind, map_eq_bind_pure_comp]
  simpa only [prEvent_norm] using h.prEvent_eq p

/-- **Coupling with an extra component.** Draw a coin for the coordinate `i₀`, then a uniform pair
of an extra component and a dependent product, and overwrite the coordinate with the coin. The pair
is uniform. -/
theorem prEvent_uniformSample_prod_update {β ι : Type} [DecidableEq ι] {α : ι → Type}
    [SampleableType β] [SampleableType (∀ i, α i)] (i₀ : ι) [SampleableType (α i₀)]
    (p : β × (∀ i, α i) → Prop) :
    Pr{let c ← $ᵗ (α i₀); let ρ ← $ᵗ (β × ∀ i, α i)}[p (ρ.1, Function.update ρ.2 i₀ c)] =
      Pr{let ρ ← $ᵗ (β × ∀ i, α i)}[p ρ] := by
  have h : (do
        let c ← $ᵗ (α i₀)
        let ρ ← $ᵗ (β × ∀ i, α i)
        pure (ρ.1, Function.update ρ.2 i₀ c) : ProbComp (β × ∀ i, α i)) =ᵈ
      ($ᵗ (β × ∀ i, α i) : ProbComp (β × ∀ i, α i)) := by
    calc (do
            let c ← $ᵗ (α i₀)
            let ρ ← $ᵗ (β × ∀ i, α i)
            pure (ρ.1, Function.update ρ.2 i₀ c) : ProbComp (β × ∀ i, α i))
        = (do
            let c ← $ᵗ (α i₀)
            let b ← $ᵗ β
            let ρ ← $ᵗ (∀ i, α i)
            pure (b, Function.update ρ i₀ c) : ProbComp (β × ∀ i, α i)) := by
          simp [SampleableType.uniformSample_prod_eq_bind]
      _ =ᵈ (do
            let b ← $ᵗ β
            let c ← $ᵗ (α i₀)
            let ρ ← $ᵗ (∀ i, α i)
            pure (b, Function.update ρ i₀ c) : ProbComp (β × ∀ i, α i)) :=
          OracleComp.EvalDistEq.bind_bind_swap _ _ _
      _ = (do
            let b ← $ᵗ β
            Prod.mk b <$> (do
              let c ← $ᵗ (α i₀)
              let ρ ← $ᵗ (∀ i, α i)
              pure (Function.update ρ i₀ c)) : ProbComp (β × ∀ i, α i)) := by
          simp [map_eq_bind_pure_comp, bind_assoc]
      _ =ᵈ (do
            let b ← $ᵗ β
            Prod.mk b <$> ($ᵗ (∀ i, α i) : ProbComp (∀ i, α i)) : ProbComp (β × ∀ i, α i)) :=
          EvalDistEq.bind_right _ fun _ => (update_uniformSample_evalDistEq i₀).map _
      _ = ($ᵗ (β × ∀ i, α i) : ProbComp (β × ∀ i, α i)) := by
          simp [SampleableType.uniformSample_prod_eq_bind, map_eq_bind_pure_comp]
  simpa only [prEvent_norm] using h.prEvent_eq p

end SquirrelLogic
