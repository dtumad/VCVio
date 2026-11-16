/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.IPFunctor.Scoped.Interpretation

/-!
# Sums of binding signatures over shared sorts

Two signatures over the same sorts combine into one whose constructors are those of either
summand, with their own arguments, binders and argument sorts. A pair of interpretations in one
carrier interprets the sum, and a term of the left summand is a term of the sum with the same
meaning (`Term.denote_inl`), by fusing two folds.

This is local to the Squirrel development until a second consumer needs it.
-/

public section

universe u v w z

namespace IPFunctor.ScopedSignature

variable {S : Type u}

/-- The constructors of both signatures, over the same sorts. -/
@[expose, reducible] def sum (σ τ : ScopedSignature.{u, v, w} S) :
    ScopedSignature.{u, v, w} S where
  Op a := σ.Op a ⊕ τ.Op a
  Arg o := match o with
    | .inl o => σ.Arg o
    | .inr o => τ.Arg o
  binders o := match o with
    | .inl o => σ.binders o
    | .inr o => τ.binders o
  sort o := match o with
    | .inl o => σ.sort o
    | .inr o => τ.sort o

variable {σ τ : ScopedSignature.{u, v, w} S} {V : S → Type z}

/-- Interpret each summand's constructors with its own algebra. -/
@[expose] def Interpretation.sum (alg₁ : Interpretation σ V) (alg₂ : Interpretation τ V) :
    Interpretation (σ.sum τ) V
  | _, .inl o, next => alg₁ o next
  | _, .inr o, next => alg₂ o next

namespace Term

/-- A term of the left summand, read in the sum. -/
@[expose] def inl {Γ : List S} {a : S} (t : σ.Term Γ a) : (σ.sum τ).Term Γ a :=
  t.fold (D := fun j : Judgment S => (σ.sum τ).Term j.1 j.2) (fun _ x => .pure x)
    (fun _ o next => .liftBind (Sum.inl o) next)

/-- A left-summand term means in the sum what it means in its own signature. -/
theorem denote_inl (alg₁ : Interpretation σ V) (alg₂ : Interpretation τ V)
    {Γ : List S} {a : S} (t : σ.Term Γ a) (ρ : Env V Γ) :
    (inl (τ := τ) t).denote (alg₁.sum alg₂) ρ = t.denote alg₁ ρ := by
  have h := IFreeM.fold_fusion (P := σ.polynomial)
    (D := fun j => (σ.sum τ).Term j.1 j.2) (E := fun j : Judgment S => Env V j.1 → V j.2)
    (fun _ t ρ => t.denote (alg₁.sum alg₂) ρ) (fun _ x => .pure x) (fun _ x ρ => ρ _ x)
    (fun _ o next => .liftBind (Sum.inl o) next)
    (fun _ o next ρ => alg₁ o (fun p ξ => next p (Env.append ξ ρ)))
    (fun _ _ => rfl) (fun _ _ _ => rfl) t
  exact congrFun h ρ

end Term

end IPFunctor.ScopedSignature
