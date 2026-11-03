/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import PolyFun.PFunctor.Basic

/-!
# Specifications of Available Oracles

EXPLORATORY PROTOTYPE (Option B): an `OracleSpec` *is* a `PFunctor`. Positions are oracle
inputs (`spec.Domain = spec.A`), directions are answers (`spec.Range t = spec.B t`). The index
type is no longer a parameter of the type; it is the projection `spec.Domain`.

`toPFunctor` and `ofPFunctor` remain as reducible identities so that downstream code that
crosses the old boundary keeps elaborating during a migration.
-/

@[expose] public section

universe u u' v w

-- The two universes are intentionally independent (inputs vs answers), as in `PFunctor`.
set_option linter.checkUnivs false in
/-- An oracle specification is a polynomial functor: positions are oracle inputs and the
directions at a position are the possible answers. -/
abbrev OracleSpec : Type (max (u + 1) (v + 1)) := PFunctor.{u, v}

namespace OracleSpec

/-- Identity bridge, kept for migration. -/
@[reducible]
def toPFunctor (spec : OracleSpec.{u, v}) : PFunctor.{u, v} := spec

/-- Identity bridge, kept for migration. -/
@[reducible, inline]
def ofPFunctor (P : PFunctor.{u, v}) : OracleSpec.{u, v} := P

lemma toPFunctor_ofPFunctor (P : PFunctor) :
    OracleSpec.toPFunctor (OracleSpec.ofPFunctor P) = P := rfl

lemma ofPFunctor_toPFunctor (spec : OracleSpec) :
    OracleSpec.ofPFunctor (OracleSpec.toPFunctor spec) = spec := rfl

/-- The type of oracle inputs of `spec`. -/
abbrev Domain (spec : OracleSpec.{u, v}) : Type u := spec.A
/-- The type of answers that the oracles of `spec` return to a query on input `t`. -/
abbrev Range (spec : OracleSpec.{u, v}) (t : spec.Domain) : Type v := spec.B t

section ofFn

/-- The oracle specification whose oracle answers a query on input `t : ι` in the type `F t`. -/
@[reducible, always_inline] def ofFn {ι : Type u} (F : ι → Type v) : OracleSpec.{u, v} := ⟨ι, F⟩
/-- `A →ₒ B` specifies oracles that take inputs in `A` and answer every query in `B`. -/
notation:25 (name := singletonSpec) A:25 " →ₒ " B:26 =>
  OracleSpec.ofFn (ι := A) (fun _ => B)

end ofFn

section add

/-- `spec₁ + spec₂` is `PFunctor` addition, re-typed at `OracleSpec` so that dot notation on
the sum resolves in the `OracleSpec` namespace. -/
instance : HAdd OracleSpec.{u, v} OracleSpec.{u', v} OracleSpec.{max u u', v} where
  hAdd spec spec' := ⟨spec.A ⊕ spec'.A, Sum.elim spec.B spec'.B⟩

/-! Index-type instances for sums. Instance search does not reduce `(spec + spec').Domain` to
`spec.Domain ⊕ spec'.Domain`, so each class needs a forwarding instance. -/

instance (spec : OracleSpec.{u, v}) (spec' : OracleSpec.{u', v}) [DecidableEq spec.Domain]
    [DecidableEq spec'.Domain] : DecidableEq (spec + spec').Domain :=
  inferInstanceAs (DecidableEq (spec.Domain ⊕ spec'.Domain))

/-- The sum is `PFunctor` addition. -/
lemma add_eq_pfunctor_add (spec : OracleSpec.{u, v}) (spec' : OracleSpec.{u', v}) :
    spec + spec' = PFunctor.add spec spec' := rfl

@[simp] lemma add_B_inl (spec : OracleSpec.{u, v}) (spec' : OracleSpec.{u', v})
    (t : spec.Domain) : (spec + spec').Range (.inl t) = spec.Range t := rfl

@[simp] lemma add_B_inr (spec : OracleSpec.{u, v}) (spec' : OracleSpec.{u', v})
    (t : spec'.Domain) : (spec + spec').Range (.inr t) = spec'.Range t := rfl

instance (spec : OracleSpec.{u, v}) (spec' : OracleSpec.{u', v})
    [h : ∀ t, Fintype (spec.Range t)] [h' : ∀ t, Fintype (spec'.Range t)] :
    ∀ t, Fintype ((spec + spec').Range t)
  | .inl i => h i
  | .inr i => h' i

instance (spec : OracleSpec.{u, v}) (spec' : OracleSpec.{u', v})
    [h : ∀ t, DecidableEq (spec.Range t)] [h' : ∀ t, DecidableEq (spec'.Range t)] :
    ∀ t, DecidableEq ((spec + spec').Range t)
  | .inl i => h i
  | .inr i => h' i

instance (spec : OracleSpec.{u, v}) (spec' : OracleSpec.{u', v})
    [h : ∀ t, Inhabited (spec.Range t)] [h' : ∀ t, Inhabited (spec'.Range t)] :
    ∀ t, Inhabited ((spec + spec').Range t)
  | .inl i => h i
  | .inr i => h' i

end add

section sigma

/-- Indexed sum of oracle specifications (`PFunctor.sigma`). -/
@[reducible] protected def sigma {ι : Type w} (specs : ι → OracleSpec.{u, v}) :
    OracleSpec.{max w u, v} :=
  PFunctor.sigma specs

end sigma

section mul

/-- `spec₁ * spec₂` is `PFunctor` multiplication: a pair of inputs answered by one side. -/
instance : HMul OracleSpec.{u, v} OracleSpec.{u', v} OracleSpec.{max u u', v} where
  hMul spec spec' := spec.toPFunctor * spec'.toPFunctor

end mul

section pi

/-- Indexed product of oracle specifications (`PFunctor.pi`). -/
@[reducible] protected def pi {ι : Type w} (specs : ι → OracleSpec.{u, v}) :
    OracleSpec.{max w u, max w v} :=
  PFunctor.pi specs

end pi

section emptySpec

/-- Specifies access to no oracles, using the empty type as the indexing type. -/
@[reducible] def emptySpec : OracleSpec := PEmpty →ₒ PEmpty
/-- `[]ₒ` is the specification `emptySpec`, which provides no oracles. -/
notation "[]ₒ" => emptySpec

end emptySpec

end OracleSpec

/-- Access to a coin flipping oracle. -/
@[reducible] def coinSpec : OracleSpec.{0, 0} := Unit →ₒ Bool

section unifSpec

/-- Access to oracles for uniformly selecting from `Fin (n + 1)` for arbitrary `n : ℕ`. -/
@[inline, reducible] def unifSpec : OracleSpec.{0, 0} :=
  OracleSpec.ofFn fun n : ℕ => Fin (n + 1)

end unifSpec

section probSpec
/-- Select uniformly from `Fin (m + 1)` for a pair `(n, m) : ℕ × ℕ`. -/
@[inline, reducible] def probSpec : OracleSpec.{0, 0} :=
  OracleSpec.ofFn fun ((_n, m) : ℕ × ℕ) => Fin (m + 1)

end probSpec
