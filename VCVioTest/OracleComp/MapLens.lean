/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.MapLens

/-!
# Lifts as transport along lenses

`liftComp` is transport along the lens `liftLens` read off a query lift, and simulating a
transported computation is simulating the original one with the pulled-back handler. The concrete
runs use two summands answered differently and a backward map that is not the identity, so they
fail if a lift picks the wrong summand or if a pulled-back handler ignores the backward map.
-/

@[expose] public section

universe u v w

open OracleComp OracleSpec PFunctor

open scoped PFunctor

namespace VCVioTest.MapLens

section Generic

variable {ι : Type u} {τ : Type v} {spec : OracleSpec.{u, w} ι} {superSpec : OracleSpec.{v, w} τ}
  [MonadLiftT (OracleQuery spec) (OracleQuery superSpec)] {α : Type w}

example (mx : OracleComp spec α) :
    liftComp mx superSpec = mx.mapLens (liftLens spec superSpec) :=
  liftComp_def superSpec mx

example (mx : OracleComp spec α) :
    liftComp mx superSpec = simulateQ (fun t => liftM (spec.query t)) mx :=
  liftComp_eq_simulateQ superSpec mx

example {m : Type w → Type w} [Monad m] [LawfulMonad m] (impl : QueryImpl superSpec m)
    (mx : OracleComp spec α) :
    simulateQ impl (liftComp mx superSpec) =
      simulateQ (impl.comapLens (liftLens spec superSpec)) mx := by
  rw [liftComp_def, simulateQ_mapLens]

end Generic

/-! ### Concrete specifications -/

/-- One query, answered by a number. -/
abbrev natSpec : OracleSpec Unit := fun _ ↦ ℕ

/-- One query, answered by a bit. -/
abbrev bitSpec : OracleSpec Unit := fun _ ↦ Bool

/-- Ask the number oracle once and return its answer. -/
def ask : OracleComp natSpec ℕ := liftM (natSpec.query ())

/-- Answer the number oracle with `1` and the bit oracle with `true`. -/
def answers : QueryImpl (natSpec + bitSpec) Id
  | .inl _ => (1 : ℕ)
  | .inr _ => true

/-- The lift into the left summand sends the query to the left. -/
example : (liftLens natSpec (natSpec + bitSpec)).toFunA () = .inl () := rfl

/-- The lift into the right summand sends the query to the right. -/
example : (liftLens bitSpec (natSpec + bitSpec)).toFunA () = .inr () := rfl

/-- The lifted computation is answered by the left handler. -/
example : simulateQ answers (liftComp ask (natSpec + bitSpec)) = (1 : ℕ) := rfl

/-- The automatic lift agrees with `liftComp`. -/
example : simulateQ answers (ask : OracleComp (natSpec + bitSpec) ℕ) = (1 : ℕ) := rfl

/-- The inclusion's lens is the left injection. -/
example (mx : OracleComp natSpec ℕ) :
    liftComp mx (natSpec + bitSpec) = mx.mapLens (Sum.inl ⇆ fun _ => id) :=
  liftComp_add_left_eq_mapLens mx

/-- Two lifts in a row are the direct lift: the lens equation holds by `rfl`. -/
example (mx : OracleComp natSpec ℕ) :
    liftComp (liftComp mx (natSpec + bitSpec)) ((natSpec + bitSpec) + bitSpec) =
      liftComp mx ((natSpec + bitSpec) + bitSpec) :=
  liftComp_liftComp (spec₁ := natSpec) (spec₂ := natSpec + bitSpec)
    (spec₃ := (natSpec + bitSpec) + bitSpec) rfl mx

/-- On a repeated summand the lift takes the right copy. This pins the current behaviour, so a
change to it is noticed. -/
example : (liftLens natSpec (natSpec + natSpec)).toFunA () = .inr () := rfl

/-! ### A backward map that is not the identity -/

/-- Keep the query and add `100` to its answer. -/
def shift : Lens natSpec.toPFunctor natSpec.toPFunctor :=
  (fun _ ↦ ()) ⇆ fun _ n ↦ n + 100

/-- Answer every query with `3`. -/
def three : QueryImpl natSpec Id := fun _ ↦ (3 : ℕ)

/-- The transported computation reads `3` and translates it back to `103`. -/
example : simulateQ three (ask.mapLens shift) = (103 : ℕ) := rfl

/-- The pulled-back handler answers `103` directly. -/
example : simulateQ (three.comapLens shift) ask = (103 : ℕ) := rfl

/-- The two runs agree by `simulateQ_mapLens`. -/
example : simulateQ three (ask.mapLens shift) = simulateQ (three.comapLens shift) ask :=
  simulateQ_mapLens shift three ask

end VCVioTest.MapLens
