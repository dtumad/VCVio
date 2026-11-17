/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import SquirrelLogic.Indist
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Read bounds and long attacker tapes

LICS23 takes the attacker tape `ρa` to be a finite bitstring "long enough" for the machines
considered (§II-A.3), and CCS26's proof of FreshL (App. C.2, footnote 2, p. 17) samples a fresh
name "from the adversarial randomness", from bits that the terms do not read. This module states
the two facts that argument needs, without imposing either on any rule:

* `RV.ReadsBelow X b`: the random variable `X` depends on `ρa` only through its bits below `b η`.
  An `adv` term has this property for a polynomial `b`, the read bound of its machine
  (`RV.readsBelow_of_eval`, `AdvClass.Adv.readsBelow`), from the closure field
  `AdvClass.readBound_mem`.
* `Model.LongTapes M`: the attacker tape is eventually longer than every polynomial, the formal
  counterpart of LICS23's "long enough" tapes and of the room that CCS26's footnote makes on the
  tape. It is a condition on models, to be taken as a hypothesis on the model restriction `R`.

The checks at the end show that a read bound constrains a machine: the machine reading bit `0`
reads below `1` and not below `0`.
-/

public section

namespace SquirrelLogic

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B} {M : Model D} {τs : List (Ty B)} {β : Ty B}

/-- The random variable `X` depends on the attacker tape only through its bits below `b η`. -/
@[expose] def RV.ReadsBelow {τ : Ty B} (X : RV M τ) (b : ℕ → ℕ) : Prop :=
  ∀ η (ρa ρa' : M.TapeA η) (ρh : M.TapeH η), (∀ i < b η, M.readBit ρa i = M.readBit ρa' i) →
    X η (ρa, ρh) = X η (ρa', ρh)

/-- A random variable computed by an attacker machine that reads below `b` depends on the
attacker tape only through its bits below `b η`. -/
theorem RV.readsBelow_of_eval {X : RV M (Ty.arrows τs β)} {A : AdvMachine M τs β}
    (hX : ∀ η ρ, X η ρ = A.eval η ρ.1) {b : ℕ → ℕ} (hA : Machine.ReadsBelow A b) :
    X.ReadsBelow b := fun η ρa ρa' ρh hρ =>
  (hX η (ρa, ρh)).trans ((AdvMachine.eval_eq_of_readsBelow hA hρ).trans (hX η (ρa', ρh)).symm)

/-- An `adv` term depends on the attacker tape only through its bits below a polynomial: the
read bound of the admitted machine that computes it. -/
theorem AdvClass.Adv.readsBelow {C : AdvClass M} {X : RV M (Ty.arrows τs β)} (h : C.Adv X) :
    ∃ p : Polynomial ℕ, X.ReadsBelow fun η => p.eval η :=
  let ⟨_, hA, hX⟩ := h
  let ⟨p, hp⟩ := C.readBound_mem hA
  ⟨p, RV.readsBelow_of_eval hX hp⟩

/-- Long attacker tapes: the length of `ρa` eventually exceeds every polynomial. -/
@[expose] def Model.LongTapes (M : Model D) : Prop :=
  ∀ p : Polynomial ℕ, ∀ᶠ η in Filter.atTop, p.eval η < M.lenA η

/-! ## Checks -/

/-- The machine that returns bit `0` of the attacker tape. -/
@[expose] def Machine.readZero : Machine M τs .bool := fun _ => Machine.read 0

theorem Machine.readsBelow_readZero_one :
    (Machine.readZero : Machine M τs .bool).ReadsBelow fun _ => 1 :=
  fun _ => (OracleComp.allQueriesSatisfy_query_iff _ _).2 Nat.one_pos

/-- A read bound constrains a machine: the machine reading bit `0` does not read below `0`. -/
theorem Machine.not_readsBelow_readZero_zero :
    ¬ (Machine.readZero : Machine M τs .bool).ReadsBelow fun _ => 0 :=
  fun h => Nat.lt_irrefl 0
    ((OracleComp.allQueriesSatisfy_query_iff (spec := M.Iface 0 τs) (.inl 0) _).1 (h 0))

end SquirrelLogic
