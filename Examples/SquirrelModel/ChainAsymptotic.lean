/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Examples.SquirrelModel.ChainSecrecy
public import Examples.SquirrelModel.Asymptotic

/-!
# Forward secrecy of the hash chain, asymptotically

Squirrel states its results asymptotically: a probability is negligible in the security parameter
`η`. `chainAdv_le` gives the concrete bound `(q + 1) / |K|`. With `η`-bit keys
(`K = Fin (2 ^ η)`) and an attacker family making polynomially many queries, that bound is
negligible (`negligible_chainAdv`).

The statement is information-theoretic: it holds for every attacker family with a polynomial query
bound, with no restriction on running time, so no polynomial-time class is needed.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SquirrelModel.Chain

variable {M : Type} [DecidableEq M]

/-- **Negligible forward secrecy.** With `η`-bit keys, an attacker family making at most
`p(η)` queries other than coins, for a polynomial `p`, outputs the initial key with negligible
probability, whatever order it queries in and whenever it corrupts. -/
theorem negligible_chainAdv (A : (η : ℕ) → ChainAdversary (Fin (2 ^ η)) M) (p : Polynomial ℕ)
    (hA : ∀ η, IsQueryBoundP (A η) (fun t => isCoin t = false) (p.eval η)) :
    negligible fun η => chainAdv (A η) := by
  refine negligible_of_le (fun η => ?_)
    (negligible_polynomial_mul Asymptotic.negligible_inv_two_pow (p + 1))
  refine (chainAdv_le (A η) (hA η)).trans (le_of_eq ?_)
  simp [Polynomial.eval_add]

end SquirrelModel.Chain
