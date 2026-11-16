/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Examples.SquirrelModel.ChainAsymptotic
public import VCVio.CryptoFoundations.PRF

/-!
# Forward secrecy of the keyed hash chain, from a PRF

This is the paper's own model of the hash chain (Hérouard, Jacomme, Koutsos, Lallemand, CCS 2026,
Section 2). The hash is keyed (`hash h. name k`): the chain updates `ck := h(<ck, x>, k)` under a
secret key `k`, the attacker's ROM action gives it oracle access to `h(·, k)`, and Squirrel assumes
that `h` is a PRF. Here the hash oracle of `ChainSecrecy` is answered by `prf.eval k` for a secret
key `k ← prf.keygen` (`prfChainExp`); the attacker and its four oracles are those of
`ChainSecrecy`.

`prfChainAdv_le` bounds the attacker's probability of outputting the initial key by the PRF
advantage of the named reduction `chainReduction A` plus the random-oracle bound `(q + 1) / |K|`
of `chainAdv_le`. Against the keyed function the reduction is the keyed chain experiment
(`prfRealExperiment_chainReduction`); against a random function it is the random-oracle chain
experiment (`prfIdealExperiment_chainReduction`).

The bound is computational and adaptive, at `t = init`, and holds for every attacker, with the
reduction named. Efficiency enters only in its asymptotic reading (`negligible_prfChainAdv`): PRF
security bounds the advantage of efficient distinguishers, so it needs `chainReduction A` to stay in
the efficient class whenever `A` does. The reduction runs `A`, draws one uniform key and makes one
equality test on `K`.
-/

public section

open OracleComp OracleSpec ENNReal PRFScheme

namespace SquirrelModel.Chain

variable {K M Kp : Type} [SampleableType K]

/-! ## The keyed chain experiment -/

/-- The forward-secrecy experiment with a keyed hash: draw the hash key `k` and the initial chain
key `s`, run the attacker against the chain with hash queries answered by `prf.eval k`, and return
`s` with the attacker's guess. -/
@[expose] def prfChainExp (prf : PRFScheme Kp (K × M) K) (A : ChainAdversary K M) :
    ProbComp (K × K) := do
  let k ← prf.keygen
  let s ← $ᵗ K
  let z ← simulateQ (prf.prfRealQueryImpl k) ((simulateQ chainImpl A).run' s)
  return (s, z)

/-- The attacker's probability of outputting the initial key against the keyed chain. -/
noncomputable def prfChainAdv (prf : PRFScheme Kp (K × M) K) (A : ChainAdversary K M) : ℝ≥0∞ :=
  Pr{let z ← prfChainExp prf A}[z.2 = z.1]

/-- Guessing a fixed key wins the keyed chain experiment with probability `1 / |K|`. -/
theorem prfChainAdv_pure [Fintype K] (prf : PRFScheme Kp (K × M) K) (k : K) :
    prfChainAdv prf (pure k : OracleComp (advSpec K M) K) = (Fintype.card K : ℝ≥0∞)⁻¹ := by
  simp only [prfChainAdv, prfChainExp, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure,
    prEvent_norm]
  rw [OracleComp.prEvent_bind_const]
  exact SampleableType.prEvent_uniformSample_eq_singleton' k

/-! ## The reduction -/

variable [DecidableEq K]

/-- The PRF distinguisher built from a chain attacker: draw an initial key `s`, run the attacker
against the chain started at `s`, its hash queries forwarded to the PRF oracle, and output whether
the attacker's guess is `s`. It makes the same queries as `A` plus one uniform draw and one
equality test on `K`, so it is as efficient as `A` whenever sampling and equality on `K` are, as
for bitstrings. -/
@[expose] def chainReduction (A : ChainAdversary K M) : PRFAdversary (K × M) K :=
  (do
    let s ← liftComp ($ᵗ K) (PRFOracleSpec (K × M) K)
    let z ← (simulateQ chainImpl A).run' s
    return decide (z = s) : OracleComp (PRFOracleSpec (K × M) K) Bool)

/-- **Real world.** Against the keyed function, the reduction outputs `true` exactly when the
attacker wins the keyed chain experiment. -/
theorem prfRealExperiment_chainReduction (prf : PRFScheme Kp (K × M) K)
    (A : ChainAdversary K M) :
    Pr{let b ← prf.prfRealExperiment (chainReduction A)}[b = true] = prfChainAdv prf A := by
  simp only [prfRealExperiment, chainReduction, prfChainAdv, prfChainExp, simulateQ_bind,
    simulateQ_prfRealQueryImpl_liftComp, simulateQ_map, prEvent_norm, decide_eq_true_eq]

variable [DecidableEq M]

/-- **Ideal world.** Against a lazily sampled random function, the reduction outputs `true` exactly
when the attacker wins the random-oracle chain experiment `chainExp`. The draw of `s` moves out of
the random oracle's state, which it does not touch. -/
theorem prfIdealExperiment_chainReduction (A : ChainAdversary K M) :
    Pr{let b ← prfIdealExperiment (chainReduction A)}[b = true] = chainAdv A := by
  have h (s : K) := run_realImpl_chainGame s A
  rw [chainAdv_eq]
  simp only [prfIdealExperiment, chainReduction, simulateQ_bind,
    simulateQ_prfIdealQueryImpl_liftComp, StateT.run'_liftM_bind, bind_pure_comp]
  simp only [prfIdealQueryImpl, StateT.run'_eq, simulateQ_map, StateT.run_map, ← h, prEvent_norm,
    decide_eq_true_eq, Prod.map_fst, id_eq]

/-! ## The bound -/

/-- **Forward secrecy of the initial key, from a PRF.** An attacker making at most `q` queries
other than coins outputs the initial key of the keyed chain with probability at most the PRF
advantage of `chainReduction A` plus `(q + 1) / |K|`, whatever order it queries in and however
often and whenever it corrupts. -/
theorem prfChainAdv_le [Fintype K] (prf : PRFScheme Kp (K × M) K) (A : ChainAdversary K M)
    {q : ℕ} (hA : IsQueryBoundP A (fun t => isCoin t = false) q) :
    prfChainAdv prf A ≤
      prfAdvantage prf (chainReduction A) + (q + 1) * (Fintype.card K : ℝ≥0∞)⁻¹ := by
  rw [← prfRealExperiment_chainReduction, prEvent_eq_evalDist_singleton, prfAdvantage, add_comm]
  refine (MeasureTheory.Measure.apply_true_le_add_boolDist _
    𝒟[prfIdealExperiment (chainReduction A)]).trans ?_
  rw [← prEvent_eq_evalDist_singleton, prfIdealExperiment_chainReduction]
  gcongr
  exact chainAdv_le A hA

/-- The reduction built from a fixed guess never queries the PRF oracle, so its PRF advantage is
zero, and at `q = 0` the bound of `prfChainAdv_le` is attained (`prfChainAdv_pure`). -/
theorem prfAdvantage_chainReduction_pure [Finite K] (prf : PRFScheme Kp (K × M) K) (k : K) :
    prfAdvantage prf (chainReduction (pure k : OracleComp (advSpec K M) K)) = 0 := by
  have := Fintype.ofFinite K
  rw [prfAdvantage, MeasureTheory.Measure.boolDist, ← prEvent_eq_evalDist_singleton,
    ← prEvent_eq_evalDist_singleton, prfRealExperiment_chainReduction,
    prfIdealExperiment_chainReduction, prfChainAdv_pure, chainAdv_pure, ENNReal.absDiff_self]

/-! ## Asymptotically -/

/-- **Negligible forward secrecy, from a PRF.** With `η`-bit chain keys, an attacker family making
at most `p(η)` queries other than coins, for a polynomial `p`, outputs the initial key of the keyed
chain with negligible probability, provided the PRF advantage of the reduction family
`chainReduction (A η)` is negligible. The hypothesis concerns that one named family, not every
distinguisher: it follows from PRF security whenever `chainReduction (A η)` is in the efficient
class, which holds when `A η` is, since sampling and equality on `Fin (2 ^ η)` are efficient. -/
theorem negligible_prfChainAdv {Key : ℕ → Type}
    (prf : (η : ℕ) → PRFScheme (Key η) (Fin (2 ^ η) × M) (Fin (2 ^ η)))
    (A : (η : ℕ) → ChainAdversary (Fin (2 ^ η)) M) (p : Polynomial ℕ)
    (hA : ∀ η, IsQueryBoundP (A η) (fun t => isCoin t = false) (p.eval η))
    (hprf : negligible fun η => prfAdvantage (prf η) (chainReduction (A η))) :
    negligible fun η => prfChainAdv (prf η) (A η) := by
  refine negligible_of_le (fun η => ?_) (negligible_add hprf
    (negligible_polynomial_mul Asymptotic.negligible_inv_two_pow (p + 1)))
  refine (prfChainAdv_le (prf η) (A η) (hA η)).trans (le_of_eq ?_)
  simp [Polynomial.eval_add]

/-- The hypotheses of `negligible_prfChainAdv` can be met together, by the attacker family that
guesses a fixed key, against every PRF family. -/
example {Key : ℕ → Type} (prf : (η : ℕ) → PRFScheme (Key η) (Fin (2 ^ η) × M) (Fin (2 ^ η))) :
    negligible fun η =>
      prfChainAdv (prf η) (pure 0 : OracleComp (advSpec (Fin (2 ^ η)) M) (Fin (2 ^ η))) :=
  negligible_prfChainAdv prf (fun η => (pure 0 : OracleComp (advSpec (Fin (2 ^ η)) M) _)) 0
    (fun _ => isQueryBoundP_pure _ _ _)
    (negligible_of_zero fun _ => prfAdvantage_chainReduction_pure _ _)

end SquirrelModel.Chain
