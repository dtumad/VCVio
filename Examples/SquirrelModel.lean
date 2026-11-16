/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Examples.SquirrelModel.Execution
public import Examples.SquirrelModel.NonAdaptive
public import Examples.SquirrelModel.TracePrice
public import Examples.SquirrelModel.Deduction
public import Examples.SquirrelModel.OracleRules
public import Examples.SquirrelModel.GuessQuery
public import Examples.SquirrelModel.Asymptotic
public import Examples.SquirrelModel.ChainSecrecy
public import Examples.SquirrelModel.SquirrelStatement
public import Examples.SquirrelModel.ChainAsymptotic
public import Examples.SquirrelModel.ChainLaterKeys
public import Examples.SquirrelModel.PRFChain
public import Examples.SquirrelModel.Healing

/-!
# Squirrel inside PolyFun and VCVio: a tour

Hérouard, Jacomme, Koutsos and Lallemand (CCS 2026) add a secrecy logic to the Squirrel prover and
prove post-compromise security of a ratchet with it. These files model Squirrel's semantics with
free programs and handlers, check its secrecy rules as lemmas about named reductions, price its
fixed traces, prove the paper's motivating example with adaptive corruption, and prove one healing
step of its ratchet.

## Execution

1. `Execution.lean`. The attacker's view is a polynomial functor (`iface`), the protocol a stateful
   handler (`Protocol.handler`), the attacker a fixed-schedule program (`ofSchedule`).
   **`run_ofSchedule`**: running the program against the handler computes Squirrel's macros.
2. `NonAdaptive.lean`. **`eq_ofSchedule_bind_residual`**: Squirrel's attackers are exactly the
   non-adaptive programs.
3. `TracePrice.lean`. **`prEvent_run_eq_sum_guided`**: an adaptive attacker's success is the sum,
   over traces, of the success of Squirrel attackers (`guided p σ`); so a bound for every trace
   costs a factor `|Act| ^ n` (`prEvent_run_le_card_pow_mul`), and `twoStep` shows a loss is real.

## Secrecy

4. `Deduction.lean`. `deduceAdv`, the concrete form of `u ⊬ v`, with FreshL, WeakL, WeakR,
   Rw-Equiv (**`deduceAdv_le_rwEquiv`**) and CDH.
5. `OracleRules.lean`. The rules Squirrel proves only on paper, by identical-until-bad:
   **`deduceAdvO_le_rwOracle`**, `deduceAdvO_le_pcOracle`.
6. `GuessQuery.lean`. The factor-`q` step to Squirrel's premise `u, o' ⊬ m`:
   **`deduceAdvO_le_pcOracle_sum`**.
7. `Asymptotic.lean`. Squirrel's `[φ]`, `∼`, `⊬`, `▷` over a class of adversaries, with the rules
   lifted (**`NonDeducible.rwEquiv`**) and every efficiency assumption a named hypothesis.

## The paper's example: a hash chain

8. `ChainSecrecy.lean`. **`chainAdv_le`**: with a random oracle, an attacker that interleaves
   freely and corrupts adaptively outputs the initial key with probability at most `(q + 1) / |K|`.
9. `SquirrelStatement.lean`. **`squirrel_forward_secrecy`**: the paper's own statement,
   `frame@t' ⊬ ck@init`, for Squirrel's fixed-trace attacker, as a corollary.
10. `ChainAsymptotic.lean`. **`negligible_chainAdv`**: negligible for `η`-bit keys and
    polynomially many queries.
11. `ChainLaterKeys.lean`. **`keyAdv_le`**: every safe key `ck_t`, against an attacker whose first
    `t` chain operations are updates and which corrupts freely afterwards:
    `((t + 1) q + 1) / |K|`.
12. `PRFChain.lean`. **`prfChainAdv_le`**: the paper's keyed hash, assumed a PRF: the bound is the
    PRF advantage of the named reduction `chainReduction A` plus `(q + 1) / |K|`.

## The ratchet: one healing step

13. `Healing.lean`. **`healingAdv_le`**: after a compromise leaks `rk`, one honest Diffie–Hellman
    exchange makes `rk' = H(rk, g^{ab})` secret again, up to the CDH success of named guessing
    reductions plus `1 / |K|`; Pc-Oracle and CDH-as-non-deduction composed.

## What the statements assume

The random-oracle results (`chainAdv_le`, `keyAdv_le` and their corollaries, the oracle rules)
are information-theoretic: they hold against every adversary, counting only its oracle queries. The
rule lemmas, `prfChainAdv_le` and `healingAdv_le` hold for every adversary and name the reductions
they use, so each reduction's cost is its code. Efficiency enters only in `Asymptotic.lean` and in
`negligible_prfChainAdv`, as named hypotheses: closure of the adversary class, and PRF security
for the one reduction family used.
-/
