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
public import Examples.SquirrelModel.CoreRules
public import Examples.SquirrelModel.ChainSecrecy
public import Examples.SquirrelModel.SquirrelStatement
public import Examples.SquirrelModel.ChainMacros
public import Examples.SquirrelModel.TapeAndLength
public import Examples.SquirrelModel.ChainAsymptotic
public import Examples.SquirrelModel.ChainLaterKeys
public import Examples.SquirrelModel.PRFChain
public import Examples.SquirrelModel.Healing

/-!
# Squirrel inside PolyFun and VCVio: a tour

Hérouard, Jacomme, Koutsos and Lallemand (CCS 2026) add a secrecy logic to the Squirrel prover and
prove post-compromise security of a ratchet with it. These files model Squirrel's execution
semantics with free programs and handlers, prove counterparts of its secrecy rules as lemmas about
named reductions, price its fixed traces, prove the paper's motivating example with adaptive
corruption, and prove one healing-style step. They do not formalize Squirrel's logic itself: see
Scope.

## Translation

* Actions (timestamps) are positions of `iface Act Msg`; a protocol's mutable cells are the state
  of a `Protocol`; names are values that the protocol or the experiment samples.
* The attacker functions `att`, reading a shared random tape, are one free program over the
  attacker's interface: adaptive in general, `ofSchedule att σ` for a fixed trace `σ`.
* The macros `input@τ`, `exec@τ` and `frame@τ` are the run of `Protocol.handler`.
* `u ⊬ v` is `deduceAdv` at a fixed security parameter and `NonDeducible` over a class of
  adversaries; `u, o ⊬ v` with an oracle is `deduceAdvO`; `u ▷ v` is `DeducibleBy`; `u ∼ v` is
  `Indist`; `[φ]` is `Overwhelming`; `adv` is `AdvClass`.
* Validity in all models is universal quantification over protocols, handlers and adversaries.
* The keyed hash `h(·, k)` is a random oracle (`ChainSecrecy`, `ChainLaterKeys`, `Healing`) or a
  PRF (`PRFChain`).

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
8. `CoreRules.lean`. The core rules Neg, Ineq and Trans, concrete and asymptotic
   (**`NonDeducible.ineq`**, `DeducibleBy.trans`), and PRF.R with a random oracle
   (**`deduceAdvO_le_prfR`**).

## The paper's example: a hash chain

9. `ChainSecrecy.lean`. **`chainAdv_le`**: with a random oracle, an attacker that interleaves
   freely and corrupts adaptively outputs the initial key with probability at most `(q + 1) / |K|`.
10. `SquirrelStatement.lean`. **`squirrel_forward_secrecy`**: the paper's own statement,
    `frame@t' ⊬ ck@init`, for Squirrel's fixed-trace attacker, as a corollary.
11. `ChainMacros.lean`. **`squirrel_forward_secrecy_macros`**: the chain written as a `Protocol`;
    its macros compute the chain game (`macros_chainProtocolO`), so the bound holds for the frame
    Squirrel's macro equations compute.
12. `TapeAndLength.lean`. **`squirrel_forward_secrecy_tape`**: attackers reading a random tape;
    **`negligible_prEvent_run_of_forall_trace`**: for a fixed number of actions, negligible per
    trace gives negligible adaptively, and the ladder shows the fixed number is needed.
13. `ChainAsymptotic.lean`. **`negligible_chainAdv`**: negligible for `η`-bit keys and
    polynomially many queries.
14. `ChainLaterKeys.lean`. **`keyAdv_le`**: every safe key `ck_t`, against an attacker whose first
    `t` chain operations are updates and which corrupts freely afterwards:
    `((t + 1) q + 1) / |K|`.
15. `PRFChain.lean`. **`prfChainAdv_le`**: the paper's keyed hash, assumed a PRF: the bound is the
    PRF advantage of the named reduction `chainReduction A` plus `(q + 1) / |K|`.

## The ratchet: one healing step

16. `Healing.lean`. **`healingAdv_le`**: after a compromise leaks `rk`, one honest Diffie–Hellman
    exchange makes `rk' = H(rk, g^{ab})` secret again, up to the CDH success of named guessing
    reductions plus `1 / |K|`; Pc-Oracle and CDH-as-non-deduction composed.

## What the statements assume

The random-oracle results (`chainAdv_le`, `keyAdv_le` and their corollaries, the oracle rules)
are information-theoretic: they hold against every adversary, counting only its oracle queries. The
rule lemmas, `prfChainAdv_le` and `healingAdv_le` hold for every adversary and name the reductions
they use, so each reduction's cost is its code. Efficiency enters only in `Asymptotic.lean` and in
`negligible_prfChainAdv`, as named hypotheses: closure of the adversary class, and PRF security
for the one reduction family used.

## Scope

Proved here: the execution of a fixed-trace attacker as a handler run (`run_ofSchedule`), and
Squirrel's attackers as the non-adaptive programs (as programs, ignoring cost); counterparts of the
rules FreshL, WeakL, WeakR, Rw-Equiv, CDH, Neg, Ineq, Trans, Rw-Oracle, Pc-Oracle and PRF.R (the
last with a random oracle), for the definitions of these files; the chain's forward secrecy for
the frame its macros compute, with random tapes; the price of fixed traces and its tightness; one
healing-style step.

Modelled by hand: `macros` transcribes the macro equations of Squirrel's documentation (Squirrel's
own translation from processes is not formally defined); the keyed hash is a random oracle in
`ChainSecrecy`, `ChainLaterKeys`, `CoreRules` and `Healing`, and a PRF only in `PRFChain`.

Not formalized: Squirrel's term language, models, validity and proof system, and the soundness of
its own rules for its logic; PRF.L, EUF-CMA and Gap-DH; asymptotic forms of the oracle rules; the
compilation of processes to actions; the asymmetric ratchet, its health predicates and its PCS
theorem; any polynomial-time class of adversaries.
-/
