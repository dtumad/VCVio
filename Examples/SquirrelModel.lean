/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Examples.SquirrelModel.Execution
public import Examples.SquirrelModel.NonAdaptive
public import Examples.SquirrelModel.Deduction
public import Examples.SquirrelModel.OracleRules
public import Examples.SquirrelModel.GuessQuery
public import Examples.SquirrelModel.Asymptotic
public import Examples.SquirrelModel.ChainSecrecy
public import Examples.SquirrelModel.SquirrelStatement
public import Examples.SquirrelModel.ChainAsymptotic

/-!
# Squirrel inside PolyFun and VCVio: a tour

Hérouard, Jacomme, Koutsos and Lallemand (CCS 2026) add a secrecy logic to the Squirrel prover and
prove post-compromise security of a ratchet with it. These files model Squirrel's semantics with
free programs and handlers, check its secrecy rules as lemmas about named reductions, and prove the
paper's motivating example, with adaptive corruption.

## Execution

1. `Execution.lean`. The attacker's view is a polynomial functor (`iface`), the protocol a stateful
   handler (`Protocol.handler`), the attacker a fixed-schedule program (`ofSchedule`).
   **`run_ofSchedule`**: running the program against the handler computes Squirrel's macros.
2. `NonAdaptive.lean`. **`eq_ofSchedule_bind_residual`**: Squirrel's attackers are exactly the
   non-adaptive programs.

## Secrecy

3. `Deduction.lean`. `deduceAdv`, the concrete form of `u ⊬ v`, with FreshL, WeakL, WeakR,
   Rw-Equiv (**`deduceAdv_le_rwEquiv`**) and CDH.
4. `OracleRules.lean`. The rules Squirrel proves only on paper, by identical-until-bad:
   **`deduceAdvO_le_rwOracle`**, `deduceAdvO_le_pcOracle`.
5. `GuessQuery.lean`. The factor-`q` step to Squirrel's premise `u, o' ⊬ m`:
   **`deduceAdvO_le_pcOracle_sum`**.
6. `Asymptotic.lean`. Squirrel's `[φ]`, `∼`, `⊬`, `▷` over a class of adversaries closed under
   composition, with the rules lifted (**`NonDeducible.rwEquiv`**) and a nontrivial instance.

## The paper's example: a hash chain

7. `ChainSecrecy.lean`. **`chainAdv_le`**: an attacker that interleaves freely and corrupts
   adaptively outputs the initial key with probability at most `(q + 1) / |K|`.
8. `SquirrelStatement.lean`. **`squirrel_forward_secrecy`**: the paper's own statement,
   `frame@t' ⊬ ck@init`, for Squirrel's fixed-trace attacker, as a corollary.
9. `ChainAsymptotic.lean`. **`negligible_chainAdv`**: negligible for `η`-bit keys and
   polynomially many queries.
-/
