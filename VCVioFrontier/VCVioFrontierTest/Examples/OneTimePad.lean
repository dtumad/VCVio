/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import VCVioFrontier.Examples.OneTimePad.Machine

/-!
# One-time-pad machine regressions

The empty word exercises the sampler's base case. Distinct one-bit messages exercise secrecy,
and an asymmetric bit pattern detects a reversed key or data encoding.
-/

open VCVioFrontier.OneTimePad

example : word (1 : BitVec 3) = [true, false, false] := by decide

example : roundTripMachine.output [] = PMF.pure [] := by
  simpa [word] using roundTripMachine_correct (0 : BitVec 0)

example : encryptMachine.output [false] = encryptMachine.output [true] := by
  exact encryptMachine_rows (0 : BitVec 1) (1 : BitVec 1)

example : xorMachine.output ([true, false, false], [false, true, false]) =
    PMF.pure [true, true, false] :=
  xorMachine_exact (1 : BitVec 3) (2 : BitVec 3)

example : xorMachine.output ([true, false, false], [true, true, false]) =
    PMF.pure [false, true, false] :=
  xorMachine_decrypt (1 : BitVec 3) (2 : BitVec 3)
