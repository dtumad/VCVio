/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVioFrontier.Examples.ElGamal.Transport

/-! # Two challenge-bit branches of VCVio's ElGamal reduction -/

public section

namespace VCVioFrontierTest.ElGamal

/-- Two distinct challenge messages and a saved state. -/
@[expose] def choose : _root_.ProbComp (ℤ × ℤ × ℤ) := pure (2, 7, 13)

/-- The distinguisher checks that the saved state, first ciphertext component and masked message
all survived the reduction. With this challenge it identifies the first message. -/
@[expose] def guess (st : ℤ) (ct : ℤ × ℤ) : _root_.ProbComp Bool :=
  pure (decide (st = 13 ∧ ct = (3, 7)))

/-- The first message produces the ciphertext checked by the adversary. -/
theorem distinguishFirst : Cslib.ProbComp.eval (elGamalAsymmEnc.oneTimeDDHReductionBody
    choose (pure true) guess 3 5) = PMF.pure true := by
  simp [elGamalAsymmEnc.oneTimeDDHReductionBody, elGamalAsymmEnc.oneTimeDDHReductionWith,
    choose, guess]

/-- The second message produces a different ciphertext and the guess is false. -/
theorem distinguishSecond : Cslib.ProbComp.eval (elGamalAsymmEnc.oneTimeDDHReductionBody
    choose (pure false) guess 3 5) = PMF.pure true := by
  simp [elGamalAsymmEnc.oneTimeDDHReductionBody, elGamalAsymmEnc.oneTimeDDHReductionWith,
    choose, guess]

end VCVioFrontierTest.ElGamal
