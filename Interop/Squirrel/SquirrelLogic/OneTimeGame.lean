/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA.OneTime

/-!
# The one-time IND-CPA game as two branches

`IND_CPA_OneTime_Advantage_probComp_eq_absDiff`: at the `ProbComp` runtime, the one-time IND-CPA
advantage of an adversary is the distance between the probabilities that it answers `true` in the
two branches of the game, the branch encrypting the first message and the branch encrypting the
second (`IND_CPA_OneTime_Branch`). There is no factor of two: the advantage is the bias of the
hidden-bit game, `|Pr[win] − Pr[lose]|`, which is the distance between the branches by
`evalDist_boolBias_bind_uniformBool`.

Nothing here mentions Squirrel. It is local to this library until a second consumer needs it.
-/

public section

namespace SquirrelLogic

open AsymmEncAlg

variable {M PK SK C : Type}

/-- One branch of the one-time IND-CPA game, with the hidden bit fixed to `b`: generate a key,
let the adversary choose two messages, encrypt the first if `b` and the second otherwise, and
return the adversary's guess. -/
@[expose] def IND_CPA_OneTime_Branch (encAlg : AsymmEncAlg ProbComp M PK SK C)
    (adv : IND_CPA_OneTime_Adversary encAlg) (b : Bool) : ProbComp Bool := do
  let (pk, _) ← encAlg.keygen
  let (m₁, m₂, state) ← adv.chooseMessages pk
  let c ← encAlg.encrypt pk (if b then m₁ else m₂)
  adv.distinguish state c

/-- **The game's shape.** The one-time IND-CPA advantage at the `ProbComp` runtime is the distance
between the probabilities that the adversary answers `true` in the two branches. -/
theorem IND_CPA_OneTime_Advantage_probComp_eq_absDiff (encAlg : AsymmEncAlg ProbComp M PK SK C)
    (adv : IND_CPA_OneTime_Adversary encAlg) :
    IND_CPA_OneTime_Advantage encAlg ProbCompRuntime.probComp adv =
      ENNReal.absDiff Pr{let z ← IND_CPA_OneTime_Branch encAlg adv true}[z = true]
        Pr{let z ← IND_CPA_OneTime_Branch encAlg adv false}[z = true] := by
  have hgame : IND_CPA_OneTime_Game adv ProbCompRuntime.probComp = (do
      let b ← $ᵗ Bool
      let z ← if b then IND_CPA_OneTime_Branch encAlg adv true
        else IND_CPA_OneTime_Branch encAlg adv false
      pure (b == z)) := by
    refine bind_congr fun b => ?_
    cases b <;> simp [IND_CPA_OneTime_Branch]
  rw [IND_CPA_OneTime_Advantage, ProbCompRuntime.probComp_evalDist, hgame,
    evalDist_boolBias_bind_uniformBool, MeasureTheory.Measure.boolDist,
    prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton]

end SquirrelLogic
