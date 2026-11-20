/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- frontier: CslibFrontier.Computability.Probabilistic.Sampling

public import PolyFunFrontier.PFunctor.Free.Realization
public import VCVioFrontier.OracleComp.Measure

/-!
# Uniform machines for handled oracle programs

A machine realization implements one family of source programs closed by a probabilistic
handler. The same machine and polynomial clock give the encoded output law on each input and
bound the halting time on every input word. The law also holds in VCVio's measure semantics.
-/

public section

namespace VCVioFrontier

open PFunctor MeasureTheory

variable {P : PFunctor} {α β : Type}

/-- A finite fair-coin machine implementing the handler fold at the given boundary encodings. -/
structure MachineRealization (H : Handler _root_.ProbComp P)
    (input : α ↪ List Bool) (encoding : β ↪ List Bool) (program : α → P.FreeM β) where
  tapes : ℕ
  State : Type
  [finiteState : Finite State]
  machine : Turing.MultiTapePTM tapes Bool State
  coefficient : ℕ
  degree : ℕ
  encoded_law (a : α) :
    Cslib.ProbComp.eval (machine.runClosed (coefficient * ((input a).length + 1) ^ degree)
      (input a)) = (Cslib.ProbComp.eval ((program a).liftM H)).map encoding
  halts (w : List Bool) :
    ∀ cfg ∈ (Cslib.ProbComp.eval (machine.runConfigFrom (Cslib.ProbComp.uniform Bool)
      Empty.elim (coefficient * (w.length + 1) ^ degree) (machine.initialConfig w))).support,
      cfg.tapes.state = none

namespace MachineRealization

variable {H : Handler _root_.ProbComp P} {input : α ↪ List Bool} {encoding : β ↪ List Bool}
  {program : α → P.FreeM β}

/-- Choose the uniform machine and clock supplied by a certificate for the source program. -/
noncomputable def ofCertificate (h : FreeM.PPTProgram H input encoding program) :
    MachineRealization H input encoding program := by
  apply Classical.choice
  obtain ⟨k, σ, hσ, m, c, d, law, halt⟩ := h.exists_halting_machine
  exact ⟨⟨k, σ, m, c, d, fun a => (law a).symm, halt⟩⟩

/-- The machine's output distribution at its certified clock. -/
@[expose] noncomputable def output (M : MachineRealization H input encoding program) (a : α) :
    PMF (List Bool) :=
  Cslib.ProbComp.eval (M.machine.runClosed (M.coefficient * ((input a).length + 1) ^ M.degree)
    (input a))

/-- The measured output agrees with VCVio's evaluation of the encoded, handled source.
The word space can carry any measurable structure. -/
theorem output_measure (M : MachineRealization H input encoding program) (a : α)
    (words : MeasurableSpace (List Bool)) :
    let _ := words
    (M.output a).toMeasure = 𝒟[encoding <$> (program a).liftM H] := by
  let _ := words
  dsimp only
  rw [output, M.encoded_law, evalDist_eq_toMeasure, Cslib.ProbComp.eval_map]

end MachineRealization

end VCVioFrontier
