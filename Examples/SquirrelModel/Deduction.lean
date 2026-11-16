/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
public import VCVio.EvalDist.ProbabilityBounds
public import ToMathlib.MeasureTheory.Measure.Bool

/-!
# Non-deduction as the success of a named adversary

Hérouard, Jacomme, Koutsos and Lallemand (CCS 2026) add to the Squirrel prover a non-deduction
predicate `u ⊬ v`: no polynomial-time attacker computes `v` from `u`, except with negligible
probability. Here the same notion is a concrete quantity. A joint sample `uv : ProbComp (α × β)`
gives the two random variables, and `deduceAdv uv f` is the probability that the adversary `f`
computes the second component from the first. Squirrel's rules for `⊬` then become statements
about named reductions:

* `deduceAdv_freshL`: a fresh sample on the left does not help (rule FreshL);
* `deduceAdv_weakL`: whatever is computable from `u'` is no more useful than `u'` (rule WeakL);
* `deduceAdv_le_weakR`: if `w` is computable from `v`, computing `v` is no easier than computing
  `w` (rule WeakR);
* `deduceAdv_le_rwEquiv`: indistinguishable joint samples have close advantages, up to a named
  distinguisher (rule Rw-Equiv);
* `deduceAdv_cdhPair`: the non-deduction `g, a•g, b•g ⊬ (a*b)•g` is the CDH experiment.

Each rule names the reduction it uses, so no statement quantifies over an unbounded adversary
type. The bounds are concrete at a fixed security parameter; there is no polynomial-time layer,
which is where Squirrel's `adv` predicate does its work.
-/

public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace SquirrelModel

variable {α α' β γ : Type}

/-- The probability that the adversary `f` computes the second component of the joint sample
`uv` from its first component: the concrete counterpart of Squirrel's `u ⊬ v`, which asks this to
be negligible for every polynomial-time `f`. -/
@[expose] noncomputable def deduceAdv (uv : ProbComp (α × β)) (f : α → ProbComp β) : ℝ≥0∞ :=
  Pr{let z ← uv; let w ← f z.1}[w = z.2]

/-! ## Structural rules -/

/-- The reduction behind FreshL: draw the fresh value itself. -/
@[expose] def freshLReduction {N : Type} [SampleableType N] (f : α × N → ProbComp β) :
    α → ProbComp β :=
  fun u => do let n ← $ᵗ N; f (u, n)

/-- **FreshL.** Adding a fresh uniform sample to the left gives no advantage: the adversary's
success equals that of `freshLReduction`, which samples the value itself. -/
theorem deduceAdv_freshL {N : Type} [SampleableType N] (uv : ProbComp (α × β))
    (f : α × N → ProbComp β) :
    deduceAdv (do let z ← uv; let n ← $ᵗ N; pure ((z.1, n), z.2)) f =
      deduceAdv uv (freshLReduction f) := by
  simp only [deduceAdv, freshLReduction, prEvent_norm]

/-- **WeakL.** If `u` is computed from `u'` by `g`, jointly with the target, then any adversary
against `u` gives one against `u'` with the same success: run `g`, then the adversary. -/
theorem deduceAdv_weakL (uv' : ProbComp (α' × β)) (g : α' → ProbComp α)
    (f : α → ProbComp β) :
    deduceAdv (do let z ← uv'; let u ← g z.1; pure (u, z.2)) f =
      deduceAdv uv' (fun u' => g u' >>= f) := by
  simp only [deduceAdv, prEvent_norm]

/-- **WeakR.** If `w = h v`, an adversary computing `v` yields one computing `w` with at least
the same success: apply `h` to its output. -/
theorem deduceAdv_le_weakR (uv : ProbComp (α × β)) (h : β → γ) (f : α → ProbComp β) :
    deduceAdv uv f ≤ deduceAdv (Prod.map id h <$> uv) (fun u => h <$> f u) := by
  have key := prEvent_mono (do let z ← uv; let w ← f z.1; pure (z, w))
    (fun x => x.2 = x.1.2) (fun x => h x.2 = h x.1.2) (fun x hx => congrArg h hx)
  simpa only [deduceAdv, prEvent_norm, Prod.map_fst, Prod.map_snd, id_eq] using key

/-- The distinguisher behind Rw-Equiv: run the adversary on the first component and test its
answer against the second. -/
@[expose] def deduceDistinguisher [DecidableEq β] (f : α → ProbComp β) (z : α × β) :
    ProbComp Bool := do
  let w ← f z.1
  pure (decide (w = z.2))

/-- An adversary's success is the probability that `deduceDistinguisher` accepts. -/
theorem deduceAdv_eq_evalDist_deduceDistinguisher [DecidableEq β] (uv : ProbComp (α × β))
    (f : α → ProbComp β) :
    deduceAdv uv f = 𝒟[uv >>= deduceDistinguisher f] {true} := by
  have key := prEvent_eq_evalDist_decide (do let z ← uv; let w ← f z.1; pure (z, w))
    (fun x => x.2 = x.1.2)
  rw [show deduceDistinguisher f = fun z => do let w ← f z.1; pure (decide (w = z.2)) from rfl]
  simpa only [deduceAdv, prEvent_norm] using key

/-- **Rw-Equiv.** Changing the joint sample changes the adversary's success by at most the
advantage of the named distinguisher `deduceDistinguisher f` between the two samples. -/
theorem deduceAdv_le_rwEquiv [DecidableEq β] (uv₁ uv₂ : ProbComp (α × β))
    (f : α → ProbComp β) :
    deduceAdv uv₁ f ≤ deduceAdv uv₂ f +
      𝒟[uv₁ >>= deduceDistinguisher f].boolDist 𝒟[uv₂ >>= deduceDistinguisher f] := by
  rw [deduceAdv_eq_evalDist_deduceDistinguisher, deduceAdv_eq_evalDist_deduceDistinguisher]
  exact Measure.apply_true_le_add_boolDist _ _

/-! ## Computational Diffie–Hellman as non-deduction -/

section CDH

open DiffieHellman

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [SampleableType F] [DecidableEq G]

/-- The joint sample of Squirrel's CDH rule: the public values `(g, a • g, b • g)` and the
target `(a * b) • g`. -/
@[expose] def cdhPair (g : G) : ProbComp ((G × G × G) × G) := do
  let a ← $ᵗ F
  let b ← $ᵗ F
  pure ((g, a • g, b • g), (a * b) • g)

/-- A non-deduction adversary for `cdhPair` as a CDH adversary. -/
@[expose] def cdhReduction (f : G × G × G → ProbComp G) : CDHAdversary F G :=
  fun g A B => f (g, A, B)

/-- **CDH as non-deduction.** Computing `(a * b) • g` from `(g, a • g, b • g)` is exactly the
CDH experiment, played by `cdhReduction f`. -/
theorem deduceAdv_cdhPair (g : G) (f : G × G × G → ProbComp G) :
    deduceAdv (cdhPair (F := F) g) f =
      Pr{let b ← cdhExperiment g (cdhReduction (F := F) f)}[b = true] := by
  simp only [deduceAdv, cdhPair, cdhExperiment, cdhReduction, prEvent_norm, decide_eq_true_eq]

end CDH

end SquirrelModel
