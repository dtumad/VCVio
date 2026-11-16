/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Examples.SquirrelModel.Deduction
public import VCVio.CryptoFoundations.Asymptotics.Security

/-!
# Squirrel's secrecy logic over a class of adversaries

Squirrel's global formulas are asymptotic: `[φ]` holds when `φ` is true with overwhelming
probability in the security parameter `η`; `u ∼ v` when no polynomial-time attacker
distinguishes them; `u ⊬ v := ∀ f [adv], [f u ≠ v]`; and `u ▷ v := ∃ f [adv], [f u = v]`. Its
`adv` predicate is a built-in notion of polynomial-time adversary.

VCVio has no polynomial-time class, so this file takes the class as a parameter: an `AdvClass`
is any class of `η`-indexed adversaries closed under the three compositions the rules use, namely
sequencing, drawing a fresh uniform value, and testing an answer against a target. Over such a
class, the predicates are:

* `Overwhelming p`: `1 - p` is negligible, Squirrel's `[φ]`;
* `NonDeducible C uv`: every adversary in `C` computes the second component of `uv` from the
  first with negligible probability, Squirrel's `u ⊬ v`. This is VCVio's
  `SecurityGame.secureAgainst` for the deduction game;
* `DeducibleBy C g uv`: the named adversary `g ∈ C` computes it with overwhelming probability,
  Squirrel's `u ▷ v` with its witness made explicit;
* `Indist C x y`: every distinguisher in `C` has negligible advantage, Squirrel's `u ∼ v`.

The rules FreshL, WeakL, WeakR and Rw-Equiv lift from the concrete lemmas of `Deduction.lean`, each
by one closure property of the class. Deducers and simulators are explicit arguments, never
existentials. `AdvClass.all`, the class of all adversaries, shows the closure conditions can be
met; for it `NonDeducible` is information-theoretic secrecy. `nonDeducible_uniform` shows the
rules' hypotheses can be met by a nontrivial family: a uniform `η`-bit number cannot be computed
from nothing, using `negligible_inv_two_pow`. Wiring in a computational class (for
instance one built from VCVio's backend-relative `IsPPTBy`) is not attempted here; that is where
assumptions such as CDH would enter.
-/

public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace SquirrelModel.Asymptotic

/-- An adversary indexed by the security parameter, from `α` to `β`. -/
abbrev Adv (α β : Type) : Type := ℕ → α → ProbComp β

/-- A class of `η`-indexed adversaries closed under the compositions Squirrel's rules use. -/
structure AdvClass where
  /-- Membership in the class. -/
  mem : {α β : Type} → Adv α β → Prop
  /-- Running one member after another stays in the class (rules WeakL and WeakR). -/
  kleisli {α β γ : Type} {g : Adv α β} {f : Adv β γ} :
    mem g → mem f → mem (fun η a => g η a >>= f η)
  /-- Drawing a fresh uniform value before running stays in the class (rule FreshL). -/
  fresh {α β N : Type} [SampleableType N] {f : Adv (α × N) β} :
    mem f → mem (fun η u => freshLReduction (f η) u)
  /-- Testing a member's answer against a target stays in the class (rule Rw-Equiv). -/
  eqTest {α β : Type} [DecidableEq β] {f : Adv α β} :
    mem f → mem (fun η z => deduceDistinguisher (f η) z)

/-- The class of all adversaries meets every closure condition. -/
def AdvClass.all : AdvClass where
  mem _ := True
  kleisli _ _ := trivial
  fresh _ := trivial
  eqTest _ := trivial

variable {α α' β γ : Type}

/-- Squirrel's `[φ]`: the probability `p` is overwhelming in the security parameter. -/
def Overwhelming (p : ℕ → ℝ≥0∞) : Prop := negligible fun η => 1 - p η

/-- The deduction game of a family of joint samples: an adversary's advantage is its success at
computing the second component from the first. -/
noncomputable def deduceGame (uv : ℕ → ProbComp (α × β)) : SecurityGame (Adv α β) :=
  ⟨fun f η => deduceAdv (uv η) (f η)⟩

/-- Squirrel's `u ⊬ v` over the class `C`. -/
def NonDeducible (C : AdvClass) (uv : ℕ → ProbComp (α × β)) : Prop :=
  (deduceGame uv).secureAgainst C.mem

/-- Squirrel's `u ▷ v`, with its witness named: `g ∈ C` computes the second component of `uv`
from the first with overwhelming probability. -/
def DeducibleBy (C : AdvClass) (g : Adv α β) (uv : ℕ → ProbComp (α × β)) : Prop :=
  C.mem g ∧ Overwhelming fun η => deduceAdv (uv η) (g η)

/-- Squirrel's `u ∼ v` over the class `C`: every distinguisher in `C` has negligible advantage. -/
def Indist (C : AdvClass) (x y : ℕ → ProbComp γ) : Prop :=
  ∀ D : Adv γ Bool, C.mem D → negligible fun η => 𝒟[x η >>= D η].boolDist 𝒟[y η >>= D η]

/-! ## The rules -/

/-- **FreshL.** A fresh uniform value on the left keeps a secret secret. -/
theorem NonDeducible.freshL (C : AdvClass) {N : Type} [SampleableType N]
    {uv : ℕ → ProbComp (α × β)} (h : NonDeducible C uv) :
    NonDeducible C (fun η => do let z ← uv η; let n ← $ᵗ N; pure ((z.1, n), z.2)) := by
  intro f hf
  have hred := h _ (C.fresh hf)
  simpa only [deduceGame, deduceAdv_freshL] using hred

/-- **WeakL.** If the named simulator `g ∈ C` computes `u` from `u'`, a secret from `u'` is a
secret from `u`. -/
theorem NonDeducible.weakL (C : AdvClass) {uv' : ℕ → ProbComp (α' × β)} (g : Adv α' α)
    (hg : C.mem g) (h : NonDeducible C uv') :
    NonDeducible C (fun η => do let z ← uv' η; let u ← g η z.1; pure (u, z.2)) := by
  intro f hf
  have hred := h _ (C.kleisli hg hf)
  simpa only [deduceGame, deduceAdv_weakL] using hred

/-- **WeakR.** If `w = h v` and `h` is computable within `C`, a secret `w` makes `v` secret. -/
theorem NonDeducible.weakR (C : AdvClass) {uv : ℕ → ProbComp (α × β)} (h : β → γ)
    (hh : C.mem (fun (_ : ℕ) (b : β) => (pure (h b) : ProbComp γ)))
    (hw : NonDeducible C (fun η => Prod.map id h <$> uv η)) : NonDeducible C uv := by
  intro f hf
  have hfun : (fun η a => f η a >>= fun b => (pure (h b) : ProbComp γ)) =
      (fun η u => h <$> f η u) := by
    funext η u
    rw [map_eq_bind_pure_comp]
    rfl
  have hred := hw _ (hfun ▸ C.kleisli hf hh)
  exact negligible_of_le (fun η => deduceAdv_le_weakR (uv η) h (f η)) hred

/-- **Rw-Equiv.** Indistinguishable families have the same secrets. -/
theorem NonDeducible.rwEquiv (C : AdvClass) {uv₁ uv₂ : ℕ → ProbComp (α × β)}
    (hI : Indist C uv₁ uv₂) (h : NonDeducible C uv₂) : NonDeducible C uv₁ := by
  classical
  intro f hf
  exact negligible_of_le (fun η => deduceAdv_le_rwEquiv (uv₁ η) (uv₂ η) (f η))
    (negligible_add (h f hf) (hI _ (C.eqTest hf)))

/-! ## A nontrivial secret

The rules' hypotheses can be met by a nontrivial family, even over the class of all adversaries:
a uniform `η`-bit value is a secret from nothing. -/

/-- `2^{-η}` is negligible. -/
theorem negligible_inv_two_pow : negligible fun η : ℕ => ((2 : ℝ≥0∞) ^ η)⁻¹ := by
  rw [negligible_iff_superpolynomialDecay_toReal fun η => by simp]
  intro k
  refine (tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)).congr
    fun η => ?_
  simp [div_eq_mul_inv, ENNReal.toReal_inv, ENNReal.toReal_pow]

/-- A uniform element of `Fin n` hits a given number with probability at most `1 / n`. -/
theorem prEvent_eq_val_uniformFin_le (n : ℕ) [NeZero n] (w : ℕ) :
    Pr{let v ← $ᵗ (Fin n)}[w = (v : ℕ)] ≤ (n : ℝ≥0∞)⁻¹ := by
  by_cases hw : w < n
  · refine le_of_eq ((prEvent_congr _ _ _ fun v => ?_).trans
      ((SampleableType.prEvent_uniformSample_eq_singleton' (⟨w, hw⟩ : Fin n)).trans (by simp)))
    rw [Fin.ext_iff]
  · rw [prEvent_eq_zero_of_forall_not ($ᵗ (Fin n)) (fun v : Fin n => w = (v : ℕ))
      fun v h => hw (by rw [h]; exact v.isLt)]
    exact zero_le

/-- A uniform `η`-bit number cannot be computed from nothing: `NonDeducible` holds for this
family over the class of all adversaries. -/
theorem nonDeducible_uniform :
    NonDeducible AdvClass.all fun η =>
      (fun v : Fin (2 ^ η) => ((), (v : ℕ))) <$> ($ᵗ (Fin (2 ^ η))) := by
  intro f _
  refine negligible_of_le (fun η => ?_) negligible_inv_two_pow
  have hswap : (deduceGame fun η =>
        (fun v : Fin (2 ^ η) => ((), (v : ℕ))) <$> ($ᵗ (Fin (2 ^ η)))).advantage f η =
      Pr{let w ← f η (); let v ← $ᵗ (Fin (2 ^ η))}[w = (v : ℕ)] := by
    rw [← prEvent_bind_map_swap]
    simp only [deduceGame, deduceAdv, prEvent_norm]
  rw [hswap]
  have key : Pr{let y ← (f η () >>= fun w => (fun v => (w, v)) <$> ($ᵗ (Fin (2 ^ η))))}[
      y.1 = (y.2 : ℕ)] ≤ ((2 ^ η : ℕ) : ℝ≥0∞)⁻¹ :=
    prEvent_bind_le_of_forall_le _ _ _ fun w => by
      rw [prEvent_map]
      exact prEvent_eq_val_uniformFin_le (2 ^ η) w
  simpa only [prEvent_norm, Nat.cast_pow, Nat.cast_ofNat] using key

end SquirrelModel.Asymptotic
