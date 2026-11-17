/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import SquirrelLogic.Global
import VCVio.EvalDist.ProbabilityBounds
import VCVio.OracleComp.EvalDist.Measure

/-!
# Non-deduction and deduction over a class of attacker machines

Hérouard, Jacomme, Koutsos and Lallemand (CCS26, §3.1, p. 6) define two global formulas:

* `u ⊬ v ≜ ∀̃ f. adv(f) ⇒̃ [f(u) ≠ v]`: no attacker function computes `v` from `u`, except with
  negligible probability;
* `u ▷ v ≜ ∃̃ f. adv(f) ∧̃ [f(u) = v]`: some attacker function computes `v` from `u` with
  overwhelming probability.

The logic has no product types, so a tuple `u₁, …, uₙ` on the left is a vector of the types `τs`,
and `f` is a curried function of type `Ty.arrows τs β`, applied by `Ty.appVals`. The right side
is one term. Here the two predicates are read over random variables:

* `deduceAdv g u v η` is the probability that the attacker function `g`, run on the attacker tape
  `ρa`, computes `v` from `u` at `η`, and `deduceErr g u v η` that it does not;
* `AdvClass.NonDed C u v`: `deduceAdv g.eval u v` is negligible for every admitted attacker
  machine `g` (`AdvMachine`);
* `AdvClass.Ded C u v`: `deduceErr g.eval u v` is negligible for some admitted `g`.

`g` reads the tape `ρa` that every machine of the model shares, as `adv` does in LICS23 (ledger
row L10). The spike `Examples/SquirrelModel/Deduction.lean` reads the same predicate at one `η` as
`deduceAdv uv f = Pr[f(u) = v]` for a VCVio adversary `f` that draws fresh coins: there `u ⊬ v`
holds against every adversary, here against every admitted machine reading `ρa`.

## The rules of CCS26 Fig. 3 (p. 7)

Each law is a concrete inequality at every `η` with its reduction named, then its asymptotic form.

* Neg1, Neg2: `deduceAdv g u v + deduceErr g u v = 1`, at the witness `g` of `▷`; no closure.
* Ineq: `Pr[v = w] ≤ deduceAdv g u v + deduceErr g u w`, at the witness `g` of `u ▷ w`; no
  closure.
* Trans: `deduceErr (k.comp f) u w ≤ deduceErr f u v + deduceErr k [v] w`, by the reduction
  `AttackerFn.comp`, the denotation of `AdvMachine.comp` (`AdvClass.comp_mem`: substitution and
  relabelling).
* WeakL: `deduceAdv g [v] w ≤ deduceAdv (g.comp f) u w + deduceErr f u v`, by the same reduction.
* WeakR: `deduceAdv g u w ≤ deduceAdv (k.comp g) u v + deduceErr k [w] v`, by the same reduction.
* Rw-Equiv: `deduceAdv g u₁ v₁ ≤ deduceAdv g u₂ v₂ + advantage (Machine.deduce g).test …`, by
  the reduction `Machine.deduce`, which runs `g` on the left part of the vector and tests its
  result against the last entry (`AdvClass.deduce_mem`: the equality test, substitution and
  relabelling).

Rw-Equiv is stated for a right side of Boolean or base type (`Ty.IsGround`): its distinguisher
tests `f(u) = v`, which no machine does at an arrow type.
-/

public section

namespace SquirrelLogic

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B} {M : Model D} {τs : List (Ty B)} {β γ : Ty B}

/-! ## Vectors with one more entry -/

namespace VecRV

/-- The vector of one random variable. -/
@[expose] def single (X : RV M β) : VecRV M [β] := fun η ρ => Env.cons (X η ρ) Env.empty

/-- A vector followed by one random variable: CCS26's `u, v`. -/
@[expose] def snoc (u : VecRV M τs) (X : RV M β) : VecRV M (τs ++ [β]) :=
  fun η ρ => Env.append (u η ρ) (Env.cons (X η ρ) Env.empty)

end VecRV

/-! ## Success and failure of an attacker function -/

/-- The probability that the attacker function `g` computes `v` from the vector `u` at `η`, over
uniform tapes: CCS26's `Pr[f(u) = v]`. -/
@[expose] noncomputable def deduceAdv (g : AttackerFn M (Ty.arrows τs β)) (u : VecRV M τs)
    (v : RV M β) (η : ℕ) : ENNReal :=
  Pr{let ρ ← $ᵗ (M.Tape η)}[Ty.appVals (g η ρ.1) (u η ρ) = v η ρ]

/-- The probability that the attacker function `g` does not compute `v` from `u` at `η`. -/
@[expose] noncomputable def deduceErr (g : AttackerFn M (Ty.arrows τs β)) (u : VecRV M τs)
    (v : RV M β) (η : ℕ) : ENNReal :=
  Pr{let ρ ← $ᵗ (M.Tape η)}[Ty.appVals (g η ρ.1) (u η ρ) ≠ v η ρ]

/-- Success and failure partition the tapes. -/
theorem deduceAdv_add_deduceErr (g : AttackerFn M (Ty.arrows τs β)) (u : VecRV M τs)
    (v : RV M β) (η : ℕ) : deduceAdv g u v η + deduceErr g u v η = 1 := by
  rw [deduceAdv, deduceErr, prEvent_add_prEvent_not_eq_prEvent_true,
    OracleComp.prEvent_true_eq_one]

/-- An event is at most a second one plus the probability that a third, which with the first
implies the second, fails. -/
private theorem prEvent_le_add_of_imp {α : Type} (mx : ProbComp α) {p q r : α → Prop}
    (h : ∀ x, p x → r x → q x) :
    Pr{let x ← mx}[p x] ≤ Pr{let x ← mx}[q x] + Pr{let x ← mx}[¬ r x] :=
  (prEvent_le_prEvent_add_prEvent_and_not mx p q).trans
    (add_le_add le_rfl (prEvent_mono _ _ _ fun x hx hr => hx.2 (h x hx.1 hr)))

/-! ## The predicates -/

namespace AdvClass

/-- `u ⊬ v` (CCS26 §3.1): every admitted attacker machine computes `v` from `u` with negligible
probability. -/
@[expose] def NonDed (C : AdvClass M) (u : VecRV M τs) (v : RV M β) : Prop :=
  ∀ g : AdvMachine M τs β, C.mem g → negligible (deduceAdv g.eval u v)

/-- `u ▷ v` (CCS26 §3.1): some admitted attacker machine computes `v` from `u` with overwhelming
probability. -/
@[expose] def Ded (C : AdvClass M) (u : VecRV M τs) (v : RV M β) : Prop :=
  ∃ g : AdvMachine M τs β, C.mem g ∧ negligible (deduceErr g.eval u v)

end AdvClass

/-! ## Concrete statements at every `η` -/

section Bounds

variable {τs' : List (Ty B)}

/-- Ineq at `η`: `v` and `w` agree only where `g` computes `v` or misses `w`. -/
theorem prEvent_eq_le_deduceAdv_add_deduceErr (g : AttackerFn M (Ty.arrows τs β))
    (u : VecRV M τs) (v w : RV M β) (η : ℕ) :
    Pr{let ρ ← $ᵗ (M.Tape η)}[v η ρ = w η ρ] ≤ deduceAdv g u v η + deduceErr g u w η :=
  prEvent_le_add_of_imp _ fun _ h h' => h' ▸ h.symm

/-- Trans at `η`, by the reduction `AttackerFn.comp k f`. -/
theorem deduceErr_comp_le (k : AttackerFn M (.arrow β γ)) (f : AttackerFn M (Ty.arrows τs β))
    (u : VecRV M τs) (v : RV M β) (w : RV M γ) (η : ℕ) :
    deduceErr (k.comp f) u w η ≤
      deduceErr f u v η + deduceErr (τs := [β]) k (VecRV.single v) w η := by
  rw [add_comm]
  refine prEvent_le_add_of_imp _ fun ρ h h' => ?_
  simp only [AttackerFn.comp, Ty.appVals_postcomp, VecRV.single] at h h' ⊢
  rwa [← h']

/-- WeakL at `η`, by the reduction `AttackerFn.comp g f`: an attacker function computing `w` from
`v` computes it from `u` through `f`, wherever `f` computes `v`. -/
theorem deduceAdv_single_le (g : AttackerFn M (.arrow β γ)) (f : AttackerFn M (Ty.arrows τs β))
    (u : VecRV M τs) (v : RV M β) (w : RV M γ) (η : ℕ) :
    deduceAdv (τs := [β]) g (VecRV.single v) w η ≤
      deduceAdv (g.comp f) u w η + deduceErr f u v η :=
  prEvent_le_add_of_imp _ fun ρ h h' => by
    simp only [AttackerFn.comp, Ty.appVals_postcomp, VecRV.single] at h h' ⊢
    rwa [h']

/-- WeakR at `η`, by the reduction `AttackerFn.comp k g`: wherever `k` computes `v` from `w`, an
attacker function computing `w` computes `v` through `k`. -/
theorem deduceAdv_le_comp (g : AttackerFn M (Ty.arrows τs γ)) (k : AttackerFn M (.arrow γ β))
    (u : VecRV M τs) (v : RV M β) (w : RV M γ) (η : ℕ) :
    deduceAdv g u w η ≤
      deduceAdv (k.comp g) u v η + deduceErr (τs := [γ]) k (VecRV.single w) v η :=
  prEvent_le_add_of_imp _ fun ρ h h' => by
    simp only [AttackerFn.comp, Ty.appVals_postcomp, VecRV.single] at h h' ⊢
    rwa [h]

end Bounds

/-! ## The distinguisher of Rw-Equiv -/

/-- Rw-Equiv at `η`: the success of `g` against `u₁, v₁` is at most its success against `u₂, v₂`
plus the advantage of the reduction `Machine.deduce g` between the two vectors. -/
theorem deduceAdv_le_add_advantage (hβ : β.IsGround) (g : AdvMachine M τs β) (u₁ u₂ : VecRV M τs)
    (v₁ v₂ : RV M β) (η : ℕ) :
    deduceAdv g.eval u₁ v₁ η ≤ deduceAdv g.eval u₂ v₂ η +
      advantage (Machine.deduce hβ g).test (VecRV.snoc u₁ v₁) (VecRV.snoc u₂ v₂) η := by
  have hp : ∀ (u : VecRV M τs) (v : RV M β),
      Pr{let ρ ← $ᵗ (M.Tape η)}[(Machine.deduce hβ g).test η (VecRV.snoc u v η ρ) ρ.1 = true] =
        deduceAdv g.eval u v η := fun u v =>
    prEvent_congr _ _ _ fun ρ => by
      rw [VecRV.snoc, Machine.test, Machine.run_deduce]
      exact @decide_eq_true_iff _ (Classical.propDecidable _)
  have h := (ENNReal.absDiff_le_iff.1 (le_refl (advantage (Machine.deduce hβ g).test
    (VecRV.snoc u₁ v₁) (VecRV.snoc u₂ v₂) η))).1
  rw [hp, hp] at h
  exact h

/-! ## The laws -/

namespace AdvClass

variable {C : AdvClass M} {u : VecRV M τs} {v w : RV M β}

/-- **Neg1** (CCS26 Fig. 3): `u ⊬ v` refutes `u ▷ v`. The witness of `▷` would compute `v` with
probability negligibly close to one, and `1` is not negligible. -/
theorem NonDed.not_ded (h : C.NonDed u v) : ¬ C.Ded u v := fun ⟨g, hg, herr⟩ =>
  not_negligible_one (negligible_of_le (fun η => (deduceAdv_add_deduceErr g.eval u v η).ge)
    (negligible_add (h g hg) herr))

/-- **Neg2** (CCS26 Fig. 3): `u ▷ v` refutes `u ⊬ v`. -/
theorem Ded.not_nonDed (h : C.Ded u v) : ¬ C.NonDed u v := fun h' => h'.not_ded h

/-- **Ineq** (CCS26 Fig. 3): if `u ⊬ v` and `u ▷ w`, then `v` and `w` agree with negligible
probability, by `prEvent_eq_le_deduceAdv_add_deduceErr` at the witness of `u ▷ w`. -/
theorem NonDed.negligible_eq (h : C.NonDed u v) (h' : C.Ded u w) :
    negligible fun η => Pr{let ρ ← $ᵗ (M.Tape η)}[v η ρ = w η ρ] := by
  obtain ⟨g, hg, herr⟩ := h'
  exact negligible_of_le (prEvent_eq_le_deduceAdv_add_deduceErr g.eval u v w)
    (negligible_add (h g hg) herr)

/-- **Trans** (CCS26 Fig. 3): `u ▷ v` and `v ▷ w` give `u ▷ w`, by the reduction
`AdvMachine.comp` of the two witnesses. -/
theorem Ded.trans {w : RV M γ} (h₁ : C.Ded u v) (h₂ : C.Ded (VecRV.single v) w) : C.Ded u w := by
  obtain ⟨f, hf, hferr⟩ := h₁
  obtain ⟨k, hk, hkerr⟩ := h₂
  refine ⟨k.comp f, C.comp_mem hk hf, ?_⟩
  rw [AdvMachine.eval_comp']
  exact negligible_of_le (deduceErr_comp_le k.eval f.eval u v w) (negligible_add hferr hkerr)

/-- **WeakL** (CCS26 Fig. 3): `u ⊬ w` and `u ▷ v` give `v ⊬ w`, by the reduction
`AdvMachine.comp g f` from an attacker machine `g` against `v ⊬ w` and the witness `f`. -/
theorem NonDed.weakL {w : RV M γ} (h : C.NonDed u w) (h' : C.Ded u v) :
    C.NonDed (VecRV.single v) w := by
  obtain ⟨f, hf, hferr⟩ := h'
  intro g hg
  have hgf := h _ (C.comp_mem hg hf)
  rw [AdvMachine.eval_comp'] at hgf
  exact negligible_of_le (deduceAdv_single_le g.eval f.eval u v w) (negligible_add hgf hferr)

/-- **WeakR** (CCS26 Fig. 3): `u ⊬ v` and `w ▷ v` give `u ⊬ w`, by the reduction
`AdvMachine.comp k g` from an attacker machine `g` against `u ⊬ w` and the witness `k`. -/
theorem NonDed.weakR {w : RV M γ} (h : C.NonDed u v) (h' : C.Ded (VecRV.single w) v) :
    C.NonDed u w := by
  obtain ⟨k, hk, hkerr⟩ := h'
  intro g hg
  have hkg := h _ (C.comp_mem hk hg)
  rw [AdvMachine.eval_comp'] at hkg
  exact negligible_of_le (deduceAdv_le_comp g.eval k.eval u v w) (negligible_add hkg hkerr)

/-- **Rw-Equiv** (CCS26 Fig. 3), for a right side of Boolean or base type: `u₂ ⊬ v₂` and
`u₁, v₁ ∼ u₂, v₂` give `u₁ ⊬ v₁`, by the reduction `Machine.deduce`. -/
theorem NonDed.rwEquiv (hβ : β.IsGround) {u₁ u₂ : VecRV M τs} {v₁ v₂ : RV M β}
    (h : C.NonDed u₂ v₂) (h' : C.Indist (VecRV.snoc u₁ v₁) (VecRV.snoc u₂ v₂)) :
    C.NonDed u₁ v₁ := fun g hg =>
  negligible_of_le (deduceAdv_le_add_advantage hβ g u₁ u₂ v₁ v₂)
    (negligible_add (h g hg) (h' _ (C.deduce_mem hβ hg)))

end AdvClass

end SquirrelLogic
