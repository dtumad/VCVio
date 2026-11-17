/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import SquirrelLogic.RandomVariable
public import VCVio.CryptoFoundations.Asymptotics.Negligible
public import ToMathlib.Data.ENNReal.AbsDiff
import VCVio.EvalDist.ProbabilityBounds

/-!
# Indistinguishability over a class of distinguishers

LICS23's `u⃗ ∼ v⃗` (§II-C) says that no polynomial-time machine tells the two vectors apart. The
machines read the attacker tape `ρa`, and their inputs at `η` are values of `⟦τ⟧_η`, whose type
depends on `η`. Here:

* `Vals M η τs` is a vector of values at `η`, an environment over the types `τs`;
  `VecRV M τs` is a vector of random variables;
* `Distinguisher M τs` tests a vector of values at each `η`, reading `ρa`;
* `advantage A u v η` is `|Pr[A(u) = 1] − Pr[A(v) = 1]|` over uniform tapes;
* `AdvClass M` is the class of admitted machines, a parameter. `C.Indist u v` says every admitted
  distinguisher has negligible advantage, and `C.Adv X` says an admitted attacker computation
  equals `X` everywhere.

Each structural rule about `∼` reduces an adversary against its conclusion to adversaries against
its premises, and the reductions are named. Five of them (`Distinguisher.app`, `.fn`, `.adv`,
`.ite`, `.rename`) change a vector before running the given distinguisher, and the advantage is
unchanged at every `η`. The case split (`Indist.caseStudy`, with BC14's If1 as `Indist.if1`) uses
`Distinguisher.guard true` and `.guard false`, which run the distinguisher only when a Boolean
first entry has the given value, and at every `η` the advantage is at most the sum of theirs
(`advantage_cons_cond_le`). These are the concrete statements. `AdvClass` carries one closure
field per reduction shape, used only by the rules that need that shape.

The rules for the secrecy predicates `⊬` and `▷` (`SquirrelLogic.Secrecy`) add two shapes, each
an operation a machine performs: running one attacker function after another on the shared tape
`ρa` (`AttackerFn.comp`), and testing two values for equality (`Distinguisher.eqTest`).

The empty class meets every closure field, and then `Indist` holds of any two vectors: a statement
`C.Indist u v` is exactly as strong as `C`. `AdvClass.all` admits every distinguisher.
-/

public section

namespace SquirrelLogic

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B} {M : Model D}

/-- A vector of values of the types `τs` at `η`. -/
abbrev Vals (M : Model D) (η : ℕ) (τs : List (Ty B)) : Type := Env (Ty.Value M.carrier η) τs

/-- A vector of random variables of the types `τs`. -/
abbrev VecRV (M : Model D) (τs : List (Ty B)) : Type := (η : ℕ) → M.Tape η → Vals M η τs

/-- A distinguisher of vectors of the types `τs`: a test at each `η` that reads the attacker
tape. -/
abbrev Distinguisher (M : Model D) (τs : List (Ty B)) : Type :=
  (η : ℕ) → Vals M η τs → M.TapeA η → Bool

/-- An attacker computation of a value of type `τ` from the attacker tape. -/
abbrev AttackerFn (M : Model D) (τ : Ty B) : Type := (η : ℕ) → M.TapeA η → τ.Value M.carrier η

variable {η : ℕ} {a b τ : Ty B} {τs : List (Ty B)}

/-- Drop the first entry of a vector. -/
@[expose] def Vals.tail (e : Vals M η (τ :: τs)) : Vals M η τs := fun _ x => e _ (.succ x)

/-! ## Named reductions -/

namespace AttackerFn

/-- Post-composition of an attacker function of the tuple `τs` with an attacker function `k`,
both reading the same attacker tape: the reduction of Trans, WeakL and WeakR (CCS26 Fig. 3). -/
@[expose] def comp {τs : List (Ty B)} {β γ : Ty B} (k : AttackerFn M (.arrow β γ))
    (f : AttackerFn M (Ty.arrows τs β)) : AttackerFn M (Ty.arrows τs γ) :=
  fun η ρa => Ty.postcomp (k η ρa) (f η ρa)

end AttackerFn


namespace Distinguisher

/-- The reduction for FA-App: apply the first entry to the second, then test. -/
@[expose] def app (A : Distinguisher M (b :: τs)) : Distinguisher M (.arrow a b :: a :: τs) :=
  fun η e ρa => A η (Env.cons (e _ .zero (e _ (.succ .zero))) e.tail.tail) ρa

/-- The reduction for FA-Fn: prepend the value of an honest symbol, then test. -/
@[expose] def fn (f : D.Fn τ) (A : Distinguisher M (τ :: τs)) : Distinguisher M τs :=
  fun η e ρa => A η (Env.cons (M.fn η f) e) ρa

/-- The reduction for FA-Adv: prepend an attacker computation run on the same attacker tape,
then test. -/
@[expose] def adv (g : AttackerFn M τ) (A : Distinguisher M (τ :: τs)) : Distinguisher M τs :=
  fun η e ρa => A η (Env.cons (g η ρa) e) ρa

/-- The reduction for If: evaluate a conditional from the first three entries. -/
@[expose] def ite (A : Distinguisher M (a :: τs)) : Distinguisher M (.bool :: a :: a :: τs) :=
  fun η e ρa => A η
    (Env.cons (cond (e _ .zero) (e _ (.succ .zero)) (e _ (.succ (.succ .zero)))) e.tail.tail.tail)
    ρa

/-- The reduction for Perm: reindex the vector along a map of positions that preserves types
(PolyFun's `Renaming`). Permutation, projection and duplication are instances. -/
@[expose] def rename {τs' : List (Ty B)} (r : Renaming τs' τs) (A : Distinguisher M τs') :
    Distinguisher M τs :=
  fun η e ρa => A η (Env.rename r e) ρa

/-- The reduction for the case split: when the Boolean first entry is `c`, test the rest;
otherwise return `false`. The two halves of a case split on `b` are `guard true`, which is
`b && A(v⃗)`, and `guard false`, which is `!b && A(v⃗)`. -/
@[expose] def guard (c : Bool) (A : Distinguisher M τs) : Distinguisher M (.bool :: τs) :=
  fun η e ρa => (e _ .zero == c) && A η e.tail ρa

/-- The test whether two values are equal: the base of the distinguisher of Rw-Equiv
(CCS26 Fig. 3), which applies an attacker function to the left part of a vector and tests the
result against the last entry. -/
@[expose] noncomputable def eqTest (β : Ty B) : Distinguisher M [β, β] :=
  fun _ e _ => @decide (e _ .zero = e _ (.succ .zero)) (Classical.propDecidable _)

end Distinguisher

/-- The advantage of a distinguisher between two vectors at `η`, over uniform tapes. -/
@[expose] noncomputable def advantage (A : Distinguisher M τs) (u v : VecRV M τs) (η : ℕ) :
    ENNReal :=
  ENNReal.absDiff (Pr{let ρ ← $ᵗ (M.Tape η)}[A η (u η ρ) ρ.1 = true])
    (Pr{let ρ ← $ᵗ (M.Tape η)}[A η (v η ρ) ρ.1 = true])

/-! ## The class of machines -/

/-- The machines of a model: attacker computations for `adv`, distinguishers for `∼`, and one
closure field for each reduction shape of the structural rules about `∼`, `⊬` and `▷`. -/
structure AdvClass (M : Model D) where
  /-- Admitted attacker computations. -/
  computes : {τ : Ty B} → AttackerFn M τ → Prop
  /-- Admitted distinguishers. -/
  distinguishes : {τs : List (Ty B)} → Distinguisher M τs → Prop
  /-- FA-App (`Valid.equiv_app`). -/
  app_mem {a b : Ty B} {τs : List (Ty B)} {A : Distinguisher M (b :: τs)} :
    distinguishes A → distinguishes (A.app (a := a))
  /-- FA-Fn (`Valid.equiv_fn`). -/
  fn_mem {τ : Ty B} {τs : List (Ty B)} (f : D.Fn τ) {A : Distinguisher M (τ :: τs)} :
    distinguishes A → distinguishes (A.fn f)
  /-- FA-Adv (`Valid.equiv_adv`). -/
  adv_mem {τ : Ty B} {τs : List (Ty B)} {g : AttackerFn M τ} {A : Distinguisher M (τ :: τs)} :
    computes g → distinguishes A → distinguishes (A.adv g)
  /-- If (`Valid.equiv_ite`). -/
  ite_mem {a : Ty B} {τs : List (Ty B)} {A : Distinguisher M (a :: τs)} :
    distinguishes A → distinguishes A.ite
  /-- Perm, Restr and Dup: every reindexing of a vector (`Valid.equiv_rename`,
  `Valid.equiv_tail`, `Valid.equiv_dup`). -/
  rename_mem {τs τs' : List (Ty B)} (r : Renaming τs' τs) {A : Distinguisher M τs'} :
    distinguishes A → distinguishes (A.rename r)
  /-- The case split (`Valid.equiv_caseStudy`, `Valid.equiv_if1`). The other reductions only
  change the vector before running `A`, so they map constant distinguishers to constant ones,
  and `guard` does not: this field does not follow from the others
  (`CaseStudy.guard_not_derivable`). -/
  guard_mem {τs : List (Ty B)} (c : Bool) {A : Distinguisher M τs} :
    distinguishes A → distinguishes (A.guard c)
  /-- Trans, WeakL and WeakR for `⊬` and `▷` (`AdvClass.Ded.trans`, `AdvClass.NonDed.weakL`,
  `AdvClass.NonDed.weakR`): post-composing an admitted attacker function of a tuple with an
  admitted attacker function, both reading the shared attacker tape, is admitted. A
  polynomial-time class has it, as it has sequential composition (cslib-frontier's
  `IsPPTOn.bind`); a uniform one does. -/
  comp_mem {τs : List (Ty B)} {β γ : Ty B} {k : AttackerFn M (.arrow β γ)}
    {f : AttackerFn M (Ty.arrows τs β)} : computes k → computes f → computes (k.comp f)
  /-- Rw-Equiv (`AdvClass.NonDed.rwEquiv`): the equality test at a Boolean or base type. A
  polynomial-time class has it, uniform or not, since values of these types are bitstrings
  (cslib-frontier's `decide_eq`). It is not asked at arrow types, whose equality no machine
  tests. -/
  eqTest_mem {β : Ty B} : β.IsGround → distinguishes (Distinguisher.eqTest β)

namespace AdvClass

/-- Every machine. -/
@[expose] def all (M : Model D) : AdvClass M where
  computes _ := True
  distinguishes _ := True
  app_mem _ := trivial
  fn_mem := by intros; trivial
  adv_mem := by intros; trivial
  ite_mem _ := trivial
  rename_mem := by intros; trivial
  guard_mem := by intros; trivial
  comp_mem _ _ := trivial
  eqTest_mem _ := trivial

/-- `adv t` (LICS23 Fig. 2): an admitted attacker computation agrees with `t` everywhere. -/
@[expose] def Adv (C : AdvClass M) (X : RV M τ) : Prop :=
  ∃ g, C.computes g ∧ ∀ η ρ, X η ρ = g η ρ.1

/-- `u⃗ ∼ v⃗` (LICS23 Fig. 2): every admitted distinguisher has negligible advantage. -/
@[expose] def Indist (C : AdvClass M) (u v : VecRV M τs) : Prop :=
  ∀ A, C.distinguishes A → negligible (advantage A u v)

end AdvClass

/-! ## Laws of indistinguishability -/

namespace VecRV

/-- FA-App on vectors: the first entry applied to the second. -/
@[expose] def app (u : VecRV M (.arrow a b :: a :: τs)) : VecRV M (b :: τs) :=
  fun η ρ => Env.cons (u η ρ _ .zero (u η ρ _ (.succ .zero))) (u η ρ).tail.tail

/-- Prepend a random variable. -/
@[expose] def cons (X : RV M τ) (u : VecRV M τs) : VecRV M (τ :: τs) :=
  fun η ρ => Env.cons (X η ρ) (u η ρ)

/-- Drop the first entry. -/
@[expose] def tail (u : VecRV M (τ :: τs)) : VecRV M τs := fun η ρ => (u η ρ).tail

/-- Duplicate the first entry. -/
@[expose] def dup (u : VecRV M (τ :: τs)) : VecRV M (τ :: τ :: τs) :=
  fun η ρ => Env.cons (u η ρ _ .zero) (u η ρ)

/-- The conditional of the first three entries. -/
@[expose] def ite (u : VecRV M (.bool :: a :: a :: τs)) : VecRV M (a :: τs) :=
  fun η ρ => Env.cons (cond (u η ρ _ .zero) (u η ρ _ (.succ .zero)) (u η ρ _ (.succ (.succ .zero))))
    (u η ρ).tail.tail.tail

/-- Reindex along a map of positions. -/
@[expose] def rename {τs' : List (Ty B)} (r : Renaming τs' τs) (u : VecRV M τs) : VecRV M τs' :=
  fun η ρ => Env.rename r (u η ρ)

end VecRV

/-! ## Concrete statements: each reduction keeps or bounds the advantage at every `η` -/

section Reductions

variable (A : Distinguisher M τs)

theorem advantage_app (A : Distinguisher M (b :: τs)) (u v : VecRV M (.arrow a b :: a :: τs)) :
    advantage A u.app v.app = advantage A.app u v := rfl

theorem advantage_fn (f : D.Fn τ) (A : Distinguisher M (τ :: τs)) (u v : VecRV M τs) :
    advantage A (VecRV.cons (fun η _ => M.fn η f) u) (VecRV.cons (fun η _ => M.fn η f) v) =
      advantage (A.fn f) u v := rfl

theorem advantage_adv (g : AttackerFn M τ) (A : Distinguisher M (τ :: τs)) (u v : VecRV M τs) :
    advantage A (VecRV.cons (fun η ρ => g η ρ.1) u) (VecRV.cons (fun η ρ => g η ρ.1) v) =
      advantage (A.adv g) u v := rfl

theorem advantage_ite (A : Distinguisher M (a :: τs)) (u v : VecRV M (.bool :: a :: a :: τs)) :
    advantage A u.ite v.ite = advantage A.ite u v := rfl

theorem advantage_rename {τs' : List (Ty B)} (r : Renaming τs' τs) (A : Distinguisher M τs')
    (u v : VecRV M τs) : advantage A (u.rename r) (v.rename r) = advantage (A.rename r) u v := rfl

/-- Changing a vector where it is rarely different changes an advantage by at most the
probability that it differs. -/
theorem advantage_le_add_prEvent_ne (u u' v : VecRV M τs) (η : ℕ) :
    advantage A u v η ≤
      advantage A u' v η + Pr{let ρ ← $ᵗ (M.Tape η)}[u η ρ ≠ u' η ρ] := by
  have step : ∀ x y : VecRV M τs, (∀ ρ, x η ρ ≠ y η ρ → u η ρ ≠ u' η ρ) →
      Pr{let ρ ← $ᵗ (M.Tape η)}[A η (x η ρ) ρ.1 = true] ≤
        Pr{let ρ ← $ᵗ (M.Tape η)}[A η (y η ρ) ρ.1 = true] +
          Pr{let ρ ← $ᵗ (M.Tape η)}[u η ρ ≠ u' η ρ] := fun x y hxy =>
    (prEvent_le_prEvent_add_prEvent_and_not _ _ _).trans (add_le_add le_rfl
      (prEvent_mono _ _ _ fun ρ h => hxy ρ fun he => h.2 (he ▸ h.1)))
  refine (ENNReal.absDiff_triangle _
    (Pr{let ρ ← $ᵗ (M.Tape η)}[A η (u' η ρ) ρ.1 = true]) _).trans ?_
  rw [add_comm (advantage A u' v η)]
  exact add_le_add (ENNReal.absDiff_le_iff.2
    ⟨step u u' fun _ => id, step u' u fun _ h he => h he.symm⟩) le_rfl

/-- `absDiff` is subadditive along sums. -/
private theorem absDiff_add_add_le (a b c d : ENNReal) :
    ENNReal.absDiff (a + b) (c + d) ≤ ENNReal.absDiff a c + ENNReal.absDiff b d := by
  obtain ⟨hac, hca⟩ := ENNReal.absDiff_le_iff.1 (le_refl (ENNReal.absDiff a c))
  obtain ⟨hbd, hdb⟩ := ENNReal.absDiff_le_iff.1 (le_refl (ENNReal.absDiff b d))
  exact ENNReal.absDiff_le_iff.2 ⟨(add_le_add hac hbd).trans_eq (add_add_add_comm _ _ _ _),
    (add_le_add hca hdb).trans_eq (add_add_add_comm _ _ _ _)⟩

/-- A test of a conditional splits along its condition:
`Pr[A(if b then x else y, u⃗)] = Pr[b ∧ A(x, u⃗)] + Pr[¬b ∧ A(y, u⃗)]`. -/
private theorem prEvent_cons_cond (A : Distinguisher M (a :: τs)) (b : RV M .bool)
    (x y : RV M a) (u : VecRV M τs) (η : ℕ) :
    Pr{let ρ ← $ᵗ (M.Tape η)}[A η (VecRV.cons (fun η ρ => cond (b η ρ) (x η ρ) (y η ρ)) u η ρ)
        ρ.1 = true] =
      Pr{let ρ ← $ᵗ (M.Tape η)}[A.guard true η (VecRV.cons b (VecRV.cons x u) η ρ) ρ.1 =
        true] +
      Pr{let ρ ← $ᵗ (M.Tape η)}[A.guard false η (VecRV.cons b (VecRV.cons y u) η ρ) ρ.1 =
        true] := by
  rw [prEvent_eq_prEvent_and_add_prEvent_and_not _ _ fun ρ => b η ρ = true]
  congr 1 <;> refine prEvent_congr _ _ _ fun ρ => ?_ <;>
    simp only [VecRV.cons, Distinguisher.guard] <;> cases b η ρ <;> simp <;> rfl

/-- The case split at one `η`: the advantage against two conditionals is at most the sum of the
advantages of the named reductions `A.guard true` and `A.guard false` against the two premises.
The factor is one. -/
theorem advantage_cons_cond_le (A : Distinguisher M (a :: τs)) (b b' : RV M .bool)
    (x y x' y' : RV M a) (u v : VecRV M τs) (η : ℕ) :
    advantage A (VecRV.cons (fun η ρ => cond (b η ρ) (x η ρ) (y η ρ)) u)
        (VecRV.cons (fun η ρ => cond (b' η ρ) (x' η ρ) (y' η ρ)) v) η ≤
      advantage (A.guard true) (VecRV.cons b (VecRV.cons x u))
          (VecRV.cons b' (VecRV.cons x' v)) η +
        advantage (A.guard false) (VecRV.cons b (VecRV.cons y u))
          (VecRV.cons b' (VecRV.cons y' v)) η := by
  simp only [advantage, prEvent_cons_cond]
  exact absDiff_add_add_le _ _ _ _

end Reductions

namespace AdvClass

variable {C : AdvClass M} {u v w : VecRV M τs}

/-- Refl. -/
theorem Indist.refl (u : VecRV M τs) : C.Indist u u :=
  fun _ _ => negligible_of_zero fun _ => ENNReal.absDiff_self _

/-- Sym. -/
theorem Indist.symm (h : C.Indist u v) : C.Indist v u :=
  fun A hA => negligible_of_le (fun _ => le_of_eq (ENNReal.absDiff_comm _ _)) (h A hA)

/-- Trans: the advantage against the ends is at most the sum of the two advantages. -/
theorem Indist.trans (h₁ : C.Indist u v) (h₂ : C.Indist v w) : C.Indist u w :=
  fun A hA => negligible_of_le (fun _ => ENNReal.absDiff_triangle _ _ _)
    (negligible_add (h₁ A hA) (h₂ A hA))

/-- FA-App, by the reduction `Distinguisher.app`. -/
theorem Indist.app {u v : VecRV M (.arrow a b :: a :: τs)} (h : C.Indist u v) :
    C.Indist u.app v.app := fun A hA => by
  rw [advantage_app]
  exact h A.app (C.app_mem hA)

/-- FA-Fn, by the reduction `Distinguisher.fn`. -/
theorem Indist.fn (f : D.Fn τ) (h : C.Indist u v) :
    C.Indist (VecRV.cons (fun η _ => M.fn η f) u) (VecRV.cons (fun η _ => M.fn η f) v) :=
  fun A hA => by
  rw [advantage_fn]
  exact h (A.fn f) (C.fn_mem f hA)

/-- FA-Adv, by the reduction `Distinguisher.adv` at the attacker computation that `adv`
provides. -/
theorem Indist.adv {X : RV M τ} (hX : C.Adv X) (h : C.Indist u v) :
    C.Indist (VecRV.cons X u) (VecRV.cons X v) := by
  obtain ⟨g, hg, hXg⟩ := hX
  obtain rfl : X = fun η ρ => g η ρ.1 := funext fun η => funext (hXg η)
  intro A hA
  rw [advantage_adv]
  exact h (A.adv g) (C.adv_mem hg hA)

/-- If, by the reduction `Distinguisher.ite`. -/
theorem Indist.ite {u v : VecRV M (.bool :: a :: a :: τs)} (h : C.Indist u v) :
    C.Indist u.ite v.ite := fun A hA => by
  rw [advantage_ite]
  exact h A.ite (C.ite_mem hA)

/-- Perm, by the reduction `Distinguisher.rename`. -/
theorem Indist.rename {τs' : List (Ty B)} (r : Renaming τs' τs) (h : C.Indist u v) :
    C.Indist (u.rename r) (v.rename r) := fun A hA => by
  rw [advantage_rename]
  exact h (A.rename r) (C.rename_mem r hA)

/-- Restr: `Distinguisher.rename` at the renaming that skips the first position. -/
theorem Indist.tail {u v : VecRV M (τ :: τs)} (h : C.Indist u v) : C.Indist u.tail v.tail :=
  h.rename fun _ x => .succ x

/-- Dup: `Distinguisher.rename` at the renaming that repeats the first position. -/
theorem Indist.dup {u v : VecRV M (τ :: τs)} (h : C.Indist u v) : C.Indist u.dup v.dup := by
  have hu : ∀ w : VecRV M (τ :: τs),
      w.dup = w.rename (Env.cons .zero fun _ x => x : Renaming (τ :: τ :: τs) (τ :: τs)) :=
    fun w => by funext η ρ σ x; cases x <;> rfl
  rw [hu u, hu v]
  exact h.rename _

/-- Case split (LICS23's G.Case-Study:ITE), by the reductions `Distinguisher.guard true` and
`Distinguisher.guard false`: if `b, x, u⃗ ∼ b', x', v⃗` and `b, y, u⃗ ∼ b', y', v⃗`, then
`if b then x else y, u⃗ ∼ if b' then x' else y', v⃗`. -/
theorem Indist.caseStudy {b b' : RV M .bool} {x y x' y' : RV M a} {u v : VecRV M τs}
    (h₁ : C.Indist (VecRV.cons b (VecRV.cons x u)) (VecRV.cons b' (VecRV.cons x' v)))
    (h₂ : C.Indist (VecRV.cons b (VecRV.cons y u)) (VecRV.cons b' (VecRV.cons y' v))) :
    C.Indist (VecRV.cons (fun η ρ => cond (b η ρ) (x η ρ) (y η ρ)) u)
      (VecRV.cons (fun η ρ => cond (b' η ρ) (x' η ρ) (y' η ρ)) v) := fun A hA =>
  negligible_of_le (advantage_cons_cond_le A b b' x y x' y' u v)
    (negligible_add (h₁ (A.guard true) (C.guard_mem true hA))
      (h₂ (A.guard false) (C.guard_mem false hA)))

/-- BC14's If1, from the case split with both right-hand branches `z`: if `b, x, u⃗ ∼ b', z, v⃗`
and `b, y, u⃗ ∼ b', z, v⃗`, then `if b then x else y, u⃗ ∼ z, v⃗`. -/
theorem Indist.if1 {b b' : RV M .bool} {x y z : RV M a} {u v : VecRV M τs}
    (h₁ : C.Indist (VecRV.cons b (VecRV.cons x u)) (VecRV.cons b' (VecRV.cons z v)))
    (h₂ : C.Indist (VecRV.cons b (VecRV.cons y u)) (VecRV.cons b' (VecRV.cons z v))) :
    C.Indist (VecRV.cons (fun η ρ => cond (b η ρ) (x η ρ) (y η ρ)) u) (VecRV.cons z v) := by
  simpa only [Bool.cond_self] using h₁.caseStudy h₂

/-- Rewriting under an overwhelming equality: if `u` and `u'` differ with negligible probability,
`u` is indistinguishable from whatever `u'` is. -/
theorem Indist.of_negligible_ne {u' : VecRV M τs}
    (hne : negligible fun η => Pr{let ρ ← $ᵗ (M.Tape η)}[u η ρ ≠ u' η ρ]) (h : C.Indist u' v) :
    C.Indist u v :=
  fun A hA => negligible_of_le (fun η => advantage_le_add_prEvent_ne A u u' v η)
    (negligible_add (h A hA) hne)

end AdvClass

end SquirrelLogic
