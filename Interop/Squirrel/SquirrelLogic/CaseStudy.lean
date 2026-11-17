/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import SquirrelLogic.Derivation
public import SquirrelLogic.TwoTimePad
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Checks of the case split

Checks of `Valid.equiv_caseStudy` and BC14's If1 (`Valid.equiv_if1`). The model is the one of
`SquirrelLogic.TwoTimePad`: the pads `r` and `s` read independent uniform bits, and
`enc m = m xor r`. The condition `parity` is `enc s`, which is `s xor r`.

* `valid_flip`: `parity, r ∼ parity, enc true` holds against every class. Flipping both bits
  keeps `parity` and maps `r` to `enc true`, which is `!r`.
* `valid_if1_flip`: If1 applies with a random condition that both branches depend on. Its first
  premise is Refl and its second `valid_flip`; the conclusion is
  `if parity then enc true else r ∼ enc true`, whose left side is the pad `s`
  (`denote_ite_parity`). `if1Derivation` is the same conclusion as a derivation from the
  hypothesis `valid_flip`, and `if1Derivation_sound` closes it.
* `caseStudy_needs_condition`: the tempting variant whose premises leave out the condition,
  `x ∼ z` and `y ∼ z`, is unsound. With `x = z = enc false = r`, `y = enc true = !r` and the
  condition `r`, both premises hold and the conclusion fails: `if r then r else !r` is always
  `true`, and returning the entry has advantage one half against `r`. The condition must sit
  beside each branch, because the reductions `guard true` and `guard false` read it.
* `if1_needs_second`, `if1_needs_first`: in every model of every declaration, against all
  distinguishers, one premise holds by Refl at an instance whose conclusion is `true ∼ false`.
  So neither premise may be dropped.
* `guard_not_derivable`: the constant-`true` distinguishers are closed under the reductions
  `app`, `fn`, `adv`, `ite` and `rename`, and not under `guard true`. So `AdvClass.guard_mem`
  does not follow from the other closure fields.
-/

public section

namespace SquirrelLogic.CaseStudy

open IPFunctor IPFunctor.ScopedSignature TwoTimePad

/-- The coordinate the pad `s` reads at index `false`. -/
abbrev slotS (η : ℕ) : model.Slot η := ⟨⟨.bool, .bool, Name.s⟩, false⟩

/-- Flipping every bit of the honest tape. -/
private def flipTape (η : ℕ) : model.TapeH η ≃ model.TapeH η :=
  ⟨fun ρh k => !ρh k, fun ρh k => !ρh k, fun _ => funext fun _ => Bool.not_not _,
    fun _ => funext fun _ => Bool.not_not _⟩

/-- The condition `enc s`, which is `s xor r`. -/
@[expose] def parity : FTerm decl [] .bool := enc (pad .s)

/-- The second premise of `valid_if1_flip`: `parity, r ∼ parity, enc true`. -/
@[expose] def flipForm : Form decl [] :=
  .equiv (Env.cons parity (Env.cons (pad .r) Env.empty))
    (Env.cons parity (Env.cons (enc .tt) Env.empty))

/-- The conclusion of `valid_if1_flip`: `if parity then enc true else r ∼ enc true`. -/
@[expose] def if1Form : Form decl [] :=
  .equiv (Env.cons (FTerm.ite parity (enc .tt) (pad .r)) Env.empty) (Env.cons (enc .tt) Env.empty)

/-- `parity, r ∼ parity, enc true` holds against every class: flipping both bits of the tape keeps
`s xor r` and maps `r` to `!r`. -/
theorem valid_flip (C : ∀ M : Model decl, AdvClass M) :
    Valid (fun M => M = model) C (Γ := []) [] flipForm := by
  rintro M - rfl env -
  refine Form.holds_equiv.2 fun A _ => negligible_of_zero fun η => ENNReal.absDiff_eq_zero.2 ?_
  have he : ∀ ρ, Vec.rv model (C model) (Env.empty : Vec decl [] []) env η ρ = Env.empty :=
    fun _ => Env.eq_empty _
  simp only [Vec.rv_cons, VecRV.cons, he]
  refine Eq.trans ?_
    (SampleableType.prEvent_uniformSample_equiv ((Equiv.refl _).prodCongr (flipTape η)) _)
  refine prEvent_congr _ _ _ fun ρ => ?_
  change A η (Env.cons (xor (ρ.2 (slotS η)) (ρ.2 (slotR η))) (Env.cons (ρ.2 (slotR η)) Env.empty))
      ρ.1 = true ↔
    A η (Env.cons (xor (!ρ.2 (slotS η)) (!ρ.2 (slotR η)))
      (Env.cons (xor true (!ρ.2 (slotR η))) Env.empty)) ρ.1 = true
  cases ρ.2 (slotR η) <;> cases ρ.2 (slotS η) <;> rfl

/-- If1 at a random condition that both branches depend on: the first premise is Refl, the second
is `valid_flip`. -/
theorem valid_if1_flip (C : ∀ M : Model decl, AdvClass M) :
    Valid (fun M => M = model) C (Γ := []) [] if1Form :=
  Valid.equiv_if1 (Valid.equiv_refl _) (valid_flip C)

/-- The left side of `if1Form` is the pad `s`, and its right side `enc true` is `!r`: the two
sides are different random variables. -/
theorem denote_ite_parity (C : AdvClass model) (env : Env (Kind.Value model) []) (η : ℕ)
    (ρ : model.Tape η) :
    (FTerm.ite parity (enc .tt) (pad .r)).denote (fullInterp model C) env η ρ = ρ.2 (slotS η) := by
  change cond (xor (ρ.2 (slotS η)) (ρ.2 (slotR η))) (xor true (ρ.2 (slotR η))) (ρ.2 (slotR η)) =
    ρ.2 (slotS η)
  cases ρ.2 (slotR η) <;> cases ρ.2 (slotS η) <;> rfl

/-- `valid_if1_flip` as a one-step derivation from the hypothesis `flipForm`. -/
@[expose] def if1Derivation : Derivation decl (fun _ => False) [flipForm] if1Form :=
  .equivIf1 (.equivRefl _) (.ax List.mem_cons_self)

/-- `Derivation.sound` applies to `if1Derivation`, and `valid_flip` discharges its hypothesis. -/
theorem if1Derivation_sound (C : ∀ M : Model decl, AdvClass M) :
    Valid (fun M => M = model) C (Γ := []) [] if1Form :=
  (valid_flip C).cut (if1Derivation.sound _ C fun _ h => h.elim)

/-- Twice the probability that the pad `r` is `true` is one. -/
private theorem prEvent_padR_add_self (η : ℕ) :
    Pr{let ρ ← $ᵗ (model.Tape η)}[ρ.2 (slotR η) = true] +
      Pr{let ρ ← $ᵗ (model.Tape η)}[ρ.2 (slotR η) = true] = 1 := by
  have hsym : Pr{let ρ ← $ᵗ (model.Tape η)}[ρ.2 (slotR η) = true] =
      Pr{let ρ ← $ᵗ (model.Tape η)}[¬ ρ.2 (slotR η) = true] := by
    refine Eq.trans ?_ (SampleableType.prEvent_uniformSample_equiv
      ((Equiv.refl _).prodCongr (flipTape η)) fun ρ => ¬ ρ.2 (slotR η) = true)
    refine prEvent_congr _ _ _ fun ρ => ?_
    change _ ↔ ¬ (!ρ.2 (slotR η)) = true
    cases ρ.2 (slotR η)
    · simp
    · exact iff_of_true rfl (by simp)
  nth_rw 2 [hsym]
  rw [prEvent_add_prEvent_not_eq_prEvent_true, OracleComp.prEvent_true_eq_one]

/-- The case split needs the condition beside each branch. Without it, the premises
`enc true ∼ enc false` (`TwoTimePad.valid_fresh`) and `enc false ∼ enc false` (Refl) hold, and
`if r then enc false else enc true ∼ enc false` fails against all distinguishers: its left side
is always `true` and its right side is `r`, so returning the entry has advantage one half. -/
theorem caseStudy_needs_condition :
    Valid (fun M => M = model) (fun M => AdvClass.all M) (Γ := []) []
        (.equiv (Env.cons (enc .tt) Env.empty) (Env.cons (enc .ff) Env.empty)) ∧
      ¬ Valid (fun M => M = model) (fun M => AdvClass.all M) (Γ := []) []
        (.equiv (Env.cons (FTerm.ite (pad .r) (enc .ff) (enc .tt)) Env.empty)
          (Env.cons (enc .ff) Env.empty)) := by
  refine ⟨(valid_fresh _).equiv_symm, fun h => ?_⟩
  have hM := Form.holds_equiv.1 (h model model_respectsLabels rfl Env.empty (by simp))
    (fun _ e _ => e _ .zero) trivial
  refine not_negligible_one (negligible_of_le (fun η => ?_)
    (negligible_const_mul hM (c := 2) ENNReal.ofNat_ne_top))
  set p := Pr{let ρ ← $ᵗ (model.Tape η)}[ρ.2 (slotR η) = true] with hp
  have hadv : advantage (fun _ e _ => e _ .zero) (Vec.rv model (AdvClass.all model)
      (Env.cons (FTerm.ite (pad .r) (enc .ff) (enc .tt)) Env.empty) Env.empty)
      (Vec.rv model (AdvClass.all model) (Env.cons (enc .ff) Env.empty) Env.empty) η =
      ENNReal.absDiff 1 p := by
    refine congrArg₂ ENNReal.absDiff ?_ ?_
    · refine (prEvent_congr _ _ (fun _ => True) fun ρ => iff_true_intro ?_).trans
        (OracleComp.prEvent_true_eq_one _)
      change cond (ρ.2 (slotR η)) (xor false (ρ.2 (slotR η))) (xor true (ρ.2 (slotR η))) = true
      cases ρ.2 (slotR η) <;> rfl
    · refine prEvent_congr _ _ _ fun ρ => ?_
      change xor false (ρ.2 (slotR η)) = true ↔ _
      cases ρ.2 (slotR η) <;> rfl
  have hsum := prEvent_padR_add_self η
  rw [← hp] at hsum
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hsum ▸ le_add_self)
  have hle : p ≤ ENNReal.absDiff 1 p := by
    have h1 := (ENNReal.absDiff_le_iff.1 (le_refl (ENNReal.absDiff 1 p))).1
    rw [← hsum] at h1 ⊢
    exact (ENNReal.add_le_add_iff_left hpt).1 h1
  rw [hadv, two_mul]
  exact hsum.symm.le.trans (add_le_add hle hle)

section Countermodels

variable {B : Type} {D : Decl B}

/-- If1 without its second premise is unsound: its first premise `false, false ∼ false, false`
holds by Refl, and its conclusion `if false then false else true ∼ false` fails against all
distinguishers. -/
theorem if1_needs_second :
    Valid (D := D) (fun _ => True) AdvClass.all (Γ := []) []
        (.equiv (Env.cons .ff (Env.cons .ff Env.empty)) (Env.cons .ff (Env.cons .ff Env.empty))) ∧
      ¬ Valid (D := D) (fun _ => True) AdvClass.all (Γ := []) []
        (.equiv (Env.cons (FTerm.ite .ff .ff .tt) Env.empty) (Env.cons .ff Env.empty)) :=
  ⟨Valid.equiv_refl _, fun h => Valid.not_equiv_tt_ff fun M hl hR env hΘ => by
    have hI := Form.holds_equiv.1 (h M hl hR env hΘ)
    simp only [Vec.rv_cons, FTerm.denote_ite, FTerm.denote_ff, FTerm.denote_tt,
      Bool.cond_false] at hI
    simpa only [Form.holds_equiv, Vec.rv_cons, FTerm.denote_tt, FTerm.denote_ff] using hI⟩

/-- If1 without its first premise is unsound: its second premise `true, false ∼ true, false`
holds by Refl, and its conclusion `if true then true else false ∼ false` fails against all
distinguishers. -/
theorem if1_needs_first :
    Valid (D := D) (fun _ => True) AdvClass.all (Γ := []) []
        (.equiv (Env.cons .tt (Env.cons .ff Env.empty)) (Env.cons .tt (Env.cons .ff Env.empty))) ∧
      ¬ Valid (D := D) (fun _ => True) AdvClass.all (Γ := []) []
        (.equiv (Env.cons (FTerm.ite .tt .tt .ff) Env.empty) (Env.cons .ff Env.empty)) :=
  ⟨Valid.equiv_refl _, fun h => Valid.not_equiv_tt_ff fun M hl hR env hΘ => by
    have hI := Form.holds_equiv.1 (h M hl hR env hΘ)
    simp only [Vec.rv_cons, FTerm.denote_ite, FTerm.denote_ff, FTerm.denote_tt,
      Bool.cond_true] at hI
    simpa only [Form.holds_equiv, Vec.rv_cons, FTerm.denote_tt, FTerm.denote_ff] using hI⟩

end Countermodels

/-! ## The closure field for the case split is independent -/

/-- A distinguisher that returns `true` on every input. -/
@[expose] def ConstTrue {τs : List (Ty Empty)} (A : Distinguisher model τs) : Prop :=
  ∀ η e ρa, A η e ρa = true

/-- `AdvClass.guard_mem` does not follow from the other closure fields: the constant-`true`
distinguishers are closed under the reductions `app`, `fn`, `adv`, `ite` and `rename`, which only
change the input, and `guard true` of the constant-`true` distinguisher returns `false` when the
condition is `false`. -/
theorem guard_not_derivable :
    (∀ {a b : Ty Empty} {τs : List (Ty Empty)} {A : Distinguisher model (b :: τs)},
      ConstTrue A → ConstTrue (A.app (a := a))) ∧
    (∀ {τ : Ty Empty} {τs : List (Ty Empty)} (f : decl.Fn τ) {A : Distinguisher model (τ :: τs)},
      ConstTrue A → ConstTrue (A.fn f)) ∧
    (∀ {τ : Ty Empty} {τs : List (Ty Empty)} (g : AttackerFn model τ)
      {A : Distinguisher model (τ :: τs)}, ConstTrue A → ConstTrue (A.adv g)) ∧
    (∀ {a : Ty Empty} {τs : List (Ty Empty)} {A : Distinguisher model (a :: τs)},
      ConstTrue A → ConstTrue A.ite) ∧
    (∀ {τs τs' : List (Ty Empty)} (r : Renaming τs' τs) {A : Distinguisher model τs'},
      ConstTrue A → ConstTrue (A.rename r)) ∧
    ¬ ConstTrue (Distinguisher.guard true (fun _ _ _ => true : Distinguisher model [])) :=
  ⟨fun h _ _ _ => h _ _ _, fun {_ _} _ {_} h _ _ _ => h _ _ _, fun {_ _} _ {_} h _ _ _ => h _ _ _,
    fun h _ _ _ => h _ _ _, fun {_ _} _ {_} h _ _ _ => h _ _ _,
    fun h => Bool.false_ne_true (h 0 (Env.cons false Env.empty : Vals model 0 [.bool]) ())⟩

end SquirrelLogic.CaseStudy
