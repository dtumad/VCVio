/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import SquirrelLogic.Examples
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Reusing encryption randomness: a countermodel

Encryption rules (BC14 CCA1, SP21 ENC-KP, LICS23) require the randomness of the challenge
ciphertext to be fresh: it occurs nowhere else in the vectors. This file shows the condition is
needed, in a model where the scheme is perfectly secure for one use.

The scheme is the one-bit pad `enc m r = m xor r`, with the pad a name `r` read from a uniform
honest tape bit. Then:

* `TwoTimePad.valid_fresh`: `enc false r ∼ enc true r` holds against every class of
  distinguishers (the pad is fresh);
* `TwoTimePad.not_valid_reuse`: `enc false r, enc false r ∼ enc true r, enc false r` fails
  against the class of all distinguishers (the pad is reused): testing the two entries for
  equality has advantage one.
-/

public section

namespace SquirrelLogic.TwoTimePad

open IPFunctor IPFunctor.ScopedSignature

/-- One name, the pad, indexed by a Boolean. -/
inductive Name : Ty Empty → Ty Empty → Type where
  /-- The pad `r : bool → bool`. -/
  | r : Name .bool .bool

/-- No base types, the pad, one honest symbol (the encryption `bool → bool → bool`) and no
attacker symbols. -/
@[expose] def decl : Decl Empty where
  labels b := b.elim
  Name := Name
  nameDom_finite n := match n with | .r => trivial
  Fn := Unit
  fnTy _ := .arrow .bool (.arrow .bool .bool)
  Att := Empty
  attTy f := f.elim

/-- The pad reads the honest tape, one uniform bit; encryption is `xor`. -/
@[expose] noncomputable def model : Model decl where
  TapeA _ := Unit
  TapeH _ := Bool
  carrier b := b.elim
  nonempty b := b.elim
  name _ := fun {_ _} n => match n with | .r => fun _ ρh => ρh
  fn _ _ := fun m k => xor m k
  att _ f := f.elim

theorem model_respectsLabels : model.RespectsLabels := fun b => b.elim

/-- The pad at index `false`. -/
@[expose] def pad : FTerm decl [] .bool :=
  FTerm.app (.node (.inl (.name Name.r)) fun p => nomatch p) FTerm.ff

/-- Encryption of a message under the pad. -/
@[expose] def enc (m : FTerm decl [] .bool) : FTerm decl [] .bool :=
  FTerm.app (FTerm.app (FTerm.fn ()) m) pad

theorem denote_enc (C : AdvClass model) (m : FTerm decl [] .bool) (env : Env (Kind.Value model) [])
    (η : ℕ) (ρ : model.Tape η) :
    (enc m).denote (fullInterp model C) env η ρ =
      xor (m.denote (fullInterp model C) env η ρ) ρ.2 := rfl

/-- With a fresh pad, the two encryptions are indistinguishable for every class: flipping the
tape bit maps one to the other. -/
theorem valid_fresh (C : ∀ M : Model decl, AdvClass M) :
    Valid (fun M => M = model) C (Γ := []) []
      (.equiv (Env.cons (enc .ff) Env.empty) (Env.cons (enc .tt) Env.empty)) := by
  rintro M - rfl env -
  refine Form.holds_equiv.2 fun A _ => negligible_of_zero fun η => ENNReal.absDiff_eq_zero.2 ?_
  have he : ∀ ρ, Vec.rv model (C model) (Env.empty : Vec decl [] []) env η ρ = Env.empty :=
    fun _ => Env.eq_empty _
  simp only [Vec.rv_cons, VecRV.cons, denote_enc, FTerm.denote_tt, FTerm.denote_ff, he]
  let flip : model.TapeH η ≃ model.TapeH η := ⟨not, not, Bool.not_not, Bool.not_not⟩
  refine Eq.trans ?_ (SampleableType.prEvent_uniformSample_equiv ((Equiv.refl _).prodCongr flip) _)
  refine prEvent_congr _ _ _ fun ρ => ?_
  obtain ⟨a, b⟩ := ρ
  cases b <;> rfl

/-- With the pad reused, testing the two entries for equality tells the vectors apart with
advantage one. -/
theorem not_valid_reuse :
    ¬ Valid (fun M => M = model) (fun M => AdvClass.all M) (Γ := []) []
      (.equiv (Env.cons (enc .ff) (Env.cons (enc .ff) Env.empty))
        (Env.cons (enc .tt) (Env.cons (enc .ff) Env.empty))) := fun h => by
  have hM := Form.holds_equiv.1 (h model model_respectsLabels rfl Env.empty (by simp))
    (fun _ e _ => decide (e _ .zero = e _ (.succ .zero))) trivial
  refine not_negligible_one (negligible_of_le (fun η => le_of_eq ?_) hM)
  simp only [advantage, Vec.rv_cons, VecRV.cons, Env.cons_zero, Env.cons_succ, denote_enc,
    FTerm.denote_tt, FTerm.denote_ff, decide_true, decide_eq_true_eq]
  rw [OracleComp.prEvent_true_eq_one, prEvent_eq_zero_of_forall_not _ _ fun ρ h => by
    obtain ⟨_, b⟩ := ρ; revert h; cases b <;> exact fun h => Bool.noConfusion h,
    ENNReal.absDiff_zero_right]

end SquirrelLogic.TwoTimePad
