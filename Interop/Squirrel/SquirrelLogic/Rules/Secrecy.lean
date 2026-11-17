/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import SquirrelLogic.Secrecy

/-!
# The secrecy predicates as global formulas, and their core rules

CCS26 (§3.1, p. 6) defines non-deduction and deduction from the global connectives, with no new
primitive:

* `Form.nonDed u v` is `u⃗ ⊬ v ≜ ∀̃ f. adv(f) ⇒̃ [¬ (f(u⃗) = v)]`;
* `Form.ded u v` is `u⃗ ▷ v ≜ ∃̃ f. adv(f) ∧̃ [f(u⃗) = v]`.

`f` has the curried type `Ty.arrows τs β` and is applied to the vector `u⃗` by `FTerm.apps`.
`Form.holds_nonDed` and `Form.holds_ded` read them as `AdvClass.NonDed` and `AdvClass.Ded`.

The rules of CCS26 Fig. 3 (p. 7) other than Rw-Oracle and Pc-Oracle, which need `adv` at order
two, are `Valid.not_ded` (Neg1), `Valid.not_nonDed` (Neg2), `Valid.box_not_eq` (Ineq),
`Valid.ded_trans` (Trans), `Valid.nonDed_weakL` (WeakL), `Valid.nonDed_weakR` (WeakR) and
`Valid.nonDed_rwEquiv` (Rw-Equiv). A term in the middle of Trans or WeakL is on the right of a
`▷`, so it is a single term, written as the vector `[v]`. `Valid.ded_apps` concludes `u⃗ ▷ f(u⃗)`
from `adv(f)`, the definition of `▷` with its witness. Each rule applies one law of
`SquirrelLogic.Secrecy`, whose proof is an inequality at every `η` with the reduction named.
-/

public section

namespace SquirrelLogic

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B} {Γ : List (Kind B)} {τs : List (Ty B)} {β γ : Ty B}

/-! ## Syntax -/

/-- A term of the curried type `Ty.arrows τs β` applied to a vector of terms of the types
`τs`. -/
@[expose] def FTerm.apps : {τs : List (Ty B)} → FTerm D Γ (Ty.arrows τs β) → Vec D Γ τs →
    FTerm D Γ β
  | [], f, _ => f
  | _ :: _, f, u => FTerm.apps (FTerm.app f (u _ .zero)) fun _ x => u _ (.succ x)

/-- A vector weakened past one binder. -/
@[expose] def Vec.weaken (u : Vec D Γ τs) (s : Kind B) : Vec D (s :: Γ) τs :=
  fun _ x => (u _ x).weaken s

/-- A vector followed by one term: CCS26's `u⃗, v`. -/
@[expose] def Vec.snoc (u : Vec D Γ τs) (v : FTerm D Γ β) : Vec D Γ (τs ++ [β]) :=
  Env.append u (Env.cons v Env.empty)

/-- `u⃗ ⊬ v` (CCS26 §3.1): `∀̃ f. adv(f) ⇒̃ [¬ (f(u⃗) = v)]`. -/
@[expose] def Form.nonDed (u : Vec D Γ τs) (v : FTerm D Γ β) : Form D Γ :=
  .all (Ty.arrows τs β) (.imp (.adv (Term.var .zero))
    (.box (FTerm.not (FTerm.eq (FTerm.apps (Term.var .zero) (u.weaken _)) (v.weaken _)))))

/-- `u⃗ ▷ v` (CCS26 §3.1): `∃̃ f. adv(f) ∧̃ [f(u⃗) = v]`. -/
@[expose] def Form.ded (u : Vec D Γ τs) (v : FTerm D Γ β) : Form D Γ :=
  .ex (Ty.arrows τs β) (.and (.adv (Term.var .zero))
    (.box (FTerm.eq (FTerm.apps (Term.var .zero) (u.weaken _)) (v.weaken _))))

/-! ## Semantics -/

section Reading

variable {M : Model D} {C : AdvClass M} {env : Env (Kind.Value M) Γ}

/-- An application to a vector means the curried function applied to the vector's values. -/
theorem FTerm.denote_apps : ∀ {τs : List (Ty B)} (f : FTerm D Γ (Ty.arrows τs β))
    (u : Vec D Γ τs), (FTerm.apps f u).denote (fullInterp M C) env =
      fun η ρ => Ty.appVals (f.denote (fullInterp M C) env η ρ) (u.rv M C env η ρ)
  | [], _, _ => rfl
  | _ :: _, f, u => FTerm.denote_apps (FTerm.app f (u _ .zero)) _

theorem Vec.rv_weaken {s : Kind B} (u : Vec D Γ τs) (x : s.Value M) :
    (u.weaken s).rv M C (Env.cons x env) = u.rv M C env := by
  funext η ρ σ y
  exact congrFun (congrFun (denote_weaken_cons _ (u σ y) x env) η) ρ

theorem Vec.rv_append : ∀ {Ξ : List (Ty B)} (u : Vec D Γ Ξ) (w : Vec D Γ τs),
    Vec.rv M C (Env.append u w) env = fun η ρ => Env.append (u.rv M C env η ρ) (w.rv M C env η ρ)
  | [], _, _ => rfl
  | _ :: _, u, w => by
    funext η ρ σ x
    cases x with
    | zero => rfl
    | succ x => exact congrFun (congrFun (congrFun (congrFun
        (Vec.rv_append (fun _ y => u _ (.succ y)) w) η) ρ) σ) x

theorem Vec.rv_snoc (u : Vec D Γ τs) (v : FTerm D Γ β) :
    (Vec.snoc u v).rv M C env = VecRV.snoc (u.rv M C env) (v.denote (fullInterp M C) env) := by
  rw [Vec.snoc, Vec.rv_append]
  funext η ρ
  congr 1
  funext σ x
  cases x with
  | zero => rfl
  | succ x => exact nomatch x

theorem Vec.rv_single (v : FTerm D Γ β) :
    Vec.rv M C (Env.cons v Env.empty : Vec D Γ [β]) env =
      VecRV.single (v.denote (fullInterp M C) env) := by
  funext η ρ σ x
  cases x with
  | zero => rfl
  | succ x => exact nomatch x

/-- The local negation of a decided proposition is `false` exactly where it holds. -/
private theorem cond_decide_eq_false_iff {P : Prop} :
    cond (@decide P (Classical.propDecidable _)) false true = false ↔ P := by
  by_cases h : P <;> simp [h]

/-- The local equality under the binder of `⊬` and `▷`, at a value `X` of the bound function. -/
private theorem denote_eq_apps (u : Vec D Γ τs) (v : FTerm D Γ β) (X : RV M (Ty.arrows τs β)) :
    (FTerm.eq (FTerm.apps (Term.var .zero) (u.weaken (.loc (Ty.arrows τs β))))
        (v.weaken (.loc (Ty.arrows τs β)))).denote (fullInterp M C) (Env.cons X env) =
      fun η ρ => @decide (Ty.appVals (X η ρ) (u.rv M C env η ρ) =
        v.denote (fullInterp M C) env η ρ) (Classical.propDecidable _) := by
  rw [FTerm.denote_eq, FTerm.denote_apps, Vec.rv_weaken, denote_weaken_cons]
  rfl

/-- `u⃗ ⊬ v` holds when no admitted attacker function computes `v` from `u⃗` with
non-negligible probability. -/
theorem Form.holds_nonDed {u : Vec D Γ τs} {v : FTerm D Γ β} :
    (Form.nonDed u v).Holds M C env ↔
      C.NonDed (u.rv M C env) (v.denote (fullInterp M C) env) := by
  have hX : ∀ X : RV M (Ty.arrows τs β), Overwhelming M.toTapeModel
      ((FTerm.not (FTerm.eq (FTerm.apps (Term.var .zero) (u.weaken (.loc (Ty.arrows τs β))))
        (v.weaken (.loc (Ty.arrows τs β))))).denote (fullInterp M C) (Env.cons X env)) ↔
      negligible fun η => Pr{let ρ ← $ᵗ (M.Tape η)}[Ty.appVals (X η ρ) (u.rv M C env η ρ) =
        v.denote (fullInterp M C) env η ρ] := fun X => by
    refine iff_of_eq (congrArg negligible (funext fun η => prEvent_congr _ _ _ fun ρ => ?_))
    simp only [FTerm.not, FTerm.denote_ite, denote_eq_apps, FTerm.denote_ff, FTerm.denote_tt]
    exact cond_decide_eq_false_iff
  refine ⟨fun h g hg => (hX _).1 (h _ ⟨g, hg, fun _ _ => rfl⟩), fun h X hXg => ?_⟩
  obtain ⟨g, hg, hXg⟩ := hXg
  obtain rfl : X = fun η ρ => g η ρ.1 := funext fun η => funext (hXg η)
  exact (hX _).2 (h g hg)

/-- `u⃗ ▷ v` holds when some admitted attacker function computes `v` from `u⃗` with overwhelming
probability. -/
theorem Form.holds_ded {u : Vec D Γ τs} {v : FTerm D Γ β} :
    (Form.ded u v).Holds M C env ↔ C.Ded (u.rv M C env) (v.denote (fullInterp M C) env) := by
  have hX : ∀ X : RV M (Ty.arrows τs β), Overwhelming M.toTapeModel
      ((FTerm.eq (FTerm.apps (Term.var .zero) (u.weaken (.loc (Ty.arrows τs β))))
        (v.weaken (.loc (Ty.arrows τs β)))).denote (fullInterp M C) (Env.cons X env)) ↔
      negligible fun η => Pr{let ρ ← $ᵗ (M.Tape η)}[Ty.appVals (X η ρ) (u.rv M C env η ρ) ≠
        v.denote (fullInterp M C) env η ρ] := fun X => by
    refine iff_of_eq (congrArg negligible (funext fun η => prEvent_congr _ _ _ fun ρ => ?_))
    rw [denote_eq_apps]
    exact @decide_eq_false_iff_not _ (Classical.propDecidable _)
  refine ⟨fun ⟨X, ⟨g, hg, hXg⟩, hbox⟩ => ⟨g, hg, ?_⟩, fun ⟨g, hg, herr⟩ =>
    ⟨fun η ρ => g η ρ.1, ⟨g, hg, fun _ _ => rfl⟩, (hX _).2 herr⟩⟩
  obtain rfl : X = fun η ρ => g η ρ.1 := funext fun η => funext (hXg η)
  exact (hX _).1 hbox

end Reading

/-! ## Rules (CCS26 Fig. 3) -/

namespace Valid

variable {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M} {Θ : List (Form D Γ)}
  {u : Vec D Γ τs} {v w : FTerm D Γ β}

/-- **Neg1** (CCS26 Fig. 3): from `u⃗ ⊬ v`, conclude `¬ (u⃗ ▷ v)`. -/
theorem not_ded (h : Valid R C Θ (.nonDed u v)) : Valid R C Θ (.not (.ded u v)) :=
  fun M hl hR env hΘ => Form.holds_not.2 fun hd =>
    (Form.holds_nonDed.1 (h M hl hR env hΘ)).not_ded (Form.holds_ded.1 hd)

/-- **Neg2** (CCS26 Fig. 3): from `u⃗ ▷ v`, conclude `¬ (u⃗ ⊬ v)`. -/
theorem not_nonDed (h : Valid R C Θ (.ded u v)) : Valid R C Θ (.not (.nonDed u v)) :=
  fun M hl hR env hΘ => Form.holds_not.2 fun hn =>
    (Form.holds_ded.1 (h M hl hR env hΘ)).not_nonDed (Form.holds_nonDed.1 hn)

/-- **Ineq** (CCS26 Fig. 3): from `u⃗ ⊬ v` and `u⃗ ▷ w`, conclude `[v ≠ w]`. -/
theorem box_not_eq (h : Valid R C Θ (.nonDed u v)) (h' : Valid R C Θ (.ded u w)) :
    Valid R C Θ (.box (FTerm.not (FTerm.eq v w))) := fun M hl hR env hΘ => by
  refine Form.holds_box.2 (negligible_of_le (fun η => prEvent_mono _ _ _ fun ρ hρ => ?_)
    ((Form.holds_nonDed.1 (h M hl hR env hΘ)).negligible_eq (Form.holds_ded.1 (h' M hl hR env hΘ))))
  simp only [FTerm.not, FTerm.denote_ite, FTerm.denote_eq, FTerm.denote_ff,
    FTerm.denote_tt] at hρ
  exact cond_decide_eq_false_iff.1 hρ

/-- **Trans** (CCS26 Fig. 3): from `u⃗ ▷ v` and `v ▷ w`, conclude `u⃗ ▷ w`. -/
theorem ded_trans {w : FTerm D Γ γ} (h₁ : Valid R C Θ (.ded u v))
    (h₂ : Valid R C Θ (.ded (Env.cons v Env.empty) w)) : Valid R C Θ (.ded u w) := by
  intro M hl hR env hΘ
  have h₂' := Form.holds_ded.1 (h₂ M hl hR env hΘ)
  rw [Vec.rv_single] at h₂'
  exact Form.holds_ded.2 ((Form.holds_ded.1 (h₁ M hl hR env hΘ)).trans h₂')

/-- **WeakL** (CCS26 Fig. 3): from `u⃗ ⊬ w` and `u⃗ ▷ v`, conclude `v ⊬ w`. -/
theorem nonDed_weakL {w : FTerm D Γ γ} (h : Valid R C Θ (.nonDed u w))
    (h' : Valid R C Θ (.ded u v)) : Valid R C Θ (.nonDed (Env.cons v Env.empty) w) := by
  intro M hl hR env hΘ
  rw [Form.holds_nonDed, Vec.rv_single]
  exact (Form.holds_nonDed.1 (h M hl hR env hΘ)).weakL (Form.holds_ded.1 (h' M hl hR env hΘ))

/-- **WeakR** (CCS26 Fig. 3): from `u⃗ ⊬ v` and `w ▷ v`, conclude `u⃗ ⊬ w`. -/
theorem nonDed_weakR {w : FTerm D Γ γ} (h : Valid R C Θ (.nonDed u v))
    (h' : Valid R C Θ (.ded (Env.cons w Env.empty) v)) : Valid R C Θ (.nonDed u w) := by
  intro M hl hR env hΘ
  have h'' := Form.holds_ded.1 (h' M hl hR env hΘ)
  rw [Vec.rv_single] at h''
  exact Form.holds_nonDed.2 ((Form.holds_nonDed.1 (h M hl hR env hΘ)).weakR h'')

/-- **Rw-Equiv** (CCS26 Fig. 3), for a right side of Boolean or base type: from `u⃗₂ ⊬ v₂` and
`u⃗₁, v₁ ∼ u⃗₂, v₂`, conclude `u⃗₁ ⊬ v₁`. -/
theorem nonDed_rwEquiv (hβ : β.IsGround) {u₁ u₂ : Vec D Γ τs} {v₁ v₂ : FTerm D Γ β}
    (h : Valid R C Θ (.nonDed u₂ v₂))
    (h' : Valid R C Θ (.equiv (Vec.snoc u₁ v₁) (Vec.snoc u₂ v₂))) :
    Valid R C Θ (.nonDed u₁ v₁) := fun M hl hR env hΘ => by
  have hI := Form.holds_equiv.1 (h' M hl hR env hΘ)
  rw [Vec.rv_snoc, Vec.rv_snoc] at hI
  exact Form.holds_nonDed.2 ((Form.holds_nonDed.1 (h M hl hR env hΘ)).rwEquiv hβ hI)

/-- `u⃗ ▷ f(u⃗)` when `adv(f)`: the definition of `▷`, with `f` as the witness. -/
theorem ded_apps {f : FTerm D Γ (Ty.arrows τs β)} (hf : Valid R C Θ (.adv f)) :
    Valid R C Θ (.ded u (FTerm.apps f u)) := fun M hl hR env hΘ => by
  obtain ⟨g, hg, hfg⟩ := Form.holds_adv.1 (hf M hl hR env hΘ)
  refine Form.holds_ded.2 ⟨g, hg, negligible_of_zero fun η =>
    prEvent_eq_zero_of_forall_not _ _ fun ρ hρ => hρ ?_⟩
  rw [FTerm.denote_apps]
  exact congrArg (fun x => Ty.appVals x _) (hfg η ρ).symm

end Valid

end SquirrelLogic
