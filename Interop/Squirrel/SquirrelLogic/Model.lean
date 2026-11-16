/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import SquirrelLogic.Syntax
public import VCVio.OracleComp.Constructions.SampleableType.Basic

/-!
# Models of Squirrel's local terms, read at one point

A model of a declaration environment (LICS23 §II-A.2, §II-A.3, §II-B) gives, for each security
parameter `η`,

* each base type a nonempty set of bitstrings: a domain with its injective encoding;
* finite, nonempty sets of attacker and honest random tapes, `TapeA η` and `TapeH η`;
* each name a function of its index and the honest tape;
* each honest function symbol a value, and each attacker function symbol a function of the
  attacker tape.

`interp M η ρ` reads local syntax at the parameter `η` and the tapes `ρ = (ρa, ρh)`: booleans are
`Bool`, arrows are full function spaces, and `=_τ`, `∀_τ`, `∃_τ` have their intended meaning.
`Bool`, not `Prop`, interprets `bool`, because LICS23 interprets it as `{0, 1}` and a conditional
needs a decidable test. Equality and the quantifiers range over function spaces, so they decide
their propositions classically.

Names follow LICS23 §II-B.2 structurally: the honest tape is a product with one uniform coin per
name and index, a name reads its own coordinate, and names of one type share a sampler. So
samplings for distinct name-index pairs are independent and those of one type are identically
distributed. That samplers run in polynomial time is not a restriction here.

## Main results

* `denote_app_lam`: β-reduction is sound, from `Term.denote_substOne`;
* `denote_substOne_congr`: replacing a subterm by one with the same meaning preserves meaning,
  the semantic core of local rewriting (LICS23 Fig. 7, L.Rewrite);
* `denote_eq_app_of_eq`: function application is a congruence for local equality;
* `Ty.finite_value`, `Ty.value_eq_of_fixed`: what the labels give.
-/

public section

namespace SquirrelLogic

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type}

/-- The meaning of a type at `η`, given the carriers of the base types. -/
@[expose, reducible] def Ty.Value (carrier : B → ℕ → Set (List Bool)) (η : ℕ) : Ty B → Type
  | .bool => Bool
  | .base b => carrier b η
  | .arrow a b => a.Value carrier η → b.Value carrier η

/-- Random tapes: finite, nonempty sets for the attacker and for honest samplings. The uniform
distribution on them is VCVio's `$ᵗ`. -/
structure TapeModel where
  /-- The attacker's random tapes. -/
  TapeA : ℕ → Type
  /-- The honest random tapes, read by names. -/
  TapeH : ℕ → Type
  /-- Attacker tapes are finite and nonempty, with their uniform sampler. -/
  [sampleableA : ∀ η, SampleableType (TapeA η)]
  /-- Honest tapes are finite and nonempty, with their uniform sampler. -/
  [sampleableH : ∀ η, SampleableType (TapeH η)]

attribute [instance] TapeModel.sampleableA TapeModel.sampleableH

/-- Both tapes. -/
abbrev TapeModel.Tape (T : TapeModel) (η : ℕ) : Type := T.TapeA η × T.TapeH η

/-- A model of a declaration environment. The honest tape is not a field: it is the product of
one coin per name and index (`Model.TapeH`), and a name reads its own coordinate. -/
structure Model (D : Decl B) where
  /-- The attacker's random tapes. -/
  TapeA : ℕ → Type
  /-- Attacker tapes are finite and nonempty, with their uniform sampler. -/
  [sampleableA : ∀ η, SampleableType (TapeA η)]
  /-- Each base type is a nonempty set of bitstrings at each `η`. -/
  carrier : B → ℕ → Set (List Bool)
  /-- Carriers are nonempty. -/
  nonempty : ∀ b η, (carrier b η).Nonempty
  /-- The coins of the sampler for names of type `b`. -/
  Coin : ℕ → Ty B → Type
  /-- Coins are finite and nonempty, with their uniform sampler. -/
  [sampleableCoin : ∀ η b, SampleableType (Coin η b)]
  /-- The sampler for names of type `b`: names of one type follow one distribution. -/
  sample : ∀ η (b : Ty B), Coin η b → b.Value carrier η
  /-- Name indices are finite in the model. -/
  finite_index : ∀ η {a b : Ty B}, D.Name a b → Finite (a.Value carrier η)
  /-- An honest function symbol is a fixed value at each `η`. -/
  fn : ∀ η {τ : Ty B}, D.Fn τ → τ.Value carrier η
  /-- An attacker function symbol is computed from the attacker tape. -/
  att : ∀ η (f : D.Att), TapeA η → (D.attTy f).Value carrier η

attribute [instance] Model.sampleableA Model.sampleableCoin

variable {D : Decl B}

/-- The coordinates of the honest tape at `η`: a name with its types, and an index. -/
abbrev Model.Slot (M : Model D) (η : ℕ) : Type :=
  (n : (a : Ty B) × (b : Ty B) × D.Name a b) × n.1.Value M.carrier η

/-- The honest tape at `η`: an independent coin for every name and index (LICS23 §II-B.2). -/
@[expose] def Model.TapeH (M : Model D) (η : ℕ) : Type := (k : M.Slot η) → M.Coin η k.1.2.1

/-- The honest tape is uniform: its coordinates are independent uniform coins. -/
noncomputable instance Model.instSampleableTapeH (M : Model D) (η : ℕ) :
    SampleableType (M.TapeH η) :=
  haveI := D.finite_names
  haveI : ∀ n : (a : Ty B) × (b : Ty B) × D.Name a b, Finite (n.1.Value M.carrier η) :=
    fun n => M.finite_index η n.2.2
  haveI := Fintype.ofFinite (M.Slot η)
  haveI : ∀ k : M.Slot η, Fintype (M.Coin η k.1.2.1) := fun _ => Fintype.ofFinite _
  SampleableType.piOfFintype _

/-- Both tapes. -/
abbrev Model.Tape (M : Model D) (η : ℕ) : Type := M.TapeA η × M.TapeH η

/-- The tapes of a model. -/
@[expose, reducible] noncomputable def Model.toTapeModel (M : Model D) : TapeModel where
  TapeA := M.TapeA
  TapeH := M.TapeH

/-- A name reads the coin of its own slot and runs the sampler of its type. -/
@[expose] def Model.name (M : Model D) (η : ℕ) {a b : Ty B} (n : D.Name a b)
    (i : a.Value M.carrier η) (ρh : M.TapeH η) : b.Value M.carrier η :=
  M.sample η b (ρh ⟨⟨a, b, n⟩, i⟩)

/-! ## Labels -/

/-- What a label requires of a base type's carriers (LICS23 App. A). -/
@[expose] def Label.Holds (carrier : B → ℕ → Set (List Bool)) (b : B) : Label → Prop
  | .finite => ∀ η, (carrier b η).Finite
  | .fixed => ∀ η η', carrier b η = carrier b η'

/-- A model respects the labels declared for its base types. -/
@[expose] def Model.RespectsLabels (M : Model D) : Prop :=
  ∀ b l, D.labels b l → l.Holds M.carrier b

/-- Every type is finite when the carriers are finite. -/
theorem Ty.finite_value_of_finite {carrier : B → ℕ → Set (List Bool)}
    (h : ∀ b η, (carrier b η).Finite) (η : ℕ) : ∀ τ : Ty B, Finite (τ.Value carrier η)
  | .bool => inferInstanceAs (Finite Bool)
  | .base b => (h b η).to_subtype
  | .arrow a b =>
    have := a.finite_value_of_finite h η
    have := b.finite_value_of_finite h η
    inferInstanceAs (Finite (a.Value carrier η → b.Value carrier η))

/-- Every type is inhabited when the carriers are nonempty. -/
theorem Ty.nonempty_value {carrier : B → ℕ → Set (List Bool)}
    (h : ∀ b η, (carrier b η).Nonempty) (η : ℕ) : ∀ τ : Ty B, Nonempty (τ.Value carrier η)
  | .bool => ⟨true⟩
  | .base b => (h b η).to_subtype
  | .arrow _ b => ⟨fun _ => Classical.choice (b.nonempty_value h η)⟩

/-- A finite type is finite in every model respecting the labels. -/
theorem Ty.finite_value (M : Model D) (hM : M.RespectsLabels) (η : ℕ) :
    ∀ τ : Ty B, τ.HasLabel D.labels .finite → Finite (τ.Value M.carrier η)
  | .bool, _ => inferInstanceAs (Finite Bool)
  | .base b, h => (hM b .finite h η).to_subtype
  | .arrow a b, ⟨ha, hb⟩ =>
    have := a.finite_value M hM η ha
    have := b.finite_value M hM η hb
    inferInstanceAs (Finite (a.Value M.carrier η → b.Value M.carrier η))

/-- A fixed type has the same meaning at every security parameter. -/
theorem Ty.value_eq_of_fixed (M : Model D) (hM : M.RespectsLabels) (η η' : ℕ) :
    ∀ τ : Ty B, τ.HasLabel D.labels .fixed → τ.Value M.carrier η = τ.Value M.carrier η'
  | .bool, _ => rfl
  | .base b, h => congrArg (fun s : Set (List Bool) => (s : Type)) (hM b .fixed h η η')
  | .arrow a b, ⟨ha, hb⟩ => by
    simp only [Ty.Value, a.value_eq_of_fixed M hM η η' ha, b.value_eq_of_fixed M hM η η' hb]

/-! ## The pointwise reading -/

/-- The meaning of a sort at `η`: local types by `Ty.Value`; the global sort is not read
pointwise. -/
@[expose, reducible] def Kind.PtValue (M : Model D) (η : ℕ) : Kind B → Type
  | .loc τ => τ.Value M.carrier η
  | .glob => PUnit

/-- Local syntax read at the security parameter `η` and the tapes `ρ = (ρa, ρh)`: names read
`ρh`, attacker symbols read `ρa`. -/
@[expose] noncomputable def interp (M : Model D) (η : ℕ) (ρ : M.Tape η) :
    Interpretation (localSig D) (Kind.PtValue M η)
  | _, .app _ _, next => next 0 Env.empty (next 1 Env.empty)
  | _, .lam _ _, next => fun x => next 0 (Env.single x)
  | _, .ite _, next => cond (next 0 Env.empty) (next 1 Env.empty) (next 2 Env.empty)
  | _, .tt, _ => true
  | _, .ff, _ => false
  | _, .eq _, _ => fun x y => @decide (x = y) (Classical.propDecidable _)
  | _, .all _, _ => fun f => @decide (∀ x, f x = true) (Classical.propDecidable _)
  | _, .ex _, _ => fun f => @decide (∃ x, f x = true) (Classical.propDecidable _)
  | _, .name n, _ => fun i => M.name η n i ρ.2
  | _, .fn f, _ => M.fn η f
  | _, .att f, _ => M.att η f ρ.1

namespace LTerm

variable {M : Model D} {η : ℕ} {ρ : M.Tape η} {Γ : List (Kind B)} {a b : Ty B}
  {env : Env (Kind.PtValue M η) Γ}

@[simp] theorem denote_app (f : LTerm D Γ (.arrow a b)) (x : LTerm D Γ a) :
    (app f x).denote (interp M η ρ) env =
      f.denote (interp M η ρ) env (x.denote (interp M η ρ) env) := rfl

@[simp] theorem denote_lam (body : LTerm D (.loc a :: Γ) b) :
    (lam body).denote (interp M η ρ) env =
      fun x => body.denote (interp M η ρ) (Env.cons x env) := rfl

@[simp] theorem denote_ite (c : LTerm D Γ .bool) (t e : LTerm D Γ a) :
    (ite c t e).denote (interp M η ρ) env =
      cond (c.denote (interp M η ρ) env) (t.denote (interp M η ρ) env)
        (e.denote (interp M η ρ) env) := rfl

@[simp] theorem denote_tt : (tt : LTerm D Γ .bool).denote (interp M η ρ) env = true := rfl

@[simp] theorem denote_ff : (ff : LTerm D Γ .bool).denote (interp M η ρ) env = false := rfl

/-- `=_τ` means equality (LICS23 §II-B). -/
@[simp] theorem denote_eq_eq_true {t u : LTerm D Γ a} :
    (eq t u).denote (interp M η ρ) env = true ↔
      t.denote (interp M η ρ) env = u.denote (interp M η ρ) env :=
  @decide_eq_true_iff _ (Classical.propDecidable _)

/-- `∀_τ` means universal quantification over the whole carrier (LICS23 §II-B). -/
@[simp] theorem denote_all_eq_true {φ : LTerm D (.loc a :: Γ) .bool} :
    (all φ).denote (interp M η ρ) env = true ↔
      ∀ x, φ.denote (interp M η ρ) (Env.cons x env) = true :=
  @decide_eq_true_iff _ (Classical.propDecidable _)

/-! ## β-reduction and congruence -/

/-- **β.** A redex means its contraction, by `Term.denote_substOne`. -/
theorem denote_app_lam (body : LTerm D (.loc a :: Γ) b) (v : LTerm D Γ a) :
    (app (lam body) v).denote (interp M η ρ) env =
      (body.substOne v).denote (interp M η ρ) env := by
  rw [Term.denote_substOne, denote_app, denote_lam]

/-- Replacing a subterm by one with the same meaning preserves meaning, in any interpretation:
the semantic core of local rewriting (LICS23 Fig. 7, L.Rewrite). The context `C` is a term with
its hole as the nearest variable, so the replacement is capture-avoiding. -/
theorem denote_substOne_congr {V : Kind B → Type} (alg : Interpretation (localSig D) V)
    {s : Kind B} (C : (localSig D).Term (.loc a :: Γ) s) {t u : LTerm D Γ a}
    (ρ' : Env V Γ) (h : t.denote alg ρ' = u.denote alg ρ') :
    (C.substOne t).denote alg ρ' = (C.substOne u).denote alg ρ' := by
  rw [Term.denote_substOne, Term.denote_substOne, h]

/-- Local rewriting: where `s = t` holds, a formula about `s` means the same about `t`. -/
theorem denote_substOne_of_eq {s : Kind B} (C : (localSig D).Term (.loc a :: Γ) s)
    {t u : LTerm D Γ a} (h : (eq t u).denote (interp M η ρ) env = true) :
    (C.substOne t).denote (interp M η ρ) env = (C.substOne u).denote (interp M η ρ) env :=
  denote_substOne_congr _ C env (denote_eq_eq_true.1 h)

/-- **FA congruence.** Application preserves local equality. -/
theorem denote_eq_app_of_eq {f g : LTerm D Γ (.arrow a b)} {t u : LTerm D Γ a}
    (hf : (eq f g).denote (interp M η ρ) env = true)
    (ht : (eq t u).denote (interp M η ρ) env = true) :
    (eq (app f t) (app g u)).denote (interp M η ρ) env = true := by
  rw [denote_eq_eq_true] at hf ht ⊢
  rw [denote_app, denote_app, hf, ht]

end LTerm

end SquirrelLogic
