/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import SquirrelLogic.Global

/-!
# Terms that read none of some coordinates of the honest tape

The honest tape is a product with one coin per name and index (`Model.TapeH`), so freshness of
names is a statement about coordinates: a term is fresh for a name occurrence when its value does
not depend on the coordinate that the occurrence reads. Rules about fresh names state it
semantically.

* `FTerm.Avoids M S t`: at every `η` and every value of its free variables, the pointwise value of
  `t` is the same at two honest tapes that agree outside the coordinates `S η`. The encryption
  rule's side condition (`EncSymbols.Avoids`) is the instance at the key and coin coordinates,
  FreshR's (`SquirrelLogic.Rules.Fresh`) the instance at one name occurrence.
* `FTerm.avoids_var`, `FTerm.avoids_fn`, `FTerm.avoids_att`, `FTerm.avoids_tt`,
  `FTerm.avoids_ff`, `FTerm.Avoids.app`, `.ite`, `.eq`, `.not` and `.name`: it holds in every
  model of terms built from free variables, honest and attacker symbols, and names whose
  coordinates are outside `S`.
* `Model.FreshAt M k X`: a family over the tapes, such as a random variable or a vector of them,
  agrees at two honest tapes that agree outside the coordinate `k η`. `FTerm.Avoids.freshAt`
  gives it for the random variable of a closed term.

A decidable syntactic version is the occurrence check of PolyFun's `Term.heads`, which is not at
VCVio's PolyFun pin (`ea3b297`).
-/

public section

namespace SquirrelLogic

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B} {M : Model D} {S : (η : ℕ) → M.Slot η → Prop}
  {Γ : List (Kind B)} {a b τ : Ty B}

/-- The term reads none of the honest-tape coordinates `S η`: at every value of its free
variables, its pointwise value is the same at two honest tapes that agree outside `S η`. -/
@[expose] def FTerm.Avoids (M : Model D) (S : (η : ℕ) → M.Slot η → Prop) (t : FTerm D Γ τ) :
    Prop :=
  ∀ η ρa (ρh ρh' : M.TapeH η), (∀ k, ¬ S η k → ρh k = ρh' k) →
    ∀ e : Env (Kind.PtValue M η) Γ,
      t.denote (Interpretation.sum (interp M η (ρa, ρh)) (ptGlobal M η)) e =
        t.denote (Interpretation.sum (interp M η (ρa, ρh')) (ptGlobal M η)) e

namespace FTerm

/-- A free variable reads no honest coordinate. -/
theorem avoids_var (x : ScopedVar Γ (.loc τ)) : FTerm.Avoids M S (Term.var x : FTerm D Γ τ) :=
  fun _ _ _ _ _ _ => rfl

/-- An honest symbol reads no honest coordinate. -/
theorem avoids_fn (f : D.Fn τ) : (FTerm.fn f : FTerm D Γ τ).Avoids M S :=
  fun _ _ _ _ _ _ => rfl

/-- An attacker symbol reads no honest coordinate. -/
theorem avoids_att (f : D.Att) : (FTerm.att f : FTerm D Γ (D.attTy f)).Avoids M S :=
  fun _ _ _ _ _ _ => rfl

/-- `true` reads no honest coordinate. -/
theorem avoids_tt : (FTerm.tt : FTerm D Γ .bool).Avoids M S := fun _ _ _ _ _ _ => rfl

/-- `false` reads no honest coordinate. -/
theorem avoids_ff : (FTerm.ff : FTerm D Γ .bool).Avoids M S := fun _ _ _ _ _ _ => rfl

/-- A term avoids every smaller set of coordinates. -/
theorem Avoids.mono {S' : (η : ℕ) → M.Slot η → Prop} {t : FTerm D Γ τ} (h : t.Avoids M S')
    (hS : ∀ η k, S η k → S' η k) : t.Avoids M S :=
  fun η ρa ρh ρh' hρ => h η ρa ρh ρh' fun k hk => hρ k fun hk' => hk (hS η k hk')

/-- Application of terms that avoid `S` avoids it. -/
theorem Avoids.app {f : FTerm D Γ (.arrow a b)} {t : FTerm D Γ a} (hf : f.Avoids M S)
    (ht : t.Avoids M S) : (FTerm.app f t).Avoids M S := fun η ρa ρh ρh' h e => by
  change f.denote _ e (t.denote _ e) = f.denote _ e (t.denote _ e)
  rw [hf η ρa ρh ρh' h e, ht η ρa ρh ρh' h e]

/-- A conditional of terms that avoid `S` avoids it. -/
theorem Avoids.ite {c : FTerm D Γ .bool} {t t' : FTerm D Γ a} (hc : c.Avoids M S)
    (ht : t.Avoids M S) (ht' : t'.Avoids M S) : (FTerm.ite c t t').Avoids M S :=
  fun η ρa ρh ρh' h e => by
  change cond (c.denote _ e) (t.denote _ e) (t'.denote _ e) =
    cond (c.denote _ e) (t.denote _ e) (t'.denote _ e)
  rw [hc η ρa ρh ρh' h e, ht η ρa ρh ρh' h e, ht' η ρa ρh ρh' h e]

/-- An equality of terms that avoid `S` avoids it. -/
theorem Avoids.eq {t t' : FTerm D Γ a} (ht : t.Avoids M S) (ht' : t'.Avoids M S) :
    (FTerm.eq t t').Avoids M S :=
  Avoids.app (Avoids.app (fun _ _ _ _ _ _ => rfl) ht) ht'

/-- A negation of a term that avoids `S` avoids it. -/
theorem Avoids.not {φ : FTerm D Γ .bool} (h : φ.Avoids M S) : (FTerm.not φ).Avoids M S :=
  Avoids.ite h avoids_ff avoids_tt

/-- A name whose coordinates are all outside `S`, at an index that avoids `S`, avoids `S`: it
reads its own coordinate. -/
theorem Avoids.name (n : D.Name a b) (hn : ∀ η j, ¬ S η ⟨⟨a, b, n⟩, j⟩) {i : FTerm D Γ a}
    (hi : i.Avoids M S) : (FTerm.name n i).Avoids M S := fun η ρa ρh ρh' h e => by
  change M.sample η b (ρh ⟨⟨a, b, n⟩, i.denote _ e⟩) = M.sample η b (ρh' ⟨⟨a, b, n⟩, i.denote _ e⟩)
  rw [hi η ρa ρh ρh' h e, h _ (hn η _)]

end FTerm

/-! ## Random variables that do not read a coordinate -/

/-- A family over the tapes, such as a random variable or a vector of them, does not read the
honest-tape coordinate `k η`: it agrees at two honest tapes that agree outside it. -/
@[expose] def Model.FreshAt (M : Model D) {α : ℕ → Type} (k : (η : ℕ) → M.Slot η)
    (X : (η : ℕ) → M.Tape η → α η) : Prop :=
  ∀ η ρa (ρh ρh' : M.TapeH η), (∀ k', k' ≠ k η → ρh k' = ρh' k') → X η (ρa, ρh) = X η (ρa, ρh')

/-- The random variable of a closed term that avoids the coordinate `k η` does not read it. -/
theorem FTerm.Avoids.freshAt {k : (η : ℕ) → M.Slot η} {t : FTerm D [] τ}
    (h : t.Avoids M fun η k' => k' = k η) (C : AdvClass M) (env : Env (Kind.Value M) []) :
    M.FreshAt k (t.denote (fullInterp M C) env) := fun η ρa ρh ρh' hρ => by
  have h₁ := eval_denote_fullInterp M C η (ρa, ρh) t env
  have h₂ := eval_denote_fullInterp M C η (ρa, ρh') t env
  rw [Env.eq_empty (evalEnv M η (ρa, ρh) env)] at h₁
  rw [Env.eq_empty (evalEnv M η (ρa, ρh') env)] at h₂
  exact h₁.trans ((h η ρa ρh ρh' hρ Env.empty).trans h₂.symm)

/-- The vector of a closed vector of terms that each avoid the coordinate `k η` does not read
it. -/
theorem Vec.freshAt_rv {k : (η : ℕ) → M.Slot η} {τs : List (Ty B)} {u : Vec D [] τs}
    (h : ∀ τ x, (u τ x).Avoids M fun η k' => k' = k η) (C : AdvClass M)
    (env : Env (Kind.Value M) []) : M.FreshAt k (u.rv M C env) :=
  fun η ρa ρh ρh' hρ => funext fun τ => funext fun x =>
    (h τ x).freshAt C env η ρa ρh ρh' hρ

end SquirrelLogic
