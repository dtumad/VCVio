/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import SquirrelLogic.Global

/-!
# Derivations of global sequents

Derivations in the fragment of LICS23 Fig. 7 proved sound in `SquirrelLogic.Global`, as data:
each constructor is one rule, indexed by the context, the hypotheses and the conclusion.
`Derivation.sound` maps every derivation to validity over every model restriction and every
adversary class, one rule lemma per constructor.
-/

public section

namespace SquirrelLogic

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type}

/-- Derivations of `Θ ⊢ F` in the context `Γ`. -/
inductive Derivation (D : Decl B) : {Γ : List (Kind B)} → List (Form D Γ) → Form D Γ → Type
  /-- G.Axiom. -/
  | ax {Γ : List (Kind B)} {Θ : List (Form D Γ)} {F : Form D Γ} : F ∈ Θ → Derivation D Θ F
  /-- G.Weak. -/
  | weaken {Γ : List (Kind B)} {Θ Θ' : List (Form D Γ)} {F : Form D Γ} :
      Derivation D Θ F → Θ ⊆ Θ' → Derivation D Θ' F
  /-- G.Cut. -/
  | cut {Γ : List (Kind B)} {Θ : List (Form D Γ)} {F F' : Form D Γ} :
      Derivation D Θ F' → Derivation D (F' :: Θ) F → Derivation D Θ F
  /-- G.L-∀̃. -/
  | allLeft {Γ : List (Kind B)} {Θ : List (Form D Γ)} {F : Form D Γ} {τ : Ty B}
      {G : Form D (.loc τ :: Γ)} (t : FTerm D Γ τ) :
      Derivation D (G.substOne t :: Θ) F → Derivation D (.all τ G :: Θ) F
  /-- G.R-∀̃. -/
  | allRight {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τ : Ty B} {G : Form D (.loc τ :: Γ)} :
      Derivation D (Θ.map (Term.weaken · (.loc τ))) G → Derivation D Θ (.all τ G)
  /-- L.ByGlob, with the local sequent unfolded. -/
  | byGlob {Γ : List (Kind B)} {Θ : List (Form D Γ)} {φ : FTerm D Γ .bool}
      (Γl : List (FTerm D Γ .bool)) :
      Derivation D Θ (.box φ) → Derivation D Θ (.box (.imp (.conj Γl) φ))
  /-- G.ByLoc, with the local sequent unfolded. -/
  | byLoc {Γ : List (Kind B)} {Θ : List (Form D Γ)} {φ : FTerm D Γ .bool} :
      Derivation D Θ (.box (.imp (.conj []) φ)) → Derivation D Θ (.box φ)

variable {D : Decl B}

/-- **Soundness** of the fragment: a derivable sequent is valid for every restriction on models
and every adversary class. -/
theorem Derivation.sound (R : Model D → Prop) (C : ∀ M : Model D, AdvClass M) :
    {Γ : List (Kind B)} → {Θ : List (Form D Γ)} → {F : Form D Γ} →
      Derivation D Θ F → Valid R C Θ F
  | _, _, _, .ax h => Valid.ax h
  | _, _, _, .weaken d h => (d.sound R C).weaken h
  | _, _, _, .cut d₁ d₂ => (d₁.sound R C).cut (d₂.sound R C)
  | _, _, _, .allLeft t d => Valid.all_left t (d.sound R C)
  | _, _, _, .allRight d => Valid.all_right (d.sound R C)
  | _, _, _, .byGlob Γl d => Valid.byGlob Γl (d.sound R C)
  | _, _, _, .byLoc d => Valid.byLoc (d.sound R C)

/-- A worked derivation: from the hypothesis `∀̃ x. G`, conclude `G{x ↦ t}`. -/
def Derivation.allInst {Γ : List (Kind B)} {τ : Ty B} (G : Form D (.loc τ :: Γ))
    (t : FTerm D Γ τ) : Derivation D [.all τ G] (G.substOne t) :=
  .allLeft t (.ax List.mem_cons_self)

end SquirrelLogic
