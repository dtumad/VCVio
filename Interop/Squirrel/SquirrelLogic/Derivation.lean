/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import SquirrelLogic.Rules.Local
public import SquirrelLogic.Rules.Equiv
public import SquirrelLogic.Rules.Enc

/-!
# Derivations of global sequents

Derivations in the fragment of LICS23 proved sound in `SquirrelLogic.Global` and
`SquirrelLogic.Rules`, as data: each constructor is one rule, indexed by the context, the
hypotheses and the conclusion. `Derivation.sound` maps every derivation to validity over every
model restriction and every adversary class, one rule lemma per constructor. Name renaming
(`Valid.equiv_renameNames`) is left out: it holds only under a restriction on models.

The encryption rule (`Valid.equiv_enc`) is a constructor, at the instances that the parameter
`enc` admits; its syntactic side condition, distinct key and coin names, is a premise of the
constructor. `Derivation.sound` takes the semantic hypotheses of each admitted instance
(`EncInstance.Holds`). With `enc` empty, derivations are those of the structural fragment.
-/

public section

namespace SquirrelLogic

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type}

/-- Derivations of `Θ ⊢ F` in the context `Γ`, using the encryption rule at the instances that
`enc` admits. -/
inductive Derivation (D : Decl B) (enc : EncInstance D → Prop) :
    {Γ : List (Kind B)} → List (Form D Γ) → Form D Γ → Type
  /-- G.Axiom. -/
  | ax {Γ : List (Kind B)} {Θ : List (Form D Γ)} {F : Form D Γ} : F ∈ Θ → Derivation D enc Θ F
  /-- G.Weak. -/
  | weaken {Γ : List (Kind B)} {Θ Θ' : List (Form D Γ)} {F : Form D Γ} :
      Derivation D enc Θ F → Θ ⊆ Θ' → Derivation D enc Θ' F
  /-- G.Cut. -/
  | cut {Γ : List (Kind B)} {Θ : List (Form D Γ)} {F F' : Form D Γ} :
      Derivation D enc Θ F' → Derivation D enc (F' :: Θ) F → Derivation D enc Θ F
  /-- G.L-∀̃. -/
  | allLeft {Γ : List (Kind B)} {Θ : List (Form D Γ)} {F : Form D Γ} {τ : Ty B}
      {G : Form D (.loc τ :: Γ)} (t : FTerm D Γ τ) :
      Derivation D enc (G.substOne t :: Θ) F → Derivation D enc (.all τ G :: Θ) F
  /-- G.R-∀̃. -/
  | allRight {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τ : Ty B} {G : Form D (.loc τ :: Γ)} :
      Derivation D enc (Θ.map (Term.weaken · (.loc τ))) G → Derivation D enc Θ (.all τ G)
  /-- L.ByGlob, with the local sequent unfolded. -/
  | byGlob {Γ : List (Kind B)} {Θ : List (Form D Γ)} {φ : FTerm D Γ .bool}
      (Γl : List (FTerm D Γ .bool)) :
      Derivation D enc Θ (.box φ) → Derivation D enc Θ (.box (.imp (.conj Γl) φ))
  /-- G.ByLoc, with the local sequent unfolded. -/
  | byLoc {Γ : List (Kind B)} {Θ : List (Form D Γ)} {φ : FTerm D Γ .bool} :
      Derivation D enc Θ (.box (.imp (.conj []) φ)) → Derivation D enc Θ (.box φ)
  /-- L.R-∀, with the local sequents unfolded. -/
  | localAll {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τ : Ty B} {φ : FTerm D (.loc τ :: Γ) .bool}
      (Γl : List (FTerm D Γ .bool)) :
      Derivation D enc (Θ.map (Term.weaken · (.loc τ)))
        (.box (.imp (.conj (Γl.map (Term.weaken · (.loc τ)))) φ)) →
      Derivation D enc Θ (.box (.imp (.conj Γl) (FTerm.all φ)))
  /-- Refl. -/
  | equivRefl {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} (u : Vec D Γ τs) :
      Derivation D enc Θ (.equiv u u)
  /-- Sym. -/
  | equivSymm {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs} :
      Derivation D enc Θ (.equiv u v) → Derivation D enc Θ (.equiv v u)
  /-- Trans. -/
  | equivTrans {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)}
      {u v w : Vec D Γ τs} :
      Derivation D enc Θ (.equiv u v) → Derivation D enc Θ (.equiv v w) →
      Derivation D enc Θ (.equiv u w)
  /-- G.Equiv:FA-App. -/
  | equivApp {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {a b : Ty B} {t s : FTerm D Γ (.arrow a b)} {t' s' : FTerm D Γ a} :
      Derivation D enc Θ (.equiv (Env.cons t (Env.cons t' u)) (Env.cons s (Env.cons s' v))) →
      Derivation D enc Θ (.equiv (Env.cons (FTerm.app t t') u) (Env.cons (FTerm.app s s') v))
  /-- FA-Fn. -/
  | equivFn {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τ : Ty B} (f : D.Fn τ) : Derivation D enc Θ (.equiv u v) →
      Derivation D enc Θ (.equiv (Env.cons (FTerm.fn f) u) (Env.cons (FTerm.fn f) v))
  /-- G.Equiv:FA-Adv. -/
  | equivAdv {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τ : Ty B} {t : FTerm D Γ τ} : Derivation D enc Θ (.adv t) → Derivation D enc Θ (.equiv u v) →
      Derivation D enc Θ (.equiv (Env.cons t u) (Env.cons t v))
  /-- Restr. -/
  | equivTail {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τ : Ty B} {t s : FTerm D Γ τ} :
      Derivation D enc Θ (.equiv (Env.cons t u) (Env.cons s v)) → Derivation D enc Θ (.equiv u v)
  /-- Dup. -/
  | equivDup {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τ : Ty B} {t s : FTerm D Γ τ} :
      Derivation D enc Θ (.equiv (Env.cons t u) (Env.cons s v)) →
      Derivation D enc Θ (.equiv (Env.cons t (Env.cons t u)) (Env.cons s (Env.cons s v)))
  /-- If. -/
  | equivIte {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {a : Ty B} {c c' : FTerm D Γ .bool} {t t' s s' : FTerm D Γ a} :
      Derivation D enc Θ (.equiv (Env.cons c (Env.cons t (Env.cons t' u)))
        (Env.cons c' (Env.cons s (Env.cons s' v)))) →
      Derivation D enc Θ (.equiv (Env.cons (FTerm.ite c t t') u) (Env.cons (FTerm.ite c' s s') v))
  /-- Rewriting an entry under an overwhelming equality. -/
  | equivRewrite {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u : Vec D Γ τs}
      {τ : Ty B} {t t' : FTerm D Γ τ} {w : Vec D Γ (τ :: τs)} :
      Derivation D enc Θ (.box (FTerm.eq t t')) → Derivation D enc Θ (.equiv (Env.cons t' u) w) →
      Derivation D enc Θ (.equiv (Env.cons t u) w)
  /-- Encryption from one-time IND-CPA, at an admitted instance with distinct key and coin
  names. -/
  | equivEnc {Θ : List (Form D [])} (e : EncInstance D) : enc e →
      e.E.keyName ≠ e.E.coinName →
      Derivation D enc Θ (.equiv (e.E.challenge e.m₀ e.u) (e.E.challenge e.m₁ e.u))

variable {D : Decl B}

/-- **Soundness** of the fragment: a derivable sequent is valid for every restriction on models
and every adversary class under which the admitted encryption instances meet their hypotheses. -/
theorem Derivation.sound {enc : EncInstance D → Prop} (R : Model D → Prop)
    (C : ∀ M : Model D, AdvClass M) (henc : ∀ e, enc e → e.Holds R C) :
    {Γ : List (Kind B)} → {Θ : List (Form D Γ)} → {F : Form D Γ} →
      Derivation D enc Θ F → Valid R C Θ F
  | _, _, _, .ax h => Valid.ax h
  | _, _, _, .weaken d h => (d.sound R C henc).weaken h
  | _, _, _, .cut d₁ d₂ => (d₁.sound R C henc).cut (d₂.sound R C henc)
  | _, _, _, .allLeft t d => Valid.all_left t (d.sound R C henc)
  | _, _, _, .allRight d => Valid.all_right (d.sound R C henc)
  | _, _, _, .byGlob Γl d => Valid.byGlob Γl (d.sound R C henc)
  | _, _, _, .byLoc d => Valid.byLoc (d.sound R C henc)
  | _, _, _, .localAll Γl d => Valid.local_all Γl (d.sound R C henc)
  | _, _, _, .equivRefl u => Valid.equiv_refl u
  | _, _, _, .equivSymm d => (d.sound R C henc).equiv_symm
  | _, _, _, .equivTrans d₁ d₂ => (d₁.sound R C henc).equiv_trans (d₂.sound R C henc)
  | _, _, _, .equivApp d => (d.sound R C henc).equiv_app
  | _, _, _, .equivFn f d => Valid.equiv_fn f (d.sound R C henc)
  | _, _, _, .equivAdv d₁ d₂ => Valid.equiv_adv (d₁.sound R C henc) (d₂.sound R C henc)
  | _, _, _, .equivTail d => (d.sound R C henc).equiv_tail
  | _, _, _, .equivDup d => (d.sound R C henc).equiv_dup
  | _, _, _, .equivIte d => (d.sound R C henc).equiv_ite
  | _, _, _, .equivRewrite d₁ d₂ => Valid.equiv_rewrite (d₁.sound R C henc) (d₂.sound R C henc)
  | _, _, _, .equivEnc e he hkr => Valid.equiv_enc e.E hkr (henc e he).1 (henc e he).2

/-- A worked derivation: from the hypothesis `∀̃ x. G`, conclude `G{x ↦ t}`. -/
def Derivation.allInst {enc : EncInstance D → Prop} {Γ : List (Kind B)} {τ : Ty B}
    (G : Form D (.loc τ :: Γ))
    (t : FTerm D Γ τ) : Derivation D enc [.all τ G] (G.substOne t) :=
  .allLeft t (.ax List.mem_cons_self)

end SquirrelLogic
