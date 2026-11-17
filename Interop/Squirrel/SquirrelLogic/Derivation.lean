/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import SquirrelLogic.Rules.Local
public import SquirrelLogic.Rules.Equiv
public import SquirrelLogic.Rules.Enc
public import SquirrelLogic.Rules.Rename
public import SquirrelLogic.Rules.Fresh
public import SquirrelLogic.Rules.FreshL
public import SquirrelLogic.Rules.PRF

/-!
# Derivations of global sequents

Derivations in the fragment of LICS23 proved sound in `SquirrelLogic.Global` and
`SquirrelLogic.Rules`, as data: each constructor is one rule, indexed by the context, the
hypotheses and the conclusion. `Derivation.sound` maps every derivation to validity over every
model restriction and every class of machines, one rule lemma per constructor. Name renaming is the
constructor for a bijection of names (`Valid.equiv_renameNames_of_equiv`), which holds in every
model. BC14's If1 (`equivIf1`) is sound by the case split (`equivCaseStudy`), but is a
constructor of its own: deriving it would rewrite `if c' then z else z` to `z`, and the fragment
has no rule proving that local equality.

The encryption rule (`Valid.equiv_enc`) is a constructor, at the instances that the parameter
`enc` admits; its syntactic side condition, distinct key and coin names, is a premise of the
constructor. `Derivation.sound` takes the semantic hypotheses of each admitted instance
(`EncInstance.Holds`). With `enc` empty, derivations are those of the structural fragment.

The secrecy rules of CCS26 Fig. 3 (Neg1, Neg2, Ineq, Trans, WeakL, WeakR, Rw-Equiv), `▷` from
`adv` (`dedApps`), FreshR and FreshL (Fig. 11) are constructors. Rw-Equiv takes the ground type of
its right side as a premise, and FreshR the label `large` and the freshness of its closed vector in
every model (`FTerm.Avoids`), so both are sound in every model.

FreshL is sound only over models with long attacker tapes (`Model.LongTapes`); without them it
fails (`FreshLCountermodel.freshL_needs_longTapes`). So derivations carry a parameter `R₀`, the
restriction on models that their rules assume: FreshL's constructor takes as premises that `R₀`
gives long tapes and polynomial bit blocks for the name's type, and that the terms read the
attacker tape below a polynomial in every model of `R₀` and of `Θ`. `Derivation.sound` holds over
every restriction `R` contained in `R₀`. Derivations that do not use FreshL take `R₀` to be every
model.

Formulas carry the order bounds of CSF24 and CCS26 (`Ty.IndistOrder`, `Ty.AdvOrder`,
`Ty.SecrecyOrder`). A constructor's conclusion carries the bound derived from its premises', and
a constructor that adds an entry or starts from no premise takes the conclusion's bound.
-/

public section

namespace SquirrelLogic

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type}

/-- Derivations of `Θ ⊢ F` in the context `Γ`, using the encryption rule at the instances that
`enc` admits and G.PRF at the instances that `prf` admits, over the models of `R₀`. -/
inductive Derivation (D : Decl B) (enc : EncInstance D → Prop) (prf : PRFInstance D → Prop)
    (R₀ : Model D → Prop) :
    {Γ : List (Kind B)} → List (Form D Γ) → Form D Γ → Type
  /-- G.Axiom. -/
  | ax {Γ : List (Kind B)} {Θ : List (Form D Γ)} {F : Form D Γ} :
      F ∈ Θ → Derivation D enc prf R₀ Θ F
  /-- G.Weak. -/
  | weaken {Γ : List (Kind B)} {Θ Θ' : List (Form D Γ)} {F : Form D Γ} :
      Derivation D enc prf R₀ Θ F → Θ ⊆ Θ' → Derivation D enc prf R₀ Θ' F
  /-- G.Cut. -/
  | cut {Γ : List (Kind B)} {Θ : List (Form D Γ)} {F F' : Form D Γ} :
      Derivation D enc prf R₀ Θ F' → Derivation D enc prf R₀ (F' :: Θ) F →
      Derivation D enc prf R₀ Θ F
  /-- G.L-∀̃. -/
  | allLeft {Γ : List (Kind B)} {Θ : List (Form D Γ)} {F : Form D Γ} {τ : Ty B}
      {G : Form D (.loc τ :: Γ)} (t : FTerm D Γ τ) :
      Derivation D enc prf R₀ (G.substOne t :: Θ) F → Derivation D enc prf R₀ (.all τ G :: Θ) F
  /-- G.R-∀̃. -/
  | allRight {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τ : Ty B} {G : Form D (.loc τ :: Γ)} :
      Derivation D enc prf R₀ (Θ.map (Term.weaken · (.loc τ))) G →
      Derivation D enc prf R₀ Θ (.all τ G)
  /-- L.ByGlob, with the local sequent unfolded. -/
  | byGlob {Γ : List (Kind B)} {Θ : List (Form D Γ)} {φ : FTerm D Γ .bool}
      (Γl : List (FTerm D Γ .bool)) :
      Derivation D enc prf R₀ Θ (.box φ) → Derivation D enc prf R₀ Θ (.box (.imp (.conj Γl) φ))
  /-- G.ByLoc, with the local sequent unfolded. -/
  | byLoc {Γ : List (Kind B)} {Θ : List (Form D Γ)} {φ : FTerm D Γ .bool} :
      Derivation D enc prf R₀ Θ (.box (.imp (.conj []) φ)) → Derivation D enc prf R₀ Θ (.box φ)
  /-- L.R-∀, with the local sequents unfolded. -/
  | localAll {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τ : Ty B} {φ : FTerm D (.loc τ :: Γ) .bool}
      (Γl : List (FTerm D Γ .bool)) :
      Derivation D enc prf R₀ (Θ.map (Term.weaken · (.loc τ)))
        (.box (.imp (.conj (Γl.map (Term.weaken · (.loc τ)))) φ)) →
      Derivation D enc prf R₀ Θ (.box (.imp (.conj Γl) (FTerm.all φ)))
  /-- Refl. -/
  | equivRefl {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} (u : Vec D Γ τs)
      (ho : Ty.IndistOrder τs) : Derivation D enc prf R₀ Θ (.equiv u u ho)
  /-- Sym. -/
  | equivSymm {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {ho : Ty.IndistOrder τs} :
      Derivation D enc prf R₀ Θ (.equiv u v ho) → Derivation D enc prf R₀ Θ (.equiv v u ho)
  /-- Trans. -/
  | equivTrans {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)}
      {u v w : Vec D Γ τs} {ho : Ty.IndistOrder τs} :
      Derivation D enc prf R₀ Θ (.equiv u v ho) → Derivation D enc prf R₀ Θ (.equiv v w ho) →
      Derivation D enc prf R₀ Θ (.equiv u w ho)
  /-- G.Equiv:FA-App. -/
  | equivApp {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {a b : Ty B} {t s : FTerm D Γ (.arrow a b)} {t' s' : FTerm D Γ a}
      {ho : Ty.IndistOrder (.arrow a b :: a :: τs)} :
      Derivation D enc prf R₀ Θ
        (.equiv (Env.cons t (Env.cons t' u)) (Env.cons s (Env.cons s' v)) ho) →
      Derivation D enc prf R₀ Θ
        (.equiv (Env.cons (FTerm.app t t') u) (Env.cons (FTerm.app s s') v) ho.app)
  /-- FA-Fn. -/
  | equivFn {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τ : Ty B} (ho : Ty.IndistOrder (τ :: τs)) (f : D.Fn τ) :
      Derivation D enc prf R₀ Θ (.equiv u v ho.tail) →
      Derivation D enc prf R₀ Θ (.equiv (Env.cons (FTerm.fn f) u) (Env.cons (FTerm.fn f) v) ho)
  /-- G.Equiv:FA-Adv. -/
  | equivAdv {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τs₀ : List (Ty B)} {β : Ty B} {t : FTerm D Γ (Ty.arrows τs₀ β)} {ha : Ty.AdvOrder τs₀ β}
      (ho : Ty.IndistOrder (Ty.arrows τs₀ β :: τs)) :
      Derivation D enc prf R₀ Θ (.adv t ha) → Derivation D enc prf R₀ Θ (.equiv u v ho.tail) →
      Derivation D enc prf R₀ Θ (.equiv (Env.cons t u) (Env.cons t v) ho)
  /-- Restr. -/
  | equivTail {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τ : Ty B} {t s : FTerm D Γ τ} {ho : Ty.IndistOrder (τ :: τs)} :
      Derivation D enc prf R₀ Θ (.equiv (Env.cons t u) (Env.cons s v) ho) →
      Derivation D enc prf R₀ Θ (.equiv u v ho.tail)
  /-- Dup. -/
  | equivDup {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τ : Ty B} {t s : FTerm D Γ τ} {ho : Ty.IndistOrder (τ :: τs)} :
      Derivation D enc prf R₀ Θ (.equiv (Env.cons t u) (Env.cons s v) ho) →
      Derivation D enc prf R₀ Θ
        (.equiv (Env.cons t (Env.cons t u)) (Env.cons s (Env.cons s v)) ho.dup)
  /-- If. -/
  | equivIte {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {a : Ty B} {c c' : FTerm D Γ .bool} {t t' s s' : FTerm D Γ a}
      {ho : Ty.IndistOrder (.bool :: a :: a :: τs)} :
      Derivation D enc prf R₀ Θ (.equiv (Env.cons c (Env.cons t (Env.cons t' u)))
        (Env.cons c' (Env.cons s (Env.cons s' v))) ho) →
      Derivation D enc prf R₀ Θ
        (.equiv (Env.cons (FTerm.ite c t t') u) (Env.cons (FTerm.ite c' s s') v) ho.ite)
  /-- G.Case-Study:ITE (LICS23 Fig. 8). -/
  | equivCaseStudy {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {a : Ty B} {c c' : FTerm D Γ .bool} {t t' s s' : FTerm D Γ a}
      {ho : Ty.IndistOrder (.bool :: a :: τs)} :
      Derivation D enc prf R₀ Θ
        (.equiv (Env.cons c (Env.cons t u)) (Env.cons c' (Env.cons s v)) ho) →
      Derivation D enc prf R₀ Θ
        (.equiv (Env.cons c (Env.cons t' u)) (Env.cons c' (Env.cons s' v)) ho) →
      Derivation D enc prf R₀ Θ
        (.equiv (Env.cons (FTerm.ite c t t') u) (Env.cons (FTerm.ite c' s s') v) ho.tail)
  /-- If1 (BC14 Fig. 2). -/
  | equivIf1 {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {a : Ty B} {c c' : FTerm D Γ .bool} {x y z : FTerm D Γ a}
      {ho : Ty.IndistOrder (.bool :: a :: τs)} :
      Derivation D enc prf R₀ Θ
        (.equiv (Env.cons c (Env.cons x u)) (Env.cons c' (Env.cons z v)) ho) →
      Derivation D enc prf R₀ Θ
        (.equiv (Env.cons c (Env.cons y u)) (Env.cons c' (Env.cons z v)) ho) →
      Derivation D enc prf R₀ Θ (.equiv (Env.cons (FTerm.ite c x y) u) (Env.cons z v) ho.tail)
  /-- Rewriting an entry under an overwhelming equality. -/
  | equivRewrite {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u : Vec D Γ τs}
      {τ : Ty B} {t t' : FTerm D Γ τ} {w : Vec D Γ (τ :: τs)} {ho : Ty.IndistOrder (τ :: τs)} :
      Derivation D enc prf R₀ Θ (.box (FTerm.eq t t')) →
      Derivation D enc prf R₀ Θ (.equiv (Env.cons t' u) w ho) →
      Derivation D enc prf R₀ Θ (.equiv (Env.cons t u) w ho)
  /-- Eq1 (BC14 Fig. 2). -/
  | equivEqSelf {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {τ : Ty B}
      (t : FTerm D Γ τ) (u : Vec D Γ τs) (ho : Ty.IndistOrder (.bool :: τs)) :
      Derivation D enc prf R₀ Θ (.equiv (Env.cons (FTerm.eq t t) u) (Env.cons FTerm.tt u) ho)
  /-- Restr and Perm (BC14 Fig. 2): reindexing both vectors. -/
  | equivRename {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs τs' : List (Ty B)}
      {u v : Vec D Γ τs} {ho : Ty.IndistOrder τs} (r : Renaming τs' τs) :
      Derivation D enc prf R₀ Θ (.equiv u v ho) →
      Derivation D enc prf R₀ Θ (.equiv (Env.rename r u) (Env.rename r v) (ho.rename r))
  /-- Name renaming along a bijection of names, for a closed vector. -/
  | equivRenameNames {Θ : List (Form D [])} {τs : List (Ty B)}
      (π : ∀ {a b : Ty B}, D.Name a b ≃ D.Name a b) (u : Vec D [] τs) (ho : Ty.IndistOrder τs) :
      Derivation D enc prf R₀ Θ (.equiv u (u.renameNames fun n => π n) ho)
  /-- Encryption from one-time IND-CPA, at an admitted instance with distinct key and coin
  names. -/
  | equivEnc {Θ : List (Form D [])} (e : EncInstance D) : enc e →
      e.E.keyName ≠ e.E.coinName →
      Derivation D enc prf R₀ Θ (.equiv (e.E.challenge e.m₀ e.u) (e.E.challenge e.m₁ e.u) e.order)
  /-- Neg1 (CCS26 Fig. 3). -/
  | notDed {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β : Ty B}
      {u : Vec D Γ τs} {v : FTerm D Γ β} {ho : Ty.SecrecyOrder τs β} :
      Derivation D enc prf R₀ Θ (.nonDed u v ho) → Derivation D enc prf R₀ Θ (.not (.ded u v ho))
  /-- Neg2 (CCS26 Fig. 3). -/
  | notNonDed {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β : Ty B}
      {u : Vec D Γ τs} {v : FTerm D Γ β} {ho : Ty.SecrecyOrder τs β} :
      Derivation D enc prf R₀ Θ (.ded u v ho) → Derivation D enc prf R₀ Θ (.not (.nonDed u v ho))
  /-- Ineq (CCS26 Fig. 3). -/
  | boxNotEq {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β : Ty B}
      {u : Vec D Γ τs} {v w : FTerm D Γ β} {ho : Ty.SecrecyOrder τs β} :
      Derivation D enc prf R₀ Θ (.nonDed u v ho) → Derivation D enc prf R₀ Θ (.ded u w ho) →
      Derivation D enc prf R₀ Θ (.box (FTerm.not (FTerm.eq v w)))
  /-- Trans (CCS26 Fig. 3). -/
  | dedTrans {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β γ : Ty B}
      {u : Vec D Γ τs} {v : FTerm D Γ β} {w : FTerm D Γ γ} {ho₁ : Ty.SecrecyOrder τs β}
      {ho₂ : Ty.SecrecyOrder [β] γ} :
      Derivation D enc prf R₀ Θ (.ded u v ho₁) →
      Derivation D enc prf R₀ Θ (.ded (Env.cons v Env.empty) w ho₂) →
      Derivation D enc prf R₀ Θ (.ded u w ⟨ho₁.1, ho₂.2⟩)
  /-- WeakL (CCS26 Fig. 3). -/
  | nonDedWeakL {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β γ : Ty B}
      {u : Vec D Γ τs} {v : FTerm D Γ β} {w : FTerm D Γ γ} {ho₁ : Ty.SecrecyOrder τs γ}
      {ho₂ : Ty.SecrecyOrder τs β} :
      Derivation D enc prf R₀ Θ (.nonDed u w ho₁) → Derivation D enc prf R₀ Θ (.ded u v ho₂) →
      Derivation D enc prf R₀ Θ (.nonDed (Env.cons v Env.empty) w ⟨.single ho₂.2, ho₁.2⟩)
  /-- WeakR (CCS26 Fig. 3). -/
  | nonDedWeakR {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β γ : Ty B}
      {u : Vec D Γ τs} {v : FTerm D Γ β} {w : FTerm D Γ γ} {ho₁ : Ty.SecrecyOrder τs β}
      {ho₂ : Ty.SecrecyOrder [γ] β} :
      Derivation D enc prf R₀ Θ (.nonDed u v ho₁) →
      Derivation D enc prf R₀ Θ (.ded (Env.cons w Env.empty) v ho₂) →
      Derivation D enc prf R₀ Θ (.nonDed u w ⟨ho₁.1, ho₂.1.head⟩)
  /-- Rw-Equiv (CCS26 Fig. 3), for a right side of Boolean or base type. -/
  | nonDedRwEquiv {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β : Ty B}
      {u₁ u₂ : Vec D Γ τs} {v₁ v₂ : FTerm D Γ β} {ho : Ty.SecrecyOrder τs β}
      {hoE : Ty.IndistOrder (τs ++ [β])} : β.IsGround →
      Derivation D enc prf R₀ Θ (.nonDed u₂ v₂ ho) →
      Derivation D enc prf R₀ Θ (.equiv (Vec.snoc u₁ v₁) (Vec.snoc u₂ v₂) hoE) →
      Derivation D enc prf R₀ Θ (.nonDed u₁ v₁ ho)
  /-- `u⃗ ▷ f(u⃗)` from `adv(f)`. -/
  | dedApps {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β : Ty B}
      {u : Vec D Γ τs} {f : FTerm D Γ (Ty.arrows τs β)} {ha : Ty.AdvOrder τs β}
      (ho : Ty.SecrecyOrder τs β) :
      Derivation D enc prf R₀ Θ (.adv f ha) → Derivation D enc prf R₀ Θ (.ded u (FTerm.apps f u) ho)
  /-- FreshR (CCS26 Fig. 11), for a closed vector that avoids the name's coordinate in every
  model. -/
  | nonDedFreshR {Θ : List (Form D [])} {τs : List (Ty B)} {a b : Ty B} (u : Vec D [] τs)
      (n : D.Name a b) (i : D.Fn a) (ho : Ty.SecrecyOrder τs b) : b.HasLabel D.labels .large →
      (∀ M : Model D, ∀ τ x, (u τ x).Avoids M fun η k => k = M.nameSlot n i η) →
      Derivation D enc prf R₀ Θ (.nonDed u (FTerm.name n (FTerm.fn i)) ho)
  /-- FreshL (CCS26 Fig. 11), for a closed vector, over models where `R₀` gives long attacker tapes
  and polynomial bit blocks for names of type `b`: the terms read the attacker tape below a
  polynomial in every model of `R₀` and of `Θ`, and avoid the name's coordinate. -/
  | nonDedFreshL {Θ : List (Form D [])} {τs : List (Ty B)} {a b β : Ty B} {u : Vec D [] τs}
      {v : FTerm D [] β} {ho : Ty.SecrecyOrder τs β} (ho' : Ty.SecrecyOrder (τs ++ [b]) β)
      (n : D.Name a b) (i : D.Fn a) :
      (∀ M, R₀ M → M.LongTapes ∧ M.PolyCoins b) →
      (∀ M : Model D, M.RespectsLabels → R₀ M → ∀ (C : AdvClass M) env,
        (∀ θ ∈ Θ, θ.Holds M C env) → u.ReadsPoly M C env ∧ v.ReadsPoly M C env) →
      (∀ M, R₀ M → (∀ τ x, (u τ x).Avoids M fun η k => k = M.nameSlot n i η) ∧
        v.Avoids M fun η k => k = M.nameSlot n i η) →
      Derivation D enc prf R₀ Θ (.nonDed u v ho) →
      Derivation D enc prf R₀ Θ (.nonDed (Vec.snoc u (FTerm.name n (FTerm.fn i))) v ho')
  /-- G.PRF (LICS23 p. 29; CCS26 Fig. 11), at an admitted instance meeting the syntactic side
  conditions, from `[ψ_msg]`. -/
  | equivPRF {Θ : List (Form D [])} (e : PRFInstance D) : prf e → e.Syntactic →
      Derivation D enc prf R₀ Θ (.box (e.P.psiMsg e.u e.m)) →
      Derivation D enc prf R₀ Θ (.equiv e.lhs e.rhs e.order)

variable {D : Decl B}

/-- **Soundness** of the fragment: a derivable sequent is valid for every restriction on models
contained in `R₀` and every class of machines under which the admitted encryption instances meet
their hypotheses. -/
theorem Derivation.sound {enc : EncInstance D → Prop} {prf : PRFInstance D → Prop}
    {R₀ : Model D → Prop} (R : Model D → Prop) (C : ∀ M : Model D, AdvClass M)
    (henc : ∀ e, enc e → e.Holds R C) (hprf : ∀ e, prf e → e.Holds R C)
    (hR : ∀ M, R M → R₀ M) :
    {Γ : List (Kind B)} → {Θ : List (Form D Γ)} → {F : Form D Γ} →
      Derivation D enc prf R₀ Θ F → Valid R C Θ F
  | _, _, _, .ax h => Valid.ax h
  | _, _, _, .weaken d h => (d.sound R C henc hprf hR).weaken h
  | _, _, _, .cut d₁ d₂ => (d₁.sound R C henc hprf hR).cut (d₂.sound R C henc hprf hR)
  | _, _, _, .allLeft t d => Valid.all_left t (d.sound R C henc hprf hR)
  | _, _, _, .allRight d => Valid.all_right (d.sound R C henc hprf hR)
  | _, _, _, .byGlob Γl d => Valid.byGlob Γl (d.sound R C henc hprf hR)
  | _, _, _, .byLoc d => Valid.byLoc (d.sound R C henc hprf hR)
  | _, _, _, .localAll Γl d => Valid.local_all Γl (d.sound R C henc hprf hR)
  | _, _, _, .equivRefl u _ => Valid.equiv_refl u
  | _, _, _, .equivSymm d => (d.sound R C henc hprf hR).equiv_symm
  | _, _, _, .equivTrans d₁ d₂ =>
    (d₁.sound R C henc hprf hR).equiv_trans (d₂.sound R C henc hprf hR)
  | _, _, _, .equivApp d => (d.sound R C henc hprf hR).equiv_app
  | _, _, _, .equivFn ho f d => Valid.equiv_fn (ho := ho) f (d.sound R C henc hprf hR)
  | _, _, _, .equivAdv ho d₁ d₂ =>
    Valid.equiv_adv (ho := ho) (d₁.sound R C henc hprf hR) (d₂.sound R C henc hprf hR)
  | _, _, _, .equivTail d => (d.sound R C henc hprf hR).equiv_tail
  | _, _, _, .equivDup d => (d.sound R C henc hprf hR).equiv_dup
  | _, _, _, .equivIte d => (d.sound R C henc hprf hR).equiv_ite
  | _, _, _, .equivCaseStudy d₁ d₂ =>
    (d₁.sound R C henc hprf hR).equiv_caseStudy (d₂.sound R C henc hprf hR)
  | _, _, _, .equivIf1 d₁ d₂ => (d₁.sound R C henc hprf hR).equiv_if1 (d₂.sound R C henc hprf hR)
  | _, _, _, .equivRewrite d₁ d₂ =>
    Valid.equiv_rewrite (d₁.sound R C henc hprf hR) (d₂.sound R C henc hprf hR)
  | _, _, _, .equivEqSelf t u _ => Valid.equiv_eq_self t u
  | _, _, _, .equivRename r d => Valid.equiv_rename r (d.sound R C henc hprf hR)
  | _, _, _, .equivRenameNames π u _ => Valid.equiv_renameNames_of_equiv π u
  | _, _, _, .equivEnc e he hkr => Valid.equiv_enc e.E hkr (henc e he).1 (henc e he).2
  | _, _, _, .notDed d => Valid.not_ded (d.sound R C henc hprf hR)
  | _, _, _, .notNonDed d => Valid.not_nonDed (d.sound R C henc hprf hR)
  | _, _, _, .boxNotEq d₁ d₂ =>
    Valid.box_not_eq (d₁.sound R C henc hprf hR) (d₂.sound R C henc hprf hR)
  | _, _, _, .dedTrans d₁ d₂ =>
    Valid.ded_trans (d₁.sound R C henc hprf hR) (d₂.sound R C henc hprf hR)
  | _, _, _, .nonDedWeakL d₁ d₂ =>
    Valid.nonDed_weakL (d₁.sound R C henc hprf hR) (d₂.sound R C henc hprf hR)
  | _, _, _, .nonDedWeakR d₁ d₂ =>
    Valid.nonDed_weakR (d₁.sound R C henc hprf hR) (d₂.sound R C henc hprf hR)
  | _, _, _, .nonDedRwEquiv hβ d₁ d₂ =>
    Valid.nonDed_rwEquiv hβ (d₁.sound R C henc hprf hR) (d₂.sound R C henc hprf hR)
  | _, _, _, .dedApps _ d => Valid.ded_apps (d.sound R C henc hprf hR)
  | _, _, _, .nonDedFreshR _ n i _ hl hf => Valid.nonDed_freshR n i hl fun M _ => hf M
  | _, _, _, .nonDedFreshL _ n i hl hr hf d =>
    Valid.nonDed_freshL n i (fun M hRM => hl M (hR M hRM))
      (fun M hlM hRM env hΘ => hr M hlM (hR M hRM) (C M) env hΘ) (fun M hRM => hf M (hR M hRM))
      (d.sound R C henc hprf hR)
  | _, _, _, .equivPRF e he hs d => e.valid hs (hprf e he) (d.sound R C henc hprf hR)

/-- **PRF-Simple, derived** (CCS26 Fig. 11 and p. 17): from a derivation of `u⃗ ⊬ v`, a
derivation of `u⃗, h(m, k) ⊬ v`, through the constructors of G.PRF (at the vector `u⃗, v` and a name
`n` of the hash type), Perm, FreshL and Rw-Equiv, as CCS26 derives it. The side conditions are
those of the three constructors. -/
def Derivation.nonDedPRF {enc : EncInstance D → Prop} {prf : PRFInstance D → Prop}
    {R₀ : Model D → Prop} {Θ : List (Form D [])} (P : PRFSymbols D) {τs : List (Ty B)}
    {β : Ty B} (u : OVec P [] τs) (v : OTerm P [] β) (m : OTerm P [] P.msgTy) {a : Ty B}
    (nn : D.Name a P.hTy) (i : D.Fn a) {ho : Ty.SecrecyOrder τs β}
    (ho' : Ty.SecrecyOrder (τs ++ [P.hTy]) β) (hβ : β.IsGround)
    (horder : Ty.IndistOrder ((τs ++ [β]) ++ [P.hTy]))
    (hprf : prf ⟨P, τs ++ [β], Env.append u (Env.cons v Env.empty), m, a, nn, i, horder⟩)
    (hs : PRFInstance.Syntactic ⟨P, τs ++ [β], Env.append u (Env.cons v Env.empty), m, a, nn, i,
      horder⟩)
    (hl : ∀ M, R₀ M → M.LongTapes ∧ M.PolyCoins P.hTy)
    (hread : ∀ M : Model D, M.RespectsLabels → R₀ M → ∀ (C : AdvClass M) env,
      (∀ θ ∈ Θ, θ.Holds M C env) →
        Vec.ReadsPoly M C (P.closeVec u) env ∧ FTerm.ReadsPoly M C (P.close v) env)
    (hfresh : ∀ M, R₀ M →
      (∀ τ x, FTerm.Avoids M (fun η k => k = M.nameSlot nn i η) (P.close (u τ x))) ∧
        FTerm.Avoids M (fun η k => k = M.nameSlot nn i η) (P.close v))
    (dmsg : Derivation D enc prf R₀ Θ (.box (P.psiMsg (Env.append u (Env.cons v Env.empty)) m)))
    (d : Derivation D enc prf R₀ Θ (.nonDed (P.closeVec u) (P.close v) ho)) :
    Derivation D enc prf R₀ Θ
      (.nonDed (Vec.snoc (P.closeVec u) (P.hashTerm (P.close m))) (P.close v) ho') :=
  let dprf := Derivation.equivPRF (Θ := Θ) _ hprf hs dmsg
  have hlhs : PRFInstance.lhs ⟨P, τs ++ [β], Env.append u (Env.cons v Env.empty), m, a, nn, i,
      horder⟩ = Vec.snoc (Vec.snoc (P.closeVec u) (P.close v)) (P.hashTerm (P.close m)) := by
    rw [PRFInstance.lhs, P.closeVec_append, P.closeVec_single]
    rfl
  have hrhs : PRFInstance.rhs ⟨P, τs ++ [β], Env.append u (Env.cons v Env.empty), m, a, nn, i,
      horder⟩ = Vec.snoc (Vec.snoc (P.closeVec u) (P.close v)) (FTerm.name nn (FTerm.fn i)) := by
    rw [PRFInstance.rhs, P.closeVec_append, P.closeVec_single]
    rfl
  let dperm := Derivation.equivRename (swapLast τs P.hTy β) (hlhs ▸ hrhs ▸ dprf)
  have hperm : ∀ (w : FTerm D [] P.hTy),
      Env.rename (swapLast τs P.hTy β) (Vec.snoc (Vec.snoc (P.closeVec u) (P.close v)) w) =
        Vec.snoc (Vec.snoc (P.closeVec u) w) (P.close v) := fun w =>
    rename_swapLast (P.closeVec u) (P.close v) w
  Derivation.nonDedRwEquiv hβ
    (Derivation.nonDedFreshL ho' nn i hl hread hfresh d)
    (hperm _ ▸ hperm _ ▸ dperm)

/-- A worked derivation: from the hypothesis `∀̃ x. G`, conclude `G{x ↦ t}`. -/
def Derivation.allInst {enc : EncInstance D → Prop} {prf : PRFInstance D → Prop}
    {R₀ : Model D → Prop} {Γ : List (Kind B)}
    {τ : Ty B} (G : Form D (.loc τ :: Γ)) (t : FTerm D Γ τ) :
    Derivation D enc prf R₀ [.all τ G] (G.substOne t) :=
  .allLeft t (.ax List.mem_cons_self)

end SquirrelLogic
