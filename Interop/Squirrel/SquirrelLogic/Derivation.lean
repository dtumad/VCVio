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

/-!
# Derivations of global sequents

Derivations in the fragment of LICS23 proved sound in `SquirrelLogic.Global` and
`SquirrelLogic.Rules`, as data: each constructor is one rule, indexed by the context, the
hypotheses and the conclusion. `Derivation.sound` maps every derivation to validity over every
model restriction and every adversary class, one rule lemma per constructor. Name renaming is the
constructor for a bijection of names (`Valid.equiv_renameNames_of_equiv`), which holds in every
model. BC14's If1 (`equivIf1`) is sound by the case split (`equivCaseStudy`), but is a
constructor of its own: deriving it would rewrite `if c' then z else z` to `z`, and the fragment
has no rule proving that local equality.

The encryption rule (`Valid.equiv_enc`) is a constructor, at the instances that the parameter
`enc` admits; its syntactic side condition, distinct key and coin names, is a premise of the
constructor. `Derivation.sound` takes the semantic hypotheses of each admitted instance
(`EncInstance.Holds`). With `enc` empty, derivations are those of the structural fragment.

The secrecy rules of CCS26 Fig. 3 (Neg1, Neg2, Ineq, Trans, WeakL, WeakR, Rw-Equiv), `▷` from
`adv` (`dedApps`) and FreshR (Fig. 11) are constructors. Rw-Equiv takes the ground type of its
right side as a premise, and FreshR the label `large` and the freshness of its closed vector in
every model (`FTerm.Avoids`), so both are sound in every model.
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
  | equivRefl {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} (u : Vec D Γ τs)
      (ho : Ty.IndistOrder τs) : Derivation D enc Θ (.equiv u u ho)
  /-- Sym. -/
  | equivSymm {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {ho : Ty.IndistOrder τs} :
      Derivation D enc Θ (.equiv u v ho) → Derivation D enc Θ (.equiv v u ho)
  /-- Trans. -/
  | equivTrans {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)}
      {u v w : Vec D Γ τs} {ho : Ty.IndistOrder τs} :
      Derivation D enc Θ (.equiv u v ho) → Derivation D enc Θ (.equiv v w ho) →
      Derivation D enc Θ (.equiv u w ho)
  /-- G.Equiv:FA-App. -/
  | equivApp {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {a b : Ty B} {t s : FTerm D Γ (.arrow a b)} {t' s' : FTerm D Γ a}
      {ho : Ty.IndistOrder (.arrow a b :: a :: τs)} :
      Derivation D enc Θ (.equiv (Env.cons t (Env.cons t' u)) (Env.cons s (Env.cons s' v)) ho) →
      Derivation D enc Θ
        (.equiv (Env.cons (FTerm.app t t') u) (Env.cons (FTerm.app s s') v) ho.app)
  /-- FA-Fn. -/
  | equivFn {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τ : Ty B} (ho : Ty.IndistOrder (τ :: τs)) (f : D.Fn τ) :
      Derivation D enc Θ (.equiv u v ho.tail) →
      Derivation D enc Θ (.equiv (Env.cons (FTerm.fn f) u) (Env.cons (FTerm.fn f) v) ho)
  /-- G.Equiv:FA-Adv. -/
  | equivAdv {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τs₀ : List (Ty B)} {β : Ty B} {t : FTerm D Γ (Ty.arrows τs₀ β)} {ha : Ty.AdvOrder τs₀ β}
      (ho : Ty.IndistOrder (Ty.arrows τs₀ β :: τs)) :
      Derivation D enc Θ (.adv t ha) → Derivation D enc Θ (.equiv u v ho.tail) →
      Derivation D enc Θ (.equiv (Env.cons t u) (Env.cons t v) ho)
  /-- Restr. -/
  | equivTail {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τ : Ty B} {t s : FTerm D Γ τ} {ho : Ty.IndistOrder (τ :: τs)} :
      Derivation D enc Θ (.equiv (Env.cons t u) (Env.cons s v) ho) →
      Derivation D enc Θ (.equiv u v ho.tail)
  /-- Dup. -/
  | equivDup {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τ : Ty B} {t s : FTerm D Γ τ} {ho : Ty.IndistOrder (τ :: τs)} :
      Derivation D enc Θ (.equiv (Env.cons t u) (Env.cons s v) ho) →
      Derivation D enc Θ (.equiv (Env.cons t (Env.cons t u)) (Env.cons s (Env.cons s v)) ho.dup)
  /-- If. -/
  | equivIte {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {a : Ty B} {c c' : FTerm D Γ .bool} {t t' s s' : FTerm D Γ a}
      {ho : Ty.IndistOrder (.bool :: a :: a :: τs)} :
      Derivation D enc Θ (.equiv (Env.cons c (Env.cons t (Env.cons t' u)))
        (Env.cons c' (Env.cons s (Env.cons s' v))) ho) →
      Derivation D enc Θ
        (.equiv (Env.cons (FTerm.ite c t t') u) (Env.cons (FTerm.ite c' s s') v) ho.ite)
  /-- G.Case-Study:ITE (LICS23 Fig. 8). -/
  | equivCaseStudy {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {a : Ty B} {c c' : FTerm D Γ .bool} {t t' s s' : FTerm D Γ a}
      {ho : Ty.IndistOrder (.bool :: a :: τs)} :
      Derivation D enc Θ (.equiv (Env.cons c (Env.cons t u)) (Env.cons c' (Env.cons s v)) ho) →
      Derivation D enc Θ (.equiv (Env.cons c (Env.cons t' u)) (Env.cons c' (Env.cons s' v)) ho) →
      Derivation D enc Θ
        (.equiv (Env.cons (FTerm.ite c t t') u) (Env.cons (FTerm.ite c' s s') v) ho.tail)
  /-- If1 (BC14 Fig. 2). -/
  | equivIf1 {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {a : Ty B} {c c' : FTerm D Γ .bool} {x y z : FTerm D Γ a}
      {ho : Ty.IndistOrder (.bool :: a :: τs)} :
      Derivation D enc Θ (.equiv (Env.cons c (Env.cons x u)) (Env.cons c' (Env.cons z v)) ho) →
      Derivation D enc Θ (.equiv (Env.cons c (Env.cons y u)) (Env.cons c' (Env.cons z v)) ho) →
      Derivation D enc Θ (.equiv (Env.cons (FTerm.ite c x y) u) (Env.cons z v) ho.tail)
  /-- Rewriting an entry under an overwhelming equality. -/
  | equivRewrite {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u : Vec D Γ τs}
      {τ : Ty B} {t t' : FTerm D Γ τ} {w : Vec D Γ (τ :: τs)} {ho : Ty.IndistOrder (τ :: τs)} :
      Derivation D enc Θ (.box (FTerm.eq t t')) →
      Derivation D enc Θ (.equiv (Env.cons t' u) w ho) →
      Derivation D enc Θ (.equiv (Env.cons t u) w ho)
  /-- Eq1 (BC14 Fig. 2). -/
  | equivEqSelf {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {τ : Ty B}
      (t : FTerm D Γ τ) (u : Vec D Γ τs) (ho : Ty.IndistOrder (.bool :: τs)) :
      Derivation D enc Θ (.equiv (Env.cons (FTerm.eq t t) u) (Env.cons FTerm.tt u) ho)
  /-- Restr and Perm (BC14 Fig. 2): reindexing both vectors. -/
  | equivRename {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs τs' : List (Ty B)}
      {u v : Vec D Γ τs} {ho : Ty.IndistOrder τs} (r : Renaming τs' τs) :
      Derivation D enc Θ (.equiv u v ho) →
      Derivation D enc Θ (.equiv (Env.rename r u) (Env.rename r v) (ho.rename r))
  /-- Name renaming along a bijection of names, for a closed vector. -/
  | equivRenameNames {Θ : List (Form D [])} {τs : List (Ty B)}
      (π : ∀ {a b : Ty B}, D.Name a b ≃ D.Name a b) (u : Vec D [] τs) (ho : Ty.IndistOrder τs) :
      Derivation D enc Θ (.equiv u (u.renameNames fun n => π n) ho)
  /-- Encryption from one-time IND-CPA, at an admitted instance with distinct key and coin
  names. -/
  | equivEnc {Θ : List (Form D [])} (e : EncInstance D) : enc e →
      e.E.keyName ≠ e.E.coinName →
      Derivation D enc Θ (.equiv (e.E.challenge e.m₀ e.u) (e.E.challenge e.m₁ e.u) e.order)
  /-- Neg1 (CCS26 Fig. 3). -/
  | notDed {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β : Ty B}
      {u : Vec D Γ τs} {v : FTerm D Γ β} {ho : Ty.SecrecyOrder τs β} :
      Derivation D enc Θ (.nonDed u v ho) → Derivation D enc Θ (.not (.ded u v ho))
  /-- Neg2 (CCS26 Fig. 3). -/
  | notNonDed {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β : Ty B}
      {u : Vec D Γ τs} {v : FTerm D Γ β} {ho : Ty.SecrecyOrder τs β} :
      Derivation D enc Θ (.ded u v ho) → Derivation D enc Θ (.not (.nonDed u v ho))
  /-- Ineq (CCS26 Fig. 3). -/
  | boxNotEq {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β : Ty B}
      {u : Vec D Γ τs} {v w : FTerm D Γ β} {ho : Ty.SecrecyOrder τs β} :
      Derivation D enc Θ (.nonDed u v ho) → Derivation D enc Θ (.ded u w ho) →
      Derivation D enc Θ (.box (FTerm.not (FTerm.eq v w)))
  /-- Trans (CCS26 Fig. 3). -/
  | dedTrans {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β γ : Ty B}
      {u : Vec D Γ τs} {v : FTerm D Γ β} {w : FTerm D Γ γ} {ho₁ : Ty.SecrecyOrder τs β}
      {ho₂ : Ty.SecrecyOrder [β] γ} :
      Derivation D enc Θ (.ded u v ho₁) → Derivation D enc Θ (.ded (Env.cons v Env.empty) w ho₂) →
      Derivation D enc Θ (.ded u w ⟨ho₁.1, ho₂.2⟩)
  /-- WeakL (CCS26 Fig. 3). -/
  | nonDedWeakL {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β γ : Ty B}
      {u : Vec D Γ τs} {v : FTerm D Γ β} {w : FTerm D Γ γ} {ho₁ : Ty.SecrecyOrder τs γ}
      {ho₂ : Ty.SecrecyOrder τs β} :
      Derivation D enc Θ (.nonDed u w ho₁) → Derivation D enc Θ (.ded u v ho₂) →
      Derivation D enc Θ (.nonDed (Env.cons v Env.empty) w ⟨.single ho₂.2, ho₁.2⟩)
  /-- WeakR (CCS26 Fig. 3). -/
  | nonDedWeakR {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β γ : Ty B}
      {u : Vec D Γ τs} {v : FTerm D Γ β} {w : FTerm D Γ γ} {ho₁ : Ty.SecrecyOrder τs β}
      {ho₂ : Ty.SecrecyOrder [γ] β} :
      Derivation D enc Θ (.nonDed u v ho₁) →
      Derivation D enc Θ (.ded (Env.cons w Env.empty) v ho₂) →
      Derivation D enc Θ (.nonDed u w ⟨ho₁.1, ho₂.1.head⟩)
  /-- Rw-Equiv (CCS26 Fig. 3), for a right side of Boolean or base type. -/
  | nonDedRwEquiv {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β : Ty B}
      {u₁ u₂ : Vec D Γ τs} {v₁ v₂ : FTerm D Γ β} {ho : Ty.SecrecyOrder τs β}
      {hoE : Ty.IndistOrder (τs ++ [β])} : β.IsGround →
      Derivation D enc Θ (.nonDed u₂ v₂ ho) →
      Derivation D enc Θ (.equiv (Vec.snoc u₁ v₁) (Vec.snoc u₂ v₂) hoE) →
      Derivation D enc Θ (.nonDed u₁ v₁ ho)
  /-- `u⃗ ▷ f(u⃗)` from `adv(f)`. -/
  | dedApps {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β : Ty B}
      {u : Vec D Γ τs} {f : FTerm D Γ (Ty.arrows τs β)} {ha : Ty.AdvOrder τs β}
      (ho : Ty.SecrecyOrder τs β) :
      Derivation D enc Θ (.adv f ha) → Derivation D enc Θ (.ded u (FTerm.apps f u) ho)
  /-- FreshR (CCS26 Fig. 11), for a closed vector that avoids the name's coordinate in every
  model. -/
  | nonDedFreshR {Θ : List (Form D [])} {τs : List (Ty B)} {a b : Ty B} (u : Vec D [] τs)
      (n : D.Name a b) (i : D.Fn a) (ho : Ty.SecrecyOrder τs b) : b.HasLabel D.labels .large →
      (∀ M : Model D, ∀ τ x, (u τ x).Avoids M fun η k => k = M.nameSlot n i η) →
      Derivation D enc Θ (.nonDed u (FTerm.name n (FTerm.fn i)) ho)

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
  | _, _, _, .equivRefl u _ => Valid.equiv_refl u
  | _, _, _, .equivSymm d => (d.sound R C henc).equiv_symm
  | _, _, _, .equivTrans d₁ d₂ => (d₁.sound R C henc).equiv_trans (d₂.sound R C henc)
  | _, _, _, .equivApp d => (d.sound R C henc).equiv_app
  | _, _, _, .equivFn ho f d => Valid.equiv_fn (ho := ho) f (d.sound R C henc)
  | _, _, _, .equivAdv ho d₁ d₂ =>
    Valid.equiv_adv (ho := ho) (d₁.sound R C henc) (d₂.sound R C henc)
  | _, _, _, .equivTail d => (d.sound R C henc).equiv_tail
  | _, _, _, .equivDup d => (d.sound R C henc).equiv_dup
  | _, _, _, .equivIte d => (d.sound R C henc).equiv_ite
  | _, _, _, .equivCaseStudy d₁ d₂ => (d₁.sound R C henc).equiv_caseStudy (d₂.sound R C henc)
  | _, _, _, .equivIf1 d₁ d₂ => (d₁.sound R C henc).equiv_if1 (d₂.sound R C henc)
  | _, _, _, .equivRewrite d₁ d₂ => Valid.equiv_rewrite (d₁.sound R C henc) (d₂.sound R C henc)
  | _, _, _, .equivEqSelf t u _ => Valid.equiv_eq_self t u
  | _, _, _, .equivRename r d => Valid.equiv_rename r (d.sound R C henc)
  | _, _, _, .equivRenameNames π u _ => Valid.equiv_renameNames_of_equiv π u
  | _, _, _, .equivEnc e he hkr => Valid.equiv_enc e.E hkr (henc e he).1 (henc e he).2
  | _, _, _, .notDed d => Valid.not_ded (d.sound R C henc)
  | _, _, _, .notNonDed d => Valid.not_nonDed (d.sound R C henc)
  | _, _, _, .boxNotEq d₁ d₂ => Valid.box_not_eq (d₁.sound R C henc) (d₂.sound R C henc)
  | _, _, _, .dedTrans d₁ d₂ => Valid.ded_trans (d₁.sound R C henc) (d₂.sound R C henc)
  | _, _, _, .nonDedWeakL d₁ d₂ => Valid.nonDed_weakL (d₁.sound R C henc) (d₂.sound R C henc)
  | _, _, _, .nonDedWeakR d₁ d₂ => Valid.nonDed_weakR (d₁.sound R C henc) (d₂.sound R C henc)
  | _, _, _, .nonDedRwEquiv hβ d₁ d₂ =>
    Valid.nonDed_rwEquiv hβ (d₁.sound R C henc) (d₂.sound R C henc)
  | _, _, _, .dedApps _ d => Valid.ded_apps (d.sound R C henc)
  | _, _, _, .nonDedFreshR _ n i _ hl hf => Valid.nonDed_freshR n i hl fun M _ => hf M

/-- A worked derivation: from the hypothesis `∀̃ x. G`, conclude `G{x ↦ t}`. -/
def Derivation.allInst {enc : EncInstance D → Prop} {Γ : List (Kind B)} {τ : Ty B}
    (G : Form D (.loc τ :: Γ))
    (t : FTerm D Γ τ) : Derivation D enc [.all τ G] (G.substOne t) :=
  .allLeft t (.ax List.mem_cons_self)

end SquirrelLogic
