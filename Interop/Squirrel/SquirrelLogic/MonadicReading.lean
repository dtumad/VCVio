/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import SquirrelLogic.Sum

/-!
# Call-by-value monadic readings of scoped syntax

`Term.denote` reads a term in an algebra whose arguments are functions of their bound variables.
A call-by-value reading in a monad `m` is the same fold with two changes: a constructor receives
each argument as a *computation* depending on the values bound by the constructor
(`CBVAlgebra`), and a variable returns its value by `pure` (`Term.cbv`). A language whose arrows
are read as Kleisli arrows `a → m b` is interpreted this way: the algebra decides when an argument
is evaluated, so effects happen in call-by-value order, and an abstraction becomes a closure that
runs its body when applied. Constructors whose algebra performs effects are the language's
*effectful operations*.

The fundamental lemma of logical relations relates the two folds (`Term.cbv_rel`): given a
relation between plain values and computed values, and one between plain values and computations,
if `pure` sends related values to related computations and each constructor in a fragment `ok`
sends related arguments to related results, then every term of the fragment (`Term.Every ok`)
denotes related meanings in related environments. Adequacy of a monadic reading against an
ordinary one is the instance where a computation is related to a value when running it gives a
related value. `Term.denote_eq_of_every` is the congruence of the plain reading: two algebras that
agree on the constructors of a fragment agree on its terms. `Term.Every ok` is itself a fold, and
it is decidable when `ok` is and constructors have finitely many arguments
(`Term.decidableEvery`).

Nothing here is specific to Squirrel: this is general language theory, kept beside
`SquirrelLogic.Sum` until a second consumer moves both to PolyFun.
-/

public section

universe u v w z z'

namespace IPFunctor.ScopedSignature

variable {S : Type u}

/-- A call-by-value algebra in the monad `m`: each constructor receives each argument as a
computation of the argument's value from the values of its bound variables. -/
abbrev CBVAlgebra (σ : ScopedSignature.{u, v, w} S) (m : Type z → Type z') (V : S → Type z) :=
  ∀ {a} (op : σ.Op a), ((p : σ.Arg op) → Env V (σ.binders op p) → m (V (σ.sort op p))) → m (V a)

namespace CBVAlgebra

variable {σ τ : ScopedSignature.{u, v, w} S} {m : Type z → Type z'} {V : S → Type z}

/-- Interpret each summand's constructors with its own call-by-value algebra. -/
@[expose] def sum (alg₁ : CBVAlgebra σ m V) (alg₂ : CBVAlgebra τ m V) : CBVAlgebra (σ.sum τ) m V
  | _, .inl o, next => alg₁ o next
  | _, .inr o, next => alg₂ o next

end CBVAlgebra

namespace Env

variable {V : S → Type z} {W : S → Type z'} {Γ : List S}

/-- Two environments of one context are related at every position. -/
@[expose] def Rel (R : ∀ a, W a → V a → Prop) (η : Env W Γ) (ζ : Env V Γ) : Prop :=
  ∀ a x, R a (η a x) (ζ a x)

/-- Related blocks extend related environments. -/
theorem Rel.append {R : ∀ a, W a → V a → Prop} {η : Env W Γ} {ζ : Env V Γ}
    (h : Rel R η ζ) : ∀ {Ξ : List S} {ξ : Env W Ξ} {ψ : Env V Ξ}, Rel R ξ ψ →
      Rel R (Env.append ξ η) (Env.append ψ ζ)
  | [], _, _, _ => h
  | _ :: _, _, _, hξ => fun _ x => by
    cases x with
    | zero => exact hξ _ .zero
    | succ x => exact Rel.append h (fun _ y => hξ _ y.succ) _ x

end Env

namespace Term

variable {σ : ScopedSignature.{u, v, w} S} {Γ : List S}

/-- Every constructor of the term satisfies `ok`: a fragment of the language, cut out by its
constructors. -/
@[expose] def Every (ok : ∀ {a}, σ.Op a → Prop) {a : S} (t : σ.Term Γ a) : Prop :=
  t.fold (D := fun _ => Prop) (fun _ _ => True) (fun _ op next => ok op ∧ ∀ p, next p)

theorem every_var (ok : ∀ {a}, σ.Op a → Prop) {a : S} (x : ScopedVar Γ a) :
    (var (σ := σ) x).Every ok :=
  trivial

theorem every_node {ok : ∀ {a}, σ.Op a → Prop} {a : S} (op : σ.Op a)
    (args : (p : σ.Arg op) → σ.Term (σ.binders op p ++ Γ) (σ.sort op p)) :
    (node op args).Every ok ↔ ok op ∧ ∀ p, (args p).Every ok :=
  Iff.rfl

/-- `Every ok` is decidable when `ok` is and every constructor has finitely many arguments: a
structural recursion over the term. -/
@[expose] def decidableEvery (ok : ∀ {a}, σ.Op a → Prop) [∀ {a} (op : σ.Op a), Decidable (ok op)]
    [∀ {a} (op : σ.Op a), Fintype (σ.Arg op)] :
    {j : Judgment S} → (t : IFreeM σ.polynomial (fun j => ScopedVar j.1 j.2) j) →
      Decidable (Every ok (Γ := j.1) (a := j.2) t)
  | _, .pure _ => isTrue trivial
  | _, .liftBind op args =>
    have := fun p => decidableEvery ok (args p)
    inferInstanceAs (Decidable (ok op ∧ ∀ p, Every ok (args p)))

instance {ok : ∀ {a}, σ.Op a → Prop} [∀ {a} (op : σ.Op a), Decidable (ok op)]
    [∀ {a} (op : σ.Op a), Fintype (σ.Arg op)] {a : S} (t : σ.Term Γ a) : Decidable (t.Every ok) :=
  decidableEvery ok t

theorem Every.mono {ok ok' : ∀ {a}, σ.Op a → Prop} (h : ∀ {a} (op : σ.Op a), ok op → ok' op)
    {a : S} {t : σ.Term Γ a} (ht : t.Every ok) : t.Every ok' := by
  induction t using Term.inductionOn with
  | hvar Γ a x => trivial
  | hnode Γ a op args ih => exact ⟨h op ht.1, fun p => ih p (ht.2 p)⟩

/-- Two algebras that agree on the constructors of a fragment give the same reading to its
terms. -/
theorem denote_eq_of_every {V : S → Type z} {ok : ∀ {a}, σ.Op a → Prop}
    (alg₁ alg₂ : Interpretation σ V)
    (h : ∀ {a} (op : σ.Op a), ok op → ∀ next, alg₁ op next = alg₂ op next) {a : S}
    (t : σ.Term Γ a) (ht : t.Every ok) (env : Env V Γ) :
    t.denote alg₁ env = t.denote alg₂ env := by
  induction t using Term.inductionOn with
  | hvar Γ a x => rfl
  | hnode Γ a op args ih =>
    rw [denote_node, denote_node, h op ht.1]
    congr 1
    funext p ξ
    exact ih p (ht.2 p) _

variable {m : Type z → Type z'} [Pure m] {V : S → Type z}

/-- The call-by-value reading: the fold of `Term.denote` in a call-by-value algebra, with each
variable returning its value by `pure`. -/
@[expose] def cbv (alg : CBVAlgebra σ m V) {a : S} (t : σ.Term Γ a) (env : Env V Γ) : m (V a) :=
  t.fold (D := fun j : Judgment S => Env V j.1 → m (V j.2))
    (fun _ x env => pure (env _ x))
    (fun _ op next env => alg op (fun p ξ => next p (Env.append ξ env))) env

@[simp] theorem cbv_var (alg : CBVAlgebra σ m V) {a : S} (x : ScopedVar Γ a) (env : Env V Γ) :
    (var (σ := σ) x).cbv alg env = pure (env a x) :=
  rfl

@[simp] theorem cbv_node (alg : CBVAlgebra σ m V) {a : S} (op : σ.Op a)
    (args : (p : σ.Arg op) → σ.Term (σ.binders op p ++ Γ) (σ.sort op p)) (env : Env V Γ) :
    (node op args).cbv alg env = alg op (fun p ξ => (args p).cbv alg (Env.append ξ env)) :=
  rfl

/-- **The fundamental lemma** of a logical relation between a plain reading and a call-by-value
reading. `RV` relates plain values to computed values and `RC` plain values to computations. If
`pure` sends related values to related computations, and every constructor of the fragment `ok`
sends arguments related at related bound values to related results, then every term of the
fragment means related things in related environments. -/
theorem cbv_rel {W : S → Type z'} (alg₀ : Interpretation σ W) (alg : CBVAlgebra σ m V)
    {ok : ∀ {a}, σ.Op a → Prop} (RV : ∀ a, W a → V a → Prop) (RC : ∀ a, W a → m (V a) → Prop)
    (hpure : ∀ a w v, RV a w v → RC a w (pure v))
    (hop : ∀ {a} (op : σ.Op a), ok op →
      ∀ (nextW : (p : σ.Arg op) → Env W (σ.binders op p) → W (σ.sort op p))
        (nextV : (p : σ.Arg op) → Env V (σ.binders op p) → m (V (σ.sort op p))),
        (∀ p ξW ξV, Env.Rel RV ξW ξV → RC _ (nextW p ξW) (nextV p ξV)) →
          RC a (alg₀ op nextW) (alg op nextV))
    {a : S} (t : σ.Term Γ a) (ht : t.Every ok) {envW : Env W Γ} {envV : Env V Γ}
    (henv : Env.Rel RV envW envV) : RC a (t.denote alg₀ envW) (t.cbv alg envV) := by
  induction t using Term.inductionOn with
  | hvar Γ a x => exact hpure a _ _ (henv a x)
  | hnode Γ a op args ih =>
    exact hop op ht.1 _ _ fun p ξW ξV hξ => ih p (ht.2 p) (henv.append hξ)

end Term

end IPFunctor.ScopedSignature
