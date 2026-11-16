/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import SquirrelLogic.Global
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Renaming names

Renaming the names of a closed vector of terms gives an indistinguishable vector (BC14's
α-renaming of names). `Term.renameNames π` replaces every name `n` by `π n`; names are indexed by
their types, so `π` preserves types and the renaming needs no casts.

The rule is sound in models where renaming the names is a bijection `σ` of the honest tapes:
`n` reads from `σ ρh` what `π n` reads from `ρh` (`Model.RenamesNames`). The uniform distribution
is invariant under `σ`, so every distinguisher has advantage zero. LICS23 asks of names only that
their samplings be independent and identically distributed for each output type; when each name
and index reads its own slice of the honest tape, such a `σ` exchanges the slices. The
restriction is a hypothesis of the rule, not derived from those requirements.

The vectors must be closed: a free variable stands for any random variable, which may read the
honest tape, and then renaming is unsound.
-/

public section

namespace SquirrelLogic

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B}

/-- Replace every name `n` by `π n`. -/
@[expose] def Term.renameNames (π : ∀ {a b : Ty B}, D.Name a b → D.Name a b)
    {Γ : List (Kind B)} {s : Kind B} (t : (fullSig D).Term Γ s) : (fullSig D).Term Γ s :=
  t.fold (D := fun j : Judgment (Kind B) => (fullSig D).Term j.1 j.2) (fun _ x => .pure x)
    fun ⟨_, s⟩ o next => match s, o, next with
      | _, .inl (.name n), _ => .liftBind (.inl (.name (π n))) fun p => nomatch p
      | _, o, next => .liftBind o next

/-- Rename the names of every entry of a vector. -/
@[expose] def Vec.renameNames (π : ∀ {a b : Ty B}, D.Name a b → D.Name a b)
    {Γ : List (Kind B)} {τs : List (Ty B)} (u : Vec D Γ τs) : Vec D Γ τs :=
  fun _ x => Term.renameNames π (u _ x)

/-- Renaming names along `π` is the bijection `σ` of the honest tapes at `η`. -/
@[expose] def Model.RenamesNames (π : ∀ {a b : Ty B}, D.Name a b → D.Name a b) (M : Model D) :
    Prop :=
  ∀ η, ∃ σ : M.TapeH η ≃ M.TapeH η,
    ∀ {a b : Ty B} (n : D.Name a b) i ρh, M.name η (π n) i ρh = M.name η n i (σ ρh)

variable {M : Model D} {π : ∀ {a b : Ty B}, D.Name a b → D.Name a b}

/-- Pointwise, renaming names along `π` reads the honest tape through `σ`. -/
theorem denote_renameNames {η : ℕ} {σ : M.TapeH η ≃ M.TapeH η}
    (hσ : ∀ {a b : Ty B} (n : D.Name a b) i ρh, M.name η (π n) i ρh = M.name η n i (σ ρh))
    (ρ : M.Tape η) {Γ : List (Kind B)} {s : Kind B} (t : (fullSig D).Term Γ s)
    (e : Env (Kind.PtValue M η) Γ) :
    (Term.renameNames π t).denote (Interpretation.sum (interp M η ρ) (ptGlobal M η)) e =
      t.denote (Interpretation.sum (interp M η (ρ.1, σ ρ.2)) (ptGlobal M η)) e := by
  have h := IFreeM.fold_fusion (P := (fullSig D).polynomial)
    (D := fun j : Judgment (Kind B) => (fullSig D).Term j.1 j.2)
    (E := fun j : Judgment (Kind B) => Env (Kind.PtValue M η) j.1 → Kind.PtValue M η j.2)
    (fun _ t e => t.denote (Interpretation.sum (interp M η ρ) (ptGlobal M η)) e)
    (fun _ x => .pure x) (fun _ x e => e _ x)
    (fun ⟨_, s⟩ o next => match s, o, next with
      | _, .inl (.name n), _ => .liftBind (.inl (.name (π n))) fun p => nomatch p
      | _, o, next => .liftBind o next)
    (fun _ o next e => Interpretation.sum (interp M η (ρ.1, σ ρ.2)) (ptGlobal M η) o
      fun p ξ => next p (Env.append ξ e))
    (fun _ _ => rfl) ?_ t
  · exact congrFun h e
  rintro ⟨Γ, s⟩ (o | o) ds
  · cases o <;> first | rfl | (funext e i; exact hσ _ i ρ.2)
  · rfl

/-- A closed term with its names renamed reads the honest tape through `σ`. -/
theorem denote_renameNames_closed (C : AdvClass M) {η : ℕ} {σ : M.TapeH η ≃ M.TapeH η}
    (hσ : ∀ {a b : Ty B} (n : D.Name a b) i ρh, M.name η (π n) i ρh = M.name η n i (σ ρh))
    (ρ : M.Tape η) {τ : Ty B} (t : FTerm D [] τ) (env : Env (Kind.Value M) []) :
    (Term.renameNames π t).denote (fullInterp M C) env η ρ =
      t.denote (fullInterp M C) env η (ρ.1, σ ρ.2) := by
  have h₁ := eval_denote_fullInterp M C η ρ (Term.renameNames π t) env
  have h₂ := eval_denote_fullInterp M C η (ρ.1, σ ρ.2) t env
  refine h₁.trans ((denote_renameNames hσ ρ t _).trans (Eq.trans ?_ h₂.symm))
  rw [Env.eq_empty (evalEnv M η ρ env), Env.eq_empty (evalEnv M η (ρ.1, σ ρ.2) env)]

/-- **Name renaming.** In models where renaming names is a bijection of the honest tapes, a
closed vector is indistinguishable from its renaming: every distinguisher has advantage zero. -/
theorem Valid.equiv_renameNames {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M}
    (hR : ∀ M, R M → M.RenamesNames π) {Θ : List (Form D [])} {τs : List (Ty B)}
    (u : Vec D [] τs) : Valid R C Θ (.equiv u (u.renameNames π)) := by
  intro M _ hRM env _
  refine Form.holds_equiv.2 fun A _ => negligible_of_zero fun η => ENNReal.absDiff_eq_zero.2 ?_
  obtain ⟨σ, hσ⟩ := hR M hRM η
  have hrv : ∀ ρ, Vec.rv M (C M) (u.renameNames π) env η ρ =
      Vec.rv M (C M) u env η (ρ.1, σ ρ.2) :=
    fun ρ => funext fun _ => funext fun x => denote_renameNames_closed (C M) hσ ρ (u _ x) env
  simp only [hrv]
  exact (SampleableType.prEvent_uniformSample_equiv ((Equiv.refl _).prodCongr σ)
    fun ρ => A η (Vec.rv M (C M) u env η ρ) ρ.1 = true).symm

end SquirrelLogic
