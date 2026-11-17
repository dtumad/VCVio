/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import SquirrelLogic.Global

/-!
# Structural rules for indistinguishability

The rules of BC14 (Fig. 2) and LICS23 (Figs. 5, 8) about `∼` that need no cryptographic
assumption, sound over `Valid` for every model restriction and every adversary class:

* `Valid.equiv_refl`, `Valid.equiv_symm`, `Valid.equiv_trans`;
* FA, as LICS23 splits it: `Valid.equiv_fn` (an honest symbol may be added), `Valid.equiv_adv`
  (G.Equiv:FA-Adv, a term the attacker computes may be added) and `Valid.equiv_app`
  (G.Equiv:FA-App, two entries may be replaced by the application of one to the other). BC14's
  FA for an honest symbol `f` is `equiv_fn` followed by `equiv_app`;
* `Valid.equiv_tail` (Restr), `Valid.equiv_dup` (Dup), `Valid.equiv_ite` (If);
* `Valid.equiv_rewrite`: rewriting an entry under an overwhelming equality `[t = t']`;
* `Valid.equiv_eq_self` (BC14's Eq1): `EQ(t, t)` may be replaced by `true`.

Each rule reads its premise and conclusion through `Form.holds_equiv` and applies one law of
`SquirrelLogic.Indist`, whose proof is a named reduction and an equality of advantages at every
`η`. The vector entries that rules act on are the first ones.
-/

public section

namespace SquirrelLogic

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B} {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M}
  {Γ : List (Kind B)} {Θ : List (Form D Γ)} {a τ : Ty B} {τs : List (Ty B)} {u v w : Vec D Γ τs}

namespace Valid

/-- **Refl.** -/
theorem equiv_refl (u : Vec D Γ τs) : Valid R C Θ (.equiv u u) :=
  fun _ _ _ _ _ => Form.holds_equiv.2 (AdvClass.Indist.refl _)

/-- **Sym.** -/
theorem equiv_symm (h : Valid R C Θ (.equiv u v)) : Valid R C Θ (.equiv v u) :=
  fun M hl hR env hΘ => Form.holds_equiv.2 (Form.holds_equiv.1 (h M hl hR env hΘ)).symm

/-- **Trans.** -/
theorem equiv_trans (h₁ : Valid R C Θ (.equiv u v)) (h₂ : Valid R C Θ (.equiv v w)) :
    Valid R C Θ (.equiv u w) := fun M hl hR env hΘ => Form.holds_equiv.2 <|
  (Form.holds_equiv.1 (h₁ M hl hR env hΘ)).trans (Form.holds_equiv.1 (h₂ M hl hR env hΘ))

/-- **G.Equiv:FA-App.** Two entries may be replaced by the application of the first to the
second. -/
theorem equiv_app {b : Ty B} {t s : FTerm D Γ (.arrow a b)} {t' s' : FTerm D Γ a}
    (h : Valid R C Θ (.equiv (Env.cons t (Env.cons t' u)) (Env.cons s (Env.cons s' v)))) :
    Valid R C Θ (.equiv (Env.cons (FTerm.app t t') u) (Env.cons (FTerm.app s s') v)) := by
  intro M hl hR env hΘ
  have hI := Form.holds_equiv.1 (h M hl hR env hΘ)
  simp only [Form.holds_equiv, Vec.rv_cons] at hI ⊢
  exact hI.app

/-- **FA-Fn.** An honest symbol may be added. -/
theorem equiv_fn (f : D.Fn τ) (h : Valid R C Θ (.equiv u v)) :
    Valid R C Θ (.equiv (Env.cons (FTerm.fn f) u) (Env.cons (FTerm.fn f) v)) := by
  intro M hl hR env hΘ
  simp only [Form.holds_equiv, Vec.rv_cons, FTerm.denote_fn]
  exact (Form.holds_equiv.1 (h M hl hR env hΘ)).fn f

/-- **G.Equiv:FA-Adv.** A term the attacker computes may be added. -/
theorem equiv_adv {t : FTerm D Γ τ} (ht : Valid R C Θ (.adv t)) (h : Valid R C Θ (.equiv u v)) :
    Valid R C Θ (.equiv (Env.cons t u) (Env.cons t v)) := by
  intro M hl hR env hΘ
  simp only [Form.holds_equiv, Vec.rv_cons]
  exact (Form.holds_equiv.1 (h M hl hR env hΘ)).adv (Form.holds_adv.1 (ht M hl hR env hΘ))

/-- **Restr.** An entry may be dropped. -/
theorem equiv_tail {t s : FTerm D Γ τ} (h : Valid R C Θ (.equiv (Env.cons t u) (Env.cons s v))) :
    Valid R C Θ (.equiv u v) := by
  intro M hl hR env hΘ
  have hI := Form.holds_equiv.1 (h M hl hR env hΘ)
  simp only [Vec.rv_cons] at hI
  exact Form.holds_equiv.2 hI.tail

/-- **Dup.** An entry may be duplicated. -/
theorem equiv_dup {t s : FTerm D Γ τ} (h : Valid R C Θ (.equiv (Env.cons t u) (Env.cons s v))) :
    Valid R C Θ (.equiv (Env.cons t (Env.cons t u)) (Env.cons s (Env.cons s v))) := by
  intro M hl hR env hΘ
  have hI := Form.holds_equiv.1 (h M hl hR env hΘ)
  simp only [Form.holds_equiv, Vec.rv_cons] at hI ⊢
  exact hI.dup

/-- **If.** A condition and two branches may be replaced by the conditional. -/
theorem equiv_ite {c c' : FTerm D Γ .bool} {t t' s s' : FTerm D Γ a}
    (h : Valid R C Θ (.equiv (Env.cons c (Env.cons t (Env.cons t' u)))
      (Env.cons c' (Env.cons s (Env.cons s' v))))) :
    Valid R C Θ (.equiv (Env.cons (FTerm.ite c t t') u) (Env.cons (FTerm.ite c' s s') v)) := by
  intro M hl hR env hΘ
  have hI := Form.holds_equiv.1 (h M hl hR env hΘ)
  simp only [Form.holds_equiv, Vec.rv_cons] at hI ⊢
  exact hI.ite

/-- **Rewriting under an overwhelming equality.** If `[t = t']`, an entry `t` may be replaced by
`t'`. LICS23's G.Rewrite, for an equivalence atom. -/
theorem equiv_rewrite {t t' : FTerm D Γ τ} {w : Vec D Γ (τ :: τs)}
    (heq : Valid R C Θ (.box (FTerm.eq t t')))
    (h : Valid R C Θ (.equiv (Env.cons t' u) w)) : Valid R C Θ (.equiv (Env.cons t u) w) := by
  intro M hl hR env hΘ
  have hI := Form.holds_equiv.1 (h M hl hR env hΘ)
  simp only [Form.holds_equiv, Vec.rv_cons] at hI ⊢
  refine hI.of_negligible_ne (negligible_of_le (fun η => prEvent_mono _ _ _ fun ρ hne => ?_)
    (Form.holds_box.1 (heq M hl hR env hΘ)))
  simp only [FTerm.denote_eq]
  refine @decide_eq_false _ (Classical.propDecidable _) fun he => hne ?_
  change Env.cons _ _ = Env.cons _ _
  rw [he]

/-- **Perm.** Reindexing both vectors along one map of positions that preserves types; this
permutes, projects and duplicates entries. -/
theorem equiv_rename {τs' : List (Ty B)} (r : Renaming τs' τs) (h : Valid R C Θ (.equiv u v)) :
    Valid R C Θ (.equiv (Env.rename r u) (Env.rename r v)) :=
  fun M hl hR env hΘ => Form.holds_equiv.2 ((Form.holds_equiv.1 (h M hl hR env hΘ)).rename r)

/-- **Eq1** (BC14 Fig. 2): `EQ(t, t), u⃗ ∼ true, u⃗`. The two vectors have the same values at
every tape. -/
theorem equiv_eq_self (t : FTerm D Γ τ) (u : Vec D Γ τs) :
    Valid R C Θ (.equiv (Env.cons (FTerm.eq t t) u) (Env.cons FTerm.tt u)) := by
  intro M _ _ env _
  refine Form.holds_equiv.2 fun A _ => negligible_of_zero fun η => ENNReal.absDiff_eq_zero.2 ?_
  have h : Vec.rv M (C M) (Env.cons (FTerm.eq t t) u) env =
      Vec.rv M (C M) (Env.cons FTerm.tt u) env := by
    simp only [Vec.rv_cons, FTerm.denote_eq, FTerm.denote_tt]
    congr 1
  rw [h]

/-- **FA** (BC14) for an honest symbol of arrow type: FA-Fn, then FA-App. -/
theorem equiv_fa {b : Ty B} (f : D.Fn (.arrow a b)) {t s : FTerm D Γ a}
    (h : Valid R C Θ (.equiv (Env.cons t u) (Env.cons s v))) :
    Valid R C Θ (.equiv (Env.cons (FTerm.app (FTerm.fn f) t) u)
      (Env.cons (FTerm.app (FTerm.fn f) s) v)) :=
  (equiv_fn f h).equiv_app

end Valid

end SquirrelLogic
