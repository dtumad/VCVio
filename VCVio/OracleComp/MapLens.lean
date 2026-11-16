/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/

module

public import VCVio.OracleComp.Coercions.Add.Basic
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Lifts and query bounds along polynomial lenses

`OracleComp.mapLens` (`VCVio.OracleComp.MapLens.Basic`) transports a computation along a lens
`l : PFunctor.Lens spec.toPFunctor spec'.toPFunctor`. This file relates it to oracle-spec
inclusions and to query bounds:

* `liftComp_eq_mapLens`: the lift along a sub-spec inclusion `h : spec ⊂ₒ superSpec` is
  `mapLens h.toLens`, with the summand inclusions into `spec₁ + spec₂` as instances;
* `IsQueryBound.mapLens`, `IsTotalQueryBound.mapLens`, `IsQueryBoundP.mapLens`,
  `AllQueriesSatisfy.mapLens`: a query bound on a computation, read through the lens, bounds the
  transported computation. These are PolyFun's `IsRollBound.mapLens` and `IsChargeBound.mapLens`
  at the charges of VCVio's bounds. When every map `l.toFunB t` is surjective the bounds agree
  (`isQueryBound_mapLens_iff`, `isTotalQueryBound_mapLens_iff`, `isQueryBoundP_mapLens_iff`,
  `allQueriesSatisfy_mapLens_iff`);
* `isPerIndexQueryBound_iff_forall_isQueryBoundP`: a per-index bound is a bound at each index
  separately (PolyFun's `isChargeBound_pi_iff`), which gives `IsPerIndexQueryBound.mapLens` and,
  along a lens injective on queries,
  `IsPerIndexQueryBound.mapLens_of_injective`.
-/

public section

universe u u' w

open OracleSpec PFunctor

open scoped PFunctor

namespace OracleComp

section liftComp

variable {ι : Type u} {τ : Type u'} {spec : OracleSpec.{u, w} ι} {superSpec : OracleSpec.{u', w} τ}
  {α : Type w}

/-- Lifting a computation along a sub-spec inclusion is transport along the inclusion's lens. -/
theorem liftComp_eq_mapLens [h : spec ⊂ₒ superSpec] (mx : OracleComp spec α) :
    liftComp mx superSpec = mx.mapLens h.toLens := by
  rw [liftComp_def, SubSpec.liftLens_eq_toLens]

variable {ι₁ : Type u} {ι₂ : Type u'} {spec₁ : OracleSpec.{u, w} ι₁}
  {spec₂ : OracleSpec.{u', w} ι₂}

/-- Lifting a computation into the left summand of `spec₁ + spec₂` is transport along the
inclusion lens `Sum.inl`. -/
theorem liftComp_add_left_eq_mapLens (mx : OracleComp spec₁ α) :
    liftComp mx (spec₁ + spec₂) = mx.mapLens (Sum.inl ⇆ fun _ => id) :=
  liftComp_eq_mapLens mx

/-- Lifting a computation into the right summand of `spec₁ + spec₂` is transport along the
inclusion lens `Sum.inr`. -/
theorem liftComp_add_right_eq_mapLens (mx : OracleComp spec₂ α) :
    liftComp mx (spec₁ + spec₂) = mx.mapLens (Sum.inr ⇆ fun _ => id) :=
  liftComp_eq_mapLens mx

end liftComp

section queryBound

variable {ι ι' : Type u} {spec : OracleSpec.{u, u} ι} {spec' : OracleSpec.{u, u} ι'}
  {α : Type u} {B : Type*}

/-- A query bound on `oa`, with validity check and cost read through the lens, bounds
`oa.mapLens l`. This is PolyFun's `IsRollBound.mapLens`. -/
theorem IsQueryBound.mapLens (l : Lens spec.toPFunctor spec'.toPFunctor)
    {canQuery : ι' → B → Prop} {cost : ι' → B → B} {oa : OracleComp spec α} {b : B}
    (h : oa.IsQueryBound b (fun t => canQuery (l.toFunA t)) (fun t => cost (l.toFunA t))) :
    (oa.mapLens l).IsQueryBound b canQuery cost :=
  PFunctor.FreeM.IsRollBound.mapLens l h

/-- When every answer of `spec'` is reached by the lens, the query bound on `oa.mapLens l` is the
query bound on `oa` read through the lens. This is PolyFun's `isRollBound_mapLens_iff`. -/
theorem isQueryBound_mapLens_iff (l : Lens spec.toPFunctor spec'.toPFunctor)
    (hl : ∀ t, Function.Surjective (l.toFunB t)) {canQuery : ι' → B → Prop}
    {cost : ι' → B → B} {oa : OracleComp spec α} {b : B} :
    (oa.mapLens l).IsQueryBound b canQuery cost ↔
      oa.IsQueryBound b (fun t => canQuery (l.toFunA t)) (fun t => cost (l.toFunA t)) :=
  PFunctor.FreeM.isRollBound_mapLens_iff l hl

/-- Transport along a lens preserves a total query bound. This is PolyFun's
`isTotalRollBound_mapLens`. -/
theorem IsTotalQueryBound.mapLens (l : Lens spec.toPFunctor spec'.toPFunctor)
    {oa : OracleComp spec α} {n : ℕ} (h : oa.IsTotalQueryBound n) :
    (oa.mapLens l).IsTotalQueryBound n :=
  PFunctor.FreeM.isTotalRollBound_mapLens l oa h

/-- When every answer of `spec'` is reached by the lens, the total query bounds of `oa` and
`oa.mapLens l` agree. -/
theorem isTotalQueryBound_mapLens_iff (l : Lens spec.toPFunctor spec'.toPFunctor)
    (hl : ∀ t, Function.Surjective (l.toFunB t)) {oa : OracleComp spec α} {n : ℕ} :
    (oa.mapLens l).IsTotalQueryBound n ↔ oa.IsTotalQueryBound n :=
  isQueryBound_mapLens_iff l hl

/-- A bound on the queries satisfying `p ∘ l.toFunA` bounds the queries of the transported
computation satisfying `p`. This is PolyFun's `IsChargeBound.mapLens` at the charge that counts
the queries satisfying `p`. -/
theorem IsQueryBoundP.mapLens (l : Lens spec.toPFunctor spec'.toPFunctor) {p : ι' → Prop}
    [DecidablePred p] {oa : OracleComp spec α} {n : ℕ}
    (h : oa.IsQueryBoundP (fun t => p (l.toFunA t)) n) :
    (oa.mapLens l).IsQueryBoundP p n :=
  (isQueryBoundP_iff_isChargeBound p _ n).2 <|
    PFunctor.FreeM.IsChargeBound.mapLens l <| (isQueryBoundP_iff_isChargeBound _ oa n).1 h

/-- When every answer of `spec'` is reached by the lens, the bound on the queries of
`oa.mapLens l` satisfying `p` is the bound on the queries of `oa` satisfying `p ∘ l.toFunA`. -/
theorem isQueryBoundP_mapLens_iff (l : Lens spec.toPFunctor spec'.toPFunctor)
    (hl : ∀ t, Function.Surjective (l.toFunB t)) {p : ι' → Prop} [DecidablePred p]
    {oa : OracleComp spec α} {n : ℕ} :
    (oa.mapLens l).IsQueryBoundP p n ↔ oa.IsQueryBoundP (fun t => p (l.toFunA t)) n :=
  (isQueryBoundP_iff_isChargeBound p _ n).trans <|
    (PFunctor.FreeM.isChargeBound_mapLens_iff l hl).trans
      (isQueryBoundP_iff_isChargeBound _ oa n).symm

/-- A predicate-only bound on `oa` at `P ∘ l.toFunA` is a predicate-only bound at `P` on the
transported computation. -/
theorem AllQueriesSatisfy.mapLens (l : Lens spec.toPFunctor spec'.toPFunctor) {P : ι' → Prop}
    {oa : OracleComp spec α} (h : oa.AllQueriesSatisfy fun t => P (l.toFunA t)) :
    (oa.mapLens l).AllQueriesSatisfy P := by
  classical
  exact (allQueriesSatisfy_iff_isChargeBound _ P).2 <|
    PFunctor.FreeM.IsChargeBound.mapLens l <| (allQueriesSatisfy_iff_isChargeBound oa _).1 h

/-- When every answer of `spec'` is reached by the lens, `oa.mapLens l` satisfies `P` at every
query exactly when `oa` satisfies `P ∘ l.toFunA`. -/
theorem allQueriesSatisfy_mapLens_iff (l : Lens spec.toPFunctor spec'.toPFunctor)
    (hl : ∀ t, Function.Surjective (l.toFunB t)) {P : ι' → Prop} {oa : OracleComp spec α} :
    (oa.mapLens l).AllQueriesSatisfy P ↔ oa.AllQueriesSatisfy fun t => P (l.toFunA t) := by
  rw [allQueriesSatisfy_def, allQueriesSatisfy_def]
  exact isQueryBound_mapLens_iff l hl

/-- A per-index bound is a bound at each index separately. With the per-index charges
`fun t => Pi.single t 1`, this is PolyFun's `isChargeBound_pi_iff`. -/
theorem isPerIndexQueryBound_iff_forall_isQueryBoundP [DecidableEq ι] (oa : OracleComp spec α)
    (qb : ι → ℕ) :
    oa.IsPerIndexQueryBound qb ↔ ∀ t, oa.IsQueryBoundP (· = t) (qb t) := by
  rw [isPerIndexQueryBound_iff_isChargeBound, PFunctor.FreeM.isChargeBound_pi_iff]
  refine forall_congr' fun t => ?_
  rw [isQueryBoundP_iff_isChargeBound]
  simp only [Pi.single_apply, Pi.zero_apply, @eq_comm _ t]

/-- A per-index bound on the transported computation follows from a bound, at each index `t'`,
on the queries of `oa` that the lens sends to `t'`. -/
theorem IsPerIndexQueryBound.mapLens [DecidableEq ι'] (l : Lens spec.toPFunctor spec'.toPFunctor)
    {oa : OracleComp spec α} {qb : ι' → ℕ}
    (h : ∀ t', oa.IsQueryBoundP (fun t => l.toFunA t = t') (qb t')) :
    (oa.mapLens l).IsPerIndexQueryBound qb :=
  (isPerIndexQueryBound_iff_forall_isQueryBoundP _ qb).2 fun t' => IsQueryBoundP.mapLens l (h t')

/-- Along a lens injective on queries, a per-index bound at `qb ∘ l.toFunA` is a per-index bound
at `qb` on the transported computation. -/
theorem IsPerIndexQueryBound.mapLens_of_injective [DecidableEq ι] [DecidableEq ι']
    (l : Lens spec.toPFunctor spec'.toPFunctor) (hl : Function.Injective l.toFunA)
    {oa : OracleComp spec α} {qb : ι' → ℕ} (h : oa.IsPerIndexQueryBound (qb ∘ l.toFunA)) :
    (oa.mapLens l).IsPerIndexQueryBound qb := by
  refine IsPerIndexQueryBound.mapLens l fun t' => ?_
  rw [isPerIndexQueryBound_iff_forall_isQueryBoundP] at h
  by_cases ht : ∃ s, l.toFunA s = t'
  · obtain ⟨s, rfl⟩ := ht
    exact (h s).of_imp fun t hts => hl hts
  · exact (((isQueryBoundP_zero_iff oa fun t => l.toFunA t ≠ t').2
      (allQueriesSatisfy_of_forall (fun t htt => ht ⟨t, htt⟩) oa)).of_imp
        fun t htt => not_not.2 htt).mono (Nat.zero_le _)

end queryBound

end OracleComp
