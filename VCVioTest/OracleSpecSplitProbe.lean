/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose
public import PolyFun.PFunctor.Free.WP

/-!
# Exploratory probe: do PolyFun fold lemmas fire on `simulateQ` goals?

Each example closes a `simulateQ` goal using only a PolyFun/CSLib lemma about
`PFunctor.FreeM.liftM`, through `simp only` or `rw` (syntactic/keyed matching), never through
`exact`/`change` (definitional unfolding). Failing examples mark lemmas that VCVio must restate.
-/

public section

namespace VCVioTest.OracleSpecSplitProbe

universe u

open OracleSpec OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {m : Type u → Type u} [Monad m] [LawfulMonad m]
  {α β : Type u}

/-! ## P1: `liftM_bind` -/

example (impl : QueryImpl spec m) (mx : OracleComp spec α) (my : α → OracleComp spec β) :
    simulateQ impl (mx >>= my) = simulateQ impl mx >>= fun x => simulateQ impl (my x) := by
  simp only [PFunctor.FreeM.liftM_bind]

example (impl : QueryImpl spec m) (mx : OracleComp spec α) (my : α → OracleComp spec β) :
    simulateQ impl (mx >>= my) = simulateQ impl mx >>= fun x => simulateQ impl (my x) := by
  rw [PFunctor.FreeM.liftM_bind]

/-! ## P2: `liftM_map`, `liftM_pure`, `liftM_seq` -/

example (impl : QueryImpl spec m) (mx : OracleComp spec α) (f : α → β) :
    simulateQ impl (f <$> mx) = f <$> simulateQ impl mx := by
  simp only [PFunctor.FreeM.liftM_map]

example (impl : QueryImpl spec m) (mx : OracleComp spec α) (f : α → β) :
    simulateQ impl (f <$> mx) = f <$> simulateQ impl mx := by
  rw [PFunctor.FreeM.liftM_map]

example (impl : QueryImpl spec m) (og : OracleComp spec (α → β)) (mx : OracleComp spec α) :
    simulateQ impl (og <*> mx) = simulateQ impl og <*> simulateQ impl mx := by
  simp only [PFunctor.FreeM.liftM_seq]

/-! ## P3: query lemma (`liftM_lift`) on the canonical primitive query -/

example (impl : QueryImpl spec m) (t : spec.Domain) :
    simulateQ impl (PFunctor.FreeM.lift (P := spec.toPFunctor) t) = impl t := by
  simp only [PFunctor.FreeM.liftM_lift]

example (impl : QueryImpl spec m) (q : OracleQuery spec α) :
    simulateQ impl (liftM q) = q.cont <$> impl q.input := by
  simp only [PFunctor.FreeM.liftM_liftObj]

example (impl : QueryImpl spec m) (t : spec.Domain) :
    simulateQ impl (liftM (spec.query t)) = impl t := by
  simp only [PFunctor.FreeM.liftM_liftObj]

/-! ## P4: `liftM_mapLens` -/

example {ι' : Type u} {spec' : OracleSpec.{u, u} ι'}
    (l : PFunctor.Lens spec.toPFunctor spec'.toPFunctor) (impl : QueryImpl spec' m)
    (mx : OracleComp spec α) :
    simulateQ impl (mx.mapLens l) =
      simulateQ (fun t => l.toFunB t <$> impl (l.toFunA t)) mx := by
  rw [PFunctor.FreeM.liftM_mapLens]

/-! ## P5: `liftM_natural` (monad-morphism naturality) -/

example {n : Type u → Type u} [Monad n] [LawfulMonad n] (φ : m →ᵐ n) (impl : QueryImpl spec m)
    (mx : OracleComp spec α) :
    φ (simulateQ impl mx) = simulateQ (fun t => φ (impl t)) mx := by
  rw [PFunctor.FreeM.liftM_natural]

/-! ## P6: `liftM_comp` (composition of folds) -/

example {ι' : Type u} {spec' : OracleSpec.{u, u} ι'} (so' : QueryImpl spec' m)
    (so : QueryImpl spec (OracleComp spec')) (mx : OracleComp spec α) :
    simulateQ so' (simulateQ so mx) = simulateQ (fun t => simulateQ so' (so t)) mx := by
  rw [PFunctor.FreeM.liftM_comp]

/-! ## P7: `wpFold_liftM` -/

example {ι' : Type u} {spec' : OracleSpec.{u, u} ι'} {l : Type u} [CompleteLattice l]
    (handler : QueryImpl spec (OracleComp spec')) (Φ : PFunctor.OpSpec spec'.toPFunctor l)
    (mx : OracleComp spec α) (post : α → l) :
    PFunctor.FreeM.wpFold Φ (simulateQ handler mx) post =
      PFunctor.FreeM.wpFold (Φ.pullback handler) mx post := by
  rw [PFunctor.FreeM.wpFold_liftM]

/-! ## P8: the reverse direction — VCVio's `simulateQ_bind` on a raw `FreeM.liftM` goal -/

example (impl : QueryImpl spec m) (mx : OracleComp spec α) (my : α → OracleComp spec β) :
    PFunctor.FreeM.liftM impl (mx >>= my) =
      PFunctor.FreeM.liftM impl mx >>= fun x => PFunctor.FreeM.liftM impl (my x) := by
  simp only [simulateQ_bind]

/-! ## P9: `IsRollBound` lemmas on `IsQueryBound` goals (unchanged by Option A) -/

example (oa : OracleComp spec α) (f : α → β) (b : ℕ) (canQuery : ι → ℕ → Prop)
    (cost : ι → ℕ → ℕ) :
    IsQueryBound (f <$> oa) b canQuery cost ↔ IsQueryBound oa b canQuery cost := by
  simp only [PFunctor.FreeM.isRollBound_map_iff]

example (oa : OracleComp spec α) (f : α → β) (b : ℕ) (canQuery : ι → ℕ → Prop)
    (cost : ι → ℕ → ℕ) :
    IsQueryBound (f <$> oa) b canQuery cost ↔ IsQueryBound oa b canQuery cost := by
  rw [PFunctor.FreeM.isRollBound_map_iff]

/-! ## P10: default `simp` still normalizes through `simulateQ` -/

example (impl : QueryImpl spec m) (mx : OracleComp spec α) (my : α → OracleComp spec β)
    (f : β → α) :
    simulateQ impl (f <$> (mx >>= my)) =
      f <$> (simulateQ impl mx >>= fun x => simulateQ impl (my x)) := by
  simp

end VCVioTest.OracleSpecSplitProbe
