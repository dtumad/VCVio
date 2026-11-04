/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.MeasuredProgram.Composition
public import PolyFun.PFunctor.Free.Cost.Measured
public import PolyFun.PFunctor.Handler.Free

/-!
# Measured programs as PolyFun measured programs

A measured program is PolyFun's `PFunctor.FreeM.MeasuredProgram` whose answers to an operation
`o` at view `v` are the responses `(spec v).Range o` of its instruction set
(`MeasuredProgram.toFreeM`). The translation keeps the view, the operations, the program, the
answers and the charges, so it preserves the run definitionally (`run_toFreeM`) and the cost bound
through the path-charge reading of `WorstCaseCostBound` (`costAtMost_toFreeM_iff`).

The composite `outer.comp inner` and the PolyFun composite of the translations have the same
views and operations, but not the same answer family, charges or program as terms: the composite
instruction set is a sum of `OracleSpec.sigma` specifications, PolyFun's is a family defined by
cases, and the inner and outer programs are embedded by simulating lifted queries rather than by
relabelling along a lens. They agree after relabelling along the lens `compLens`, which is the
identity on operations and on answers (`program_comp_eq_mapLens`). Hence the composite runs as the
PolyFun composite (`run_comp_eq_toFreeM`), and a PolyFun cost bound on the composite of the
translations bounds the composite (`costAtMost_comp_of_toFreeM`).
-/

public section

open OracleSpec PFunctor

namespace OracleComp

namespace MeasuredProgram

variable {A B C ω : Type}

/-- A measured program as a PolyFun measured program, answering an operation `o` at view `v` by
the responses of its instruction set. -/
@[expose] def toFreeM (M : MeasuredProgram A B ω) : FreeM.MeasuredProgram A B ω where
  View := M.View
  view := M.view
  Op := M.Op
  Ans v o := (M.spec v).Range o
  program := M.program
  answer v o := M.answer v o
  cost := M.cost

/-- The translation runs the same handlers' execution. -/
@[simp] theorem run_toFreeM (M : MeasuredProgram A B ω) (input : A) :
    M.toFreeM.run input = M.run input :=
  rfl

/-- The translation realizes the same functions. -/
@[simp] theorem realizes_toFreeM_iff (M : MeasuredProgram A B ω) (f : A → B) :
    M.toFreeM.Realizes f ↔ M.Realizes f :=
  Iff.rfl

/-- The translation has the same cost bounds: a worst-case cost bound bounds the charge of every
completed path. -/
@[simp] theorem costAtMost_toFreeM_iff [AddCommMonoid ω] [Preorder ω] (M : MeasuredProgram A B ω)
    (budget : ω) : M.toFreeM.CostAtMost budget ↔ M.CostAtMost budget :=
  forall_congr' fun v =>
    (worstCaseCostBound_iff_forall_charge_le (M.program v) ⟨M.cost⟩ budget).symm

/-- The lens from the PolyFun composite interface of the translations to the composite
instruction set: the identity on operations and on answers. -/
@[expose] def compLens (outer : MeasuredProgram B C ω) (inner : MeasuredProgram A B ω)
    (v : inner.View) :
    Lens ⟨_, (outer.toFreeM.comp inner.toFreeM).Ans v⟩ ((outer.comp inner).spec v).toPFunctor where
  toFunA o := o
  toFunB
    | .inl _, b => b
    | .inr _, b => b

/-- The composite program is the PolyFun composite program of the translations, relabelled along
`compLens`. -/
theorem program_comp_eq_mapLens (outer : MeasuredProgram B C ω) (inner : MeasuredProgram A B ω)
    (v : inner.View) :
    (outer.comp inner).program v =
      ((outer.toFreeM.comp inner.toFreeM).program v).mapLens (compLens outer inner v) := by
  let li : Lens (inner.spec v).toPFunctor ((outer.comp inner).spec v).toPFunctor :=
    ⟨fun q => Sum.inl ⟨v, q⟩, fun _ b => b⟩
  let lo (r : B) : Lens (outer.spec (outer.view r)).toPFunctor
      ((outer.comp inner).spec v).toPFunctor :=
    ⟨fun q => Sum.inr ⟨outer.view r, q⟩, fun _ b => b⟩
  change FreeM.bind (FreeM.liftM (Handler.ofLens li) (inner.program v))
    (fun r => FreeM.liftM (Handler.ofLens (lo r)) (outer.program (outer.view r))) = _
  simp only [Handler.liftM_ofLens]
  refine Eq.trans ?_ (FreeM.mapLens_bind (compLens outer inner v) _ _).symm
  refine congrArg₂ FreeM.bind ?_ (funext fun r => ?_)
  · exact (FreeM.mapLens_mapLens (compLens outer inner v)
      (outer.toFreeM.innerLens inner.toFreeM v) (inner.program v)).symm
  · exact (FreeM.mapLens_mapLens (compLens outer inner v)
      (outer.toFreeM.outerLens inner.toFreeM v (outer.view r)) (outer.program (outer.view r))).symm

/-- The composite runs as the PolyFun composite of the translations. -/
theorem run_comp_eq_toFreeM (outer : MeasuredProgram B C ω) (inner : MeasuredProgram A B ω)
    (input : A) : (outer.comp inner).run input = (outer.toFreeM.comp inner.toFreeM).run input := by
  change (outer.comp inner).toFreeM.run input = _
  rw [FreeM.MeasuredProgram.run_eq_output, FreeM.MeasuredProgram.run_eq_output]
  have key : ∀ x : FreeM ((outer.comp inner).spec (inner.view input)).toPFunctor C,
      x = ((outer.toFreeM.comp inner.toFreeM).program (inner.view input)).mapLens
        (compLens outer inner (inner.view input)) →
      FreeM.output x (FreeM.Path.ofHandler ((outer.comp inner).answer (inner.view input)) x) =
        FreeM.output ((outer.toFreeM.comp inner.toFreeM).program (inner.view input))
          (FreeM.Path.ofHandler ((outer.toFreeM.comp inner.toFreeM).answer (inner.view input))
            _) := by
    rintro x rfl
    rw [FreeM.output_mapLens_ofHandler]
    congr 2
    funext o
    rcases o with ⟨_, _⟩ | ⟨_, _⟩ <;> rfl
  exact key _ (program_comp_eq_mapLens outer inner (inner.view input))

/-- A PolyFun cost bound on the composite of the translations bounds the composite. -/
theorem costAtMost_comp_of_toFreeM [AddCommMonoid ω] [Preorder ω]
    {outer : MeasuredProgram B C ω} {inner : MeasuredProgram A B ω} {budget : ω}
    (h : (outer.toFreeM.comp inner.toFreeM).CostAtMost budget) :
    (outer.comp inner).CostAtMost budget := by
  rw [← costAtMost_toFreeM_iff]
  intro (v : inner.View)
  have key : ∀ x : FreeM ((outer.comp inner).spec v).toPFunctor C,
      x = ((outer.toFreeM.comp inner.toFreeM).program v).mapLens (compLens outer inner v) →
      ∀ q : FreeM.Path x, FreeM.Path.charge (outer.comp inner).cost x q ≤ budget := by
    rintro x rfl q
    rw [FreeM.Path.charge_pullMapLens]
    convert h v (FreeM.Path.pullMapLens _ _ q) using 2
    funext o
    rcases o with ⟨_, _⟩ | ⟨_, _⟩ <;> rfl
  exact key _ (program_comp_eq_mapLens outer inner v)

end MeasuredProgram

end OracleComp
