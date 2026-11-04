/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.CostModel

/-!
# Complete-path costs with determined responses

When a deterministic handler gives the only inhabitant of every response type, the free
instrumented computation has exactly one execution path: the handler's. Its worst-case cost bound
is then the cost recorded by running that handler once. Certified instruction sets, whose response
types are singleton subtypes, have this property. Without it, a worst-case bound still bounds the
cost recorded by any deterministic handler, since that execution is one path.

A bound on declared query costs does not account for computation inside the handler.
-/

public section

open OracleComp OracleSpec

namespace OracleComp

variable {ι ω A : Type} {spec : OracleSpec ι} [AddCommMonoid ω]

/-- A deterministic handler's instrumented execution returns the output and the charge of the one
path the handler picks. -/
theorem run_simulateQ_withAddCost_id (answer : QueryImpl spec Id) (c : spec.Domain → ω)
    (oa : OracleComp spec A) :
    (simulateQ (answer.withAddCost c) oa).run =
      (PFunctor.FreeM.output oa (PFunctor.FreeM.Path.ofHandler answer oa),
        Multiplicative.ofAdd (PFunctor.FreeM.Path.charge c oa
          (PFunctor.FreeM.Path.ofHandler answer oa))) := by
  induction oa using PFunctor.FreeM.rec with
  | pure a => rfl
  | liftBind t k ih =>
    change (simulateQ (answer.withAddCost c) ((spec.query t : OracleComp spec _) >>= k)).run = _
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      QueryImpl.withAddCost_apply, map_bind, id_map, bind_assoc, WriterT.run_bind,
      AddWriterT.run_addTell, WriterT.run_liftM, bind_map_left, one_mul, Prod.mk.eta, id_map',
      pure_bind]
    exact congrArg (fun x => (x.1, Multiplicative.ofAdd (c t) * x.2)) (ih (answer t))

/-- A deterministic handler's execution, with its recorded cost, is one path of the instrumented
computation. -/
theorem run_withAddCost_mem_support_costDist (answer : QueryImpl spec Id)
    (oa : OracleComp spec A) (cm : CostModel spec ω) :
    (simulateQ (answer.withAddCost cm.queryCost) oa).run ∈ support (costDist oa cm) := by
  rw [support_costDist_eq_range_charge, run_simulateQ_withAddCost_id]
  exact ⟨_, rfl⟩

/-- A worst-case cost bound bounds the cost recorded by any deterministic handler. -/
theorem worstCaseCostBound_runAdd_withAddCost_le [Preorder ω] {oa : OracleComp spec A}
    {cm : CostModel spec ω} {B : ω} (h : WorstCaseCostBound oa cm B)
    (answer : QueryImpl spec Id) :
    (simulateQ (answer.withAddCost cm.queryCost) oa).runAdd.2 ≤ B :=
  (worstCaseCostBound_iff_support_bound oa cm B).mp h _
    (run_withAddCost_mem_support_costDist answer oa cm)

/-- If every response equals the handler's answer, the instrumented computation has the handler's
execution as its only path. -/
theorem support_costDist_of_forall_eq_answer (answer : QueryImpl spec Id)
    (hanswer : ∀ t (u : spec.Range t), u = answer t) (oa : OracleComp spec A)
    (cm : CostModel spec ω) :
    support (costDist oa cm) = {(simulateQ (answer.withAddCost cm.queryCost) oa).run} := by
  have : ∀ t, Subsingleton (spec.Range t) :=
    fun t => ⟨fun u v => (hanswer t u).trans (hanswer t v).symm⟩
  rw [support_costDist_eq_range_charge, run_simulateQ_withAddCost_id]
  ext z
  exact ⟨fun ⟨p, h⟩ => Subsingleton.elim p (PFunctor.FreeM.Path.ofHandler answer oa) ▸ h.symm,
    fun h => ⟨_, h.symm⟩⟩

/-- If every response equals the handler's answer, a worst-case cost bound is exactly a bound on
the cost of the handler's execution. -/
theorem worstCaseCostBound_iff_of_forall_eq_answer [Preorder ω] (answer : QueryImpl spec Id)
    (hanswer : ∀ t (u : spec.Range t), u = answer t) (oa : OracleComp spec A)
    (cm : CostModel spec ω) (B : ω) :
    WorstCaseCostBound oa cm B ↔
      (simulateQ (answer.withAddCost cm.queryCost) oa).runAdd.2 ≤ B := by
  rw [worstCaseCostBound_iff_support_bound, support_costDist_of_forall_eq_answer answer hanswer]
  simp only [Set.mem_singleton_iff, forall_eq, AddWriterT.runAdd]
  rfl

end OracleComp
