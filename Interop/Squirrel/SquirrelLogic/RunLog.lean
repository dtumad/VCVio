/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Runs with fixed answers, and their query logs

A free program run with a fixed answer for every query (VCVio's `evalWithAnswerFn`) follows one
path through the program. `OracleComp.runLog ans oa` is the list of the queries on that path,
oldest first, each with its answer: VCVio's `withQueryLog`, run with the same answers. Nothing
here depends on the interface; the facts are those that the reductions of the secrecy rules need
about runs:

* answering every query by `pure` of fixed answers, in any lawful monad, is `pure` of the run
  (`OracleComp.simulateQ_pure_comp`), the fusion of a handler into a run;
* the log of a sequence is the concatenation of the logs (`OracleComp.runLog_bind`), and a query
  logs itself (`OracleComp.runLog_query`);
* two answer functions that agree at every query of the run with the first give the same run
  (`OracleComp.evalWithAnswerFn_eq_of_forall_mem_runLog`): identical until bad, on one path;
* a program making at most `n` queries that satisfy `p`, on every path, logs at most `n` of them
  on its run (`OracleComp.length_filterMap_runLog_le`), so a query bound bounds a log;
* the queries of a simulated run are those of the handler's runs at the queries of the program's
  run (`OracleComp.forall_mem_runLog_simulateQ`).
-/

public section

namespace OracleComp

open OracleSpec

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-- Answering every query by `pure` of the answer `f t`, in any lawful monad, is `pure` of the run
with the answers `f`: the monad morphism `pure` commutes with the fold. -/
theorem simulateQ_pure_comp {m : Type → Type*} [Monad m] [LawfulMonad m] (f : QueryImpl spec Id)
    (oa : OracleComp spec α) :
    simulateQ (fun t => (pure (f t) : m (spec.Range t))) oa = pure (evalWithAnswerFn f oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih => simp [ih]

/-- The queries of the run of `oa` with the answers `ans`, oldest first, with their answers. -/
@[expose] def runLog (ans : QueryImpl spec Id) (oa : OracleComp spec α) : QueryLog spec :=
  (evalWithAnswerFn ans oa.withQueryLog).2

variable (ans : QueryImpl spec Id)

theorem fst_evalWithAnswerFn_withQueryLog (oa : OracleComp spec α) :
    (evalWithAnswerFn ans oa.withQueryLog).1 = evalWithAnswerFn ans oa :=
  (evalWithAnswerFn_map ans Prod.fst _).symm.trans
    (congrArg (evalWithAnswerFn ans) (loggingOracle.fst_map_run_simulateQ oa))

@[simp] theorem runLog_pure (a : α) : runLog ans (pure a : OracleComp spec α) = [] := rfl

theorem runLog_bind (oa : OracleComp spec α) (f : α → OracleComp spec β) :
    runLog ans (oa >>= f) = runLog ans oa ++ runLog ans (f (evalWithAnswerFn ans oa)) := by
  rw [runLog, withQueryLog_bind, evalWithAnswerFn_bind, evalWithAnswerFn_map,
    fst_evalWithAnswerFn_withQueryLog]
  rfl

theorem runLog_query (t : spec.Domain) :
    runLog ans (liftM (spec.query t) : OracleComp spec _) = [⟨t, ans t⟩] := by
  rw [runLog, withQueryLog_query, evalWithAnswerFn_bind]
  rfl

theorem runLog_query_bind (t : spec.Domain) (k : spec.Range t → OracleComp spec α) :
    runLog ans (liftM (spec.query t) >>= k) = ⟨t, ans t⟩ :: runLog ans (k (ans t)) := by
  rw [runLog_bind, runLog_query]
  rfl

@[simp] theorem runLog_map (g : α → β) (oa : OracleComp spec α) :
    runLog ans (g <$> oa) = runLog ans oa := by
  rw [map_eq_bind_pure_comp, runLog_bind, Function.comp_apply, runLog_pure, List.append_nil]

/-- **Identical until bad, on one path.** Answers that agree with `ans` at every query of the run
with `ans` give the same run. -/
theorem evalWithAnswerFn_eq_of_forall_mem_runLog {ans' : QueryImpl spec Id} :
    ∀ oa : OracleComp spec α, (∀ e ∈ runLog ans oa, ans e.1 = ans' e.1) →
      evalWithAnswerFn ans oa = evalWithAnswerFn ans' oa := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => exact fun _ => rfl
  | query_bind t k ih =>
    intro h
    rw [runLog_query_bind] at h
    have ht : ans t = ans' t := h _ List.mem_cons_self
    rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
      evalWithAnswerFn_liftM_query, ih (ans t) fun e he => h e (List.mem_cons_of_mem _ he), ht]

/-- **A query bound bounds a log.** If `oa` makes at most `n` queries satisfying `p` on every path,
the run with `ans` logs at most `n` entries that a filter `f` keeps, when `f` keeps only queries
satisfying `p`. -/
theorem length_filterMap_runLog_le {p : ι → Prop} [DecidablePred p] {X : Type}
    (f : ((t : spec.Domain) × spec.Range t) → Option X) (hf : ∀ e, (f e).isSome → p e.1) :
    ∀ {oa : OracleComp spec α} {n : ℕ}, IsQueryBoundP oa p n →
      ((runLog ans oa).filterMap f).length ≤ n := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => exact fun _ => Nat.zero_le _
  | query_bind t k ih =>
    intro n h
    rw [isQueryBoundP_query_bind_iff] at h
    rw [runLog_query_bind, List.filterMap_cons]
    cases hfe : f ⟨t, ans t⟩ with
    | none =>
      refine (ih (ans t) (h.2 (ans t))).trans ?_
      split_ifs <;> omega
    | some x =>
      have hp : p t := hf ⟨t, ans t⟩ (by rw [hfe]; rfl)
      have hn : 0 < n := h.1.resolve_left (not_not.2 hp)
      have := ih (ans t) (h.2 (ans t))
      simp only [hp, ↓reduceIte] at this
      rw [List.length_cons]
      omega

/-- **The queries of a simulated run.** Running `simulateQ impl oa` with `ans` makes, in order,
the queries of the runs of the handler at the queries of `oa`'s run with the induced answers; a
property of every query of those handler runs holds of every query of the simulated run. -/
theorem forall_mem_runLog_simulateQ {ι' : Type} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec (OracleComp spec')) (ans : QueryImpl spec' Id)
    {P : spec'.Domain → Prop} :
    ∀ oa : OracleComp spec α,
      (∀ e ∈ runLog (fun t => evalWithAnswerFn ans (impl t)) oa, ∀ e' ∈ runLog ans (impl e.1),
        P e'.1) →
      ∀ e' ∈ runLog ans (simulateQ impl oa), P e'.1 := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => exact fun _ _ h => absurd h List.not_mem_nil
  | query_bind t k ih =>
    intro h e' he'
    rw [runLog_query_bind] at h
    rw [simulateQ_bind, simulateQ_spec_query, runLog_bind] at he'
    rcases List.mem_append.1 he' with he' | he'
    · exact h _ List.mem_cons_self e' he'
    · exact ih _ (fun e he => h e (List.mem_cons_of_mem _ he)) e' he'

end OracleComp
