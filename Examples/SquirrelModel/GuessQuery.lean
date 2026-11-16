/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Examples.SquirrelModel.OracleRules
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# From "the attacker queries `m`" to "the attacker computes `m`"

**Translation.** Squirrel's premise `u, o' ⊬ m` of Pc-Oracle says, at a fixed security parameter,
that `deduceAdvO s u m o' g` is small for every attacker `g`. The guessing argument names the
attackers it uses, `guessQuery d₀ i f` for each query position `i`, and the attacker's query budget
is `IsQueryBoundP`.

`deduceAdvO_le_pcOracle` bounds the cost of puncturing an oracle at `m` by `queryAdvO`, the
probability that the attacker *queries* `m`. Squirrel's Pc-Oracle rule instead ends in a
non-deduction `u, o' ⊬ m`: no attacker *computes* `m`. This file closes that gap with the usual
guessing argument. The reduction `guessQuery d₀ i f` runs `f`, logging its queries, and outputs the
input of its `i`-th query. If `f` makes at most `q` queries, then

  `queryAdvO s u o f {m} ≤ ∑ i < q, deduceAdvO s u m o (guessQuery d₀ i f)`,

so Pc-Oracle holds with the single-message premise of Squirrel's rule, at a cost of one deducing
adversary per query position (`deduceAdvO_le_pcOracle_sum`). This is the factor `q` in the
soundness proof of Rw-Oracle by Hérouard, Jacomme, Koutsos and Lallemand (CCS 2026), Appendix C.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SquirrelModel

variable {Ω α β D R : Type}

/-! ## The guessing reduction -/

/-- The guessing reduction: run `f` with a query log and output the input of its `i`-th query,
oldest first, or `d₀` if it made fewer than `i + 1` queries. -/
@[expose] def guessQuery (d₀ : D) (i : ℕ) (f : α → OracleComp (D →ₒ R) β) (a : α) :
    OracleComp (D →ₒ R) D :=
  (fun z => (z.2.map (·.1)).getD i d₀) <$> (f a).withQueryLog

/-! ## Logs of the logging handler -/

/-- Running from a nonempty log only appends the old log below the new queries. -/
theorem run_simulateQ_logImpl_append (o : D → R) {γ : Type} (oa : OracleComp (D →ₒ R) γ)
    (L : List D) :
    (simulateQ (logImpl o) oa).run L =
      (fun z => (z.1, z.2 ++ L)) <$> (simulateQ (logImpl o) oa).run [] := by
  induction oa using OracleComp.inductionOn generalizing L with
  | pure a => simp
  | query_bind d k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, logImpl_run, pure_bind]
    rw [ih (o d) (d :: L), ih (o d) [d]]
    simp [Functor.map_map, List.append_assoc]

/-- The attacker's own query log, read through the logging handler: it records the same queries,
oldest first, with the handler's answers. -/
theorem run_simulateQ_logImpl_withQueryLog (o : D → R) {γ : Type}
    (oa : OracleComp (D →ₒ R) γ) :
    (simulateQ (logImpl o) oa.withQueryLog).run [] =
      (fun z => ((z.1, z.2.reverse.map fun d => (⟨d, o d⟩ : (_ : D) × R)), z.2)) <$>
        (simulateQ (logImpl o) oa).run [] := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind d k ih =>
    rw [withQueryLog_bind, withQueryLog_query]
    simp only [bind_assoc, pure_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_map,
      StateT.run_bind, StateT.run_map, logImpl_run]
    rw [run_simulateQ_logImpl_append (o := o) _ [d], ih (o d),
      run_simulateQ_logImpl_append (o := o) (k (o d)) [d]]
    simp [Functor.map_map, List.reverse_append]

/-- Running the guessing reduction is running the attacker and reading its `i`-th query off the
log. -/
theorem oracleExp_guessQuery (d₀ : D) (i : ℕ) (s : ProbComp Ω) (u : Ω → α) (o : Ω → D → R)
    (f : α → OracleComp (D →ₒ R) β) :
    oracleExp s u o (guessQuery d₀ i f) =
      (fun y => (y.1, y.2.2.reverse.getD i d₀, y.2.2)) <$> oracleExp s u o f := by
  simp only [oracleExp, guessQuery, simulateQ_map, StateT.run_map,
    run_simulateQ_logImpl_withQueryLog, map_bind, Functor.map_map]
  congr 1
  funext x
  congr 1
  funext z
  simp [List.map_map, Function.comp_def]

/-- The guessing reduction's success is the probability that the attacker's `i`-th query is the
target. -/
theorem deduceAdvO_guessQuery (d₀ : D) (i : ℕ) (s : ProbComp Ω) (u : Ω → α) (m : Ω → D)
    (o : Ω → D → R) (f : α → OracleComp (D →ₒ R) β) :
    deduceAdvO s u m o (guessQuery d₀ i f) =
      Pr{let y ← oracleExp s u o f}[y.2.2.reverse.getD i d₀ = m y.1] := by
  rw [deduceAdvO, oracleExp_guessQuery, prEvent_map]

/-! ## The guessing bound -/

/-- An attacker making at most `q` queries leaves a log of length at most `q`. -/
theorem length_le_of_mem_support_oracleExp (s : ProbComp Ω) (u : Ω → α) (o : Ω → D → R)
    (f : α → OracleComp (D →ₒ R) β) {q : ℕ}
    (hq : ∀ a, IsQueryBoundP (f a) (fun _ => True) q) :
    ∀ y ∈ support (oracleExp s u o f), y.2.2.length ≤ q := by
  intro y hy
  simp only [oracleExp, mem_support_bind_iff, support_map, Set.mem_image] at hy
  obtain ⟨x, -, z, hz, rfl⟩ := hy
  have := (hq (u x)).cost_le_of_mem_support_run_simulateQ (impl := logImpl (o x)) List.length
    (fun t _ s z hz => by
      simp only [logImpl_run, support_pure, Set.mem_singleton_iff] at hz
      simp [hz])
    (fun _ h => absurd trivial h) [] z hz
  simpa using this

/-- **The guessing bound.** If `f` makes at most `q` queries, the probability that it queries `m`
is at most the summed success of the `q` guessing reductions at computing `m`. -/
theorem queryAdvO_singleton_le_sum (d₀ : D) (s : ProbComp Ω) (u : Ω → α) (m : Ω → D)
    (o : Ω → D → R) (f : α → OracleComp (D →ₒ R) β) {q : ℕ}
    (hq : ∀ a, IsQueryBoundP (f a) (fun _ => True) q) :
    queryAdvO s u o f (fun x => {m x}) ≤
      ∑ i ∈ Finset.range q, deduceAdvO s u m o (guessQuery d₀ i f) := by
  simp only [deduceAdvO_guessQuery]
  calc queryAdvO s u o f (fun x => {m x})
      ≤ Pr{let y ← oracleExp s u o f}[∃ i ∈ Finset.range q, y.2.2.reverse.getD i d₀ = m y.1] := by
        refine prEvent_mono_of_support _ _ _ fun y hy ⟨d, hd, hm⟩ => ?_
        have hlen := length_le_of_mem_support_oracleExp s u o f hq y hy
        rw [Set.mem_singleton_iff] at hm
        rw [← List.mem_reverse, List.mem_iff_getElem] at hd
        obtain ⟨i, hi, hget⟩ := hd
        refine ⟨i, Finset.mem_range.2 (lt_of_lt_of_le hi (by simpa using hlen)), ?_⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hget, hm]
    _ ≤ ∑ i ∈ Finset.range q, Pr{let y ← oracleExp s u o f}[y.2.2.reverse.getD i d₀ = m y.1] :=
        prEvent_exists_finset_le _ _ _

/-- **Pc-Oracle, in Squirrel's form.** Puncturing the oracle at `m` costs at most the summed
success of the guessing reductions at computing `m` with the punctured oracle: Squirrel's premise
`u, o' ⊬ m`, made concrete. -/
theorem deduceAdvO_le_pcOracle_sum [DecidableEq D] (d₀ : D) (s : ProbComp Ω) (u : Ω → α)
    (v : Ω → β) (o : Ω → D → R) (f : α → OracleComp (D →ₒ R) β) (m : Ω → D) (w : Ω → R)
    {q : ℕ} (hq : ∀ a, IsQueryBoundP (f a) (fun _ => True) q) :
    deduceAdvO s u v o f ≤
      deduceAdvO s u v (fun x => Function.update (o x) (m x) (w x)) f +
        ∑ i ∈ Finset.range q,
          deduceAdvO s u m (fun x => Function.update (o x) (m x) (w x)) (guessQuery d₀ i f) :=
  (deduceAdvO_le_pcOracle s u v o f m w).trans
    (add_le_add le_rfl (queryAdvO_singleton_le_sum d₀ s u m _ f hq))

/-! ## Boundary cases -/

/-- An attacker that makes no queries never queries the target. -/
theorem queryAdvO_singleton_eq_zero (d₀ : D) (s : ProbComp Ω) (u : Ω → α) (m : Ω → D)
    (o : Ω → D → R) (f : α → OracleComp (D →ₒ R) β)
    (hq : ∀ a, IsQueryBoundP (f a) (fun _ => True) 0) :
    queryAdvO s u o f (fun x => {m x}) = 0 :=
  le_antisymm (by simpa using queryAdvO_singleton_le_sum d₀ s u m o f hq) zero_le

/-- The query-bound hypothesis can be met: an attacker that queries its input once makes at most
one query. -/
example : ∀ a : D, IsQueryBoundP (liftM ((D →ₒ R).query a) : OracleComp (D →ₒ R) R)
    (fun _ => True) 1 :=
  fun _ => by simp

end SquirrelModel
