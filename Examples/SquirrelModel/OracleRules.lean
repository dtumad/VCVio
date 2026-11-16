/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.OracleComp.SimSemantics.StateT.UntilBad

/-!
# Squirrel's oracle rules as identical-until-bad

Squirrel's secrecy logic (Hérouard, Jacomme, Koutsos and Lallemand, CCS 2026) has two rules about
oracles on the left of a non-deduction `u, o ⊬ v`:

* **Rw-Oracle** replaces the oracle `o₁` by `o₂` when the two agree on every query the attacker
  can make;
* **Pc-Oracle** punctures the oracle at a point `m`, changing its answer there to `w`, when `m`
  itself cannot be computed.

The paper proves both on paper only (Appendix C, Theorem C.1), noting that Rw-Oracle "cannot be
proved directly in Squirrel, since … it involves reasoning inductively on the number of calls
made by an adversary to an oracle". Its argument is identical-until-bad: the two runs coincide
until the attacker queries a point where the oracles differ.

Here the attacker is a free program over the oracle's interface, so that induction is the
handler theory VCVio already has. The oracle is answered by `logImpl`, which records the queries.
`deduceAdvO` is the attacker's success at computing `v`, and `queryAdvO` is the success of the
*query-log reduction*: run the attacker and look for a logged query in a given set.

* `deduceAdvO_le_rwOracle`: if `o₁` and `o₂` agree outside `B`, the success with `o₁` is at most
  the success with `o₂` plus the probability that the attacker, run with `o₂`, queries `B`.
* `deduceAdvO_le_pcOracle`: the puncturing instance, with `B = {m}`; it also shows that the
  hypothesis of `deduceAdvO_le_rwOracle` can be met.

Squirrel's rules end in a single-message non-deduction `u, o' ⊬ m`. Turning the query-log bound
into that form costs a factor of the attacker's query count (guess which query hits `m`); that
step is not formalized here. The adversary's only oracle is the hash oracle: its own randomness
can be supplied through `u`, sampled with the rest by `s`.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SquirrelModel

variable {Ω α β D R : Type}

/-- The oracle `o` as a handler that logs every query, newest first. -/
@[expose] def logImpl (o : D → R) : QueryImpl (D →ₒ R) (StateT (List D) ProbComp) :=
  fun d => do modify (d :: ·); pure (o d)

theorem logImpl_run (o : D → R) (d : D) (log : List D) :
    (logImpl o d).run log = pure (o d, d :: log) := by
  simp [logImpl]

/-- Sample the shared randomness `x ← s`, then run the attacker `f` on `u x` with the oracle
`o x`, logging its queries. Returns the sample, the attacker's output and its query log. -/
@[expose] def oracleExp (s : ProbComp Ω) (u : Ω → α) (o : Ω → D → R)
    (f : α → OracleComp (D →ₒ R) β) : ProbComp (Ω × β × List D) :=
  s >>= fun x => (fun z => (x, z.1, z.2)) <$> (simulateQ (logImpl (o x)) (f (u x))).run []

/-- The attacker's success at computing `v` from `u` with oracle access to `o`: the concrete
counterpart of Squirrel's `u, o ⊬ v`. -/
@[expose] noncomputable def deduceAdvO (s : ProbComp Ω) (u : Ω → α) (v : Ω → β)
    (o : Ω → D → R) (f : α → OracleComp (D →ₒ R) β) : ℝ≥0∞ :=
  Pr{let y ← oracleExp s u o f}[y.2.1 = v y.1]

/-- The success of the query-log reduction: the probability that the attacker queries a point
of `B`. -/
@[expose] noncomputable def queryAdvO (s : ProbComp Ω) (u : Ω → α) (o : Ω → D → R)
    (f : α → OracleComp (D →ₒ R) β) (B : Ω → Set D) : ℝ≥0∞ :=
  Pr{let y ← oracleExp s u o f}[∃ d ∈ y.2.2, d ∈ B y.1]

/-- Logging handlers for oracles that agree outside `B` agree until a query in `B` is logged. -/
theorem agreeUntilBad_logImpl (o₁ o₂ : D → R) (B : Set D)
    (h : ∀ d, d ∉ B → o₁ d = o₂ d) :
    QueryImpl.AgreeUntilBad (logImpl o₁) (logImpl o₂) fun log => ∃ d ∈ log, d ∈ B := by
  refine QueryImpl.AgreeUntilBad.of_run_eq_or_bad fun d log _ => ?_
  by_cases hd : d ∈ B
  · refine .inr ⟨?_, ?_⟩ <;>
    · intro z hz
      simp only [logImpl_run, support_pure, Set.mem_singleton_iff] at hz
      exact ⟨d, by simp [hz], hd⟩
  · exact .inl (by rw [logImpl_run, logImpl_run, h d hd])

/-- Once a query in `B` is logged, it stays logged. -/
theorem preservesInv_logImpl (o : D → R) (B : Set D) :
    QueryImpl.PreservesInv (logImpl o) fun log => ∃ d ∈ log, d ∈ B := by
  intro d log ⟨d', hd', hB⟩ z hz
  simp only [logImpl_run, support_pure, Set.mem_singleton_iff] at hz
  exact ⟨d', by simp [hz, hd'], hB⟩

/-- **Rw-Oracle.** If `o₁` and `o₂` agree outside `B`, the attacker's success with `o₁` exceeds
its success with `o₂` by at most the success of the query-log reduction run with `o₂`. -/
theorem deduceAdvO_le_rwOracle (s : ProbComp Ω) (u : Ω → α) (v : Ω → β) (o₁ o₂ : Ω → D → R)
    (f : α → OracleComp (D →ₒ R) β) (B : Ω → Set D)
    (h : ∀ x d, d ∉ B x → o₁ x d = o₂ x d) :
    deduceAdvO s u v o₁ f ≤ deduceAdvO s u v o₂ f + queryAdvO s u o₂ f B := by
  unfold deduceAdvO queryAdvO oracleExp
  refine prEvent_bind_le_add_of_forall_le _ _ _ _ _ _ _ fun x => ?_
  simp only [prEvent_map]
  exact (agreeUntilBad_logImpl (o₁ x) (o₂ x) (B x) (h x)).prEvent_simulateQ_run_le_add_bad_right
    (preservesInv_logImpl (o₂ x) (B x)) (f (u x)) [] fun z => z.1 = v x

/-- **Pc-Oracle.** Puncturing the oracle at `m`, i.e. answering `w` there instead, changes the
attacker's success by at most the probability that the attacker, run with the punctured oracle,
queries `m`. -/
theorem deduceAdvO_le_pcOracle [DecidableEq D] (s : ProbComp Ω) (u : Ω → α) (v : Ω → β)
    (o : Ω → D → R) (f : α → OracleComp (D →ₒ R) β) (m : Ω → D) (w : Ω → R) :
    deduceAdvO s u v o f ≤
      deduceAdvO s u v (fun x => Function.update (o x) (m x) (w x)) f +
        queryAdvO s u (fun x => Function.update (o x) (m x) (w x)) f fun x => {m x} :=
  deduceAdvO_le_rwOracle s u v o _ f _ fun x d hd =>
    (Function.update_of_ne (by simpa using hd) _ _).symm

end SquirrelModel
