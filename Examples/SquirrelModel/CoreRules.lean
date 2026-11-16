/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Examples.SquirrelModel.Asymptotic
public import Examples.SquirrelModel.Healing

import all Examples.SquirrelModel.Asymptotic

/-!
# Squirrel's core rules for deduction and non-deduction

**Translation.** A Squirrel model with three terms `u`, `v`, `w` is a joint sample
`uvw : ProbComp (α × β × γ)`, and a judgment about two of the terms is about the matching
projection of `uvw`. At a fixed security parameter, `u ▷ v` with the named witness `g` is the error
`1 - deduceAdv uv g`, `u ⊬ v` is a bound on the success `deduceAdv uv f` of every `f`, and `[φ]` is
the probability of `φ`. The asymptotic forms use `Asymptotic.lean`'s `NonDeducible`, `DeducibleBy`
and `Overwhelming` over a class `C`. A hash `h(m, k)` with a secret key is a random oracle `H`, and
an attacker with oracle access is a free program over `H`'s interface, as in `OracleRules.lean`.

Squirrel's secrecy logic (Hérouard, Jacomme, Koutsos and Lallemand, CCS 2026) has three core rules
relating deduction `u ▷ v` and non-deduction `u ⊬ v`:

* **Neg**: `u ▷ v` and `u ⊬ v` are incompatible (`one_le_add_neg`, `NonDeducible.neg`);
* **Ineq**: from `u ⊬ v` and `u ▷ w`, infer `[v ≠ w]` (`prEvent_eq_le_ineq`,
  `NonDeducible.ineq`);
* **Trans**: from `u ▷ v` and `v ▷ w`, infer `u ▷ w` (`one_sub_deduceAdv_le_trans`,
  `DeducibleBy.trans`).

Each concrete form is an inequality between the errors and successes of named attackers, and each
asymptotic form follows from it. Neg's asymptotic form is unconditional, since a constant `1` is
not negligible. Trans needs the composite witness `g >=> g'` in the class, which is
`AdvClass.kleisli`.

The right PRF rule **PRF.R** derives the secrecy of a hash `h(m, k)` from that of `m`. Its
random-oracle form is `deduceAdvO_le_prfR`: if `(u, m)` is sampled without querying `H`, an attacker
that reads `u` and makes at most `q` queries to `H` outputs `H m` with probability at most the
summed success of the guessing reductions `guessQuery d₀ i f` at computing `m` from `u` and `H`
(Squirrel's premise `u, o ⊬ m`), plus `1 / |K|`. The proof is the one of `Healing.lean`: program
the oracle at `m`, puncture it with Pc-Oracle (`deduceAdvO_le_pcOracle_sum`), and bound the ideal
world by `1 / |K|`. The paper's PRF.R is about a keyed hash under the PRF assumption, which this
file does not model.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SquirrelModel

variable {α β γ : Type}

/-! ## Concrete forms -/

/-- The error of `f` at computing the second component is the probability that it answers
anything else. -/
theorem one_sub_deduceAdv (uv : ProbComp (α × β)) (f : α → ProbComp β) :
    1 - deduceAdv uv f = Pr{let z ← uv; let y ← f z.1}[y ≠ z.2] := by
  have h := prEvent_not_eq_one_sub (do let z ← uv; let y ← f z.1; pure (z, y))
    fun x => x.2 = x.1.2
  simpa [deduceAdv, prEvent_norm] using h.symm

/-- A pointwise split of three continuation events survives a common draw. -/
private theorem prEvent_bind_le_add_of_forall {δ : Type} (mx : ProbComp δ)
    (f g k : δ → ProbComp Prop) (h : ∀ a, prEvent (f a) ≤ prEvent (g a) + prEvent (k a)) :
    prEvent (mx >>= f) ≤ prEvent (mx >>= g) + prEvent (mx >>= k) := by
  simpa using prEvent_bind_le_add_of_forall_le mx f g k id id id (by simpa using h)

/-- **Neg.** If `g` computes `v` from `u` with error at most `ε`, and the success of `g` at
computing `v` is at most `δ`, then `1 ≤ ε + δ`: a judgment `u ▷ v` and a judgment `u ⊬ v` cannot
both hold with small error. -/
theorem one_le_add_neg (uv : ProbComp (α × β)) (g : α → ProbComp β) {ε δ : ℝ≥0∞}
    (hε : 1 - deduceAdv uv g ≤ ε) (hδ : deduceAdv uv g ≤ δ) : 1 ≤ ε + δ :=
  (le_tsub_add).trans (add_le_add hε hδ)

/-- **Ineq.** If `u ⊬ v` and `g` computes `w` from `u`, then `v ≠ w`: the probability that
`v = w` is at most the error of `g` at computing `w` plus the success of `g` at computing `v`. -/
theorem prEvent_eq_le_ineq (uvw : ProbComp (α × β × β)) (g : α → ProbComp β) :
    Pr{let z ← uvw}[z.2.1 = z.2.2] ≤
      (1 - deduceAdv ((fun z => (z.1, z.2.2)) <$> uvw) g) +
        deduceAdv ((fun z => (z.1, z.2.1)) <$> uvw) g := by
  rw [one_sub_deduceAdv]
  have key := (prEvent_mono (do let z ← uvw; let y ← g z.1; pure (z, y))
    (fun x => x.1.2.1 = x.1.2.2) (fun x => x.2 ≠ x.1.2.2 ∨ x.2 = x.1.2.1)
    fun x hx => by
      by_cases hy : x.2 = x.1.2.2
      · exact .inr (hy.trans hx.symm)
      · exact .inl hy).trans (prEvent_or_le _ _ _)
  simp only [prEvent_norm] at key
  simp only [deduceAdv, prEvent_norm, bind_map_left]
  refine le_of_eq_of_le ?_ key
  simp only [← bind_pure_comp]
  refine prEvent_bind_congr_of_support _ _ _ fun z _ => ?_
  rw [OracleComp.prEvent_bind_const]

/-- **Trans.** If `g` computes `v` from `u` and `g'` computes `w` from `v`, then running `g'` after
`g` computes `w` from `u`, with error at most the sum of the two errors. -/
theorem one_sub_deduceAdv_le_trans (uvw : ProbComp (α × β × γ)) (g : α → ProbComp β)
    (g' : β → ProbComp γ) :
    1 - deduceAdv ((fun z => (z.1, z.2.2)) <$> uvw) (fun a => g a >>= g') ≤
      (1 - deduceAdv ((fun z => (z.1, z.2.1)) <$> uvw) g) +
        (1 - deduceAdv ((fun z => (z.2.1, z.2.2)) <$> uvw) g') := by
  simp only [one_sub_deduceAdv, prEvent_norm, bind_map_left]
  refine prEvent_bind_le_add_of_forall _ _ _ _ fun z => ?_
  rw [← OracleComp.prEvent_bind_const (g z.1) ((fun y => y ≠ z.2.2) <$> g' z.2.1)]
  simp only [← bind_pure_comp]
  refine prEvent_bind_le_add_of_forall _ _ _ _ fun y => ?_
  by_cases hy : y = z.2.1
  · subst hy
    exact le_add_self
  · calc _ ≤ 1 := prEvent_le_one _
      _ ≤ _ := le_add_right (by simp [hy])

/-! ## Asymptotic forms -/

namespace Asymptotic

/-- The constant `1` is not negligible. -/
private theorem not_negligible_one : ¬ negligible fun _ : ℕ => (1 : ℝ≥0∞) := by
  intro h
  simpa using h 0

/-- **Neg.** No family is both a secret and deducible within the same class: `u ⊬ v` over `C`
and `u ▷ v` with a witness in `C` contradict each other. -/
theorem NonDeducible.neg {C : AdvClass} {uv : ℕ → ProbComp (α × β)} {g : Adv α β}
    (h : NonDeducible C uv) (hg : DeducibleBy C g uv) : False :=
  not_negligible_one (negligible_of_le (fun η => one_le_add_neg (uv η) (g η) le_rfl le_rfl)
    (negligible_add hg.2 (h g hg.1)))

/-- **Ineq.** If `u ⊬ v` over `C` and `g ∈ C` computes `w` from `u`, then `[v ≠ w]`. The three
terms are projections of one family of joint samples `uvw`. -/
theorem NonDeducible.ineq {C : AdvClass} {uvw : ℕ → ProbComp (α × β × β)} {g : Adv α β}
    (h : NonDeducible C fun η => (fun z => (z.1, z.2.1)) <$> uvw η)
    (hg : DeducibleBy C g fun η => (fun z => (z.1, z.2.2)) <$> uvw η) :
    Overwhelming fun η => Pr{let z ← uvw η}[z.2.1 ≠ z.2.2] := by
  refine negligible_of_le (fun η => ?_) (negligible_add hg.2 (h g hg.1))
  rw [← prEvent_not_eq_one_sub]
  simpa only [ne_eq, not_not, Pi.add_apply, deduceGame] using prEvent_eq_le_ineq (uvw η) (g η)

/-- **Trans.** If `g ∈ C` computes `v` from `u` and `g' ∈ C` computes `w` from `v`, then running
`g'` after `g`, which is in `C` by `AdvClass.kleisli`, computes `w` from `u`. -/
theorem DeducibleBy.trans {C : AdvClass} {uvw : ℕ → ProbComp (α × β × γ)} {g : Adv α β}
    {g' : Adv β γ} (hg : DeducibleBy C g fun η => (fun z => (z.1, z.2.1)) <$> uvw η)
    (hg' : DeducibleBy C g' fun η => (fun z => (z.2.1, z.2.2)) <$> uvw η) :
    DeducibleBy C (fun η a => g η a >>= g' η) fun η => (fun z => (z.1, z.2.2)) <$> uvw η :=
  ⟨C.kleisli hg.1 hg'.1, negligible_of_le
    (fun η => one_sub_deduceAdv_le_trans (uvw η) (g η) (g' η)) (negligible_add hg.2 hg'.2)⟩

/-- The hypotheses of `NonDeducible.ineq` hold for a nontrivial family over the class of all
adversaries: a uniform `η`-bit number `v` is a secret from nothing and `w = 0` is computed from
nothing, so `v ≠ 0` with overwhelming probability. -/
example : Overwhelming fun η =>
    Pr{let z ← (fun v : Fin (2 ^ η) => ((), (v : ℕ), 0)) <$> ($ᵗ (Fin (2 ^ η)))}[
      z.2.1 ≠ z.2.2] := by
  refine NonDeducible.ineq (C := AdvClass.all) (g := fun _ _ => pure 0) ?_ ⟨trivial, ?_⟩
  · convert nonDeducible_uniform using 2 with η
    simp [Functor.map_map]
  · refine negligible_of_zero fun η => ?_
    simp [deduceAdv]

/-- The hypotheses of `DeducibleBy.trans` hold for a nontrivial family: three copies of a uniform
`η`-bit number, each computed from the previous one by returning it. -/
example : DeducibleBy AdvClass.all (fun _ (a : ℕ) => pure a >>= fun b => pure b)
    fun η => (fun z => (z.1, z.2.2)) <$>
      ((fun v : Fin (2 ^ η) => ((v : ℕ), (v : ℕ), (v : ℕ))) <$> ($ᵗ (Fin (2 ^ η)))) := by
  refine DeducibleBy.trans (g := fun _ a => pure a) (g' := fun _ b => pure b)
    ⟨trivial, negligible_of_zero fun η => ?_⟩ ⟨trivial, negligible_of_zero fun η => ?_⟩ <;>
    simp [deduceAdv]

end Asymptotic

/-! ## PRF.R in the random-oracle model -/

section PRFR

variable {D K : Type}

/-- The randomness of PRF.R in the random-oracle model: a joint sample `(u, m)` and, independently,
a uniformly random hash `H`. -/
@[expose] def prfRSample [SampleableType (D → K)] (um : ProbComp (α × D)) :
    ProbComp ((α × D) × (D → K)) := do
  let z ← um
  let H ← $ᵗ (D → K)
  pure (z, H)

/-- `prfRSample` with the value of the hash at `m` drawn separately as a fresh key `r`. -/
@[expose] def prfRProgrammedSample [SampleableType K] [SampleableType (D → K)]
    (um : ProbComp (α × D)) : ProbComp ((α × D) × (D → K) × K) := do
  let z ← um
  let H ← $ᵗ (D → K)
  let r ← $ᵗ K
  pure (z, H, r)

/-- An event with the same probability after every outcome of a draw keeps that probability. -/
private theorem prEvent_bind_eq_of_forall_prEvent_eq {δ : Type} (mx : ProbComp δ)
    (f : δ → ProbComp Prop) {ε : ℝ≥0∞} (h : ∀ a, prEvent (f a) = ε) :
    prEvent (mx >>= f) = ε := by
  simpa using prEvent_bind_eq_of_forall_eq mx (prEvent_true_eq_one mx) f id (by simpa using h)

/-- Overwriting the hash at `m` with the fresh key `r`, and asking for `r`, is the random-oracle
experiment asking for `H m`. -/
theorem deduceAdvO_prfRSample_eq [SampleableType K] [DecidableEq D] [SampleableType (D → K)]
    (um : ProbComp (α × D)) (f : α → OracleComp (D →ₒ K) K) :
    deduceAdvO (prfRSample um) (fun x => x.1.1) (fun x => x.2 x.1.2) (fun x => x.2) f =
      deduceAdvO (prfRProgrammedSample um) (fun x => x.1.1) (fun x => x.2.2)
        (fun x => Function.update x.2.1 x.1.2 x.2.2) f := by
  simp only [deduceAdvO, oracleExp, prfRSample, prfRProgrammedSample, prEvent_norm, bind_assoc]
  refine prEvent_bind_congr_of_support _ _ _ fun z _ => ?_
  have key := ((Healing.uniformSample_update_evalDistEq z.2).bind_left
    fun p : (D → K) × K =>
      (fun y => y.1 = p.2) <$> (simulateQ (logImpl p.1) (f z.1)).run []).symm
  simpa [bind_assoc] using key.prEvent_eq id

/-- In the punctured world the fresh key `r` is independent of the attacker's view and oracle, so
the attacker outputs it with probability exactly `1 / |K|`. -/
theorem deduceAdvO_prfRProgrammedSample_eq_inv_card [SampleableType K] [Fintype K]
    [SampleableType (D → K)] (um : ProbComp (α × D)) (f : α → OracleComp (D →ₒ K) K) :
    deduceAdvO (prfRProgrammedSample um) (fun x => x.1.1) (fun x => x.2.2) (fun x => x.2.1) f =
      (Fintype.card K : ℝ≥0∞)⁻¹ := by
  simp only [deduceAdvO, oracleExp, prfRProgrammedSample, prEvent_norm, bind_assoc]
  refine prEvent_bind_eq_of_forall_prEvent_eq _ _ fun z =>
    prEvent_bind_eq_of_forall_prEvent_eq _ _ fun H => ?_
  rw [prEvent_bind_map_swap]
  exact prEvent_bind_eq_of_forall_prEvent_eq _ _ fun y =>
    SampleableType.prEvent_uniformSample_eq_singleton' y.1

/-- The fresh key is unused by an attacker run against `H` itself. -/
theorem deduceAdvO_prfRProgrammedSample_eq_prfRSample [SampleableType K]
    [SampleableType (D → K)] (um : ProbComp (α × D)) (v : α × D → β)
    (f : α → OracleComp (D →ₒ K) β) :
    deduceAdvO (prfRProgrammedSample um) (fun x => x.1.1) (fun x => v x.1) (fun x => x.2.1) f =
      deduceAdvO (prfRSample um) (fun x => x.1.1) (fun x => v x.1) (fun x => x.2) f := by
  simp only [deduceAdvO, oracleExp, prfRProgrammedSample, prfRSample, prEvent_norm, bind_assoc]
  refine prEvent_bind_congr_of_support _ _ _ fun z _ => prEvent_bind_congr_of_support _ _ _
    fun H _ => ?_
  rw [OracleComp.prEvent_bind_const]

/-- **PRF.R, random-oracle form.** Let `m` be sampled jointly with `u`, and let the hash `H` be a
random oracle that the sampling of `(u, m)` never queries. An attacker that reads `u` and makes at
most `q` queries to `H` outputs `H m` with probability at most the summed success of the `q`
named guessing reductions `guessQuery d₀ i f` at computing `m` from `u` with the same oracle
(Squirrel's premise `u, o ⊬ m`), plus `1 / |K|`. -/
theorem deduceAdvO_le_prfR [SampleableType K] [Fintype K] [SampleableType (D → K)] (d₀ : D)
    (um : ProbComp (α × D)) (f : α → OracleComp (D →ₒ K) K)
    {q : ℕ} (hq : ∀ a, IsQueryBoundP (f a) (fun _ => True) q) :
    deduceAdvO (prfRSample um) (fun x => x.1.1) (fun x => x.2 x.1.2) (fun x => x.2) f ≤
      ∑ i ∈ Finset.range q,
        deduceAdvO (prfRSample um) (fun x => x.1.1) (fun x => x.1.2) (fun x => x.2)
          (guessQuery d₀ i f) +
        (Fintype.card K : ℝ≥0∞)⁻¹ := by
  classical
  have key := deduceAdvO_le_pcOracle_sum d₀ (prfRProgrammedSample um) (fun x => x.1.1)
    (fun x => x.2.2) (fun x => Function.update x.2.1 x.1.2 x.2.2) f (fun x => x.1.2)
    (fun x => x.2.1 x.1.2) hq
  have hupd : (fun x : (α × D) × (D → K) × K =>
      Function.update (Function.update x.2.1 x.1.2 x.2.2) x.1.2 (x.2.1 x.1.2)) =
      fun x => x.2.1 := by
    funext x
    simp
  rw [hupd, deduceAdvO_prfRProgrammedSample_eq_inv_card] at key
  rw [deduceAdvO_prfRSample_eq, add_comm]
  refine key.trans (add_le_add le_rfl (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)))
  exact deduceAdvO_prfRProgrammedSample_eq_prfRSample um Prod.snd (guessQuery d₀ i f)

/-- The query bound of `deduceAdvO_le_prfR` can be met: an attacker that hashes its input and
outputs the answer makes one query. -/
example [SampleableType K] [Fintype K] [SampleableType (D → K)] (d₀ : D)
    (um : ProbComp (D × D)) :
    deduceAdvO (prfRSample (K := K) um) (fun x => x.1.1) (fun x => x.2 x.1.2) (fun x => x.2)
        (fun a => (liftM ((D →ₒ K).query a) : OracleComp (D →ₒ K) K)) ≤
      ∑ i ∈ Finset.range 1,
        deduceAdvO (prfRSample (K := K) um) (fun x => x.1.1) (fun x => x.1.2) (fun x => x.2)
          (guessQuery d₀ i fun a => (liftM ((D →ₒ K).query a) : OracleComp (D →ₒ K) K)) +
        (Fintype.card K : ℝ≥0∞)⁻¹ :=
  deduceAdvO_le_prfR d₀ um _ fun _ => by simp

end PRFR

end SquirrelModel
