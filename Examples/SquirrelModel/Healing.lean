/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Examples.SquirrelModel.Deduction
public import Examples.SquirrelModel.GuessQuery
public import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import Mathlib.Algebra.Field.ZMod

/-!
# Healing: one honest exchange makes the root key secret again

Hérouard, Jacomme, Koutsos and Lallemand (CCS 2026) prove post-compromise security of an
asymmetric ratchet whose root key is updated as `rk' = h(⟨rk, g^{xy}⟩, k)`. After a compromise
leaks `rk`, one honest Diffie–Hellman exchange, in which the attacker sees `g^x` and `g^y` but
neither exponent, heals the session: `rk'` is secret again. In their proof (§4.3, the healing
case) the secrecy of `g^{xy}` gives that of `rk'` through the right PRF rule PRF.R, once `rk'` is
shown to be a fresh hash; `g^{xy}` itself is secret by Gap Diffie–Hellman, since their attacker
also gets DDH oracles. With a random oracle in place of the keyed hash, the same step is
Pc-Oracle at `m = ⟨rk, g^{xy}⟩`, whose premise `u, o' ⊬ m` comes down to
`g, g^x, g^y ⊬ g^{xy}`: computational Diffie–Hellman, as here.

This file proves that step, with the group written additively (`a • g` for `g^a`).

* `healingAdv rk g A` is the probability that the attacker `A`, given the compromised `rk`, the
  generator `g` and the shares `a • g` and `b • g`, and making adaptive queries to a random oracle
  `H : K × G → K`, outputs `rk' = H (rk, (a * b) • g)`.
* `healingAdv_le`: if `A` makes at most `q` queries, then
  `healingAdv rk g A ≤ ∑ i < q, Pr[cdhExperiment g (healingReduction rk i A) = true] + 1 / |K|`.
  The reduction `healingReduction rk i A` runs `A`, answers its queries with a lazily sampled
  random oracle, and outputs the group element of `A`'s `i`-th query.
* `healingAdv_pure`: guessing a fixed key wins with probability exactly `1 / |K|`.

The proof composes the Squirrel rules of this directory.

1. Program the oracle (`healingAdv_eq_programmedAdv`): a uniformly random `H` is distributed as
   `H` with its value at the honest point overwritten by a fresh key `r`, and that `r` is `rk'`
   (`uniformSample_update_evalDistEq`).
2. Pc-Oracle in Squirrel's form (`deduceAdvO_le_pcOracle_sum`) punctures the programmed hash at the
   honest point, which gives back `H`. It costs the summed success of the guessing reductions at
   computing the honest point: Squirrel's premise `u, o' ⊬ m`.
3. In the punctured world `r` is independent of the attacker's view, so the attacker outputs it
   with probability exactly `1 / |K|` (`deduceAdvO_programmedSample_eq_inv_card`).
4. Each premise is CDH as non-deduction (`deduceAdv_cdhPair`): it is at most the CDH success of a
   named reduction (`deduceAdvO_guessQuery_le_cdhExperiment`), and sampling the oracle lazily
   leaves that success unchanged (`cdhExperiment_healingReduction_evalDistEq`).

Steps 2 to 4 hold for any distribution of the hash away from the honest point
(`programmedAdv_le`).

This is the healing case of the paper's post-compromise security proof: one step of the ratchet,
not the full protocol. The bound holds for every attacker, adaptive in its hash queries, and the
computational assumption enters only through the CDH success of the named reductions, each of
which runs `A` once and draws one uniform key per fresh query. The hash is an unkeyed random oracle
on `K × G`, where the paper's `h(·, k)` is keyed; the group is finite, so that a uniformly random
hash exists.
-/

public section

open OracleComp OracleSpec ENNReal DiffieHellman

namespace SquirrelModel.Healing

variable {F G K : Type} [Field F] [AddCommGroup G] [Module F G]

/-! ## The healing step -/

/-- A healing attacker. It sees the compromised root key `rk`, the generator `g` and the two
public Diffie–Hellman shares `a • g` and `b • g`, may query the hash `K × G → K` adaptively, and
outputs a guess for the new root key. -/
abbrev HealingAdversary (K G : Type) : Type := K × G × G × G → OracleComp (K × G →ₒ K) K

/-- The attacker's view: the compromised root key, the generator and both public shares, but
neither exponent. -/
@[expose] def healingView (rk : K) (g : G) (a b : F) : K × G × G × G :=
  (rk, g, a • g, b • g)

/-- The point `(rk, (a * b) • g)` that the ratchet hashes: the old root key and the shared
Diffie–Hellman secret. -/
@[expose] def honestPoint (rk : K) (g : G) (a b : F) : K × G :=
  (rk, (a * b) • g)

/-- The randomness of one healing step in the random-oracle model: the exponents `a` and `b` of
the honest exchange and a uniformly random hash `H`. -/
@[expose] def healingSample [SampleableType F] [SampleableType (K × G → K)] :
    ProbComp (F × F × (K × G → K)) := do
  let a ← $ᵗ F
  let b ← $ᵗ F
  let H ← $ᵗ (K × G → K)
  pure (a, b, H)

/-- The attacker's probability of outputting the new root key `rk' = H (rk, (a * b) • g)` after
one honest exchange, with oracle access to the random oracle `H`. -/
noncomputable def healingAdv [SampleableType F] [SampleableType (K × G → K)] (rk : K) (g : G)
    (A : HealingAdversary K G) : ℝ≥0∞ :=
  deduceAdvO (healingSample (F := F)) (fun x => healingView rk g x.1 x.2.1)
    (fun x => x.2.2 (honestPoint rk g x.1 x.2.1)) (fun x => x.2.2) A

/-! ## The programmed hash

The proof first moves to an equivalent experiment in which the hash's value at the honest point
is a separate fresh key `r`, and the rest of the hash `H` is drawn from any distribution `hs`. -/

/-- The randomness of the programmed experiment: the exponents `a` and `b`, the hash `H ← hs`
away from the honest point, and the fresh value `r` of the hash at that point. -/
@[expose] def programmedSample [SampleableType F] [SampleableType K] (hs : ProbComp (K × G → K)) :
    ProbComp (F × F × (K × G → K) × K) := do
  let a ← $ᵗ F
  let b ← $ᵗ F
  let H ← hs
  let r ← $ᵗ K
  pure (a, b, H, r)

/-- The programmed hash: `H`, except that at the honest point it answers the fresh key `r`. -/
@[expose] def programmedHash [DecidableEq K] [DecidableEq G] (rk : K) (g : G)
    (x : F × F × (K × G → K) × K) : K × G → K :=
  Function.update x.2.2.1 (honestPoint rk g x.1 x.2.1) x.2.2.2

/-- The new root key `r` is the programmed hash of the honest point. -/
theorem programmedHash_honestPoint [DecidableEq K] [DecidableEq G] (rk : K) (g : G)
    (x : F × F × (K × G → K) × K) :
    programmedHash rk g x (honestPoint rk g x.1 x.2.1) = x.2.2.2 := by
  simp [programmedHash]

/-- The attacker's probability of outputting the new root key `r` against the programmed hash. -/
noncomputable def programmedAdv [SampleableType F] [SampleableType K] [DecidableEq K]
    [DecidableEq G] (hs : ProbComp (K × G → K)) (rk : K) (g : G) (A : HealingAdversary K G) :
    ℝ≥0∞ :=
  deduceAdvO (programmedSample (F := F) hs) (fun x => healingView rk g x.1 x.2.1)
    (fun x => x.2.2.2) (programmedHash rk g) A

/-! ## The CDH reductions -/

/-- The CDH reduction for query position `i`. Given `(g, a • g, b • g)`, it draws the hash
`H ← hs`, runs the attacker on `(rk, g, a • g, b • g)` with oracle `H`, and outputs the group
element of the attacker's `i`-th query. -/
@[expose] def programmedReduction (hs : ProbComp (K × G → K)) (rk : K) (i : ℕ)
    (A : HealingAdversary K G) : CDHAdversary F G :=
  cdhReduction fun v => do
    let H ← hs
    let z ← (simulateQ (logImpl H) (guessQuery (rk, 0) i A (rk, v))).run []
    pure z.1.2

/-- With the hash unprogrammed, the success of the guessing reduction at computing the honest
point is at most the CDH success of `programmedReduction`. -/
theorem deduceAdvO_guessQuery_le_cdhExperiment [SampleableType F] [SampleableType K]
    [DecidableEq G] (hs : ProbComp (K × G → K)) (rk : K) (g : G) (i : ℕ)
    (A : HealingAdversary K G) :
    deduceAdvO (programmedSample (F := F) hs) (fun x => healingView rk g x.1 x.2.1)
        (fun x => honestPoint rk g x.1 x.2.1) (fun x => x.2.2.1) (guessQuery (rk, 0) i A) ≤
      Pr{let b ← cdhExperiment g (programmedReduction (F := F) hs rk i A)}[b = true] := by
  unfold programmedReduction
  rw [← deduceAdv_cdhPair]
  simp only [deduceAdv, deduceAdvO, oracleExp, programmedSample, cdhPair, healingView,
    honestPoint, prEvent_norm, bind_assoc]
  refine prEvent_bind_mono_of_support _ _ _ fun a _ => prEvent_bind_mono_of_support _ _ _
    fun b _ => prEvent_bind_mono_of_support _ _ _ fun H _ => ?_
  rw [OracleComp.prEvent_bind_const]
  exact prEvent_mono _ _ _ fun z hz => by rw [hz]

/-! ## The ideal world -/

/-- An event with the same probability after every outcome of a draw keeps that probability. -/
private theorem prEvent_bind_eq_of_forall_eq' {α : Type} (mx : ProbComp α)
    (f : α → ProbComp Prop) {ε : ℝ≥0∞} (h : ∀ a, prEvent (f a) = ε) :
    prEvent (mx >>= f) = ε := by
  simpa using prEvent_bind_eq_of_forall_eq mx (prEvent_true_eq_one mx) f id (by simpa using h)

/-- **The ideal world.** With the hash `H` unprogrammed, the new root key `r` is independent of
everything the attacker sees, and the attacker outputs it with probability exactly `1 / |K|`. -/
theorem deduceAdvO_programmedSample_eq_inv_card [SampleableType F] [SampleableType K] [Fintype K]
    (hs : ProbComp (K × G → K)) (rk : K) (g : G) (A : HealingAdversary K G) :
    deduceAdvO (programmedSample (F := F) hs) (fun x => healingView rk g x.1 x.2.1)
        (fun x => x.2.2.2) (fun x => x.2.2.1) A =
      (Fintype.card K : ℝ≥0∞)⁻¹ := by
  simp only [deduceAdvO, oracleExp, programmedSample, healingView, prEvent_norm, bind_assoc]
  refine prEvent_bind_eq_of_forall_eq' _ _ fun a => prEvent_bind_eq_of_forall_eq' _ _
    fun b => prEvent_bind_eq_of_forall_eq' _ _ fun H => ?_
  rw [prEvent_bind_map_swap]
  exact prEvent_bind_eq_of_forall_eq' _ _ fun z =>
    SampleableType.prEvent_uniformSample_eq_singleton' z.1

/-! ## Healing against the programmed hash -/

/-- Puncturing the programmed hash at the honest point with `H`'s own value there gives back `H`. -/
theorem update_programmedHash [DecidableEq K] [DecidableEq G] (rk : K) (g : G) :
    (fun x : F × F × (K × G → K) × K =>
      Function.update (programmedHash rk g x) (honestPoint rk g x.1 x.2.1)
        (x.2.2.1 (honestPoint rk g x.1 x.2.1))) = fun x => x.2.2.1 := by
  funext x
  simp [programmedHash]

/-- **Healing, programmed form.** For any distribution `hs` of the hash away from the honest
point, an attacker making at most `q` hash queries outputs the programmed new root key with
probability at most the summed CDH success of the reductions `programmedReduction hs rk i A`,
plus `1 / |K|`. -/
theorem programmedAdv_le [SampleableType F] [SampleableType K] [Fintype K] [DecidableEq K]
    [DecidableEq G] (hs : ProbComp (K × G → K)) (rk : K) (g : G) (A : HealingAdversary K G)
    {q : ℕ} (hq : ∀ v, IsQueryBoundP (A v) (fun _ => True) q) :
    programmedAdv (F := F) hs rk g A ≤
      ∑ i ∈ Finset.range q,
        Pr{let b ← cdhExperiment g (programmedReduction (F := F) hs rk i A)}[b = true] +
        (Fintype.card K : ℝ≥0∞)⁻¹ := by
  have key := deduceAdvO_le_pcOracle_sum (rk, 0) (programmedSample (F := F) hs)
    (fun x => healingView rk g x.1 x.2.1) (fun x => x.2.2.2) (programmedHash rk g) A
    (fun x => honestPoint rk g x.1 x.2.1) (fun x => x.2.2.1 (honestPoint rk g x.1 x.2.1)) hq
  rw [update_programmedHash, deduceAdvO_programmedSample_eq_inv_card] at key
  rw [add_comm]
  exact key.trans (add_le_add le_rfl (Finset.sum_le_sum fun i _ =>
    deduceAdvO_guessQuery_le_cdhExperiment hs rk g i A))

/-! ## From the random oracle to the programmed hash -/

/-- Programming a uniformly random function at a point `m` with a fresh uniform value gives a
uniformly random function, whose value at `m` is the programmed value. -/
theorem uniformSample_update_evalDistEq {D R : Type} [DecidableEq D] [SampleableType R]
    [SampleableType (D → R)] (m : D) :
    (do let H ← $ᵗ (D → R); let r ← $ᵗ R; pure (Function.update H m r, r) :
        ProbComp ((D → R) × R)) =ᵈ
      (do let H ← $ᵗ (D → R); pure (H, H m) : ProbComp ((D → R) × R)) := by
  let e : (D → R) × R ≃ (D → R) × R :=
    { toFun := fun p => (Function.update p.1 m p.2, p.1 m)
      invFun := fun p => (Function.update p.1 m p.2, p.1 m)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  refine EvalDistEq.of_forall_prEvent_eq fun p => ?_
  simp only [prEvent_norm]
  calc Pr{let H ← $ᵗ (D → R); let r ← $ᵗ R}[p (Function.update H m r, r)]
      = Pr{let H ← $ᵗ (D → R); let r ← $ᵗ R}[p ((e (H, r)).1, (e (H, r)).1 m)] := by simp [e]
    _ = Pr{let z ← $ᵗ ((D → R) × R)}[p (z.1, z.1 m)] :=
        SampleableType.prEvent_uniformSample_pair_of_bijective (g := fun H r => e (H, r))
          (by simpa [Function.uncurry_def] using e.bijective) fun z => p (z.1, z.1 m)
    _ = Pr{let H ← $ᵗ (D → R); let _ ← $ᵗ R}[p (H, H m)] :=
        SampleableType.prEvent_uniformSample_prod _
    _ = Pr{let H ← $ᵗ (D → R)}[p (H, H m)] := by
        simp only [← bind_pure_comp]
        refine prEvent_bind_congr_of_support _ _ _ fun H _ => ?_
        rw [OracleComp.prEvent_bind_const]

/-- In the random-oracle model, the healing experiment is the programmed experiment with a
uniformly random hash. -/
theorem healingAdv_eq_programmedAdv [SampleableType F] [SampleableType K] [DecidableEq K]
    [DecidableEq G] [SampleableType (K × G → K)] (rk : K) (g : G) (A : HealingAdversary K G) :
    healingAdv (F := F) rk g A = programmedAdv (F := F) ($ᵗ (K × G → K)) rk g A := by
  simp only [healingAdv, programmedAdv, deduceAdvO, oracleExp, healingSample, programmedSample,
    programmedHash, prEvent_norm, bind_assoc]
  refine prEvent_bind_congr_of_support _ _ _ fun a _ => prEvent_bind_congr_of_support _ _ _
    fun b _ => ?_
  have key := ((uniformSample_update_evalDistEq (honestPoint rk g a b)).bind_left
    fun p : (K × G → K) × K =>
      (fun z => z.1 = p.2) <$> (simulateQ (logImpl p.1) (A (healingView rk g a b))).run []).symm
  simpa [bind_assoc] using key.prEvent_eq id

/-! ## The lazy reductions -/

/-- The CDH reduction for query position `i`. Given `(g, a • g, b • g)`, it runs the attacker on
`(rk, g, a • g, b • g)`, answering its hash queries by a lazily sampled random oracle, and outputs
the group element of the attacker's `i`-th query. It draws one uniform key per fresh query. -/
@[expose] def healingReduction [SampleableType K] [DecidableEq K] [DecidableEq G] (rk : K)
    (i : ℕ) (A : HealingAdversary K G) : CDHAdversary F G :=
  cdhReduction fun v => do
    let d ← (simulateQ randomOracle (guessQuery (rk, 0) i A (rk, v))).run' ∅
    pure d.2

/-- With fixed answers, the logging handler computes the deterministic evaluation. -/
private theorem run'_simulateQ_logImpl {D R γ : Type} (o : D → R) (oa : OracleComp (D →ₒ R) γ)
    (L : List D) :
    (simulateQ (logImpl o) oa).run' L = pure (evalWithAnswerFn (QueryImpl.ofFn o) oa) := by
  induction oa using OracleComp.inductionOn generalizing L with
  | pure a => simp
  | query_bind d k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, logImpl_run,
      pure_bind, evalWithAnswerFn_bind] at ih ⊢
    rw [ih]
    simp

/-- The lazy reduction plays the CDH experiment exactly as the programmed-form reduction with a
uniformly random hash table. -/
theorem cdhExperiment_healingReduction_evalDistEq [SampleableType F] [SampleableType K]
    [DecidableEq K] [DecidableEq G] [Finite G] [SampleableType (K × G → K)] (rk : K) (g : G)
    (i : ℕ) (A : HealingAdversary K G) :
    cdhExperiment g (healingReduction (F := F) rk i A) =ᵈ
      cdhExperiment g (programmedReduction (F := F) ($ᵗ (K × G → K)) rk i A) := by
  have hadv : ∀ v : G × G × G,
      (do let d ← (simulateQ randomOracle (guessQuery (rk, 0) i A (rk, v))).run' ∅; pure d.2) =ᵈ
        (do
          let H ← $ᵗ (K × G → K)
          let z ← (simulateQ (logImpl H) (guessQuery (rk, 0) i A (rk, v))).run []
          pure z.1.2 : ProbComp G) := fun v => by
    let : MeasurableSpace (K × G) := ⊤
    have key := EvalDistEq.of_evalDist_eq
      (evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable
        (guessQuery (rk, 0) i A (rk, v)))
    refine (key.bind_left _).trans ?_
    simp only [bind_assoc, pure_bind]
    refine EvalDistEq.bind_right _ fun H => ?_
    have h := congrArg (Prod.snd <$> ·)
      (run'_simulateQ_logImpl H (guessQuery (rk, 0) i A (rk, v)) [])
    simp only [StateT.run'_eq, Functor.map_map, map_pure] at h
    rw [bind_pure_comp]
    exact h ▸ EvalDistEq.rfl
  unfold cdhExperiment healingReduction programmedReduction cdhReduction
  exact EvalDistEq.bind_right _ fun a => EvalDistEq.bind_right _ fun b =>
    EvalDistEq.bind_left (hadv _) _

/-! ## Healing -/

/-- **Healing.** After a compromise leaks the root key `rk`, one honest Diffie–Hellman exchange
makes the new root key `rk' = H (rk, (a * b) • g)` secret again: an attacker that knows `rk`, sees
`g`, `a • g` and `b • g`, and makes at most `q` adaptive queries to the random oracle `H` outputs
`rk'` with probability at most the summed CDH success of the `q` named reductions
`healingReduction rk i A`, plus `1 / |K|`. This is one step of the ratchet, and CDH enters only
through those reductions. -/
theorem healingAdv_le [SampleableType F] [SampleableType K] [Fintype K] [DecidableEq K]
    [DecidableEq G] [Finite G] [SampleableType (K × G → K)] (rk : K) (g : G)
    (A : HealingAdversary K G) {q : ℕ} (hq : ∀ v, IsQueryBoundP (A v) (fun _ => True) q) :
    healingAdv (F := F) rk g A ≤
      ∑ i ∈ Finset.range q,
        Pr{let b ← cdhExperiment g (healingReduction (F := F) rk i A)}[b = true] +
        (Fintype.card K : ℝ≥0∞)⁻¹ := by
  rw [healingAdv_eq_programmedAdv]
  refine (programmedAdv_le _ rk g A hq).trans_eq ?_
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact ((cdhExperiment_healingReduction_evalDistEq rk g i A).prEvent_eq _).symm

/-! ## Boundary cases -/

/-- An attacker that guesses a fixed key, without querying the hash, outputs the new root key with
probability exactly `1 / |K|`: the last term of `healingAdv_le` cannot be dropped. -/
theorem healingAdv_pure [SampleableType F] [SampleableType K] [Fintype K]
    [SampleableType (K × G → K)] (rk : K) (g : G) (k : K) :
    healingAdv (F := F) rk g (fun _ => pure k) = (Fintype.card K : ℝ≥0∞)⁻¹ := by
  classical
  rw [healingAdv_eq_programmedAdv]
  simp only [programmedAdv, deduceAdvO, oracleExp, programmedSample, simulateQ_pure,
    StateT.run_pure, prEvent_norm, bind_assoc, map_pure]
  refine prEvent_bind_eq_of_forall_eq' _ _ fun a => prEvent_bind_eq_of_forall_eq' _ _
    fun b => prEvent_bind_eq_of_forall_eq' _ _ fun H => ?_
  exact SampleableType.prEvent_uniformSample_eq_singleton' k

/-- The hypotheses of `healingAdv_le` hold jointly: at the field and group `ZMod 2`, with root keys
in `Bool`, for an attacker that asks for `H (rk, a • g)` and outputs the answer. (CDH is easy in so
small a group; this checks only that the hypotheses are consistent.) -/
example (rk : Bool) (g : ZMod 2) :
    healingAdv (F := ZMod 2) rk g (fun v => liftM ((Bool × ZMod 2 →ₒ Bool).query (v.1, v.2.2.1))) ≤
      ∑ i ∈ Finset.range 1,
        Pr{let b ← cdhExperiment g (healingReduction (F := ZMod 2) rk i
              (fun v => liftM ((Bool × ZMod 2 →ₒ Bool).query (v.1, v.2.2.1))))}[b = true] +
        (Fintype.card Bool : ℝ≥0∞)⁻¹ :=
  healingAdv_le rk g _ fun _ => by simp

end SquirrelModel.Healing
