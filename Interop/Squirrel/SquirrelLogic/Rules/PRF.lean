/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import SquirrelLogic.Compile
public import SquirrelLogic.Rules.FreshL
public import SquirrelLogic.Rules.Equiv
public import VCVio.CryptoFoundations.PRF
import SquirrelLogic.ProductTape
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.QueryTracking.RandomOracle.DependentTable

/-!
# The PRF rules without an oracle on the left

LICS23's G.PRF (p. 29) and CCS26's G.PRF and PRF-Simple (Fig. 4 and Fig. 11, pp. 7 and 17):

```
u⃗, h(m, k) ∼ u⃗, n                      (G.PRF)
u⃗ ⊬ v  ⟹  u⃗, h(m, k) ⊬ v               (PRF-Simple)
```

under `ψ_key` (the key occurs only as the key of `h`), `[ψ_msg]` (no other hash with key `k` is
of `m`), `⊢pptm` and a fresh name `n` of the hash type. Both come from VCVio's PRF game
(`prfAdvantage`) through named reductions.

* `PRFSymbols.scheme P M η` is the PRF that a model implements: the key is the bit block of the
  key name, drawn uniformly, and `eval kc x = h(x, k)` at the key's sample.
* `Model.UniformSampler M τ`: names of the hash type are uniform, so that a fresh name is
  distributed as a random function's value; `Model.uniformSampler` is then VCVio's canonical
  sampler of the hash type, the one the lazily sampled random function uses
  (`PRFSymbols.prfAdv`).
* **The reductions** `PRFSymbols.hashReduction` and `PRFSymbols.freshReduction` are
  `PRFAdversary` programs built by handler composition: they draw both tapes, run the compiled
  vector and message (`PRFSymbols.prog`, `SquirrelLogic.Compile`) through the handler
  `PRFSymbols.fwd`, which answers coins and the tape from the drawn tapes and forwards each hash
  query to the PRF oracle, and log the queries (VCVio's `withQueryLog`). The first queries the
  oracle at the message's value; the second draws a fresh value with the sampler of the hash type.
  Each runs the distinguisher on the vector and the challenge, and returns `false` if the message
  was hashed before the challenge.

## The proof, in three hops

1. **Real world** (`prEvent_prfRealExperiment_hashReduction`,
   `prEvent_prfRealExperiment_freshReduction`): against the keyed hash, the forwarded run is the
   run with the answers of the tapes and the key (`simulateQ_prfRealQueryImpl_fwd`), which the
   adequacy of the compiled reading turns into the ordinary reading. Writing the PRF key into the
   key's coordinate and the fresh value into `n`'s coordinate is a uniform tape
   (`prEvent_uniformSample_update_update`), at which the conclusion's vectors have those values
   (`close_apply_couple`).
2. **Ideal world** (`prEvent_prfIdealExperiment_hashReduction`): against a lazily sampled random
   function, the two reductions output `true` equally often. The function's cache grows only at
   logged messages (`eq_none_of_mem_support_run`), so where the message was not logged its value
   is a fresh draw, as the second reduction's challenge is.
3. **The bad event**: where `ψ_msg` holds, the compiled run never hashes the message
   (`PRFSymbols.cbv_guard`), so the guard of the reductions costs at most `Pr[¬ψ_msg]`.

`PRFSymbols.advantage_le` is the concrete statement: at every `η` the advantage is at most the two
PRF advantages plus `Pr[ψ_msg = false]`. `Valid.equiv_prf` is G.PRF, `Valid.nonDed_prf` is
PRF-Simple, derived from G.PRF, Perm, FreshL and Rw-Equiv as CCS26 derives it (p. 17), and
`PRFInstance` packages G.PRF's data for derivations. `PRFSymbols.prfAdv_eq_zero_of_bijective`: a
hash that is a uniform function under a uniform key, on a finite domain, has PRF advantage zero.

## The fragment

The vector and the message are closed terms with calls, first order, in the `⊢pptm` fragment,
with entries of Boolean or base type: the distinguisher receives values, not functions, and
`ψ_msg` is generated without binders. Higher-order entries and the oracle `o_h^k` on the left are
part 3's rules (PRF.R, PRF.L).
-/

public section

namespace SquirrelLogic

open IPFunctor IPFunctor.ScopedSignature OracleComp OracleSpec PRFScheme

variable {B : Type} {D : Decl B}

/-! ## The model conditions -/

/-- The sampler of names of type `τ` is uniform on `τ`'s values at every `η`: names of `τ` are
distributed as the values of a random function with range `τ`. -/
@[expose] def Model.UniformSampler (M : Model D) (τ : Ty B) : Prop :=
  ∀ η [MeasurableSpace (τ.Value M.carrier η)] [MeasurableSingletonClass (τ.Value M.carrier η)],
    𝒟[M.sample η τ <$> ($ᵗ (M.Coin η τ))] = ProbabilityTheory.uniformOn Set.univ

/-- A uniform sampler of names of `τ`, as VCVio's canonical uniform sampler of `τ`'s values: it
draws a bit block and runs the sampler. -/
@[expose, instance_reducible] noncomputable def Model.uniformSampler (M : Model D) (τ : Ty B)
    (h : M.UniformSampler τ) (η : ℕ) : SampleableType (τ.Value M.carrier η) where
  selectElem := M.sample η τ <$> ($ᵗ (M.Coin η τ))
  evalDist_selectElem_eq_uniform := h η

namespace PRFSymbols

variable (P : PRFSymbols D) (M : Model D) (η : ℕ)

/-! ## The PRF a model implements -/

/-- The keyed hash of a model at `η`, as a PRF: a key is the bit block of the key name, drawn
uniformly, and the hash of `x` under it is `h(x, k)` at the key's sample. -/
@[expose] noncomputable def scheme : PRFScheme (M.Coin η P.keyTy) (P.Dom M η) (P.Rng M η) where
  keygen := $ᵗ (M.Coin η P.keyTy)
  eval kc x := M.fn η P.hOf x (M.sample η P.keyTy kc)

/-- The PRF advantage of a distinguisher against the keyed hash at `η`, VCVio's `prfAdvantage`,
with the random function's values drawn by the sampler of the hash type. -/
@[expose] noncomputable def prfAdv (hU : M.UniformSampler P.hTy)
    (adv : PRFAdversary (P.Dom M η) (P.Rng M η)) : ENNReal :=
  @prfAdvantage _ _ _ (Classical.decEq _) (M.uniformSampler P.hTy hU η) (P.scheme M η) adv

/-! ## The reductions -/

/-- The handler of a reduction: coins and the attacker tape from the tapes `ρ` that the reduction
draws, and the hash from the PRF oracle. -/
@[expose] def fwd (ρ : M.Tape η) :
    QueryImpl (P.Iface M η) (OracleComp (PRFOracleSpec (P.Dom M η) (P.Rng M η)))
  | .inl (.inl k) => pure (ρ.2 k)
  | .inl (.inr ()) => pure ρ.1
  | .inr x => functionQuery x

variable {P M η} {τs : List (Ty B)}

/-- The reduction with a challenge program `chal`: draw both tapes; run the compiled `u⃗` and `m`,
logging their queries, with the handler `fwd`; obtain a challenge from `chal` at the message's
value; and run the distinguisher on the vector followed by the challenge, with the attacker tape
it drew. It returns `false` if the message was hashed before the challenge. -/
@[expose] noncomputable def reductionWith (u : OVec P [] τs) (m : OTerm P [] P.msgTy)
    (A : Distinguisher M (τs ++ [P.hTy]))
    (chal : P.Dom M η → OracleComp (PRFOracleSpec (P.Dom M η) (P.Rng M η)) (P.Rng M η)) :
    PRFAdversary (P.Dom M η) (P.Rng M η) :=
  (do
    let ρ ← liftComp ($ᵗ (M.Tape η)) (PRFOracleSpec (P.Dom M η) (P.Rng M η))
    let r ← simulateQ (P.fwd M η ρ) (P.prog M η u m).withQueryLog
    let y ← chal r.1.2
    pure (A η (Env.append r.1.1 (Env.cons y Env.empty)) ρ.1 &&
      !(@QueryLog.wasQueried _ _ (Classical.decEq _) r.2 (Sum.inr r.1.2))) :
    OracleComp (PRFOracleSpec (P.Dom M η) (P.Rng M η)) Bool)

variable (η) in
/-- **The first reduction**: the challenge is the PRF oracle at the message. -/
@[expose] noncomputable def hashReduction (u : OVec P [] τs) (m : OTerm P [] P.msgTy)
    (A : Distinguisher M (τs ++ [P.hTy])) : PRFAdversary (P.Dom M η) (P.Rng M η) :=
  reductionWith u m A fun x => functionQuery x

variable (η) in
/-- **The second reduction**: the challenge is drawn by the sampler of the hash type, as a fresh
name of that type is. -/
@[expose] noncomputable def freshReduction (u : OVec P [] τs) (m : OTerm P [] P.msgTy)
    (A : Distinguisher M (τs ++ [P.hTy])) : PRFAdversary (P.Dom M η) (P.Rng M η) :=
  reductionWith u m A fun _ =>
    liftComp (M.sample η P.hTy <$> ($ᵗ (M.Coin η P.hTy))) (PRFOracleSpec (P.Dom M η) (P.Rng M η))

/-! ## The real world -/

/-- In the real world, the forwarded run is the run with the answers of the tapes and the key. -/
theorem simulateQ_prfRealQueryImpl_fwd (ρ : M.Tape η) (kc : M.Coin η P.keyTy) {α : Type}
    (c : OracleComp (P.Iface M η) α) :
    simulateQ ((P.scheme M η).prfRealQueryImpl kc) (simulateQ (P.fwd M η ρ) c) =
      pure (evalWithAnswerFn (P.answer M η ρ (M.sample η P.keyTy kc)) c) := by
  induction c using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_bind, evalWithAnswerFn_bind]
    rcases t with (k' | ⟨⟩) | x
    · simp only [simulateQ_spec_query, fwd, simulateQ_pure, pure_bind, ih]
      rfl
    · simp only [simulateQ_spec_query, fwd, simulateQ_pure, pure_bind, ih]
      rfl
    · simp only [simulateQ_spec_query, fwd, simulateQ_prfRealQueryImpl_functionQuery, pure_bind,
        ih]
      rfl

/-- The result and the query log of the reduction's program, run with the answers of the tapes
`ρ` and hashes keyed by `kv`. -/
@[expose] noncomputable def run (u : OVec P [] τs) (m : OTerm P [] P.msgTy) (ρ : M.Tape η)
    (kv : P.keyTy.Value M.carrier η) :
    (Vals M η τs × P.Dom M η) × QueryLog (P.Iface M η) :=
  evalWithAnswerFn (P.answer M η ρ kv) (P.prog M η u m).withQueryLog

/-- The outcome of a reduction whose program ran at `ρ` and `kv`, with the challenge `y`: the
distinguisher's output, unless the message was hashed before the challenge. -/
@[expose] noncomputable def outcome (u : OVec P [] τs) (m : OTerm P [] P.msgTy)
    (A : Distinguisher M (τs ++ [P.hTy])) (ρ : M.Tape η) (kv : P.keyTy.Value M.carrier η)
    (y : P.Rng M η) : Bool :=
  A η (Env.append (run u m ρ kv).1.1 (Env.cons y Env.empty)) ρ.1 &&
    !(@QueryLog.wasQueried _ _ (Classical.decEq _) (run u m ρ kv).2 (Sum.inr (run u m ρ kv).1.2))

variable (u : OVec P [] τs) (m : OTerm P [] P.msgTy) (A : Distinguisher M (τs ++ [P.hTy]))

/-- **The first reduction in the real world** draws the key and both tapes, and hashes the
message under the key. -/
theorem prEvent_prfRealExperiment_hashReduction :
    Pr{let b ← (P.scheme M η).prfRealExperiment (hashReduction η u m A)}[b = true] =
      Pr{let kc ← $ᵗ (M.Coin η P.keyTy); let ρ ← $ᵗ (M.Tape η)}[
        outcome u m A ρ (M.sample η P.keyTy kc)
          (M.fn η P.hOf (run u m ρ (M.sample η P.keyTy kc)).1.2 (M.sample η P.keyTy kc)) =
            true] := by
  simp only [prfRealExperiment, hashReduction, reductionWith, simulateQ_bind, simulateQ_map,
    simulateQ_prfRealQueryImpl_liftComp, simulateQ_prfRealQueryImpl_fwd, pure_bind, map_pure,
    simulateQ_prfRealQueryImpl_functionQuery, prEvent_norm]
  rfl

/-- **The second reduction in the real world** draws the key, both tapes and the challenge's bit
block. -/
theorem prEvent_prfRealExperiment_freshReduction :
    Pr{let b ← (P.scheme M η).prfRealExperiment (freshReduction η u m A)}[b = true] =
      Pr{let kc ← $ᵗ (M.Coin η P.keyTy); let ρ ← $ᵗ (M.Tape η); let yc ← $ᵗ (M.Coin η P.hTy)}[
        outcome u m A ρ (M.sample η P.keyTy kc) (M.sample η P.hTy yc) = true] := by
  simp only [prfRealExperiment, freshReduction, reductionWith, simulateQ_bind, simulateQ_map,
    simulateQ_prfRealQueryImpl_liftComp, simulateQ_prfRealQueryImpl_fwd, pure_bind,
    prEvent_norm]
  rfl

/-! ## The coupling with the tapes of the conclusion -/

section Coupling

variable [DecidableEq (M.Slot η)] {a : Ty B} {nn : D.Name a P.hTy} {i : D.Fn a}

/-- With the key's coordinate and the fresh name's coordinate overwritten, the key is read from
its new coin. -/
theorem keyVal_update_update (hkn : P.keySlot M η ≠ M.nameSlot nn i η) (ρh : M.TapeH η)
    (kc : M.Coin η P.keyTy) (yc : M.Coin η P.hTy) :
    P.keyVal M η (Function.update (Function.update ρh (P.keySlot M η) kc) (M.nameSlot nn i η) yc) =
      M.sample η P.keyTy kc := by
  change M.sample η P.keyTy (Function.update (Function.update ρh (P.keySlot M η) kc)
    (M.nameSlot nn i η) yc (P.keySlot M η)) = _
  rw [Function.update_of_ne hkn, Function.update_self]

/-- A closed term with calls, without the key name, whose closed-up term does not read the fresh
name's coordinate, means at the coupled tapes what its compiled reading computes from the
reduction's tapes and the key's coin. -/
theorem close_apply_couple (C : AdvClass M)
    (env : Env (Kind.Value M) []) {τ : Ty B} (t : OTerm P [] τ) (hk : P.KeyFree t)
    (hf : M.FreshAt (M.nameSlot nn i) ((P.close t).denote (fullInterp M C) env))
    (kc : M.Coin η P.keyTy) (ρ : M.Tape η) (yc : M.Coin η P.hTy) :
    (P.close t).denote (fullInterp M C) env η
        (ρ.1, Function.update (Function.update ρ.2 (P.keySlot M η) kc) (M.nameSlot nn i η) yc) =
      t.denote (P.ointerp M η ρ (M.sample η P.keyTy kc)) Env.empty := by
  rw [hf η ρ.1 _ (Function.update ρ.2 (P.keySlot M η) kc)
    fun k hk => Function.update_of_ne hk _ _, denote_close_apply]
  change t.denote (P.ointerp M η _ (M.sample η P.keyTy (Function.update ρ.2 (P.keySlot M η) kc
    (P.keySlot M η)))) Env.empty = _
  rw [Function.update_self]
  exact ointerp_eq_of_keyFree (fun k hk => Function.update_of_ne
    (fun h => hk (congrArg Sigma.fst h)) _ _) _ t hk _

end Coupling

/-! ## The ideal world -/

section Ideal

variable [DecidableEq (P.Dom M η)] [SampleableType (P.Rng M η)]

/-- A run of the forwarded program against the lazily sampled random function leaves uncached
every message that its log does not hash: the cache grows only at hashed messages. -/
theorem eq_none_of_mem_support_run (ρ : M.Tape η) {α : Type} (c : OracleComp (P.Iface M η) α) :
    ∀ (s₀ : (P.Dom M η →ₒ P.Rng M η).QueryCache) z,
      z ∈ support ((simulateQ (P.Dom M η →ₒ P.Rng M η).romImpl
        (simulateQ (P.fwd M η ρ) c.withQueryLog)).run s₀) →
      ∀ x, s₀ x = none → Sum.inr x ∉ z.1.2.map (fun e => e.1) → z.2 x = none := by
  induction c using OracleComp.inductionOn with
  | pure a =>
    intro s₀ z hz x h₀ _
    simp only [withQueryLog_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact h₀
  | query_bind t k ih =>
    intro s₀ z hz x h₀ hlog
    rw [withQueryLog_bind, withQueryLog_query, bind_assoc] at hz
    simp only [pure_bind, simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map,
      mem_support_bind_iff, support_map, Set.mem_image] at hz
    obtain ⟨⟨u, s₁⟩, h₁, z', hz', rfl⟩ := hz
    simp only [Prod.map_snd, List.singleton_append, List.map_cons, List.mem_cons,
      not_or] at hlog
    refine ih u s₁ z' hz' x ?_ hlog.2
    rw [simulateQ_spec_query] at h₁
    rcases t with (k' | ⟨⟩) | x'
    · simp only [fwd, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at h₁
      exact h₁.2 ▸ h₀
    · simp only [fwd, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at h₁
      exact h₁.2 ▸ h₀
    · have hx : x ≠ x' := fun h => hlog.1 (h ▸ rfl)
      simp only [fwd, functionQuery, simulateQ_spec_query, OracleSpec.romImpl_apply_inr,
        randomOracle.run_eq] at h₁
      cases hs : s₀.toFn x' with
      | some v =>
        simp only [hs, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h₁
        exact h₁.2 ▸ h₀
      | none =>
        simp only [hs, mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at h₁
        obtain ⟨v, -, -, rfl⟩ := h₁
        exact (QueryCache.cacheQuery_of_ne s₀ v hx).trans h₀

/-- **The middle hop**: against a lazily sampled random function whose values are drawn by the
sampler of the hash type, the two reductions output `true` equally often. Where the message was
not hashed before the challenge, the random function's value there is fresh
(`eq_none_of_mem_support_run`), and a fresh value is drawn as the second reduction draws its
challenge; where it was, both reductions return `false`. -/
theorem prEvent_prfIdealExperiment_hashReduction
    (hsel : ($ᵗ (P.Rng M η)) = M.sample η P.hTy <$> ($ᵗ (M.Coin η P.hTy))) :
    Pr{let b ← prfIdealExperiment (hashReduction η u m A)}[b = true] =
      Pr{let b ← prfIdealExperiment (freshReduction η u m A)}[b = true] := by
  simp only [prfIdealExperiment, hashReduction, freshReduction, reductionWith, simulateQ_bind,
    simulateQ_prfIdealQueryImpl_liftComp, StateT.run'_liftM_bind]
  refine prEvent_bind_congr _ _ _ _ _ fun ρ => ?_
  simp only [StateT.run'_eq, StateT.run_bind, simulateQ_pure,
    simulateQ_prfIdealQueryImpl_functionQuery, prEvent_norm]
  refine prEvent_bind_congr_of_support _ _ _ fun p hp => ?_
  by_cases hb : (@QueryLog.wasQueried _ _ (Classical.decEq _) p.1.2 (Sum.inr p.1.1.2)) = true
  · simp [hb]
  · have hnone := eq_none_of_mem_support_run ρ _ ∅ p hp p.1.1.2 rfl fun h => hb (by
      rw [@QueryLog.wasQueried_eq_decide_mem_map_fst _ _ (Classical.decEq _)]
      simpa using h)
    simp only [StateT.run_map, randomOracle.run_eq, hnone, StateT.run_liftM, hsel, prEvent_norm]

end Ideal

/-! ## The bound at one security parameter -/

/-- An advantage between two events is at most the advantage between them where a third fails,
plus the probability of the third. -/
private theorem absDiff_le_absDiff_and_not_add {α : Type} (mx : ProbComp α) (p q r : α → Prop) :
    ENNReal.absDiff Pr{let x ← mx}[p x] Pr{let x ← mx}[q x] ≤
      ENNReal.absDiff Pr{let x ← mx}[p x ∧ ¬ r x] Pr{let x ← mx}[q x ∧ ¬ r x] +
        Pr{let x ← mx}[r x] := by
  rw [prEvent_eq_prEvent_and_add_prEvent_and_not mx p (fun x => ¬ r x),
    prEvent_eq_prEvent_and_add_prEvent_and_not mx q (fun x => ¬ r x)]
  refine (absDiff_add_add_le _ _ _ _).trans (add_le_add le_rfl ?_)
  have hp := prEvent_mono mx (fun x => p x ∧ ¬¬ r x) r fun _ h => not_not.1 h.2
  have hq := prEvent_mono mx (fun x => q x ∧ ¬¬ r x) r fun _ h => not_not.1 h.2
  exact ENNReal.absDiff_le_iff.2 ⟨le_add_left hp, le_add_left hq⟩

/-- The PRF advantage is the distance between the two experiments' probabilities of `true`. -/
theorem prfAdv_eq (hU : M.UniformSampler P.hTy) (adv : PRFAdversary (P.Dom M η) (P.Rng M η)) :
    P.prfAdv M η hU adv = ENNReal.absDiff
      Pr{let b ← (P.scheme M η).prfRealExperiment adv}[b = true]
      Pr{let b ← (@prfIdealExperiment _ _ (Classical.decEq _) (M.uniformSampler P.hTy hU η)
        adv)}[b = true] := by
  change MeasureTheory.Measure.boolDist _ _ = _
  rw [MeasureTheory.Measure.boolDist, prEvent_eq_evalDist_singleton,
    prEvent_eq_evalDist_singleton]

/-- **A perfect PRF.** If the hash under a uniform key is a uniform function on a finite domain,
every distinguisher has PRF advantage zero: the real experiment draws a uniform function table,
and the lazily sampled random function has the law of one
(`OracleComp.evalDist_simulateQ_romImpl_run'_eq_completeTable`). -/
theorem prfAdv_eq_zero_of_bijective (hU : M.UniformSampler P.hTy) [Finite (P.Dom M η)]
    (hb : Function.Bijective fun (kc : M.Coin η P.keyTy) (x : P.Dom M η) =>
      M.fn η P.hOf x (M.sample η P.keyTy kc))
    (adv : PRFAdversary (P.Dom M η) (P.Rng M η)) : P.prfAdv M η hU adv = 0 := by
  let _ : DecidableEq (P.Dom M η) := Classical.decEq _
  let _ : Fintype (P.Dom M η) := Fintype.ofFinite _
  let rng : SampleableType (P.Rng M η) := M.uniformSampler P.hTy hU η
  let _ : SampleableType (P.Dom M η → P.Rng M η) :=
    @SampleableType.piOfFintype _ _ (fun _ : P.Dom M η => P.Rng M η)
      (fun _ => Fintype.ofFinite _) fun _ => inferInstance
  let X : (P.Dom M η → P.Rng M η) → ProbComp Bool := fun g =>
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (completeTable ∅ g))) adv
  have hreal : (P.scheme M η).prfRealExperiment adv =ᵈ ($ᵗ (P.Dom M η → P.Rng M η)) >>= X := by
    refine EvalDistEq.trans ?_
      ((SampleableType.map_uniformSample_evalDistEq_of_bijective hb).bind_left X)
    rw [bind_map_left]
    refine EvalDistEq.bind_right _ fun kc => ?_
    have himpl : (P.scheme M η).prfRealQueryImpl kc = unifFwdAnswerImpl (QueryImpl.ofFn
        (completeTable ∅ fun x => M.fn η P.hOf x (M.sample η P.keyTy kc))) := by
      funext t
      rcases t with n | x
      · rfl
      · rfl
    change simulateQ _ adv =ᵈ X _
    rw [himpl]
  have hideal : @prfIdealExperiment _ _ (Classical.decEq _) rng adv =ᵈ
      ($ᵗ (P.Dom M η → P.Rng M η)) >>= X :=
    let _ : MeasurableSpace Bool := ⊤
    EvalDistEq.of_evalDist_eq (evalDist_simulateQ_romImpl_run'_eq_completeTable adv ∅)
  rw [prfAdv_eq, ENNReal.absDiff_eq_zero]
  exact (hreal.prEvent_eq _).trans (hideal.prEvent_eq _).symm

/-- **G.PRF at `η`** (LICS23 p. 29; CCS26 Fig. 11 and App. C.3). The advantage of a distinguisher
between `u⃗, h(m, k)` and `u⃗, n(i)` is at most the PRF advantages of the two named reductions
`hashReduction` and `freshReduction`, plus the probability that `ψ_msg` fails. -/
theorem advantage_le (hU : M.UniformSampler P.hTy) {a : Ty B} (nn : D.Name a P.hTy)
    (i : D.Fn a) (hkn : P.keySlot M η ≠ M.nameSlot nn i η) (u : OVec P [] τs)
    (m : OTerm P [] P.msgTy) (hg : ∀ τ ∈ τs, τ.IsGround) (hmg : P.msgTy.IsGround)
    (hku : ∀ τ x, P.KeyFree (u τ x)) (hkm : P.KeyFree m) (hpu : ∀ τ x, P.Pptm (u τ x))
    (hpm : P.Pptm m) (hfu : ∀ τ x, P.FirstOrder (u τ x)) (hfm : P.FirstOrder m)
    (C : AdvClass M) (env : Env (Kind.Value M) [])
    (hnu : ∀ τ x, M.FreshAt (M.nameSlot nn i) ((P.close (u τ x)).denote (fullInterp M C) env))
    (hnm : M.FreshAt (M.nameSlot nn i) ((P.close m).denote (fullInterp M C) env))
    (A : Distinguisher M (τs ++ [P.hTy])) :
    advantage A (Vec.rv M C (Vec.snoc (P.closeVec u) (P.hashTerm (P.close m))) env)
        (Vec.rv M C (Vec.snoc (P.closeVec u) (FTerm.name nn (FTerm.fn i))) env) η ≤
      P.prfAdv M η hU (hashReduction η u m A) + P.prfAdv M η hU (freshReduction η u m A) +
        Pr{let ρ ← $ᵗ (M.Tape η)}[(P.psiMsg u m).denote (fullInterp M C) env η ρ = false] := by
  classical
  -- What the reductions' program computes from their tapes `ρ` and the key's coin `kc`.
  have hrun : ∀ (ρ : M.Tape η) (kc : M.Coin η P.keyTy),
      (run u m ρ (M.sample η P.keyTy kc)).1 =
        ((fun τ x => (u τ x).denote (P.ointerp M η ρ (M.sample η P.keyTy kc)) Env.empty),
          m.denote (P.ointerp M η ρ (M.sample η P.keyTy kc)) Env.empty) := fun ρ kc =>
    (fst_evalWithAnswerFn_withQueryLog _ _).trans (prog_spec (fun _ => True) u m hg hmg hpu hpm
      (fun _ _ => snd_denote_guardInterp_true _ _) (snd_denote_guardInterp_true _ _)).1
  -- Overwriting the key's coordinate changes no coordinate of another name.
  have hagree : ∀ (ρh : M.TapeH η) (kc : M.Coin η P.keyTy) (k : M.Slot η), k.1 ≠ P.keyName →
      Function.update ρh (P.keySlot M η) kc k = ρh k :=
    fun _ _ _ hk => Function.update_of_ne (fun h => hk (congrArg Sigma.fst h)) _ _
  have hkey1 : ∀ (ρh : M.TapeH η) (kc : M.Coin η P.keyTy),
      P.keyVal M η (Function.update ρh (P.keySlot M η) kc) = M.sample η P.keyTy kc := by
    intro ρh kc
    change M.sample η P.keyTy (Function.update ρh (P.keySlot M η) kc (P.keySlot M η)) = _
    rw [Function.update_self]
  -- **The bad event.** Where `ψ_msg` holds, the program never hashes the message.
  have hbad : ∀ (ρ : M.Tape η) (kc : M.Coin η P.keyTy),
      (@QueryLog.wasQueried _ _ (Classical.decEq _) (run u m ρ (M.sample η P.keyTy kc)).2
        (Sum.inr (run u m ρ (M.sample η P.keyTy kc)).1.2)) = true →
      (P.psiMsg u m).denote (fullInterp M C) env η
        (ρ.1, Function.update ρ.2 (P.keySlot M η) kc) = false := by
    intro ρ kc hb
    by_contra hψ
    rw [Bool.not_eq_false, psiMsg_eq_true_iff] at hψ
    simp only [hkey1] at hψ
    have hm' : m.denote (P.ointerp M η (ρ.1, Function.update ρ.2 (P.keySlot M η) kc)
        (M.sample η P.keyTy kc)) Env.empty =
          m.denote (P.ointerp M η ρ (M.sample η P.keyTy kc)) Env.empty :=
      ointerp_eq_of_keyFree (hagree ρ.2 kc) _ m hkm _
    have hguard : ∀ {σ : Ty B} (t : OTerm P [] σ), P.KeyFree t → P.FirstOrder t →
        (∀ t' ∈ P.calls t, t' ∈ P.vecCalls u ++ P.calls m) →
        (t.denote (P.guardInterp ρ (M.sample η P.keyTy kc)
          fun x => x ≠ m.denote (P.ointerp M η ρ (M.sample η P.keyTy kc)) Env.empty)
          (pairEnv Env.empty)).2 := by
      intro σ t hk hf hsub
      change (t.denote (P.guardInterp (ρ.1, ρ.2) _ _) _).2
      rw [← guardInterp_eq_of_keyFree (hagree ρ.2 kc) _ t hk, snd_denote_guardInterp_iff _ t hf]
      intro t' ht'
      rw [← hm']
      exact hψ t' (hsub t' ht')
    obtain ⟨-, hok⟩ := prog_spec _ u m hg hmg hpu hpm
      (fun τ x => hguard _ (hku τ x) (hfu τ x) fun t' h =>
        List.mem_append_left _ (mem_vecCalls.2 ⟨τ, x, h⟩))
      (hguard m hkm hfm fun t' h => List.mem_append_right _ h)
    rw [@QueryLog.wasQueried_eq_decide_mem_map_fst _ _ (Classical.decEq _)] at hb
    simp only [decide_eq_true_eq] at hb
    rw [hrun] at hb
    exact hok _ hb rfl
  -- The events, as functions of the key's coin, the reductions' tapes and the challenge's bits.
  let kv : M.Coin η P.keyTy → P.keyTy.Value M.carrier η := M.sample η P.keyTy
  let Eh : M.Coin η P.keyTy → M.Tape η → Prop := fun kc ρ =>
    A η (Env.append (run u m ρ (kv kc)).1.1
      (Env.cons (M.fn η P.hOf (run u m ρ (kv kc)).1.2 (kv kc)) Env.empty)) ρ.1 = true
  let En : M.Coin η P.keyTy → M.Tape η → M.Coin η P.hTy → Prop := fun kc ρ yc =>
    A η (Env.append (run u m ρ (kv kc)).1.1 (Env.cons (M.sample η P.hTy yc) Env.empty)) ρ.1 = true
  let Bad : M.Coin η P.keyTy → M.Tape η → Prop := fun kc ρ =>
    (@QueryLog.wasQueried _ _ (Classical.decEq _) (run u m ρ (kv kc)).2
      (Sum.inr (run u m ρ (kv kc)).1.2)) = true
  let T : ProbComp (M.Coin η P.keyTy × M.Tape η × M.Coin η P.hTy) := do
    let kc ← $ᵗ (M.Coin η P.keyTy)
    let ρ ← $ᵗ (M.Tape η)
    let yc ← $ᵗ (M.Coin η P.hTy)
    pure (kc, ρ, yc)
  have hT : ∀ p : M.Coin η P.keyTy → M.Tape η → M.Coin η P.hTy → Prop,
      Pr{let kc ← $ᵗ (M.Coin η P.keyTy); let ρ ← $ᵗ (M.Tape η); let yc ← $ᵗ (M.Coin η P.hTy)}[
        p kc ρ yc] = Pr{let x ← T}[p x.1 x.2.1 x.2.2] := fun p => by
    simp only [T, prEvent_norm]
  have hT₂ : ∀ p : M.Coin η P.keyTy → M.Tape η → Prop,
      Pr{let kc ← $ᵗ (M.Coin η P.keyTy); let ρ ← $ᵗ (M.Tape η)}[p kc ρ] =
        Pr{let x ← T}[p x.1 x.2.1] := fun p => by
    refine Eq.trans ?_ (hT fun kc ρ _ => p kc ρ)
    have h : (do
        let kc ← $ᵗ (M.Coin η P.keyTy)
        let ρ ← $ᵗ (M.Tape η)
        pure (p kc ρ) : ProbComp Prop) =ᵈ (do
          let kc ← $ᵗ (M.Coin η P.keyTy)
          let ρ ← $ᵗ (M.Tape η)
          let _ ← $ᵗ (M.Coin η P.hTy)
          pure (p kc ρ) : ProbComp Prop) :=
      EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ =>
        (OracleComp.EvalDistEq.bind_const _ _).symm
    simpa only [prEvent_norm, id] using h.prEvent_eq id
  -- **Hop 1 and hop 3, real side**: the reductions in the real world are the events where the
  -- message was not hashed before the challenge.
  have hrh : Pr{let b ← (P.scheme M η).prfRealExperiment (hashReduction η u m A)}[b = true] =
      Pr{let x ← T}[Eh x.1 x.2.1 ∧ ¬ Bad x.1 x.2.1] := by
    refine (prEvent_prfRealExperiment_hashReduction u m A).trans
      (Eq.trans ?_ (hT₂ fun kc ρ => Eh kc ρ ∧ ¬ Bad kc ρ))
    refine prEvent_bind_congr_of_forall _ _ _ _ _ fun kc => prEvent_congr _ _ _ fun ρ => ?_
    simp [outcome, Eh, Bad, kv]
  have hrf : Pr{let b ← (P.scheme M η).prfRealExperiment (freshReduction η u m A)}[b = true] =
      Pr{let x ← T}[En x.1 x.2.1 x.2.2 ∧ ¬ Bad x.1 x.2.1] := by
    refine (prEvent_prfRealExperiment_freshReduction u m A).trans
      (Eq.trans ?_ (hT fun kc ρ yc => En kc ρ yc ∧ ¬ Bad kc ρ))
    refine prEvent_bind_congr_of_support _ _ _ fun kc _ =>
      prEvent_bind_congr_of_support _ _ _ fun ρ _ => prEvent_congr _ _ _ fun yc => ?_
    simp [outcome, En, Bad, kv]
  -- **The coupling**: the conclusion's tapes are the reductions' tapes with the key's
  -- coordinate and the fresh name's coordinate overwritten.
  have hcpl : ∀ (kc : M.Coin η P.keyTy) (ρ : M.Tape η) (yc : M.Coin η P.hTy),
      (P.closeVec u).rv M C env η (ρ.1, Function.update (Function.update ρ.2 (P.keySlot M η) kc)
        (M.nameSlot nn i η) yc) = (run u m ρ (kv kc)).1.1 := fun kc ρ yc => by
    rw [hrun]
    funext τ x
    exact close_apply_couple C env (u τ x) (hku τ x) (hnu τ x) kc ρ yc
  have hph : Pr{let ρ ← $ᵗ (M.Tape η)}[A η (Vec.rv M C (Vec.snoc (P.closeVec u)
      (P.hashTerm (P.close m))) env η ρ) ρ.1 = true] = Pr{let x ← T}[Eh x.1 x.2.1] := by
    refine (prEvent_uniformSample_update_update (β := M.TapeA η)
      (α := fun k : M.Slot η => M.Coin η k.1.2.1) (P.keySlot M η) (M.nameSlot nn i η) _).symm.trans
      (Eq.trans ?_ (hT fun kc ρ _ => Eh kc ρ))
    refine prEvent_bind_congr_of_support _ _ _ fun kc _ =>
      prEvent_bind_congr_of_support _ _ _ fun ρ _ => prEvent_congr _ _ _ fun yc => ?_
    refine Iff.of_eq (congrArg (fun v => A η v ρ.1 = true) ?_)
    rw [Vec.rv_snoc, P.denote_hashTerm]
    dsimp only [VecRV.snoc]
    rw [hcpl, keyVal_update_update hkn, close_apply_couple C env m hkm hnm kc ρ yc, hrun]
  have hpn : Pr{let ρ ← $ᵗ (M.Tape η)}[A η (Vec.rv M C (Vec.snoc (P.closeVec u)
      (FTerm.name nn (FTerm.fn i))) env η ρ) ρ.1 = true] = Pr{let x ← T}[En x.1 x.2.1 x.2.2] := by
    refine (prEvent_uniformSample_update_update (β := M.TapeA η)
      (α := fun k : M.Slot η => M.Coin η k.1.2.1) (P.keySlot M η) (M.nameSlot nn i η) _).symm.trans
      (Eq.trans ?_ (hT fun kc ρ yc => En kc ρ yc))
    refine prEvent_bind_congr_of_support _ _ _ fun kc _ =>
      prEvent_bind_congr_of_support _ _ _ fun ρ _ => prEvent_congr _ _ _ fun yc => ?_
    refine Iff.of_eq (congrArg (fun v => A η v ρ.1 = true) ?_)
    rw [Vec.rv_snoc, FTerm.denote_name]
    dsimp only [VecRV.snoc]
    rw [hcpl]
    change _ = Env.append _ (Env.cons (M.sample η P.hTy yc) Env.empty)
    congr 2
    exact congrArg (M.sample η P.hTy) (Function.update_self _ _ _)
  -- **The bad event** is bounded by the failure of `ψ_msg`.
  have hpb : Pr{let x ← T}[Bad x.1 x.2.1] ≤
      Pr{let ρ ← $ᵗ (M.Tape η)}[(P.psiMsg u m).denote (fullInterp M C) env η ρ = false] :=
    (prEvent_mono T _ _ fun x hx => hbad x.2.1 x.1 hx).trans (le_of_eq
      ((hT₂ fun kc ρ => (P.psiMsg u m).denote (fullInterp M C) env η
        (ρ.1, Function.update ρ.2 (P.keySlot M η) kc) = false).symm.trans
      (prEvent_uniformSample_prod_update (β := M.TapeA η)
        (α := fun k : M.Slot η => M.Coin η k.1.2.1) (P.keySlot M η)
        fun ρ => (P.psiMsg u m).denote (fullInterp M C) env η ρ = false)))
  -- **Hop 2**: in the ideal world the two reductions agree.
  have hid := @prEvent_prfIdealExperiment_hashReduction _ _ P M η _ u m A (Classical.decEq _)
    (M.uniformSampler P.hTy hU η) rfl
  rw [advantage, hph, hpn]
  refine (absDiff_le_absDiff_and_not_add T _ _ fun x => Bad x.1 x.2.1).trans
    (add_le_add ?_ hpb)
  rw [← hrh, ← hrf, prfAdv_eq, prfAdv_eq, hid]
  exact (ENNReal.absDiff_triangle _ _ _).trans
    (add_le_add le_rfl (ENNReal.absDiff_comm _ _).le)

end PRFSymbols

/-! ## The rules -/

section Vectors

variable {S : Type} {V : S → Type}

/-- A property of every entry of two vectors holds of every entry of their concatenation. -/
theorem Env.forall_append {Γ : List S} {p : ∀ a, V a → Prop} :
    ∀ {Ξ : List S} {ξ : Env V Ξ} {η : Env V Γ}, (∀ a x, p a (ξ a x)) → (∀ a x, p a (η a x)) →
      ∀ a x, p a (Env.append ξ η a x)
  | [], _, _, _, hη => hη
  | _ :: _, _, _, hξ, hη => fun a x => by
    cases x with
    | zero => exact hξ _ .zero
    | succ x => exact Env.forall_append (fun _ y => hξ _ y.succ) hη a x

/-- The renaming that exchanges the last two entries of `(Ξ ++ [b]) ++ [c]`. -/
@[expose] def swapLast (Ξ : List S) (b c : S) : Renaming ((Ξ ++ [b]) ++ [c]) ((Ξ ++ [c]) ++ [b]) :=
  Env.append (Env.append (fun _ x => renameInl (Γ := [b]) _ (renameInl (Γ := [c]) _ x))
      (Env.cons (renameInr (Ξ ++ [c]) _ .zero) Env.empty))
    (Env.cons (renameInl (Γ := [b]) _ (renameInr Ξ _ .zero)) Env.empty)

theorem Env.append_renameInl {Ξ Γ : List S} (ξ : Env V Ξ) (η : Env V Γ) {a : S}
    (z : ScopedVar Ξ a) : Env.append ξ η a (renameInl a z) = ξ a z :=
  congrFun (congrFun (Env.rename_renameInl_append ξ η) a) z

theorem rename_swapLast {Ξ : List S} {b c : S} (w : Env V Ξ) (x : V c) (y : V b) :
    Env.rename (swapLast Ξ b c)
        (Env.append (Env.append w (Env.cons x Env.empty)) (Env.cons y Env.empty)) =
      Env.append (Env.append w (Env.cons y Env.empty)) (Env.cons x Env.empty) := by
  rw [swapLast, Env.rename_append_renaming, Env.rename_append_renaming]
  congr 2
  · funext a z
    exact (Env.append_renameInl _ _ _).trans (Env.append_renameInl _ _ _)
  · funext a z
    cases z with
    | zero => exact Env.append_renameInr _ _ _ _
    | succ z => exact nomatch z
  · funext a z
    cases z with
    | zero => exact (Env.append_renameInl _ _ _).trans (Env.append_renameInr _ _ _ _)
    | succ z => exact nomatch z

end Vectors

theorem PRFSymbols.closeVec_append (P : PRFSymbols D) {Γ : List (Kind B)} {τs' : List (Ty B)} :
    ∀ {τs : List (Ty B)} (u : OVec P Γ τs) (w : OVec P Γ τs'),
      P.closeVec (Env.append u w) = Env.append (P.closeVec u) (P.closeVec w)
  | [], _, _ => rfl
  | _ :: _, u, w => by
    funext a x
    cases x with
    | zero => rfl
    | succ x => exact congrFun (congrFun
        (PRFSymbols.closeVec_append P (fun _ y => u _ (.succ y)) w) a) x

theorem PRFSymbols.closeVec_single (P : PRFSymbols D) {Γ : List (Kind B)} {β : Ty B}
    (v : OTerm P Γ β) :
    P.closeVec (Env.cons v Env.empty : OVec P Γ [β]) =
      (Env.cons (P.close v) Env.empty : Vec D Γ [β]) := by
  funext a x
  cases x with
  | zero => rfl
  | succ x => exact nomatch x

/-- A vector of Boolean and base types has order at most one. -/
theorem Ty.IndistOrder.of_isGround {τs : List (Ty B)} (h : ∀ τ ∈ τs, τ.IsGround) :
    Ty.IndistOrder τs :=
  fun τ hτ => (Ty.isGround_iff_order_eq_zero.1 (h τ hτ)).trans_le zero_le_one

/-- Distinct names read distinct coordinates. -/
theorem PRFSymbols.keySlot_ne_nameSlot (P : PRFSymbols D) {M : Model D} {a : Ty B}
    {nn : D.Name a P.hTy} (i : D.Fn a)
    (hnk : (⟨a, P.hTy, nn⟩ : (a : Ty B) × (b : Ty B) × D.Name a b) ≠ P.keyName) (η : ℕ) :
    P.keySlot M η ≠ M.nameSlot nn i η :=
  fun h => hnk (congrArg Sigma.fst h).symm

namespace Valid

variable {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M} {τs : List (Ty B)}

/-- **G.PRF** (LICS23 p. 29; CCS26 Fig. 11, p. 17), without an oracle on the left:

```
u⃗, h(m, k) ∼ u⃗, n(i)
```

for a closed vector `u⃗` and message `m` given as terms with calls, closed up (`PRFSymbols.close`),
and a name `n` of the hash type.

* `ψ_key` (`hku`, `hkm`): the key name does not occur in the terms with calls, so it occurs only
  as the key of `h` in `u⃗` and `m`.
* `⊢pptm` (`hpu`, `hpm`): the terms are in the fragment of the compiled reading, first order, with
  entries and message of Boolean or base type.
* `[ψ_msg]` (`hmsg`): over the calls of `u⃗` and `m`, the argument differs from `m`, overwhelmingly.
* `n` is not the key name, and in every model of `R` the terms do not read `n(i)`'s coordinate;
  names of the hash type are uniform there (`Model.UniformSampler`), so that `n(i)` is distributed
  as a random function's value.
* `hprf` is the assumption, on the image of the class under the two named reductions
  `PRFSymbols.hashReduction` and `PRFSymbols.freshReduction`: for every admitted machine, their
  PRF advantages (`PRFSymbols.prfAdv`, VCVio's `prfAdvantage`) are negligible.

At every `η` the advantage is at most the sum of the two PRF advantages and the probability that
`ψ_msg` fails (`PRFSymbols.advantage_le`). -/
theorem equiv_prf (P : PRFSymbols D) {Θ : List (Form D [])} (u : OVec P [] τs)
    (m : OTerm P [] P.msgTy) {a : Ty B} (nn : D.Name a P.hTy) (i : D.Fn a)
    {ho : Ty.IndistOrder (τs ++ [P.hTy])} (hg : ∀ τ ∈ τs, τ.IsGround) (hmg : P.msgTy.IsGround)
    (hku : ∀ τ x, P.KeyFree (u τ x)) (hkm : P.KeyFree m) (hpu : ∀ τ x, P.Pptm (u τ x))
    (hpm : P.Pptm m) (hfu : ∀ τ x, P.FirstOrder (u τ x)) (hfm : P.FirstOrder m)
    (hnk : (⟨a, P.hTy, nn⟩ : (a : Ty B) × (b : Ty B) × D.Name a b) ≠ P.keyName)
    (hR : ∀ M, R M → M.UniformSampler P.hTy ∧
      (∀ τ x, FTerm.Avoids M (fun η k => k = M.nameSlot nn i η) (P.close (u τ x))) ∧
      FTerm.Avoids M (fun η k => k = M.nameSlot nn i η) (P.close m))
    (hprf : ∀ M : Model D, M.RespectsLabels → R M → ∀ hU : M.UniformSampler P.hTy,
      ∀ A : Machine M (τs ++ [P.hTy]) .bool, (C M).mem A →
        negligible (fun η => P.prfAdv M η hU (P.hashReduction η u m A.test)) ∧
          negligible (fun η => P.prfAdv M η hU (P.freshReduction η u m A.test)))
    (hmsg : Valid R C Θ (.box (P.psiMsg u m))) :
    Valid R C Θ (.equiv (Vec.snoc (P.closeVec u) (P.hashTerm (P.close m)))
      (Vec.snoc (P.closeVec u) (FTerm.name nn (FTerm.fn i))) ho) := by
  intro M hl hRM env hΘ
  obtain ⟨hU, hau, ham⟩ := hR M hRM
  have hbox := Form.holds_box.1 (hmsg M hl hRM env hΘ)
  refine Form.holds_equiv.2 fun A hA => ?_
  obtain ⟨h₁, h₂⟩ := hprf M hl hRM hU A hA
  exact negligible_of_le (fun η => P.advantage_le hU nn i (P.keySlot_ne_nameSlot i hnk η) u m hg
    hmg hku hkm hpu hpm hfu hfm (C M) env (fun τ x => FTerm.Avoids.freshAt (hau τ x) (C M) env)
    (FTerm.Avoids.freshAt ham (C M) env) A.test) (negligible_add (negligible_add h₁ h₂) hbox)

/-- **PRF-Simple** (CCS26 Fig. 4 and Fig. 11, pp. 7 and 17): from `u⃗ ⊬ v` conclude
`u⃗, h(m, k) ⊬ v`, derived as CCS26 derives it (p. 17): G.PRF on the vector `u⃗, v` gives
`u⃗, v, h(m, k) ∼ u⃗, v, n(i)` for a name `n` fresh in `u⃗`, `v` and `m`; Perm moves `v` last;
FreshL turns `u⃗ ⊬ v` into `u⃗, n(i) ⊬ v`; and Rw-Equiv, for a secret of Boolean or base type,
gives the conclusion.

The side conditions are those of the three rules: `ψ_key`, `⊢pptm`, first order and `[ψ_msg]` on
`u⃗, v` and `m` (G.PRF); long tapes, polynomial bit blocks for the hash type, and read bounds of
`u⃗` and `v` under `Θ` (FreshL); `n(i)` fresh in `u⃗`, `v` and `m`, and names of the hash type
uniform (both). `hprf` is G.PRF's assumption at the vector `u⃗, v`. -/
theorem nonDed_prf (P : PRFSymbols D) {Θ : List (Form D [])} {β : Ty B} (u : OVec P [] τs)
    (v : OTerm P [] β) (m : OTerm P [] P.msgTy) {a : Ty B} (nn : D.Name a P.hTy) (i : D.Fn a)
    {ho : Ty.SecrecyOrder τs β} {ho' : Ty.SecrecyOrder (τs ++ [P.hTy]) β}
    (hg : ∀ τ ∈ τs, τ.IsGround) (hβ : β.IsGround) (hmg : P.msgTy.IsGround)
    (hhg : P.hTy.IsGround) (hku : ∀ τ x, P.KeyFree (u τ x)) (hkv : P.KeyFree v)
    (hkm : P.KeyFree m) (hpu : ∀ τ x, P.Pptm (u τ x)) (hpv : P.Pptm v) (hpm : P.Pptm m)
    (hfu : ∀ τ x, P.FirstOrder (u τ x)) (hfv : P.FirstOrder v) (hfm : P.FirstOrder m)
    (hnk : (⟨a, P.hTy, nn⟩ : (a : Ty B) × (b : Ty B) × D.Name a b) ≠ P.keyName)
    (hR : ∀ M, R M → M.UniformSampler P.hTy ∧ M.LongTapes ∧ M.PolyCoins P.hTy ∧
      (∀ τ x, FTerm.Avoids M (fun η k => k = M.nameSlot nn i η) (P.close (u τ x))) ∧
      FTerm.Avoids M (fun η k => k = M.nameSlot nn i η) (P.close v) ∧
      FTerm.Avoids M (fun η k => k = M.nameSlot nn i η) (P.close m))
    (hread : ∀ M : Model D, M.RespectsLabels → R M → ∀ env, (∀ θ ∈ Θ, θ.Holds M (C M) env) →
      Vec.ReadsPoly M (C M) (P.closeVec u) env ∧ FTerm.ReadsPoly M (C M) (P.close v) env)
    (hprf : ∀ M : Model D, M.RespectsLabels → R M → ∀ hU : M.UniformSampler P.hTy,
      ∀ A : Machine M ((τs ++ [β]) ++ [P.hTy]) .bool, (C M).mem A →
        negligible (fun η => P.prfAdv M η hU
          (P.hashReduction η (Env.append u (Env.cons v Env.empty)) m A.test)) ∧
        negligible (fun η => P.prfAdv M η hU
          (P.freshReduction η (Env.append u (Env.cons v Env.empty)) m A.test)))
    (hmsg : Valid R C Θ (.box (P.psiMsg (Env.append u (Env.cons v Env.empty)) m)))
    (h : Valid R C Θ (.nonDed (P.closeVec u) (P.close v) ho)) :
    Valid R C Θ (.nonDed (Vec.snoc (P.closeVec u) (P.hashTerm (P.close m))) (P.close v) ho') := by
  have hgv : ∀ τ ∈ τs ++ [β], τ.IsGround := fun τ hτ =>
    (List.mem_append.1 hτ).elim (hg τ) fun h' => (List.mem_singleton.1 h') ▸ hβ
  have hall : ∀ {p : ∀ τ, OTerm P [] τ → Prop}, (∀ τ x, p τ (u τ x)) → p β v →
      ∀ τ x, p τ (Env.append u (Env.cons v Env.empty) τ x) := fun hu hv =>
    Env.forall_append hu fun _ x => by
      cases x with
      | zero => exact hv
      | succ x => exact nomatch x
  have hprf' := equiv_prf P (Env.append u (Env.cons v Env.empty)) m nn i
    (ho := Ty.IndistOrder.of_isGround fun τ hτ => (List.mem_append.1 hτ).elim (hgv τ)
      fun h' => (List.mem_singleton.1 h') ▸ hhg)
    hgv hmg (hall hku hkv) hkm (hall hpu hpv) hpm (hall hfu hfv) hfm hnk
    (fun M hRM => ⟨(hR M hRM).1, hall (p := fun _ t => FTerm.Avoids M _ (P.close t))
      (hR M hRM).2.2.2.1 (hR M hRM).2.2.2.2.1, (hR M hRM).2.2.2.2.2⟩) hprf hmsg
  rw [P.closeVec_append, P.closeVec_single] at hprf'
  have hperm := equiv_rename (swapLast τs P.hTy β) hprf'
  rw [Vec.snoc, Vec.snoc, rename_swapLast, rename_swapLast] at hperm
  exact nonDed_rwEquiv hβ (nonDed_freshL nn i (fun M hRM => ⟨(hR M hRM).2.1, (hR M hRM).2.2.1⟩)
    hread (fun M hRM => ⟨(hR M hRM).2.2.2.1, (hR M hRM).2.2.2.2.1⟩) h) hperm

end Valid

/-! ## Instances, for derivations -/

/-- An instance of G.PRF: the keyed hash, a closed vector and a message with calls, and a name of
the hash type at an honest index. -/
structure PRFInstance (D : Decl B) where
  /-- The keyed hash. -/
  P : PRFSymbols D
  /-- The types of the vector. -/
  τs : List (Ty B)
  /-- The vector, with calls. -/
  u : OVec P [] τs
  /-- The message, with calls. -/
  m : OTerm P [] P.msgTy
  /-- The index type of the fresh name. -/
  a : Ty B
  /-- The fresh name, of the hash type. -/
  nn : D.Name a P.hTy
  /-- The index at which the fresh name is read. -/
  i : D.Fn a
  /-- The vectors of the conclusion have order at most one. -/
  order : Ty.IndistOrder (τs ++ [P.hTy])

namespace PRFInstance

variable (e : PRFInstance D)

/-- The syntactic side conditions of G.PRF: entries and message of Boolean or base type, `ψ_key`,
`⊢pptm`, first order, and a fresh name that is not the key name. -/
@[expose] def Syntactic : Prop :=
  (∀ τ ∈ e.τs, τ.IsGround) ∧ e.P.msgTy.IsGround ∧ (∀ τ x, e.P.KeyFree (e.u τ x)) ∧
    e.P.KeyFree e.m ∧ (∀ τ x, e.P.Pptm (e.u τ x)) ∧ e.P.Pptm e.m ∧
    (∀ τ x, e.P.FirstOrder (e.u τ x)) ∧ e.P.FirstOrder e.m ∧
    (⟨e.a, e.P.hTy, e.nn⟩ : (a : Ty B) × (b : Ty B) × D.Name a b) ≠ e.P.keyName

/-- The semantic hypotheses of G.PRF: in every model of `R`, names of the hash type are uniform
and the terms do not read the fresh name's coordinate; and the two reductions of every admitted
machine have negligible PRF advantage. -/
@[expose] def Holds (R : Model D → Prop) (C : ∀ M : Model D, AdvClass M) : Prop :=
  (∀ M, R M → M.UniformSampler e.P.hTy ∧
      (∀ τ x, FTerm.Avoids M (fun η k => k = M.nameSlot e.nn e.i η) (e.P.close (e.u τ x))) ∧
      FTerm.Avoids M (fun η k => k = M.nameSlot e.nn e.i η) (e.P.close e.m)) ∧
    ∀ M : Model D, M.RespectsLabels → R M → ∀ hU : M.UniformSampler e.P.hTy,
      ∀ A : Machine M (e.τs ++ [e.P.hTy]) .bool, (C M).mem A →
        negligible (fun η => e.P.prfAdv M η hU (e.P.hashReduction η e.u e.m A.test)) ∧
          negligible (fun η => e.P.prfAdv M η hU (e.P.freshReduction η e.u e.m A.test))

/-- The left vector of the conclusion, `u⃗, h(m, k)`. -/
@[expose] def lhs : Vec D [] (e.τs ++ [e.P.hTy]) :=
  Vec.snoc (e.P.closeVec e.u) (e.P.hashTerm (e.P.close e.m))

/-- The right vector of the conclusion, `u⃗, n(i)`. -/
@[expose] def rhs : Vec D [] (e.τs ++ [e.P.hTy]) :=
  Vec.snoc (e.P.closeVec e.u) (FTerm.name e.nn (FTerm.fn e.i))

/-- G.PRF at an instance. -/
theorem valid {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M} {Θ : List (Form D [])}
    (hs : e.Syntactic) (hh : e.Holds R C) (hmsg : Valid R C Θ (.box (e.P.psiMsg e.u e.m))) :
    Valid R C Θ (.equiv e.lhs e.rhs e.order) :=
  Valid.equiv_prf e.P e.u e.m e.nn e.i hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1
    hs.2.2.2.2.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.2 hh.1 hh.2 hmsg

end PRFInstance

end SquirrelLogic
