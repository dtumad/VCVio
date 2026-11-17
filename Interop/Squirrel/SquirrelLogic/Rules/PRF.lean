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

/-!
# The PRF rule without an oracle on the left
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

end Valid

end SquirrelLogic
