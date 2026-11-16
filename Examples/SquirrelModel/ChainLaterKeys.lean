/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Examples.SquirrelModel.ChainSecrecy

/-!
# Forward secrecy of later keys of the hash chain

**Translation.** In Hérouard, Jacomme, Koutsos and Lallemand (CCS 2026), §2, the key `ck@t` is safe
when no corruption happens up to `t`. Here `ck@t` is the key after the first `t` updates, and
`[safe t]` is a restriction on the attacker's type, `SafeAdversary K M t`: no corruption among its
first `t` chain operations. The keyed hash is the random oracle of `ChainSecrecy`, and
`frame@t' ⊬ ck@t` is the bound on `keyAdv t A`, the attacker's probability of outputting that key.

`ChainSecrecy` bounds the attacker's chance of outputting the initial key `ck₀ = s`. The paper's
statement covers every safe key: `[happens(t, t')] → [safe t] → frame@t' ⊬ ck@t`. Here it is proved
for every `t`, against an adaptive attacker in the random-oracle model.

A `t`-safe attacker (`SafeAdversary K M t`) makes updates as its first `t` chain operations:
before each of them it uses only coins and the hash oracle, and it chooses each update's input from
what it has seen. After them it is an arbitrary chain attacker, which may update and corrupt as it
likes, so it can learn every key after `ck_t`. `SafeAdversary.toChain` reads it as a chain attacker,
and `snd_map_keyRun` shows that the experiment `keyExp` runs exactly that attacker against the
chain, recording `ck_t`. `keyAdv_le` bounds its chance of outputting `ck_t` by
`((t + 1) q + 1) / |K|`, where `q` bounds the hash queries of the run from every initial key: the
attacker's own and one for each chain operation, the `t` safe updates included. At `t = 0` this is
`chainAdv_le` (`keyAdv_zero`).

## Proof

By induction on `t`; the base case is `chainAdv_le`. The step (`prEvent_stepRun_le`) concerns the
first update `ck₁ = H(s, x)` under a uniform secret `s`. Reading it as the derivation of `x` under
the secret (`chainEncoding`), `SecretEncoding.prEvent_realImpl_le_add_mul` replaces it by an
independent uniform value at a cost of `q / |K|`. The prefix that chose `x` never sees that value,
so it can be drawn before the prefix (`OracleComp.prEvent_bind_bind_swap`). It then plays the
initial key of the attacker `SafeAdversary.drop t A`, which skips the first update and has one safe
update fewer. The ideal game's table is read once, at a point fixed by the attacker's type, so
moving its entry to the front needs only this exchange of two independent draws rather than a
general lazy-to-eager argument.

## Scope

Safety is part of the attacker's type: it cannot corrupt during its first `t` chain operations.
A game that lets every attacker corrupt and bounds the probability that `t` was safe and the guess
is right is not covered. The bound grows linearly in `t`, one loss of `q / |K|` per safe update.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SquirrelModel.Chain

/-- The inclusion of `spec₁` as the left summand of `spec₁ + spec₂`. -/
@[reducible] def leftLift {ι₁ ι₂ : Type} (spec₁ : OracleSpec ι₁) (spec₂ : OracleSpec ι₂) :
    MonadLiftT (OracleQuery spec₁) (OracleQuery (spec₁ + spec₂)) :=
  inferInstance

variable {K M : Type}

/-! ## Programs over coins and the hash oracle inside larger interfaces -/

/-- Run a program over coins and the hash oracle with the oracles `spec` also available. -/
@[expose] def liftHash {ι : Type} (spec : OracleSpec ι) {α : Type}
    (oa : OracleComp (unifSpec + hashSpec K M) α) : OracleComp (unifSpec + hashSpec K M + spec) α :=
  liftComp oa (unifSpec + hashSpec K M + spec) (h := leftLift _ _)

/-- A handler runs a lifted program as its left summand does. -/
theorem simulateQ_liftHash {ι : Type} {spec : OracleSpec ι} {m : Type → Type*} [Monad m]
    [LawfulMonad m] (impl : QueryImpl (unifSpec + hashSpec K M + spec) m) {α : Type}
    (oa : OracleComp (unifSpec + hashSpec K M) α) :
    simulateQ impl (liftHash spec oa) = simulateQ (fun t => impl (.inl t)) oa :=
  QueryImpl.simulateQ_liftComp_left_eq_of_apply impl _ (fun _ => rfl) oa

/-- Lifting a program commutes with bind. -/
theorem liftHash_bind {ι : Type} (spec : OracleSpec ι) {α β : Type}
    (oa : OracleComp (unifSpec + hashSpec K M) α) (f : α → OracleComp (unifSpec + hashSpec K M) β) :
    liftHash spec (oa >>= f) = liftHash spec oa >>= fun x => liftHash spec (f x) :=
  liftComp_bind (h := leftLift _ _) _ oa f

/-- A lifted query is the same query in the left summand. -/
theorem liftHash_query {ι : Type} (spec : OracleSpec ι) (t : (unifSpec + hashSpec K M).Domain) :
    liftHash spec (liftM ((unifSpec + hashSpec K M).query t) :
        OracleComp (unifSpec + hashSpec K M) _) =
      (liftM ((unifSpec + hashSpec K M + spec).query (.inl t)) :
        OracleComp (unifSpec + hashSpec K M + spec) _) := by
  rw [liftHash, liftComp_liftM_query (h := leftLift _ _)]
  rfl

/-- A budget on a program over coins and the hash oracle is a budget on its lift, for a predicate
that agrees on the left summand. -/
theorem isQueryBoundP_liftHash {ι : Type} {spec : OracleSpec ι} {α : Type}
    {oa : OracleComp (unifSpec + hashSpec K M) α} {p : (unifSpec + hashSpec K M).Domain → Prop}
    [DecidablePred p] {p' : (unifSpec + hashSpec K M + spec).Domain → Prop} [DecidablePred p']
    (hp : ∀ t, p' (.inl t) ↔ p t) {n : ℕ} (h : IsQueryBoundP oa p n) :
    IsQueryBoundP (liftHash spec oa) p' n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x => simp [liftHash]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [liftHash_bind, liftHash_query, isQueryBoundP_query_bind_iff]
    simp only [hp]
    exact ⟨h.1, fun u => ih u (h.2 u)⟩

/-- A handler forwarding each query unchanged into a state monad leaves the state unchanged. -/
private theorem run_simulateQ_lift_query {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (oa : OracleComp spec α) (st : σ) :
    (simulateQ (fun t => StateT.lift (liftM (spec.query t)) :
        QueryImpl spec (StateT σ (OracleComp spec))) oa).run st = (·, st) <$> oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp [simulateQ_bind, StateT.run_bind, StateT.run_lift, ih]

/-- A program over coins and the hash oracle leaves the chain's key unchanged. -/
theorem run_simulateQ_chainImpl_liftHash {α : Type} (oa : OracleComp (unifSpec + hashSpec K M) α)
    (ck : K) :
    (simulateQ chainImpl (liftHash (chainSpec K M) oa)).run ck = (·, ck) <$> oa := by
  rw [simulateQ_liftHash]
  exact run_simulateQ_lift_query oa ck

/-! ## One safe update -/

section step

variable {β : Type}

/-- One safe update followed by `rest`: run the prefix `P`, update the key `ck` with the input it
names, and continue with `rest` from the new key. -/
@[expose] def stepRun (P : OracleComp (unifSpec + hashSpec K M) (M × β))
    (rest : β → K → OracleComp (unifSpec + hashSpec K M) (K × K)) (ck : K) :
    OracleComp (unifSpec + hashSpec K M) (K × K) := do
  let p ← P
  let ck' ← (liftM ((unifSpec + hashSpec K M).query (.inr (ck, p.1))) :
    OracleComp (unifSpec + hashSpec K M) K)
  rest p.2 ck'

/-- `stepRun` in the derivation world: the update is the derivation of its input. -/
def stepRunD (P : OracleComp (unifSpec + hashSpec K M) (M × β))
    (rest : β → K → OracleComp (unifSpec + hashSpec K M) (K × K)) :
    OracleComp (derivSpec K M) (K × K) := do
  let p ← liftHash (M →ₒ K) P
  let ck ← (liftM ((derivSpec K M).query (.inr p.1)) : OracleComp (derivSpec K M) K)
  liftHash (M →ₒ K) (rest p.2 ck)

/-- Answering the derivation under the secret `s` turns `stepRunD` into `stepRun` from `s`. -/
theorem simulateQ_deriveImpl_stepRunD (s : K) (P : OracleComp (unifSpec + hashSpec K M) (M × β))
    (rest : β → K → OracleComp (unifSpec + hashSpec K M) (K × K)) :
    simulateQ (chainEncoding.deriveImpl s) (stepRunD P rest) = stepRun P rest s := by
  have hl {α : Type} (oa : OracleComp (unifSpec + hashSpec K M) α) :
      simulateQ (chainEncoding.deriveImpl s) (liftHash (M →ₒ K) oa) = oa := by
    rw [simulateQ_liftHash]
    exact simulateQ_id' oa
  simp only [stepRunD, stepRun, simulateQ_bind, hl, simulateQ_spec_query]
  simp [SecretEncoding.deriveImpl, chainEncoding]

/-- A budget on the hash queries of `stepRun` is a budget on the public queries of `stepRunD`:
the update becomes a derivation, which is free. -/
theorem isQueryBoundP_stepRunD {P : OracleComp (unifSpec + hashSpec K M) (M × β)}
    {rest : β → K → OracleComp (unifSpec + hashSpec K M) (K × K)} {s : K} {n : ℕ}
    (h : IsQueryBoundP (stepRun P rest s) (fun t => t.isRight = true) n) :
    IsQueryBoundP (stepRunD P rest) (fun t => isPublic t = true) n := by
  have hp (t : (unifSpec + hashSpec K M).Domain) : isPublic (.inl t) = true ↔ t.isRight = true :=
    by rcases t with n | t <;> simp [isPublic]
  induction P using OracleComp.inductionOn generalizing n with
  | pure p =>
    simp only [stepRun, pure_bind, isQueryBoundP_query_bind_iff] at h
    simp only [stepRunD, liftHash, liftComp_pure, pure_bind, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by simp [isPublic]), fun u => ?_⟩
    simp only [isPublic, Bool.false_eq_true, ite_false]
    exact (isQueryBoundP_liftHash hp (h.2 u)).mono (by simp)
  | query_bind t k ih =>
    simp only [stepRun, bind_assoc, isQueryBoundP_query_bind_iff] at h
    simp only [stepRunD, liftHash_bind, liftHash_query, bind_assoc,
      isQueryBoundP_query_bind_iff, hp]
    exact ⟨h.1, fun u => ih u (h.2 u)⟩

/-- A budget on `stepRun` from the key `s` is a budget on running the prefix and then `rest` from
`s`, skipping the update. -/
theorem isQueryBoundP_bind_of_stepRun {P : OracleComp (unifSpec + hashSpec K M) (M × β)}
    {rest : β → K → OracleComp (unifSpec + hashSpec K M) (K × K)} {s : K} {n : ℕ}
    (h : IsQueryBoundP (stepRun P rest s) (fun t => t.isRight = true) n) :
    IsQueryBoundP (P >>= fun p => rest p.2 s) (fun t => t.isRight = true) n := by
  induction P using OracleComp.inductionOn generalizing n with
  | pure p =>
    simp only [stepRun, pure_bind, isQueryBoundP_query_bind_iff] at h
    simp only [pure_bind]
    exact (h.2 s).mono (by simp)
  | query_bind t k ih =>
    simp only [stepRun, bind_assoc, isQueryBoundP_query_bind_iff] at h
    simp only [bind_assoc, isQueryBoundP_query_bind_iff]
    exact ⟨h.1, fun u => ih u (h.2 u)⟩

end step

/-! ## Attackers that leave the key after `t` updates safe -/

/-- An attacker against the key after `t` updates that leaves it safe: its first `t` chain
operations are updates. At `t = 0` it is any chain attacker. At `t + 1` it is a program over coins
and the hash oracle, run up to its first chain operation, returning the input of that update and
the attacker it continues as. -/
abbrev SafeAdversary (K M : Type) : ℕ → Type
  | 0 => ChainAdversary K M
  | t + 1 => OracleComp (unifSpec + hashSpec K M) (M × SafeAdversary K M t)

namespace SafeAdversary

/-- The chain attacker it describes: before each of the first `t` updates, run the prefix, then
update with the input it names. -/
@[expose] def toChain : (t : ℕ) → SafeAdversary K M t → ChainAdversary K M
  | 0, A => A
  | t + 1, A => (do
      let p ← liftHash (chainSpec K M) (A : OracleComp (unifSpec + hashSpec K M)
        (M × SafeAdversary K M t))
      let _ ← (liftM ((advSpec K M).query (.inr (.inl p.1))) : OracleComp (advSpec K M) Unit)
      toChain t p.2 : OracleComp (advSpec K M) K)

/-- The attacker that skips the first update, so that its initial key plays the key after it. -/
@[expose] def drop : (t : ℕ) → SafeAdversary K M (t + 1) → SafeAdversary K M t
  | 0, A => (do
      let p ← liftHash (chainSpec K M) (A : OracleComp (unifSpec + hashSpec K M)
        (M × SafeAdversary K M 0))
      p.2 : OracleComp (advSpec K M) K)
  | t + 1, A => ((A : OracleComp (unifSpec + hashSpec K M) (M × SafeAdversary K M (t + 1))) >>=
      fun p => p.2 : OracleComp (unifSpec + hashSpec K M) (M × SafeAdversary K M t))

end SafeAdversary

/-- From the key `ck`: run a `t`-safe attacker through its first `t` updates and then against the
chain; return the key after those updates and the attacker's guess. -/
@[expose] def keyRun : (t : ℕ) → SafeAdversary K M t → K →
    OracleComp (unifSpec + hashSpec K M) (K × K)
  | 0, A, ck => (fun z => (ck, z)) <$> (simulateQ chainImpl (A : ChainAdversary K M)).run' ck
  | t + 1, A, ck => stepRun A (keyRun t) ck

/-- `keyRun` runs the chain attacker `toChain t A`, recording the key after its first `t`
updates. -/
theorem snd_map_keyRun : (t : ℕ) → (A : SafeAdversary K M t) → (ck : K) →
    Prod.snd <$> keyRun t A ck = (simulateQ chainImpl (SafeAdversary.toChain t A)).run' ck
  | 0, A, ck => by simp [keyRun, SafeAdversary.toChain]
  | t + 1, A, ck => by
    simp [keyRun, stepRun, SafeAdversary.toChain, StateT.run'_eq, run_simulateQ_chainImpl_liftHash,
      chainImpl, snd_map_keyRun t]

/-- Skipping the first update runs the prefix and then the rest from the initial key. -/
theorem keyRun_drop : (t : ℕ) → (A : SafeAdversary K M (t + 1)) → (ck : K) →
    keyRun t (SafeAdversary.drop t A) ck =
      (A : OracleComp (unifSpec + hashSpec K M) (M × SafeAdversary K M t)) >>= fun p =>
        keyRun t p.2 ck
  | 0, A, ck => by
    simp [keyRun, SafeAdversary.drop, StateT.run'_eq, run_simulateQ_chainImpl_liftHash]
  | t + 1, A, ck => by
    simp [keyRun, SafeAdversary.drop, stepRun]

/-- Each query of a chain attacker other than a coin makes exactly one hash query of the chain, so
a budget on the hash queries of the chain run is a budget on the attacker's queries. -/
theorem isQueryBoundP_of_run'_simulateQ_chainImpl {A : ChainAdversary K M} {ck : K} {q : ℕ}
    (h : IsQueryBoundP ((simulateQ chainImpl A).run' ck) (fun t => t.isRight = true) q) :
    IsQueryBoundP A (fun t => isCoin t = false) q := by
  induction A using OracleComp.inductionOn generalizing ck q with
  | pure x => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff]
    rcases t with (n | t) | x | u <;>
      simp only [add_apply_inl, add_apply_inr, simulateQ_bind, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, chainImpl, id_map, StateT.run'_eq,
        StateT.run_bind, StateT.run_lift, StateT.run_mk, bind_pure_comp, bind_map_left, map_bind,
        isQueryBoundP_query_bind_iff, Sum.isRight_inl, Sum.isRight_inr, Bool.false_eq_true,
        Bool.true_eq_false, not_false_eq_true, not_true_eq_false, true_or, false_or, true_and,
        ↓reduceIte, isQueryBoundP_map_iff, isCoin] at h ⊢
    · exact fun u => ih u (by simpa [StateT.run'_eq] using h u)
    · exact ⟨h.1, fun u => ih u (by simpa [StateT.run'_eq] using h.2 u)⟩
    · exact ⟨h.1, fun u => ih u (by simpa [StateT.run'_eq] using h.2 ck)⟩
    · exact ⟨h.1, fun u => ih u (by simpa [StateT.run'_eq] using h.2 u)⟩

variable [SampleableType K] [DecidableEq K] [DecidableEq M]

/-! ## The ideal game of one update -/

/-- The ideal game runs a public program as the random oracle does, on its public cache. -/
theorem run_simulateQ_idealImpl_liftHash {α : Type} (oa : OracleComp (unifSpec + hashSpec K M) α)
    (C : (hashSpec K M).QueryCache) (D : (M →ₒ K).QueryCache) :
    (simulateQ (SecretEncoding.idealImpl (hashSpec K M) M K) (liftHash (M →ₒ K) oa)).run (C, D) =
      (fun z => (z.1, (z.2, D))) <$> (simulateQ (hashSpec K M).romImpl oa).run C := by
  rw [simulateQ_liftHash]
  induction oa using OracleComp.inductionOn generalizing C with
  | pure x => simp
  | query_bind t k ih =>
    have hstep : (SecretEncoding.idealImpl (hashSpec K M) M K (.inl t)).run (C, D) =
        (fun z => (z.1, (z.2, D))) <$> ((hashSpec K M).romImpl t).run C := by
      rcases t with n | t
      · simp [SecretEncoding.idealImpl, unifFwdImpl, bind_pure_comp]
      · rfl
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, hstep, bind_map_left,
      map_bind]
    exact bind_congr fun z => ih z.1 z.2

/-- The ideal game draws the updated key uniformly, after the prefix has run. -/
theorem map_run_simulateQ_idealImpl_stepRunD {β : Type}
    (P : OracleComp (unifSpec + hashSpec K M) (M × β))
    (rest : β → K → OracleComp (unifSpec + hashSpec K M) (K × K)) :
    Prod.fst <$> (simulateQ (SecretEncoding.idealImpl (hashSpec K M) M K) (stepRunD P rest)).run
        (∅, ∅) =
      (do
        let pc ← (simulateQ (hashSpec K M).romImpl P).run ∅
        let u ← $ᵗ K
        (simulateQ (hashSpec K M).romImpl (rest pc.1.2 u)).run' pc.2) := by
  simp only [stepRunD, simulateQ_bind, StateT.run_bind, run_simulateQ_idealImpl_liftHash,
    simulateQ_spec_query, bind_map_left, map_bind]
  refine bind_congr fun pc => ?_
  rw [SecretEncoding.idealImpl_run_derive_none (by rfl)]
  simp [run_simulateQ_idealImpl_liftHash, StateT.run'_eq]

/-- **One safe update.** Updating a uniformly drawn key once, with an input chosen by a prefix
that uses only coins and the hash oracle, makes the new key as good as a fresh uniform key, up to
`n / |K|`, where `n` bounds the public queries of the derivation-world run. -/
theorem prEvent_stepRun_le [Fintype K] {β : Type}
    (P : OracleComp (unifSpec + hashSpec K M) (M × β))
    (rest : β → K → OracleComp (unifSpec + hashSpec K M) (K × K)) {n : ℕ}
    (h : IsQueryBoundP (stepRunD P rest) (fun t => isPublic t = true) n) :
    Pr{let s ← $ᵗ K; let z ← (simulateQ (hashSpec K M).romImpl (stepRun P rest s)).run' ∅}[
        z.2 = z.1] ≤
      Pr{let s ← $ᵗ K; let z ← (simulateQ (hashSpec K M).romImpl
          (P >>= fun p => rest p.2 s)).run' ∅}[z.2 = z.1] + n * (Fintype.card K : ℝ≥0∞)⁻¹ := by
  have key := chainEncoding.prEvent_realImpl_le_add_mul (ms := $ᵗ K)
    prEvent_mem_range_chainEncoding (p := fun t => isPublic t = true) (fun _ _ => rfl) h
    (fun _ z => z.1.2 = z.1.1)
  dsimp only at key
  have hreal (s : K) : (simulateQ (hashSpec K M).romImpl (stepRun P rest s)).run' ∅ =
      Prod.fst <$> (simulateQ (chainEncoding.realImpl s) (stepRunD P rest)).run ∅ := by
    rw [SecretEncoding.realImpl, QueryImpl.simulateQ_compose, simulateQ_deriveImpl_stepRunD,
      StateT.run'_eq]
  have hl := congrArg (fun c => Pr{let w ← c}[w.2 = w.1])
    (map_run_simulateQ_idealImpl_stepRunD P rest)
  simp only [prEvent_norm] at hl
  refine (le_of_eq ?_).trans (key.trans (add_le_add (le_of_eq ?_) le_rfl))
  · simp only [hreal, prEvent_norm]
  · rw [OracleComp.prEvent_bind_const, hl]
    simp only [simulateQ_bind, StateT.run'_bind', map_bind, prEvent_norm]
    rw [OracleComp.prEvent_bind_bind_swap]

/-! ## Secrecy of the key after `t` updates -/

/-- The secrecy experiment for the key after `t` updates: draw the initial key `s`, run `keyRun`
from it under a lazily sampled random oracle, and return the key after `t` updates with the
attacker's guess. -/
@[expose] noncomputable def keyExp (t : ℕ) (A : SafeAdversary K M t) : ProbComp (K × K) := do
  let s ← $ᵗ K
  (simulateQ (hashSpec K M).romImpl (keyRun t A s)).run' ∅

/-- The attacker's probability of outputting the key after `t` updates. -/
noncomputable def keyAdv (t : ℕ) (A : SafeAdversary K M t) : ℝ≥0∞ :=
  Pr{let z ← keyExp t A}[z.2 = z.1]

/-- The chain attacker's advantage, with the experiment `chainExp` written out. -/
theorem chainAdv_eq_prEvent (A : ChainAdversary K M) :
    chainAdv A = Pr{
      let s ← $ᵗ K
      let z ← (simulateQ (hashSpec K M).romImpl ((simulateQ chainImpl A).run' s)).run' ∅}[
        z = s] := by
  have h (s : K) := run_realImpl_chainGame s A
  rw [chainAdv_eq]
  simp only [StateT.run'_eq, simulateQ_map, StateT.run_map, ← h, prEvent_norm, Prod.map_fst,
    id_eq]

/-- At `t = 0` this is the forward-secrecy experiment of the initial key. -/
theorem keyAdv_zero (A : SafeAdversary K M 0) : keyAdv 0 A = chainAdv A := by
  rw [chainAdv_eq_prEvent]
  simp [keyAdv, keyExp, keyRun, simulateQ_map, StateT.run'_eq, StateT.run_map, prEvent_norm]

/-- **Forward secrecy of the key after `t` updates.** An attacker whose first `t` chain
operations are updates, and whose run makes at most `q` hash queries from every initial key (its
own hash queries and one for each chain operation, the `t` safe updates included), outputs the key
after those `t` updates with probability at most `((t + 1) q + 1) / |K|`, however it updates and
corrupts afterwards. -/
theorem keyAdv_le [Fintype K] (t : ℕ) (A : SafeAdversary K M t) {q : ℕ}
    (hA : ∀ ck, IsQueryBoundP (keyRun t A ck) (fun t => t.isRight = true) q) :
    keyAdv t A ≤ ((t + 1) * q + 1) * (Fintype.card K : ℝ≥0∞)⁻¹ := by
  rcases isEmpty_or_nonempty K with hK | hK
  · simp [Fintype.card_eq_zero]
  obtain ⟨ck₀⟩ := hK
  induction t with
  | zero =>
    rw [keyAdv_zero]
    have h := hA ck₀
    rw [keyRun, isQueryBoundP_map_iff] at h
    exact (chainAdv_le A (isQueryBoundP_of_run'_simulateQ_chainImpl h)).trans (le_of_eq (by simp))
  | succ t ih =>
    have hdrop (ck : K) :
        IsQueryBoundP (keyRun t (SafeAdversary.drop t A) ck) (fun t => t.isRight = true) q := by
      rw [keyRun_drop]
      exact isQueryBoundP_bind_of_stepRun (hA ck)
    have h1 : keyAdv (t + 1) A ≤
        keyAdv t (SafeAdversary.drop t A) + (q : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ := by
      have h := prEvent_stepRun_le A (keyRun t) (isQueryBoundP_stepRunD (hA ck₀))
      refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
      · simp only [keyAdv, keyExp, keyRun, prEvent_norm]
      · congr 1
        simp only [keyAdv, keyExp, keyRun_drop, prEvent_norm]
    calc keyAdv (t + 1) A
        ≤ keyAdv t (SafeAdversary.drop t A) + (q : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ := h1
      _ ≤ ((t + 1) * q + 1) * (Fintype.card K : ℝ≥0∞)⁻¹ +
            (q : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ := add_le_add_left (ih _ hdrop) _
      _ = _ := by push_cast; ring

/-! ## The hypothesis can be met, and the bound is small -/

/-- An attacker that updates with `x` and then corrupts with `u`, guessing the key it leaks, makes
two hash queries from every initial key, so `keyAdv_le` applies to it at `t = 1` with `q = 2`:
the key it learns is the one after `ck₁`, and its guess for `ck₁` succeeds with probability at most
`5 / |K|`. -/
example [Fintype K] (x u : M) :
    keyAdv 1 (pure (x, (liftM ((advSpec K M).query (.inr (.inr u))) :
        OracleComp (advSpec K M) K)) :
        OracleComp (unifSpec + hashSpec K M) (M × ChainAdversary K M)) ≤
      ((1 + 1) * 2 + 1) * (Fintype.card K : ℝ≥0∞)⁻¹ := by
  refine (keyAdv_le 1 _ (q := 2) fun ck => ?_).trans (le_of_eq (by norm_num))
  simp [keyRun, stepRun, chainImpl, StateT.run'_eq]

/-- At a 256-bit key, `2^20` safe updates and `2^64` hash queries, the bound is below one. -/
example : (((2 ^ 20 : ℕ) + 1) * (2 ^ 64 : ℕ) + 1 : ℝ≥0∞) *
    (Fintype.card (Fin (2 ^ 256)) : ℝ≥0∞)⁻¹ < 1 := by
  rw [Fintype.card_fin, ← div_eq_mul_inv]
  refine ENNReal.div_lt_of_lt_mul ?_
  rw [one_mul]
  exact_mod_cast (by norm_num : (2 ^ 20 + 1) * 2 ^ 64 + 1 < 2 ^ 256)

end SquirrelModel.Chain
