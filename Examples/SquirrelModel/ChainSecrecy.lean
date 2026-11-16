/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Forward secrecy of the hash chain, against an adaptive attacker

**Translation.** In the motivating example of Hérouard, Jacomme, Koutsos and Lallemand
(CCS 2026), §2, the keyed hash `h(·, k)` becomes a lazily sampled random oracle `H : K × M → K`
(`hashSpec`). The actions `A i`, `Corrupt` and `ROM j` become the oracles `upd`, `corrupt` and the
hash oracle of `advSpec`, answered by `chainImpl` with the cell `ck` as state, and Squirrel's shared
random tape becomes the coin oracle. The name `s` is the uniformly sampled initial key. The
attacker is one free program `A : ChainAdversary K M` over these oracles, and `frame@t' ⊬ ck@init`
becomes the bound on `chainAdv A`, its probability of outputting `s`.

The example is a one-sided ratchet: a key `ck` starts at a secret `s`, each update replaces it
with `H(ck, x)` for an attacker-chosen `x`, and a corruption leaks the key after an update. The
paper proves forward secrecy in Squirrel, `[happens(t, t')] → [safe t] → frame@t' ⊬ ck@t`, for a
trace fixed in advance and a single corruption.

Here the attacker is a program over four oracles: uniform coins, the hash oracle, `upd x` and
`corrupt u` (`advSpec`). It may interleave them in any order, choose when to corrupt from what it
has seen, and corrupt more than once. `chainAdv A` is its probability of outputting the initial
key `s`. The theorem `chainAdv_le` bounds it by `(q + 1) / |K|` for an attacker making at most `q`
queries other than coins. That is the paper's statement at `t = init` (the initial key is always
safe), for every `t'`, made adaptive and concrete, in the random-oracle model rather than with a
keyed PRF.

## Proof

The update of the secret is a *derivation*: `H(s, x)` read at the encoded point `(s, x)`. After
it, the key is known to the game, and later updates are ordinary hash queries. `chainImplD` runs
the chain in VCVio's derivation world (`OracleSpec.withDerivations`) with state `Option K`:
`none` while the key is still the secret, `some ck` afterwards. `run_realImpl_chainGame`
identifies its real game (`SecretEncoding.realImpl`) with the actual chain run, query by query
(`chainImplD_step`). `SecretEncoding.prEvent_realImpl_le_add_mul` then compares it with the ideal
game, which never reads `s`, at a cost of `q / |K|`. The ideal game's chance of outputting `s`
is `1 / |K|`.

## Later keys

Secrecy of a later safe key `ck@t`, for `t > init`, is `keyAdv_le` in `ChainLaterKeys.lean`: a
hybrid over the updates before `t`, with bound `((t + 1) q + 1) / |K|`.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SquirrelModel.Chain

variable (K M : Type)

/-- The hash oracle `H : K × M → K`. -/
abbrev hashSpec : OracleSpec (K × M) := (K × M →ₒ K)

/-- The chain's interface: `upd x` replaces the key by `H(ck, x)`; `corrupt u` does the same and
returns the new key. -/
abbrev chainSpec : OracleSpec (M ⊕ M) := (M →ₒ Unit) + (M →ₒ K)

/-- The attacker's oracles: uniform coins, the hash oracle, and the chain. -/
abbrev advSpec : OracleSpec ((ℕ ⊕ (K × M)) ⊕ (M ⊕ M)) := (unifSpec + hashSpec K M) + chainSpec K M

/-- An attacker against the chain, outputting its guess of the initial key. -/
abbrev ChainAdversary : Type := OracleComp (advSpec K M) K

/-- The oracles of the derivation world: coins, the hash oracle, and derivations `M →ₒ K`. -/
abbrev derivSpec : OracleSpec ((ℕ ⊕ (K × M)) ⊕ M) := (hashSpec K M).withDerivations M K

variable {K M}

/-- Whether a query is a coin flip. Coins are not charged to the attacker's budget. -/
@[expose] def isCoin : (advSpec K M).Domain → Bool
  | .inl (.inl _) => true
  | _ => false

/-- The chain, with the current key as state. Coins and hash queries pass through; `upd x` and
`corrupt u` hash the current key with the attacker's input. -/
@[expose] def chainImpl :
    QueryImpl (advSpec K M) (StateT K (OracleComp (unifSpec + hashSpec K M))) := fun
  | .inl t => StateT.lift ((unifSpec + hashSpec K M).query t)
  | .inr (.inl x) => StateT.mk fun ck =>
      (fun k => ((), k)) <$> (unifSpec + hashSpec K M).query (.inr (ck, x))
  | .inr (.inr u) => StateT.mk fun ck =>
      (fun k => (k, k)) <$> (unifSpec + hashSpec K M).query (.inr (ck, u))

/-! ## The chain in the derivation world -/

/-- The secret enters the hash oracle at the points `(s, x)`. -/
@[expose] def chainEncoding : SecretEncoding (hashSpec K M) K M K where
  enc s x := (s, x)
  range_eq _ _ := rfl
  injective s := Prod.mk_right_injective s

/-- The chain in the derivation world. The state is `none` while the key is still the secret: an
update is then the derivation of its input. Afterwards the state holds the key, and updates are
public hash queries on it. -/
def chainImplD :
    QueryImpl (advSpec K M) (StateT (Option K) (OracleComp (derivSpec K M))) := fun
  | .inl t => StateT.lift ((derivSpec K M).query (.inl t))
  | .inr (.inl x) => StateT.mk fun
      | none => (fun k => ((), some k)) <$> (derivSpec K M).query (.inr x)
      | some ck => (fun k => ((), some k)) <$> (derivSpec K M).query (.inl (.inr (ck, x)))
  | .inr (.inr u) => StateT.mk fun
      | none => (fun k => (k, some k)) <$> (derivSpec K M).query (.inr u)
      | some ck => (fun k => (k, some k)) <$> (derivSpec K M).query (.inl (.inr (ck, u)))

/-- The chain game in the derivation world. -/
def chainGame (A : ChainAdversary K M) : OracleComp (derivSpec K M) (K × Option K) :=
  (simulateQ chainImplD A).run none

/-- Query by query, answering derivations under the secret `s` turns the derivation-world chain
into the chain started at `s`, reading the state `none` as the key `s`. -/
theorem chainImplD_step (s : K) (t : (advSpec K M).Domain) (st : Option K) :
    Prod.map id (·.getD s) <$>
        ((chainEncoding.deriveImpl s).mapStateTBase chainImplD t).run st =
      (chainImpl t).run (st.getD s) := by
  rcases t with t | x | u <;> cases st <;>
    simp [QueryImpl.mapStateTBase, chainImplD, chainImpl, SecretEncoding.deriveImpl,
      chainEncoding, StateT.run_lift]

/-! ## The bound -/

/-- Whether a derivation-world query is a public hash query. -/
@[expose] def isPublic : (derivSpec K M).Domain → Bool
  | .inl (.inr _) => true
  | _ => false

/-- Each attacker query costs the derivation-world chain at most one public hash query, and a
coin costs none. -/
theorem isQueryBoundP_chainGame (A : ChainAdversary K M) {q : ℕ}
    (hA : IsQueryBoundP A (fun t => isCoin t = false) q) :
    IsQueryBoundP (chainGame A) (fun t => isPublic t = true) q := by
  refine hA.simulateQ_run_StateT_of_step (fun t st => ?_) none
  rcases t with (n | t) | x | u <;> try cases st
  all_goals simp [chainImplD, isCoin, isPublic, StateT.run_lift]

variable [SampleableType K]

/-- A public point `(k, x)` encodes a derivation under a uniform secret with probability
`1 / |K|`. -/
theorem prEvent_mem_range_chainEncoding [Fintype K] (t : K × M) :
    Pr{let s ← $ᵗ K}[t ∈ Set.range (chainEncoding.enc s)] ≤ (Fintype.card K : ℝ≥0∞)⁻¹ := by
  refine le_of_eq ((prEvent_congr _ _ _ fun s => ?_).trans
    (SampleableType.prEvent_uniformSample_eq_singleton' t.1))
  simp only [chainEncoding, Set.mem_range]
  exact ⟨fun ⟨x, hx⟩ => by rw [← hx], fun h => ⟨t.2, by rw [← h]⟩⟩

variable [DecidableEq K] [DecidableEq M]

/-- The forward-secrecy experiment: draw the initial key `s`, run the attacker against the chain
under a lazily sampled random oracle, and return `s` with the attacker's guess. -/
@[expose] noncomputable def chainExp (A : ChainAdversary K M) : ProbComp (K × K) := do
  let s ← $ᵗ K
  let z ← (simulateQ (hashSpec K M).romImpl ((simulateQ chainImpl A).run' s)).run' ∅
  return (s, z)

/-- The attacker's probability of outputting the initial key. -/
noncomputable def chainAdv (A : ChainAdversary K M) : ℝ≥0∞ :=
  Pr{let z ← chainExp A}[z.2 = z.1]

/-- **Identification.** The real game of the derivation-world chain is the chain started at `s`
under the random oracle. -/
theorem run_realImpl_chainGame (s : K) (A : ChainAdversary K M) :
    Prod.map (Prod.map id (·.getD s)) id <$>
        (simulateQ (chainEncoding.realImpl s) (chainGame A)).run ∅ =
      (simulateQ (hashSpec K M).romImpl ((simulateQ chainImpl A).run s)).run ∅ := by
  have h := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    ((chainEncoding.deriveImpl s).mapStateTBase chainImplD) chainImpl (·.getD s)
    (chainImplD_step s) A none
  rw [chainGame, SecretEncoding.realImpl, QueryImpl.simulateQ_compose,
    QueryImpl.simulateQ_mapStateTBase_run]
  rw [Option.getD_none] at h
  rw [← h, simulateQ_map, StateT.run_map]
  rfl

/-- The chain experiment is the real game of the derivation-world chain, read on its output. -/
theorem chainAdv_eq (A : ChainAdversary K M) :
    chainAdv A =
      Pr{let s ← $ᵗ K; let z ← (simulateQ (chainEncoding.realImpl s) (chainGame A)).run ∅}[
        z.1.1 = s] := by
  have h (s : K) := run_realImpl_chainGame s A
  simp only [chainAdv, chainExp, StateT.run'_eq, simulateQ_map, StateT.run_map, ← h,
    prEvent_norm]
  rfl

/-- **Forward secrecy of the initial key.** An attacker making at most `q` queries other than
coins outputs the initial key with probability at most `(q + 1) / |K|`, whatever order it queries
in and however often and whenever it corrupts. -/
theorem chainAdv_le [Fintype K] (A : ChainAdversary K M) {q : ℕ}
    (hA : IsQueryBoundP A (fun t => isCoin t = false) q) :
    chainAdv A ≤ (q + 1) * (Fintype.card K : ℝ≥0∞)⁻¹ := by
  rw [chainAdv_eq]
  refine (chainEncoding.prEvent_realImpl_le_add_mul (ms := $ᵗ K)
    prEvent_mem_range_chainEncoding (p := fun t => isPublic t = true) (fun _ _ => rfl)
    (isQueryBoundP_chainGame A hA) fun s z => z.1.1 = s).trans ?_
  refine le_trans (add_le_add (?_ : _ ≤ (Fintype.card K : ℝ≥0∞)⁻¹) le_rfl) (le_of_eq (by ring))
  rw [prEvent_bind_map_swap]
  have key : Pr{let y ← ((simulateQ (SecretEncoding.idealImpl (hashSpec K M) M K) (chainGame A)).run
      (∅, ∅) >>= fun z => (fun s => (z, s)) <$> ($ᵗ K))}[y.1.1.1 = y.2] ≤
        (Fintype.card K : ℝ≥0∞)⁻¹ :=
    prEvent_bind_le_of_forall_le _ _ _ fun z => by
      rw [prEvent_map]
      exact le_of_eq (SampleableType.prEvent_uniformSample_eq_singleton' z.1.1)
  simpa only [prEvent_norm] using key

/-! ## The bound is attained, its hypothesis can be met, and it is small -/

/-- At `q = 0` the bound is attained: guessing a fixed key succeeds with probability `1 / |K|`. -/
theorem chainAdv_pure [Fintype K] (k : K) :
    chainAdv (pure k : OracleComp (advSpec K M) K) = (Fintype.card K : ℝ≥0∞)⁻¹ := by
  simp only [chainAdv, chainExp, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure,
    prEvent_norm]
  exact SampleableType.prEvent_uniformSample_eq_singleton' k

/-- A probe attacker that updates, corrupts, hashes the leaked key and guesses makes three
charged queries, so `chainAdv_le` applies to it with `q = 3`. -/
example (x u : M) :
    IsQueryBoundP (do
      let _ ← (liftM ((advSpec K M).query (.inr (.inl x))) : OracleComp (advSpec K M) Unit)
      let k ← (liftM ((advSpec K M).query (.inr (.inr u))) : OracleComp (advSpec K M) K)
      (liftM ((advSpec K M).query (.inl (.inr (k, x)))) : OracleComp (advSpec K M) K))
      (fun t => isCoin t = false) 3 := by
  refine isQueryBoundP_bind (n := 1) (m := 2) ?_ fun _ _ => ?_
  · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  refine isQueryBoundP_bind (n := 1) (m := 1) ?_ fun _ _ => ?_
  · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos

/-- At a 256-bit key and `2^64` queries the bound is below one. -/
example : ((2 ^ 64 : ℕ) + 1 : ℝ≥0∞) * (Fintype.card (Fin (2 ^ 256)) : ℝ≥0∞)⁻¹ < 1 := by
  rw [Fintype.card_fin, ← div_eq_mul_inv]
  refine ENNReal.div_lt_of_lt_mul ?_
  rw [one_mul]
  exact_mod_cast (by norm_num : 2 ^ 64 + 1 < 2 ^ 256)

end SquirrelModel.Chain
