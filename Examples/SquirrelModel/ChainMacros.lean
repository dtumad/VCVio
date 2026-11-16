/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Examples.SquirrelModel.SquirrelStatement

/-!
# Squirrel's execution of the hash chain is the chain game

**Translation.** The hash chain of Hérouard, Jacomme, Koutsos and Lallemand (CCS 2026), §2, is
`chainProtocolO`, a `Protocol` in `Execution.lean`'s format whose steps query the hash oracle. Its
cell is the key `ck`: an update `A i` replaces it by `h(⟨ck, x⟩)` and outputs a constant, `Corrupt`
does the same and outputs the new key, and `ROM j` hashes the attacker's message. Squirrel's macros
`frame@τ`, `exec@τ` and `ck@τ` along a trace are `macros (chainProtocolO n s) att τ`, a program
over coins and the hash oracle, and the hash is a random oracle when that program is answered by
`romImpl` from the empty cache. `ck@init` is the initial key `s`.

`Execution.lean` gives Squirrel's macros a handler semantics, and `ChainSecrecy.lean` proves
forward secrecy for a chain game `chainImpl` written directly as oracles. This file proves that the
two describe the same execution:

* `run_handler_chainProtocolO`: running Squirrel's fixed-trace attacker `ofSchedule att σ` against
  the protocol's handler is running it, through `toChain`, against `chainImpl`. The frames agree,
  the protocol's cell is the chain's key, and `exec` stays true;
* `macros_chainProtocolO` and `frame_map_macros_chainProtocolO`: with `run_ofSchedule`, Squirrel's
  macro equations compute the chain game's run;
* `squirrel_forward_secrecy_macros`: `frame@t' ⊬ ck@init` for the frame computed by the macro
  equations themselves, `Pr[f(frame) = s] ≤ (|σ| + 1) / |K|`, from `squirrel_forward_secrecy`.

Messages are pairs in `K × M`, as in `SquirrelStatement.lean`: updates and corruptions read the
second component, random-oracle queries hash the pair, and outputs carry a default second
component.
-/

public section

open OracleComp OracleSpec ENNReal PFunctor

namespace SquirrelModel.Chain

variable {K M : Type}

/-- A query to the hash oracle, as a program over coins and the hash oracle. -/
@[expose] def hashQuery (t : K × M) : OracleComp (unifSpec + hashSpec K M) K :=
  liftM ((unifSpec + hashSpec K M).query (.inr t))

/-- While `exec` holds, the handler runs one step of the protocol. -/
theorem run_handler_true {m : Type → Type} [Monad m] [LawfulMonad m] {Act Msg S : Type}
    (π : Protocol m Act Msg S) (q : Act × Msg) (c : S) :
    (π.handler q).run (c, true) =
      (fun r => if r.1 then (some r.2.1, (r.2.2, true)) else (none, (c, false))) <$>
        π.step q.1 q.2 c := by
  simp [Protocol.handler, StateT.run, map_eq_bind_pure_comp]

/-- The chain attacker's advantage, with the experiment `chainExp` written out. -/
private theorem chainAdv_eq_prEvent [SampleableType K] [DecidableEq K] [DecidableEq M]
    (A : ChainAdversary K M) :
    chainAdv A = Pr{
      let s ← $ᵗ K
      let z ← (simulateQ (hashSpec K M).romImpl ((simulateQ chainImpl A).run' s)).run' ∅}[
        z = s] := by
  have h (s : K) := run_realImpl_chainGame s A
  rw [chainAdv_eq]
  simp only [StateT.run'_eq, simulateQ_map, StateT.run_map, ← h, prEvent_norm, Prod.map_fst,
    id_eq]

/-! ## The chain as a protocol that queries the hash oracle -/

variable [Inhabited K] [Inhabited M]

/-- The paper's chain as a `Protocol` whose steps query the hash oracle, from the initial key `s`.
The cell is the current key `ck`. An update hashes `ck` with the message's second component and
outputs a constant; a corruption does the same and outputs the new key; a random-oracle query
hashes the message. Every condition holds. -/
@[expose] def chainProtocolO (n : ℕ) (s : K) :
    Protocol (OracleComp (unifSpec + hashSpec K M)) (ChainAct n) (K × M) K where
  init := s
  step
    | .upd _, (_, x), ck => (fun k => (true, (default, default), k)) <$> hashQuery (ck, x)
    | .corrupt, (_, u), ck => (fun k => (true, (k, default), k)) <$> hashQuery (ck, u)
    | .rom _, (k, x), ck => (fun h => (true, (h, default), ck)) <$> hashQuery (k, x)

/-- An update hashes the key with the message's second component. -/
theorem chainProtocolO_step_upd {n : ℕ} (s : K) (i : Fin n) (k ck : K) (x : M) :
    (chainProtocolO n s).step (.upd i) (k, x) ck =
      (fun k' => (true, (default, default), k')) <$> hashQuery (ck, x) := rfl

/-- A corruption hashes the key with the message's second component and outputs the result. -/
theorem chainProtocolO_step_corrupt {n : ℕ} (s : K) (k ck : K) (u : M) :
    (chainProtocolO (M := M) n s).step .corrupt (k, u) ck =
      (fun k' => (true, (k', default), k')) <$> hashQuery (ck, u) := rfl

/-- A random-oracle query hashes the message and leaves the key unchanged. -/
theorem chainProtocolO_step_rom {n : ℕ} (s : K) (j : Fin n) (k ck : K) (x : M) :
    (chainProtocolO n s).step (.rom j) (k, x) ck =
      (fun h => (true, (h, default), ck)) <$> hashQuery (k, x) := rfl

/-! ## Squirrel's execution of the chain is the chain game -/

/-- Running Squirrel's fixed-trace attacker against the protocol's handler is running it against
the chain game: the frames agree, the handler's cell is the chain's key, and `exec` stays true. -/
theorem run_handler_chainProtocolO {n : ℕ} (s : K) (att : Frame (K × M) → K × M)
    (σ : List (ChainAct n)) (fr : Frame (K × M)) (ck : K) :
    (chainProtocolO n s).handler.run (ofSchedule att σ fr) (ck, true) =
      (fun z => (z.1, (z.2, true))) <$>
        (simulateQ chainImpl ((ofSchedule att σ fr).liftM (toChain n))).run ck := by
  induction σ generalizing fr ck with
  | nil => simp [ofSchedule]
  | cons a σ ih =>
    rw [ofSchedule, Handler.Stateful.run_liftBind, FreeM.liftM, run_handler_true]
    simp only [simulateQ_bind, StateT.run_bind, map_bind]
    generalize att fr = p
    rcases p with ⟨k, x⟩
    rcases a with i | _ | j
    · rw [chainProtocolO_step_upd]
      simp only [hashQuery, toChain, chainImpl, Functor.map_map, bind_map_left, simulateQ_map,
        simulateQ_spec_query, StateT.run_map, StateT.run_mk, ↓reduceIte]
      exact bind_congr fun k' => ih _ _
    · rw [chainProtocolO_step_corrupt]
      simp only [hashQuery, toChain, chainImpl, Functor.map_map, bind_map_left, simulateQ_map,
        simulateQ_spec_query, StateT.run_map, StateT.run_mk, ↓reduceIte]
      exact bind_congr fun k' => ih _ _
    · rw [chainProtocolO_step_rom]
      simp only [hashQuery, toChain, chainImpl, Functor.map_map, bind_map_left, simulateQ_map,
        simulateQ_spec_query, StateT.run_map, StateT.run_lift, ↓reduceIte]
      exact bind_congr fun k' => ih _ _

/-- Squirrel's macros for the chain, from the initial key `s`, are the chain game's run of the
fixed-trace attacker. -/
theorem macros_chainProtocolO {n : ℕ} (s : K) (att : Frame (K × M) → K × M)
    (σ : List (ChainAct n)) :
    Macros.toRun <$> macros (chainProtocolO n s) att σ.reverse =
      (fun z => (z.1, (z.2, true))) <$>
        (simulateQ chainImpl ((ofSchedule att σ []).liftM (toChain n))).run s := by
  have h := run_ofSchedule (chainProtocolO n s) att σ.reverse
  rw [List.reverse_reverse] at h
  rw [← h]
  exact run_handler_chainProtocolO s att σ [] s

/-- The frame of Squirrel's macros for the chain is the final frame of the chain game's run. -/
theorem frame_map_macros_chainProtocolO {n : ℕ} (s : K) (att : Frame (K × M) → K × M)
    (σ : List (ChainAct n)) :
    Macros.frame <$> macros (chainProtocolO n s) att σ.reverse =
      (simulateQ chainImpl ((ofSchedule att σ []).liftM (toChain n))).run' s := by
  have h := congrArg (Prod.fst <$> ·) (macros_chainProtocolO s att σ)
  simpa [Functor.map_map, Macros.toRun, StateT.run'_eq] using h

variable [DecidableEq K] [DecidableEq M] [SampleableType K]

/-- **The paper's forward secrecy, for the frame of Squirrel's macros.** Draw the initial key
`s`, compute Squirrel's macros for the chain along the trace `σ` with the hash oracle answered by
a lazily sampled random oracle, and apply any guess `f` to the final frame: the guess is the
initial key with probability at most `(|σ| + 1) / |K|`. -/
theorem squirrel_forward_secrecy_macros [Fintype K] {n : ℕ} (σ : List (ChainAct n))
    (att : Frame (K × M) → K × M) (f : Frame (K × M) → K) :
    Pr{let s ← $ᵗ K; let Mac ← (simulateQ (hashSpec K M).romImpl
        (macros (chainProtocolO n s) att σ.reverse)).run' ∅}[f Mac.frame = s] ≤
      (σ.length + 1) * (Fintype.card K : ℝ≥0∞)⁻¹ := by
  refine le_of_eq_of_le ?_ (squirrel_forward_secrecy σ att f)
  have h (s : K) : (fun Mac => f Mac.frame = s) <$>
      (simulateQ (hashSpec K M).romImpl (macros (chainProtocolO n s) att σ.reverse)).run' ∅ =
      (fun z => z = s) <$> (simulateQ (hashSpec K M).romImpl
        ((simulateQ chainImpl (scheduleAdversary σ att f)).run' s)).run' ∅ := by
    rw [scheduleAdversary, simulateQ_map, StateT.run'_map', ← frame_map_macros_chainProtocolO,
      simulateQ_map, StateT.run'_map', simulateQ_map, StateT.run'_map']
    simp only [Functor.map_map]
  rw [chainAdv_eq_prEvent]
  exact congrArg prEvent (bind_congr fun s => h s)

end SquirrelModel.Chain
