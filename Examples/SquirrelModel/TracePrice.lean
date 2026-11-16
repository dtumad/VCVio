/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Examples.SquirrelModel.NonAdaptive
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# The price of fixed traces

**Translation.** Squirrel's attackers for a trace `σ` are the programs with `IsNonAdaptive σ`; an
attacker that picks its next action from earlier outputs is an arbitrary program over
`iface Act Msg`. A bound proved in Squirrel for every trace is the hypothesis `hε`, quantified over
all traces of length `n` and used at the guided programs `guided p σ`. The protocol is any stateful
handler with a probability semantics, `Protocol.handler` in particular.

Squirrel, as used by Hérouard, Jacomme, Koutsos and Lallemand (CCS 2026), proves a property for
every trace and every attacker against it: the attacker's messages are adaptive, but its sequence
of actions is fixed in advance. Those attackers are the non-adaptive programs (`IsNonAdaptive`,
characterized by `eq_ofSchedule_bind_residual`). This file prices the step from them to attackers
that choose their next action from earlier outputs.

* `guided p σ` follows an adaptive program `p` along a fixed trace `σ`: it copies `p` while `p`'s
  actions agree with `σ`, finishes `σ` blindly at the first disagreement, and returns `p`'s result
  only if `p` followed `σ` exactly. It is non-adaptive with schedule `σ`
  (`isNonAdaptive_guided`), so it is a Squirrel attacker.
* `prEvent_run_eq_sum_guided`: for a program making exactly `n` queries, against any stateful
  handler (in particular `Protocol.handler`), the probability of any event *equals* the sum over
  all traces `σ` of length `n` of the probability that `guided p σ` reproduces it. The traces
  partition the runs of `p`.
* `prEvent_run_le_card_pow_mul`: hence a bound `ε` proved for every fixed trace gives the bound
  `|Act| ^ n * ε` against adaptive attackers. Since `p`'s first action is fixed, only the traces
  that start with it contribute, which sharpens this to `|Act| ^ (n - 1) * ε`
  (`prEvent_run_le_card_pow_pred_mul`). The factor is exponential in the length of the trace.

The sharpened factor is attained. In `ladder`, every action is a check against the bit revealed
by the previous one (the first against a public bit), and the event is that `n + 1` checks pass.
The adaptive program `ladderAttacker (n + 1) false`, which plays each revealed bit, makes `n + 1`
queries and succeeds with probability one (`prEvent_ladder_ladderAttacker`), while every
non-adaptive program, for every schedule, succeeds with probability at most `2⁻¹ ^ n`
(`prEvent_ladder_le_of_isNonAdaptive`). So the adaptive success is exactly `|Bool| ^ n * 2⁻¹ ^ n`,
the bound of `prEvent_run_le_card_pow_pred_mul` (`prEvent_ladder_ladderAttacker_eq_card_pow_mul`),
and one factor `|Bool|` below that of `prEvent_run_le_card_pow_mul`. The family is over
`Act = Bool`; for larger action sets the same construction with fair samples from `Act` should
attain `|Act| ^ (n - 1)`, but it is not formalized here. The smaller example `twoStep`
(`prEvent_twoStep_twoStepAttacker`, `prEvent_twoStep_le_of_isNonAdaptive`) has one informative
check.
-/

public section

namespace SquirrelModel

open PFunctor ENNReal MeasureTheory

variable {Act Msg α : Type}

/-! ## Following an adaptive program along a fixed trace -/

/-- Perform the actions `σ` in order with the default message, ignore the answers and return
`none`. -/
@[expose] def pad [Inhabited Msg] : List Act → FreeM (iface Act Msg) (Option α)
  | [] => pure none
  | a :: σ => FreeM.liftBind (a, default) fun _ => pad σ

/-- Follow the program `p` along the trace `σ` (oldest action first). While `p`'s next action is
`σ`'s next action, send `p`'s message and continue as `p` on the answer. At the first mismatch,
or if `p` stops before `σ` ends, perform the rest of `σ` blindly (`pad`) and return `none`. If `σ`
ends before `p` does, return `none`. If both end together, return `p`'s result. -/
@[expose] def guided [DecidableEq Act] [Inhabited Msg] :
    FreeM (iface Act Msg) α → List Act → FreeM (iface Act Msg) (Option α)
  | .pure a, [] => pure (some a)
  | .pure _, b :: σ => pad (b :: σ)
  | .liftBind _ _, [] => pure none
  | .liftBind q k, b :: σ =>
      if q.1 = b then FreeM.liftBind q fun o => guided (k o) σ else pad (b :: σ)

/-- The blind tail visits exactly its actions. -/
theorem isNonAdaptive_pad [Inhabited Msg] (σ : List Act) :
    IsNonAdaptive σ (pad σ : FreeM (iface Act Msg) (Option α)) := by
  induction σ with
  | nil => intro path; rfl
  | cons a σ ih =>
    rintro ⟨o, tail⟩
    exact congrArg (a :: ·) (ih tail)

section guided

variable [DecidableEq Act] [Inhabited Msg]

/-- If `p`'s first action is the trace's first action, the guided program asks `p`'s query and
continues along the rest of the trace. -/
theorem guided_liftBind_cons_self (q : Act × Msg) (k : Option Msg → FreeM (iface Act Msg) α)
    (σ : List Act) :
    guided (FreeM.liftBind q k) (q.1 :: σ) = FreeM.liftBind q fun o => guided (k o) σ := by
  simp [guided]

/-- If `p`'s first action differs from the trace's, the guided program runs the trace blindly. -/
theorem guided_liftBind_cons_of_ne {q : Act × Msg} {b : Act} (hb : q.1 ≠ b)
    (k : Option Msg → FreeM (iface Act Msg) α) (σ : List Act) :
    guided (FreeM.liftBind q k) (b :: σ) = pad (b :: σ) := by
  simp [guided, hb]

/-- **Guided programs are Squirrel attackers.** Whatever `p` does, `guided p σ` visits exactly the
actions `σ`, so by `eq_ofSchedule_bind_residual` it is the fixed-trace attacker
`ofSchedule (attOf (guided p σ)) σ []` followed by a query-free continuation. -/
theorem isNonAdaptive_guided (p : FreeM (iface Act Msg) α) (σ : List Act) :
    IsNonAdaptive σ (guided p σ) := by
  induction σ generalizing p with
  | nil => cases p <;> exact fun _ => rfl
  | cons b σ ih =>
    cases p with
    | pure a => exact isNonAdaptive_pad _
    | liftBind q k =>
      by_cases hq : q.1 = b
      · subst hq
        rw [guided_liftBind_cons_self]
        rintro ⟨o, tail⟩
        exact congrArg (q.1 :: ·) (ih (k o) tail)
      · rw [guided_liftBind_cons_of_ne hq]
        exact isNonAdaptive_pad _

end guided

/-! ## Adaptive success splits over traces -/

section split

variable {m : Type → Type} [Monad m] [LawfulMonad m] {T : Type}

/-- The blind tail returns `none` and leaves the handler's state as the handler sets it. -/
theorem map_run_pad [Inhabited Msg] (h : Handler.Stateful m T (iface Act Msg)) (σ : List Act)
    (s : T) :
    (fun z : Option α × T => ((none : Option α), z.2)) <$> h.run (pad σ) s =
      h.run (pad σ) s := by
  induction σ generalizing s with
  | nil => simp [pad]
  | cons b σ ih => simp only [pad, Handler.Stateful.run_liftBind, map_bind, ih]

variable [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- No event that needs a result happens after the blind tail. -/
theorem prEvent_run_pad_eq_zero [Inhabited Msg] (h : Handler.Stateful m T (iface Act Msg))
    (σ : List Act) (s : T) (P : Option α × T → Prop) (hP : ∀ t, ¬P (none, t)) :
    Pr{let z ← h.run (pad σ : FreeM (iface Act Msg) (Option α)) s}[P z] = 0 := by
  rw [← map_run_pad, prEvent_map]
  exact prEvent_eq_zero_of_forall_not _ _ fun z => hP z.2

/-- **Adaptive success splits over traces.** Run against any stateful handler, a program all of
whose paths make exactly `n` queries produces an event `E` with the probability that some guided
program `guided p σ`, for a trace `σ` of length `n`, returns a result that produces `E`. The
traces partition the runs: a run of `guided p σ` returns a result only if `p` took the actions
`σ`. -/
theorem prEvent_run_eq_sum_guided [Fintype Act] [DecidableEq Act] [Inhabited Msg]
    (h : Handler.Stateful m T (iface Act Msg)) (n : ℕ) (p : FreeM (iface Act Msg) α)
    (hp : ∀ path : FreeM.Path p, FreeM.Path.length p path = n) (s₀ : T)
    (E : α × T → Prop) :
    Pr{let z ← h.run p s₀}[E z] =
      ∑ σ : Fin n → Act,
        Pr{let z ← h.run (guided p (List.ofFn σ)) s₀}[∃ a, z.1 = some a ∧ E (a, z.2)] := by
  induction n generalizing p s₀ with
  | zero =>
    cases p with
    | pure a =>
      rw [Fintype.sum_unique, List.ofFn_zero]
      change Pr{let z ← h.run (pure a) s₀}[E z] =
        Pr{let z ← h.run (pure (some a)) s₀}[∃ a, z.1 = some a ∧ E (a, z.2)]
      simp
    | liftBind q k =>
      exact absurd (hp ⟨none, FreeM.Path.ofHandler (fun _ => none) (k none)⟩)
        (Nat.succ_ne_zero _)
  | succ n ih =>
    cases p with
    | pure a => exact absurd (hp ⟨⟩) (Nat.succ_ne_zero n).symm
    | liftBind q k =>
      have hk (o : Option Msg) (path : FreeM.Path (k o)) : FreeM.Path.length (k o) path = n :=
        Nat.succ_injective (hp ⟨o, path⟩)
      rw [← (Fin.consEquiv fun _ => Act).sum_comp, Fintype.sum_prod_type,
        Finset.sum_eq_single q.1]
      · simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
          guided_liftBind_cons_self, Handler.Stateful.run_liftBind]
        let : MeasurableSpace (Option Msg × T) := ⊤
        simp only [prEvent_bind_eq_lintegral_of_discrete]
        rw [← lintegral_finsetSum _ fun _ _ => Measurable.of_discrete]
        exact lintegral_congr fun r => ih (k r.1) (hk r.1) r.2
      · intro b _ hb
        refine Finset.sum_eq_zero fun σ _ => ?_
        simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
        rw [guided_liftBind_cons_of_ne (Ne.symm hb)]
        exact prEvent_run_pad_eq_zero h _ s₀ _ fun t => by simp
      · exact fun hq => absurd (Finset.mem_univ _) hq

/-- **The price of fixed traces.** If every guided program of a trace of length `n`, each of them
a Squirrel attacker by `isNonAdaptive_guided`, produces the event with probability at most `ε`,
then the adaptive program produces it with probability at most `|Act| ^ n * ε`. The hypothesis
names the attackers it is used at: the guided programs of `p`. -/
theorem prEvent_run_le_card_pow_mul [Fintype Act] [DecidableEq Act] [Inhabited Msg]
    (h : Handler.Stateful m T (iface Act Msg)) (n : ℕ) (p : FreeM (iface Act Msg) α)
    (hp : ∀ path : FreeM.Path p, FreeM.Path.length p path = n) (s₀ : T)
    (E : α × T → Prop) (ε : ℝ≥0∞)
    (hε : ∀ σ : List Act, σ.length = n →
      Pr{let z ← h.run (guided p σ) s₀}[∃ a, z.1 = some a ∧ E (a, z.2)] ≤ ε) :
    Pr{let z ← h.run p s₀}[E z] ≤ (Fintype.card Act : ℝ≥0∞) ^ n * ε := by
  rw [prEvent_run_eq_sum_guided h n p hp s₀ E]
  calc _ ≤ ∑ _σ : Fin n → Act, ε := Finset.sum_le_sum fun σ _ => hε _ (List.length_ofFn)
    _ = _ := by simp [Finset.card_univ, nsmul_eq_mul]

/-- A guided program whose trace disagrees with `p`'s first action never returns a result. -/
theorem prEvent_run_guided_liftBind_cons_of_ne [DecidableEq Act] [Inhabited Msg]
    (h : Handler.Stateful m T (iface Act Msg)) {q : Act × Msg} {b : Act} (hb : q.1 ≠ b)
    (k : Option Msg → FreeM (iface Act Msg) α) (σ : List Act) (s : T) (E : α × T → Prop) :
    Pr{let z ← h.run (guided (FreeM.liftBind q k) (b :: σ)) s}[
      ∃ a, z.1 = some a ∧ E (a, z.2)] = 0 := by
  rw [guided_liftBind_cons_of_ne hb]
  exact prEvent_run_pad_eq_zero h _ s _ fun t => by simp

/-- **The price of fixed traces, sharpened.** The first action of `p` is fixed, so only the
`|Act| ^ (n - 1)` traces that start with it contribute: under the hypotheses of
`prEvent_run_le_card_pow_mul`, the adaptive program produces the event with probability at most
`|Act| ^ (n - 1) * ε`. The ladder (`prEvent_ladder_ladderAttacker_eq_card_pow_mul`) attains this
bound for every `n ≥ 1`. -/
theorem prEvent_run_le_card_pow_pred_mul [Fintype Act] [DecidableEq Act] [Inhabited Msg]
    (h : Handler.Stateful m T (iface Act Msg)) (n : ℕ) (p : FreeM (iface Act Msg) α)
    (hp : ∀ path : FreeM.Path p, FreeM.Path.length p path = n) (s₀ : T)
    (E : α × T → Prop) (ε : ℝ≥0∞)
    (hε : ∀ σ : List Act, σ.length = n →
      Pr{let z ← h.run (guided p σ) s₀}[∃ a, z.1 = some a ∧ E (a, z.2)] ≤ ε) :
    Pr{let z ← h.run p s₀}[E z] ≤ (Fintype.card Act : ℝ≥0∞) ^ (n - 1) * ε := by
  cases n with
  | zero => simpa using prEvent_run_le_card_pow_mul h 0 p hp s₀ E ε hε
  | succ n =>
    cases p with
    | pure a => exact absurd (hp ⟨⟩) (Nat.succ_ne_zero n).symm
    | liftBind q k =>
      rw [prEvent_run_eq_sum_guided h (n + 1) _ hp s₀ E, ← (Fin.consEquiv fun _ => Act).sum_comp,
        Fintype.sum_prod_type, Finset.sum_eq_single q.1]
      · calc _ ≤ ∑ _σ : Fin n → Act, ε := Finset.sum_le_sum fun σ _ => hε _ List.length_ofFn
          _ = _ := by simp [Finset.card_univ, nsmul_eq_mul]
      · intro b _ hb
        refine Finset.sum_eq_zero fun σ _ => ?_
        simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
        exact prEvent_run_guided_liftBind_cons_of_ne h (Ne.symm hb) k _ s₀ E
      · exact fun hq => absurd (Finset.mem_univ _) hq

end split

/-! ## The loss is real -/

/-- Once a condition has failed, the protocol takes no further steps: whatever the program does,
the cells stay as they were and the `exec` flag stays down. -/
theorem Protocol.map_run_handler_false {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (π : Protocol m Act Msg S) (s : S) :
    (q : FreeM (iface Act Msg) α) →
      (fun z : α × (S × Bool) => (z.1, (s, false))) <$> π.handler.run q (s, false) =
        π.handler.run q (s, false)
  | .pure a => by
    rw [FreeM.pure_eq_pure]
    simp
  | .liftBind q k => by
    rw [Handler.Stateful.run_liftBind]
    simp [Protocol.handler, StateT.run, Protocol.map_run_handler_false π s (k none)]

/-- A fixed action matches a fair bit with probability at most `1 / 2`. -/
theorem prEvent_uniformSample_head?_eq_some_le (σ : List Bool) :
    Pr{let b ← $ᵗ Bool}[σ.head? = some b] ≤ 2⁻¹ := by
  cases σ.head? with
  | none => simp
  | some a =>
    simp only [Option.some.injEq]
    exact (SampleableType.prEvent_uniformSample_eq_singleton' a).le.trans (by simp)

/-- A toy protocol with actions and messages `Bool`. Its cells hold the bit revealed so far and
whether a check has passed. The first action, whichever it is, samples a fair bit `b` and outputs
it. Every later action `a` is a check: its condition is `a = b`, and on success the cells record
that a check passed. -/
def twoStep : Protocol ProbComp Bool Bool (Option Bool × Bool) where
  init := (none, false)
  step
    | _, _, (none, c) => (fun b => (true, b, (some b, c))) <$> ($ᵗ Bool)
    | a, x, (some b, _) => pure (decide (a = b), x, (some b, true))

/-- The adaptive attacker against `twoStep`: any first action, then the revealed bit as its
second action. -/
def twoStepAttacker : FreeM (iface Bool Bool) Unit :=
  FreeM.liftBind (false, false) fun o => FreeM.liftBind (o.getD false, false) fun _ => pure ()

/-- The first action of `twoStep` reveals a fair bit. -/
theorem twoStep_handler_run_init (q : Bool × Bool) :
    (twoStep.handler q).run (twoStep.init, true) =
      (fun b => (some b, ((some b, false), true))) <$> ($ᵗ Bool) := by
  simp [Protocol.handler, twoStep, StateT.run]

/-- A later action of `twoStep` passes its check exactly when it is the revealed bit. -/
theorem twoStep_handler_run_some (q : Bool × Bool) (b : Bool) :
    (twoStep.handler q).run ((some b, false), true) =
      pure (if q.1 = b then (some q.2, ((some b, true), true))
        else (none, ((some b, false), false))) := by
  by_cases h : q.1 = b <;> simp [Protocol.handler, twoStep, StateT.run, h]

/-- The adaptive attacker passes a check of `twoStep` with probability one: the cells' flag
`z.2.1.2` is set at the end of the run. -/
theorem prEvent_twoStep_twoStepAttacker :
    Pr{let z ← twoStep.handler.run twoStepAttacker (twoStep.init, true)}[z.2.1.2 = true] = 1 := by
  have hcheck (b : Bool) : twoStep.handler.run (FreeM.liftBind (b, false) fun _ => pure ())
      ((some b, false), true) = pure ((), ((some b, true), true)) := by
    rw [Handler.Stateful.run_liftBind, twoStep_handler_run_some]
    simp
  rw [twoStepAttacker, Handler.Stateful.run_liftBind, twoStep_handler_run_init, bind_map_left]
  simp only [Option.getD_some, hcheck]
  simp

/-- **Every Squirrel attacker against `twoStep` passes a check with probability at most `1 / 2`.**
For every schedule `σ` and every program `q` that visits exactly the actions `σ`, the second action
is fixed before the bit is revealed, so it matches the bit with probability `1 / 2`, and after a
failed check the protocol is stuck. -/
theorem prEvent_twoStep_le_of_isNonAdaptive (σ : List Bool) (q : FreeM (iface Bool Bool) α)
    (hq : IsNonAdaptive σ q) :
    Pr{let z ← twoStep.handler.run q (twoStep.init, true)}[z.2.1.2 = true] ≤ 2⁻¹ := by
  match σ, q, hq with
  | _, .pure x, _ =>
    rw [FreeM.pure_eq_pure]
    simp [twoStep]
  | [], .liftBind q₀ k, hq =>
    exact absurd (hq ⟨none, FreeM.Path.ofHandler (fun _ => none) (k none)⟩)
      (List.cons_ne_nil _ _)
  | a₀ :: σ', .liftBind q₀ k, hq =>
    have hk := hq.liftBind_inv.2
    rw [Handler.Stateful.run_liftBind, twoStep_handler_run_init, bind_map_left]
    refine (prEvent_bind_le_prEvent_of_forall_eq_zero _ _ (fun b => σ'.head? = some b) _
      fun b hb => ?_).trans ?_
    · have hkb := hk (some b)
      generalize k (some b) = r at hkb
      match σ', r, hkb, hb with
      | _, .pure y, _, _ =>
        rw [FreeM.pure_eq_pure]
        simp
      | [], .liftBind q₁ k₁, hkb, _ =>
        exact absurd (hkb ⟨none, FreeM.Path.ofHandler (fun _ => none) (k₁ none)⟩)
          (List.cons_ne_nil _ _)
      | a₁ :: σ'', .liftBind q₁ k₁, hkb, hb =>
        have ha₁ : q₁.1 ≠ b := by
          rw [hkb.liftBind_inv.1]
          simpa using hb
        rw [Handler.Stateful.run_liftBind, twoStep_handler_run_some, ite_eq_right ha₁, pure_bind,
          ← Protocol.map_run_handler_false, prEvent_map]
        exact prEvent_eq_zero_of_forall_not _ _ fun _ => by simp
    · exact prEvent_uniformSample_head?_eq_some_le σ'

/-- Every run of `twoStepAttacker` makes exactly two queries. -/
theorem length_twoStepAttacker (path : FreeM.Path twoStepAttacker) :
    FreeM.Path.length twoStepAttacker path = 2 := by
  obtain ⟨_, _, ⟨⟩⟩ := path
  rfl

/-- The hypotheses of `prEvent_run_le_card_pow_mul` hold together at `twoStepAttacker`: its
guided programs are Squirrel attackers (`isNonAdaptive_guided`), so
`prEvent_twoStep_le_of_isNonAdaptive` bounds each of them by `1 / 2`, and the trace bound gives
`2 ^ 2 * (1 / 2)` against the attacker's success probability `1`. -/
example : Pr{let z ← twoStep.handler.run twoStepAttacker (twoStep.init, true)}[z.2.1.2 = true] ≤
    (Fintype.card Bool : ℝ≥0∞) ^ 2 * 2⁻¹ :=
  prEvent_run_le_card_pow_mul twoStep.handler 2 twoStepAttacker length_twoStepAttacker _
    (fun z => z.2.1.2 = true) _ fun σ _ =>
      (prEvent_mono _ _ _ fun _ ⟨_, _, hz⟩ => hz).trans
        (prEvent_twoStep_le_of_isNonAdaptive σ _ (isNonAdaptive_guided twoStepAttacker σ))

/-! ## The factor `|Act| ^ (n - 1)` is attained -/

/-- A ladder of checks, with actions and messages `Bool`. The cells hold the bit that the next
action must match, initially the public bit `false`, and the number of checks passed. Every action
`a` is a check against the stored bit: it samples a fresh fair bit and outputs it, and on success
the cells store that bit as the next one to match and count the check. -/
def ladder : Protocol ProbComp Bool Bool (Bool × ℕ) where
  init := (false, 0)
  step a _ s := (fun b => (decide (a = s.1), b, (b, s.2 + 1))) <$> ($ᵗ Bool)

/-- The ladder starts at the public bit `false`, with no checks passed. -/
theorem ladder_init : ladder.init = (false, 0) := by
  simp [ladder]

/-- A passed check of `ladder` reveals a fresh fair bit and counts the check. -/
theorem ladder_handler_run_of_eq {q : Bool × Bool} {b' : Bool} (hq : q.1 = b') (c : ℕ) :
    (ladder.handler q).run ((b', c), true) =
      (fun b => (some b, ((b, c + 1), true))) <$> ($ᵗ Bool) := by
  simp [Protocol.handler, ladder, StateT.run, hq]

/-- A failed check of `ladder` stops the protocol. -/
theorem ladder_handler_run_of_ne {q : Bool × Bool} {b' : Bool} (hq : q.1 ≠ b') (c : ℕ) :
    (ladder.handler q).run ((b', c), true) =
      (fun _ => (none, ((b', c), false))) <$> ($ᵗ Bool) := by
  simp [Protocol.handler, ladder, StateT.run, hq]

/-- The adaptive attacker against `ladder`: `n` actions, the first one `b` and each later one the
bit revealed by its predecessor. -/
def ladderAttacker : ℕ → Bool → FreeM (iface Bool Bool) Unit
  | 0, _ => pure ()
  | n + 1, b => FreeM.liftBind (b, false) fun o => ladderAttacker n (o.getD false)

/-- Every run of `ladderAttacker n b` makes exactly `n` queries. -/
theorem length_ladderAttacker (n : ℕ) (b : Bool) (path : FreeM.Path (ladderAttacker n b)) :
    FreeM.Path.length (ladderAttacker n b) path = n := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    obtain ⟨o, tail⟩ := path
    exact congrArg (· + 1) (ih _ tail)

/-- Started on the bit to match, the adaptive attacker passes all of its `n` checks. -/
theorem prEvent_ladder_ladderAttacker_of_state (n : ℕ) (b : Bool) (c : ℕ) :
    Pr{let z ← ladder.handler.run (ladderAttacker n b) ((b, c), true)}[c + n ≤ z.2.1.2] = 1 := by
  induction n generalizing b c with
  | zero => simp [ladderAttacker]
  | succ n ih =>
    rw [ladderAttacker, Handler.Stateful.run_liftBind, ladder_handler_run_of_eq rfl,
      bind_map_left]
    simp only [Option.getD_some]
    rw [show c + (n + 1) = c + 1 + n by omega]
    exact prEvent_bind_eq_of_forall_eq _
      ((SampleableType.prEvent_uniformSample_eq_one_iff _).2 fun _ => trivial) _ _
      fun b => ih b (c + 1)

/-- A non-adaptive program started on the bit `b'` passes `k + 1` checks with probability at most
`2⁻¹ ^ k`, and never if its first action is not `b'`: the first check is against a known bit, each
later one against a fresh fair bit revealed after the schedule was fixed. -/
theorem prEvent_ladder_le_of_state (σ : List Bool) :
    ∀ (q : FreeM (iface Bool Bool) α) (b' : Bool) (c k : ℕ), IsNonAdaptive σ q →
      Pr{let z ← ladder.handler.run q ((b', c), true)}[c + k + 1 ≤ z.2.1.2] ≤
        if σ.head? = some b' then 2⁻¹ ^ k else 0 := by
  induction σ with
  | nil =>
    intro q b' c k hq
    cases q with
    | pure x =>
      rw [FreeM.pure_eq_pure]
      simp
    | liftBind q₀ k₀ =>
      exact absurd (hq ⟨none, FreeM.Path.ofHandler (fun _ => none) (k₀ none)⟩)
        (List.cons_ne_nil _ _)
  | cons a₀ σ' ih =>
    intro q b' c k hq
    cases q with
    | pure x => exact absurd hq.pure_inv (List.cons_ne_nil _ _)
    | liftBind q₀ k₀ =>
      obtain ⟨hq₀, hk⟩ := hq.liftBind_inv
      simp only [List.head?_cons, Option.some.injEq]
      by_cases hb : a₀ = b'
      · rw [ite_eq_left hb, Handler.Stateful.run_liftBind, ladder_handler_run_of_eq (hq₀.trans hb),
          bind_map_left]
        cases k with
        | zero => simp
        | succ k =>
          rw [show c + (k + 1) + 1 = c + 1 + k + 1 by omega]
          refine (prEvent_bind_le_prEvent_mul_of_forall_le (ε := 2⁻¹ ^ k) _ _
            (fun b => σ'.head? = some b) _
            (fun b hb' => ?_) (fun b hb' => ?_)).trans ?_
          · simpa [hb'] using ih (k₀ (some b)) b (c + 1) k (hk _)
          · exact le_antisymm (by simpa [hb'] using ih (k₀ (some b)) b (c + 1) k (hk _)) bot_le
          · rw [pow_succ']
            exact mul_le_mul_of_nonneg_right (prEvent_uniformSample_head?_eq_some_le σ') zero_le
      · rw [ite_eq_right hb, Handler.Stateful.run_liftBind, ladder_handler_run_of_ne (hq₀ ▸ hb),
          bind_map_left]
        refine prEvent_bind_le_of_forall_le _ _ _ fun _ => ?_
        rw [← Protocol.map_run_handler_false, prEvent_map]
        exact (prEvent_eq_zero_of_forall_not _ _ fun _ => by simp).le

/-- **Every Squirrel attacker against `ladder` passes `n + 1` checks with probability at most
`2⁻¹ ^ n`**, for every schedule `σ` and every program `q` that visits exactly the actions `σ`. -/
theorem prEvent_ladder_le_of_isNonAdaptive (n : ℕ) (σ : List Bool)
    (q : FreeM (iface Bool Bool) α) (hq : IsNonAdaptive σ q) :
    Pr{let z ← ladder.handler.run q (ladder.init, true)}[n + 1 ≤ z.2.1.2] ≤ 2⁻¹ ^ n := by
  have key := prEvent_ladder_le_of_state σ q false 0 n hq
  rw [ladder_init]
  simp only [zero_add] at key
  exact key.trans (by split_ifs <;> simp)

/-- The adaptive attacker makes `n + 1` queries and passes all `n + 1` checks of `ladder`. -/
theorem prEvent_ladder_ladderAttacker (n : ℕ) :
    Pr{let z ← ladder.handler.run (ladderAttacker (n + 1) false) (ladder.init, true)}[
      n + 1 ≤ z.2.1.2] = 1 := by
  rw [ladder_init]
  simpa only [zero_add] using prEvent_ladder_ladderAttacker_of_state (n + 1) false 0

/-- **The sharpened trace bound is attained.** The adaptive attacker makes `n + 1` queries and
every Squirrel attacker succeeds with probability at most `ε = 2⁻¹ ^ n`, so
`prEvent_run_le_card_pow_pred_mul` bounds its success by `|Bool| ^ n * ε`; it succeeds with
exactly that probability. `prEvent_run_le_card_pow_mul` gives `|Bool| ^ (n + 1) * ε`, one factor
`|Bool|` above. -/
theorem prEvent_ladder_ladderAttacker_eq_card_pow_mul (n : ℕ) :
    Pr{let z ← ladder.handler.run (ladderAttacker (n + 1) false) (ladder.init, true)}[
      n + 1 ≤ z.2.1.2] = (Fintype.card Bool : ℝ≥0∞) ^ n * 2⁻¹ ^ n := by
  rw [prEvent_ladder_ladderAttacker, ← mul_pow]
  simp [ENNReal.mul_inv_cancel]

/-- The hypotheses of `prEvent_run_le_card_pow_pred_mul` hold together at `ladderAttacker`, and
its bound is the attacker's exact success probability
(`prEvent_ladder_ladderAttacker_eq_card_pow_mul`). -/
example (n : ℕ) :
    Pr{let z ← ladder.handler.run (ladderAttacker (n + 1) false) (ladder.init, true)}[
      n + 1 ≤ z.2.1.2] ≤ (Fintype.card Bool : ℝ≥0∞) ^ (n + 1 - 1) * 2⁻¹ ^ n :=
  prEvent_run_le_card_pow_pred_mul ladder.handler (n + 1) (ladderAttacker (n + 1) false)
    (length_ladderAttacker _ _) _ (fun z => n + 1 ≤ z.2.1.2) _ fun σ _ =>
      (prEvent_mono _ _ _ fun _ ⟨_, _, hz⟩ => hz).trans
        (prEvent_ladder_le_of_isNonAdaptive n σ _ (isNonAdaptive_guided _ σ))

end SquirrelModel
