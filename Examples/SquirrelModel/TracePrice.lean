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

Squirrel (Hérouard, Jacomme, Koutsos and Lallemand, CCS 2026) proves a property for every
trace and every attacker against that trace: its attackers choose their messages adaptively, but
the sequence of actions is fixed in advance. In this model those attackers are the non-adaptive
programs (`IsNonAdaptive`, characterized by `eq_ofSchedule_bind_residual`). This file prices the
step from them to attackers that choose their next action from earlier outputs.

* `guided p σ` follows an adaptive program `p` along a fixed trace `σ`: it copies `p` while `p`'s
  actions agree with `σ`, finishes `σ` blindly at the first disagreement, and returns `p`'s result
  only if `p` followed `σ` exactly. It is non-adaptive with schedule `σ`
  (`isNonAdaptive_guided`), so it is a Squirrel attacker.
* `prEvent_run_eq_sum_guided`: for a program making exactly `n` queries, against any stateful
  handler (in particular `Protocol.handler`), the probability of any event *equals* the sum over
  all traces `σ` of length `n` of the probability that `guided p σ` reproduces it. The traces
  partition the runs of `p`.
* `prEvent_run_le_card_pow_mul`: hence a bound `ε` proved for every fixed trace gives the bound
  `|Act| ^ n * ε` against adaptive attackers. The factor is exponential in the length of the
  trace.

Some loss is unavoidable. In `twoStep`, a toy protocol whose second action must match a bit
revealed by the first, the adaptive program `twoStepAttacker` passes a check with probability one
(`prEvent_twoStep_twoStepAttacker`), while every non-adaptive program, for every schedule, passes
one with probability at most `1 / 2` (`prEvent_twoStep_le_of_isNonAdaptive`). This shows a factor
of `2` at `|Act| = 2` and `n = 2`; it does not show that the factor `|Act| ^ n` is needed in
general.
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
    rw [show (FreeM.pure a : FreeM (iface Act Msg) α) = pure a from rfl]
    simp
  | .liftBind q k => by
    rw [Handler.Stateful.run_liftBind]
    simp [Protocol.handler, StateT.run, Protocol.map_run_handler_false π s (k none)]

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
    rw [show (FreeM.pure x : FreeM (iface Bool Bool) α) = pure x from rfl]
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
        rw [show (FreeM.pure y : FreeM (iface Bool Bool) α) = pure y from rfl]
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
    · cases σ'.head? with
      | none => simp
      | some a =>
        simp only [Option.some.injEq]
        exact (SampleableType.prEvent_uniformSample_eq_singleton' a).le.trans (by simp)

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

end SquirrelModel
