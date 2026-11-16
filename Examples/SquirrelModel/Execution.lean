/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Handler.Stateful
public import PolyFun.PFunctor.Free.Path.Execution

/-!
# Squirrel's execution model as a program run against a stateful handler

The Squirrel prover describes a protocol as a set of *actions*. At each action the attacker
supplies an input, the protocol checks a condition, updates its mutable cells and emits an output.
The attacker's input at an action is a function `att` of the *frame*, the sequence of outputs so
far, and a proof fixes the order of actions (the trace) in advance. Squirrel's documentation gives
the execution as macros defined by recursion along the trace:

* `input@τ = att(frame@pred τ)`;
* `exec@τ = exec@(pred τ) && cond@τ`, with `exec@init = true`;
* `frame@τ = ⟨frame@pred τ, exec@τ, if exec@τ then output@τ⟩`, with `frame@init` empty.

This file states that semantics inside PolyFun:

* `iface Act Msg` is the polynomial functor of the attacker's view: a position is an action
  together with the attacker's input, a direction is the action's output, or `none` when the
  action's condition fails;
* `Protocol.handler` is the protocol as a stateful handler for that interface;
* `ofSchedule att σ` is the attacker of a fixed schedule `σ` as a free program;
* `macros` transcribes the macro equations above directly, by recursion on the trace;
* `run_ofSchedule` proves that running the program against the handler computes the macros;
* `IsNonAdaptive σ p` says that every path of `p` visits exactly the actions `σ`; programs built by
  `ofSchedule` have it, and `adaptiveProbe` shows that a program choosing its next action from an
  output does not.

So Squirrel's trace semantics is the handler semantics of free programs restricted to programs
with a fixed action schedule. The attacker's messages stay adaptive, as in Squirrel; only the
sequence of actions is fixed.

## Modelling choices

* Frames are lists in newest-first order, so `frame@pred τ` is the tail of `frame@τ`.
* A frame entry `Option Msg` carries both components of Squirrel's entry: `none` when `exec@τ` is
  false and `some o` when it is true with output `o`. Once the condition fails, the protocol takes
  no further steps and its cells stay unchanged.
* `att` is a pure function of the frame. Squirrel's attacker functions read one shared random
  tape; a probabilistic layer samples that tape once and passes `att ρ`.
* Everything lives in `Type`, the universe of VCVio's `ProbComp`; this spike does not aim at
  universe generality.
-/

public section

namespace SquirrelModel

open PFunctor

variable {Act Msg S : Type}

/-- The attacker's view of a Squirrel system as a polynomial functor: a position is an action
together with the attacker's input to it; a direction is the action's output, or `none` when the
action's condition fails. -/
abbrev iface (Act Msg : Type) : PFunctor.{0, 0} := ⟨Act × Msg, fun _ => Option Msg⟩

/-- A Squirrel frame: one entry per executed action, newest first. `none` records an action
whose condition failed. -/
abbrev Frame (Msg : Type) : Type := List (Option Msg)

/-- A Squirrel system with mutable cells `S`, executed in a monad `m`. At action `a` with input
`x` and cells `s`, `step a x s` returns the action's condition, its output and the updated
cells. -/
structure Protocol (m : Type → Type) (Act Msg S : Type) where
  /-- The initial value of the mutable cells. -/
  init : S
  /-- One action: its condition, output and updated cells. -/
  step : Act → Msg → S → m (Bool × Msg × S)

namespace Protocol

variable {m : Type → Type} [Monad m]

/-- The protocol as a stateful handler for `iface Act Msg`. The state pairs the mutable cells
with Squirrel's `exec` flag. While `exec` holds, a query runs `step`; if the condition fails the
answer is `none`, the flag drops and the cells are kept. Once the flag is down, every query is
answered `none` and nothing changes. -/
@[expose] def handler (π : Protocol m Act Msg S) :
    Handler.Stateful m (S × Bool) (iface Act Msg) :=
  fun q s =>
    if s.2 then do
      let r ← π.step q.1 q.2 s.1
      pure (if r.1 then (some r.2.1, (r.2.2, true)) else (none, (s.1, false)))
    else pure (none, s)

end Protocol

/-- The free program of a Squirrel attacker against a fixed schedule `σ` (oldest action first),
started from the frame `fr`. At each action it sends `att` of the current frame, then extends the
frame with the answer. It returns the final frame. -/
@[expose] def ofSchedule (att : Frame Msg → Msg) :
    List Act → Frame Msg → FreeM (iface Act Msg) (Frame Msg)
  | [], fr => pure fr
  | a :: σ, fr => FreeM.liftBind (a, att fr) fun o => ofSchedule att σ (o :: fr)

/-- The values of Squirrel's macros at a timestamp: the frame, the `exec` flag and the mutable
cells. -/
structure Macros (Msg S : Type) where
  /-- `frame@τ`, newest entry first. -/
  frame : Frame Msg
  /-- `exec@τ`. -/
  exec : Bool
  /-- The mutable cells at `τ`. -/
  cells : S

/-- Squirrel's macros along a trace given newest action first, transcribed from the macro
equations: `input@τ = att(frame@pred τ)`, `exec@τ = exec@(pred τ) && cond@τ` and
`frame@τ = ⟨frame@pred τ, exec@τ, if exec@τ then output@τ⟩`. -/
@[expose] def macros {m : Type → Type} [Monad m] (π : Protocol m Act Msg S)
    (att : Frame Msg → Msg) : List Act → m (Macros Msg S)
  | [] => pure ⟨[], true, π.init⟩
  | a :: τ => do
      let M ← macros π att τ
      if M.exec then do
        let r ← π.step a (att M.frame) M.cells
        pure (if r.1 then ⟨some r.2.1 :: M.frame, true, r.2.2⟩
          else ⟨none :: M.frame, false, M.cells⟩)
      else pure ⟨none :: M.frame, false, M.cells⟩

/-- Read off the handler's final state and the program's result from the macros. -/
@[expose] def Macros.toRun (M : Macros Msg S) : Frame Msg × (S × Bool) :=
  (M.frame, (M.cells, M.exec))

section adequacy

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Adequacy, generalized to a prefix already executed: running the schedule `σ` from the macros
of `ρ` computes the macros of the longer trace. -/
theorem macros_bind_run_ofSchedule (π : Protocol m Act Msg S) (att : Frame Msg → Msg)
    (σ ρ : List Act) :
    (macros π att ρ >>= fun M => π.handler.run (ofSchedule att σ M.frame) (M.cells, M.exec)) =
      Macros.toRun <$> macros π att (σ.reverse ++ ρ) := by
  induction σ generalizing ρ with
  | nil =>
    simp only [ofSchedule, Handler.Stateful.run_pure, List.reverse_nil, List.nil_append,
      map_eq_bind_pure_comp]
    rfl
  | cons a σ ih =>
    rw [List.reverse_cons, List.append_assoc, List.singleton_append, ← ih (a :: ρ)]
    simp only [ofSchedule, Handler.Stateful.run_liftBind, macros, bind_assoc]
    refine bind_congr fun M => ?_
    cases hM : M.exec with
    | false => simp [Protocol.handler, StateT.run]
    | true =>
      simp only [Protocol.handler, ite_true, StateT.run, bind_assoc, pure_bind]
      refine bind_congr fun r => ?_
      cases r.1 <;> simp

/-- **Adequacy.** Running the fixed-schedule attacker program against the protocol's stateful
handler computes Squirrel's macros: the final frame, cells and `exec` flag are the macro values at
the end of the trace. The trace `τ` is given newest action first, the schedule `τ.reverse` oldest
first. -/
theorem run_ofSchedule (π : Protocol m Act Msg S) (att : Frame Msg → Msg) (τ : List Act) :
    π.handler.run (ofSchedule att τ.reverse []) (π.init, true) =
      Macros.toRun <$> macros π att τ := by
  have h := macros_bind_run_ofSchedule π att τ.reverse []
  simpa [macros] using h

end adequacy

/-! ## Non-adaptive programs -/

/-- A program over `iface Act Msg` is *non-adaptive* with schedule `σ` when every path through it
visits exactly the actions `σ`, in order. Only the actions are fixed: the messages it sends may
still depend on earlier outputs. This is the class of attackers Squirrel's fixed traces quantify
over. -/
def IsNonAdaptive {α : Type} (σ : List Act) (p : FreeM (iface Act Msg) α) : Prop :=
  ∀ path : FreeM.Path p, (FreeM.Path.positions p path).map Prod.fst = σ

/-- Fixed-schedule attacker programs are non-adaptive. -/
theorem isNonAdaptive_ofSchedule (att : Frame Msg → Msg) (σ : List Act) (fr : Frame Msg) :
    IsNonAdaptive σ (ofSchedule att σ fr) := by
  induction σ generalizing fr with
  | nil => intro path; rfl
  | cons a σ ih =>
    rintro ⟨o, tail⟩
    exact congrArg (a :: ·) (ih (o :: fr) tail)

/-- A program whose second action depends on the first output: action `false` first, then
action `false` again if the first answer was `none`, and action `true` otherwise. -/
def adaptiveProbe : FreeM (iface Bool Unit) Unit :=
  FreeM.liftBind (false, ()) fun o =>
    match o with
    | none => FreeM.liftBind (false, ()) fun _ => pure ()
    | some _ => FreeM.liftBind (true, ()) fun _ => pure ()

/-- `IsNonAdaptive` is not vacuous: the adaptive probe has no fixed schedule. -/
theorem not_isNonAdaptive_adaptiveProbe (σ : List Bool) : ¬ IsNonAdaptive σ adaptiveProbe := by
  intro h
  have h₁ : [false, false] = σ := h ⟨none, ⟨none, ⟨⟩⟩⟩
  have h₂ : [false, true] = σ := h ⟨some (), ⟨none, ⟨⟩⟩⟩
  simp [← h₂] at h₁

/-! ## The motivating example of the paper

The hash chain of Hérouard, Jacomme, Koutsos and Lallemand (CCS 2026, Section 2): a cell `ck`
starts at a secret `s`; action `A i` replaces it with `h(⟨ck, x⟩)` for the attacker's input `x` and
outputs a constant; `Corrupt` does the same update and outputs the new `ck`; `ROM j` answers the
attacker's hash queries. -/

/-- The actions of the motivating example. -/
inductive ChainAct (n : ℕ) where
  /-- The `i`-th honest key update. -/
  | upd (i : Fin n)
  /-- A key update that leaks the new key. -/
  | corrupt
  /-- The `j`-th random-oracle query. -/
  | rom (j : Fin n)

/-- The motivating example as a `Protocol` over the identity monad, for a keyed hash `h`, a
pairing `pair`, a constant output `ok` and an initial secret `s`. All conditions are true. -/
def chainProtocol (n : ℕ) (h : Msg → Msg) (pair : Msg → Msg → Msg) (ok s : Msg) :
    Protocol Id (ChainAct n) Msg Msg where
  init := s
  step
    | .upd _, x, ck => (true, ok, h (pair ck x))
    | .corrupt, u, ck => (true, h (pair ck u), h (pair ck u))
    | .rom _, x, ck => (true, h x, ck)

end SquirrelModel
