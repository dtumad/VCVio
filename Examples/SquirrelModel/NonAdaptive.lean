/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Examples.SquirrelModel.Execution

/-!
# Squirrel's attackers are exactly the non-adaptive programs

**Translation.** A Squirrel attacker, a fixed trace `σ` with an attacker function `att` of the
frame, is the program `ofSchedule att σ []`, and `IsNonAdaptive σ` says that a program visits
exactly the actions `σ`. The two describe the same programs, up to a query-free continuation, so
quantifying over Squirrel's attackers is quantifying over non-adaptive programs.

`Execution.lean` shows that a Squirrel attacker, a fixed schedule `σ` together with a function
`att` of the frame, is a non-adaptive program (`isNonAdaptive_ofSchedule`). This file proves the
converse: every program over `iface Act Msg` whose paths all visit exactly the actions `σ` is such
an attacker, followed by a continuation that makes no further queries.

* `residual p os` walks the program `p` along the answers `os`, oldest first.
* `attOf p fr` is the message `p` sends at the node reached by the frame `fr`.
* `eq_ofSchedule_bind_residual`: if `IsNonAdaptive σ p`, then
  `p = ofSchedule (attOf p) σ [] >>= fun fr => residual p fr.reverse`.
* `isNonAdaptive_residual`: after the whole schedule, the continuation `residual p os` makes no
  further queries.

The correspondence is between programs, not their costs: `attOf` reads the message off `p`'s
continuations, so it is as expensive to compute as `p` is.

`attOf` needs a default message for frames the program never reaches, hence `[Inhabited Msg]`.
The hypothesis cannot be dropped: with no messages at all, the query-free program `pure x` is
non-adaptive for the empty schedule, but no function `Frame Msg → Msg` exists.
-/

public section

namespace SquirrelModel

open PFunctor

variable {Act Msg α : Type}

/-- Walk a program along a list of answers, oldest first. At a leaf, or once the answers run out,
the walk stops. -/
@[expose] def residual : FreeM (iface Act Msg) α → List (Option Msg) → FreeM (iface Act Msg) α
  | p, [] => p
  | .pure x, _ :: _ => .pure x
  | .liftBind _ k, o :: os => residual (k o) os

@[simp] theorem residual_nil (p : FreeM (iface Act Msg) α) : residual p [] = p := by
  cases p <;> rfl

@[simp] theorem residual_liftBind_cons (a : Act × Msg) (k : Option Msg → FreeM (iface Act Msg) α)
    (o : Option Msg) (os : List (Option Msg)) :
    residual (.liftBind a k) (o :: os) = residual (k o) os := rfl

/-- The message a program sends at its root, or the default at a leaf. -/
def rootMsg [Inhabited Msg] : FreeM (iface Act Msg) α → Msg
  | .pure _ => default
  | .liftBind a _ => a.2

/-- The message `p` sends at the node reached by the frame `fr` (newest entry first). -/
@[expose] def attOf [Inhabited Msg] (p : FreeM (iface Act Msg) α) (fr : Frame Msg) : Msg :=
  rootMsg (residual p fr.reverse)

/-! ## Shifting a schedule's starting frame -/

/-- Mapping over a query maps inside its continuation. -/
private theorem map_liftBind {β : Type} (f : α → β) (a : Act × Msg)
    (k : Option Msg → FreeM (iface Act Msg) α) :
    f <$> FreeM.liftBind a k = FreeM.liftBind a (fun o => f <$> k o) := rfl

/-- Running a schedule from the frame `fr` is running it from the empty frame, with the attacker
reading `fr` below its own entries, and appending `fr` to the result. -/
theorem ofSchedule_eq_map_append (att : Frame Msg → Msg) (σ : List Act) (fr : Frame Msg) :
    ofSchedule att σ fr = (· ++ fr) <$> ofSchedule (fun fr' => att (fr' ++ fr)) σ [] := by
  induction σ generalizing att fr with
  | nil => rfl
  | cons a σ ih =>
    simp only [ofSchedule, List.nil_append]
    rw [map_liftBind]
    congr 1
    funext o
    rw [ih att (o :: fr), ih (fun fr' => att (fr' ++ fr)) [o], Functor.map_map]
    congr 1
    · funext x
      simp
    · congr 1
      funext fr'
      simp

/-! ## Inversion -/

/-- A program with a nonempty schedule starts with a query at the schedule's first action, and
every child continues with the rest of the schedule. -/
theorem IsNonAdaptive.liftBind_inv {a : Act} {σ : List Act} {b : Act × Msg}
    {k : Option Msg → FreeM (iface Act Msg) α}
    (h : IsNonAdaptive (a :: σ) (FreeM.liftBind b k)) :
    b.1 = a ∧ ∀ o, IsNonAdaptive σ (k o) := by
  have hk (o : Option Msg) (path : FreeM.Path (k o)) :
      b.1 :: (FreeM.Path.positions (k o) path).map Prod.fst = a :: σ := h ⟨o, path⟩
  refine ⟨(List.cons.inj (hk none (FreeM.Path.ofHandler (fun _ => none) (k none)))).1,
    fun o path => (List.cons.inj (hk o path)).2⟩

/-- A query-free program has the empty schedule only. -/
theorem IsNonAdaptive.pure_inv {σ : List Act} {x : α}
    (h : IsNonAdaptive σ (FreeM.pure x : FreeM (iface Act Msg) α)) : σ = [] :=
  (h ⟨⟩).symm

/-! ## The characterization -/

/-- **Non-adaptive programs are Squirrel attackers.** A program whose paths all visit exactly the
actions `σ` is the fixed-schedule attacker `attOf p` followed by the residual program. -/
theorem eq_ofSchedule_bind_residual [Inhabited Msg] (σ : List Act)
    (p : FreeM (iface Act Msg) α) (h : IsNonAdaptive σ p) :
    p = ofSchedule (attOf p) σ [] >>= fun fr => residual p fr.reverse := by
  induction σ generalizing p with
  | nil => simp [ofSchedule]
  | cons a σ ih =>
    cases p with
    | pure x => exact absurd h.pure_inv (List.cons_ne_nil a σ)
    | liftBind b k =>
      obtain ⟨hb, hk⟩ := h.liftBind_inv
      obtain ⟨b₁, m⟩ := b
      dsimp only at hb
      subst hb
      have hres (o : Option Msg) (fr' : Frame Msg) :
          residual (FreeM.liftBind (b₁, m) k) (fr' ++ [o]).reverse =
            residual (k o) fr'.reverse := by
        rw [List.reverse_append, List.reverse_singleton, List.singleton_append,
          residual_liftBind_cons]
      have hstep (o : Option Msg) :
          (ofSchedule (attOf (FreeM.liftBind (b₁, m) k)) σ [o] >>=
            fun fr => residual (FreeM.liftBind (b₁, m) k) fr.reverse) = k o := by
        rw [ofSchedule_eq_map_append, bind_map_left]
        have hatt : (fun fr' => attOf (FreeM.liftBind (b₁, m) k) (fr' ++ [o])) = attOf (k o) := by
          funext fr'
          simp only [attOf, hres]
        rw [hatt]
        conv_rhs => rw [ih (k o) (hk o)]
        congr 1
        funext fr'
        exact hres o fr'
      calc FreeM.liftBind (b₁, m) k
          = FreeM.liftBind (b₁, m) (fun o =>
              ofSchedule (attOf (FreeM.liftBind (b₁, m) k)) σ [o] >>=
                fun fr => residual (FreeM.liftBind (b₁, m) k) fr.reverse) := by
            congr 1
            funext o
            exact (hstep o).symm
        _ = _ := rfl

/-- **After the schedule, nothing is left to query.** Walking a non-adaptive program along as many
answers as its schedule has actions leaves a query-free program. -/
theorem isNonAdaptive_residual (σ : List Act) (p : FreeM (iface Act Msg) α)
    (h : IsNonAdaptive σ p) (os : List (Option Msg)) (hos : os.length = σ.length) :
    IsNonAdaptive [] (residual p os) := by
  induction σ generalizing p os with
  | nil =>
    rw [List.length_eq_zero_iff.1 hos, residual_nil]
    exact h
  | cons a σ ih =>
    cases p with
    | pure x => exact absurd h.pure_inv (List.cons_ne_nil a σ)
    | liftBind b k =>
      obtain ⟨o, os, rfl⟩ := List.exists_cons_of_length_eq_add_one hos
      rw [residual_liftBind_cons]
      exact ih (k o) (h.liftBind_inv.2 o) os (by simpa using hos)

/-- A query-free program with the empty schedule is non-adaptive, but with no messages there is
no attacker function, so `[Inhabited Msg]` cannot be dropped from `eq_ofSchedule_bind_residual`.
-/
example (x : α) :
    IsNonAdaptive [] (FreeM.pure x : FreeM (iface Act Empty) α) ∧
      IsEmpty (Frame Empty → Empty) :=
  ⟨fun _ => rfl, ⟨fun f => (f []).elim⟩⟩

end SquirrelModel
