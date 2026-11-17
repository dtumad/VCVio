/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import SquirrelLogic.Derivation
import SquirrelLogic.ProductTape
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Fintype.BigOperators

/-!
# Checks of the secrecy rules

The declaration has one base type `msg`, labelled `large`, three names `k`, `m`, `n : bool → msg`,
a Boolean name `b : bool → bool`, the honest index `idx : bool` and an honest symbol
`h : msg → msg`. In `model`, `msg` at `η` is the bitstrings of length `η`, every name draws a
uniform value of its type, `idx` is `false` and `h` is the identity. Then `msg` is large with
`c = 1` (`model_isLarge`), and `model` respects the labels.

* `workedDerivation`: from the hypothesis `adv(h)`, derive `h(h(k)) ⊬ n`, by FreshR (`k ⊬ n`),
  `▷` from `adv` twice (`k ▷ h(k)`, `h(k) ▷ h(h(k))`), Trans and WeakL.
  `workedDerivation_sound` is its validity from `Derivation.sound`, and `valid_worked` its
  conclusion in `model` against all machines, where the hypothesis holds (`valid_advH`).
* `valid_nonDed_n_m`, `valid_nonDed_m_n`, `not_valid_nonDed_n_n`: `⊬` is not transitive
  (CCS26 §3.2, p. 6): `n ⊬ m` and `m ⊬ n` hold, and `n ⊬ n` fails. The last also shows that
  the conclusion of the worked derivation is not trivial: `h(h(n)) ⊬ n`, the same derivation's
  conclusion with `k` replaced by `n`, fails as well (`not_valid_nonDed_hhn_n`).
* `freshL_needs_freshness`: FreshL without its side condition is unsound: `⊬ n`, with nothing on
  the left, holds by FreshR, and `n ⊬ n`, which adds `n` on the left although `n` is not fresh in
  the right side, fails.
* `freshR_needs_large`: FreshR without the label `large` is unsound: the Boolean name `b` is fresh
  in the empty vector, and `⊬ b` fails, since the constant `true` guesses `b` with probability one
  half.
-/

public section

namespace SquirrelLogic.SecrecyExamples

open IPFunctor IPFunctor.ScopedSignature

/-- The base type of messages. -/
abbrev msg : Ty Unit := .base ()

/-- Three names of messages and a Boolean name, each indexed by a Boolean. -/
inductive Name : Ty Unit → Ty Unit → Type where
  /-- A message name. -/
  | k : Name .bool msg
  /-- A message name. -/
  | m : Name .bool msg
  /-- A message name. -/
  | n : Name .bool msg
  /-- A Boolean name. -/
  | b : Name .bool .bool

/-- The honest symbols: an index and a function on messages. -/
inductive Fn : Ty Unit → Type where
  /-- The index at which names are read. -/
  | idx : Fn .bool
  /-- A function on messages. -/
  | h : Fn (.arrow msg msg)

/-- `msg` is labelled `large` and has no other label. -/
@[expose] def decl : Decl Unit where
  labels _ l := l = .large
  Name := Name
  nameDom_finite := fun n => match n with | .k | .m | .n | .b => nofun
  finite_names := Finite.of_injective (β := Bool × Bool)
    (fun n => match n with
      | ⟨_, _, .k⟩ => (false, false) | ⟨_, _, .m⟩ => (false, true)
      | ⟨_, _, .n⟩ => (true, false) | ⟨_, _, .b⟩ => (true, true))
    fun | ⟨_, _, .k⟩, ⟨_, _, .k⟩, _ => rfl | ⟨_, _, .m⟩, ⟨_, _, .m⟩, _ => rfl
        | ⟨_, _, .n⟩, ⟨_, _, .n⟩, _ => rfl | ⟨_, _, .b⟩, ⟨_, _, .b⟩, _ => rfl
  Fn := Fn
  Att := Empty
  attTy f := f.elim

/-- Messages at `η` are the bitstrings of length `η`. -/
@[expose] def carrier : Unit → ℕ → Set (List Bool) := fun _ η => {l | l.length = η}

theorem carrier_finite (b : Unit) (η : ℕ) : (carrier b η).Finite := List.finite_length_eq Bool η

theorem carrier_nonempty (b : Unit) (η : ℕ) : (carrier b η).Nonempty :=
  ⟨List.replicate η false, List.length_replicate⟩

/-- A name of type `msg` reads `η` bits and returns them as a message, and a Boolean name reads
one bit; so every name draws a uniform value of its type. `idx` is `false` and `h` the identity. -/
@[expose] noncomputable def model : Model decl where
  lenA _ := 0
  carrier := carrier
  nonempty := carrier_nonempty
  coinLen η τ := match τ with
    | .base _ => η
    | .bool => 1
    | .arrow _ _ => 0
  sample η τ := match τ with
    | .base _ => fun c => ⟨List.ofFn c, List.length_ofFn⟩
    | .bool => fun c => c 0
    | .arrow _ _ => fun _ => Classical.choice ((Ty.arrow _ _).nonempty_value carrier_nonempty η)
  finite_index η {a _} _ := a.finite_value_of_finite carrier_finite η
  fn _ {τ} f := match τ, f with
    | _, .idx => false
    | _, .h => id
  att _ f := f.elim

/-- `msg` is large in `model`, with `c = 1`: each message is drawn with probability `2^{-η}`. -/
theorem model_isLarge : model.IsLarge msg := by
  refine ⟨1, one_pos, fun η y => le_of_eq ?_⟩
  obtain ⟨l, hl⟩ := y
  change l.length = η at hl
  subst hl
  have hc : ∀ c : model.Coin l.length msg,
      (model.sample l.length msg c = ⟨l, rfl⟩) ↔ c = l.get := fun c => by
    change (⟨List.ofFn c, _⟩ : carrier () l.length) = ⟨l, rfl⟩ ↔ _
    refine ⟨fun h => List.ofFn_inj.1 ((congrArg Subtype.val h).trans (List.ofFn_get l).symm),
      fun h => ?_⟩
    subst h
    exact Subtype.ext (List.ofFn_get l)
  rw [prEvent_congr _ _ _ hc]
  refine (SampleableType.prEvent_uniformSample_eq_singleton_natCard (α := model.Coin l.length msg)
    l.get).trans ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, one_mul,
    ENNReal.rpow_neg, ENNReal.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  rfl

theorem model_respectsLabels : model.RespectsLabels := fun _ _ h => by
  subst h
  exact model_isLarge

/-! ## Terms -/

/-- A message name at the index `idx`. -/
@[expose] def nm (x : Name .bool msg) : FTerm decl [] msg :=
  FTerm.name (D := decl) x (FTerm.fn (D := decl) Fn.idx)

/-- The Boolean name at the index `idx`. -/
@[expose] def bT : FTerm decl [] .bool :=
  FTerm.name (D := decl) Name.b (FTerm.fn (D := decl) Fn.idx)

/-- The honest symbol `h`, as a function of a tuple of one message. -/
@[expose] def hFn : FTerm decl [] (Ty.arrows [msg] msg) := FTerm.fn (D := decl) Fn.h

/-- `h` applied to a message. -/
@[expose] def hT (t : FTerm decl [] msg) : FTerm decl [] msg :=
  FTerm.apps hFn (Env.cons t Env.empty)

/-- The vector of one term. -/
abbrev one {τ : Ty Unit} (t : FTerm decl [] τ) : Vec decl [] [τ] := Env.cons t Env.empty

/-- The hypothesis `adv(h)`. -/
@[expose] def advH : Form decl [] := .adv hFn

/-- A message name other than `x` avoids the coordinate of `x(idx)`, in every model. -/
theorem nm_avoids {x y : Name .bool msg} (hxy : x ≠ y) (M : Model decl) :
    (nm y).Avoids M fun η k => k = M.nameSlot (D := decl) x Fn.idx η := by
  unfold nm
  exact FTerm.Avoids.name (D := decl) y (fun _ _ h => hxy (by cases h; rfl)) (FTerm.avoids_fn _)

/-- FreshR for one message name on the left. -/
@[expose] def freshR (x y : Name .bool msg) (hxy : x ≠ y) :
    Derivation decl (fun _ => False) (Γ := []) [advH] (.nonDed (one (nm y)) (nm x)) :=
  .nonDedFreshR (one (nm y)) x Fn.idx (by decide) rfl fun M τ z => match τ, z with
    | _, .zero => nm_avoids hxy M

/-! ## The worked derivation -/

/-- From `adv(h)`, derive `h(h(k)) ⊬ n`: FreshR gives `k ⊬ n`; `▷` from `adv` gives `k ▷ h(k)` and
`h(k) ▷ h(h(k))`; Trans gives `k ▷ h(h(k))`; WeakL gives `h(h(k)) ⊬ n`. -/
@[expose] def workedDerivation :
    Derivation decl (fun _ => False) (Γ := []) [advH]
      (.nonDed (one (hT (hT (nm Name.k)))) (nm Name.n)) :=
  .nonDedWeakL (freshR Name.n Name.k nofun)
    (.dedTrans (v := hT (nm Name.k)) (.dedApps (by decide) (.ax List.mem_cons_self))
      (.dedApps (by decide) (.ax List.mem_cons_self)))

/-- The worked derivation is valid in every model restriction, against every class. -/
theorem workedDerivation_sound (R : Model decl → Prop) (C : ∀ M : Model decl, AdvClass M) :
    Valid R C [advH] (.nonDed (one (hT (hT (nm Name.k)))) (nm Name.n)) :=
  workedDerivation.sound R C fun _ h => h.elim

/-- The machine applying `h` to its input: FA-App of the input to the input, answered by the
honest symbol. -/
@[expose] noncomputable def hMachine : AdvMachine model [msg] msg :=
  ((Machine.input .zero (Ty.isGround_base ())).app (Ty.isGround_base ())).fn Fn.h

theorem hMachine_mem : (AdvClass.all model).mem hMachine :=
  AdvClass.all_mem_of_readsBelow_zero (((Machine.readsBelow_input _ _).app _).fn _)

/-- In `model`, against all machines, the hypothesis `adv(h)` holds: `hMachine` computes `h`. -/
theorem valid_advH : Valid (· = model) (fun M => AdvClass.all M) (Γ := []) [] advH := by
  rintro M - rfl env -
  refine Form.holds_adv.2 ⟨hMachine, hMachine_mem, fun η ρ => funext fun x => ?_⟩
  change model.fn η Fn.h x = hMachine.run η ρ.1 (Env.cons x Env.empty)
  rw [hMachine]
  refine Eq.symm ((Machine.run_fn _ _ _).trans ((Machine.run_app _ _ _).trans ?_))
  exact Machine.run_input _ _ _

/-- **Satisfiability.** The hypothesis of the worked derivation holds in `model`, which respects
the labels, so its conclusion `h(h(k)) ⊬ n` holds there against all machines. -/
theorem valid_worked :
    Valid (· = model) (fun M => AdvClass.all M) (Γ := []) []
      (.nonDed (one (hT (hT (nm Name.k)))) (nm Name.n)) :=
  valid_advH.cut (workedDerivation_sound _ _)

/-! ## Countermodels -/

/-- An admitted attacker machine that computes `v` from `u` everywhere refutes `u ⊬ v` against all
machines. -/
theorem not_nonDed_of_forall_eq {τs : List (Ty Unit)} {β : Ty Unit} {u : VecRV model τs}
    {v : RV model β} (g : AdvMachine model τs β) (hg : (AdvClass.all model).mem g)
    (h : ∀ η ρ, Ty.appVals (g.eval η ρ.1) (u η ρ) = v η ρ) : ¬ (AdvClass.all model).NonDed u v :=
  fun hn => not_negligible_one (negligible_of_le (fun η => le_of_eq
    ((prEvent_congr _ _ (fun _ => True) fun ρ => iff_true_intro (h η ρ)).trans
      (OracleComp.prEvent_true_eq_one _)).symm) (hn g hg))

/-- The machine returning its message input. -/
@[expose] noncomputable def idMachine : AdvMachine model [msg] msg :=
  Machine.input .zero (Ty.isGround_base ())

theorem idMachine_mem : (AdvClass.all model).mem idMachine :=
  AdvClass.all_mem_of_readsBelow_zero (Machine.readsBelow_input _ _)

/-- `n ⊬ n` fails in `model`: the identity computes `n` from `n`. -/
theorem not_valid_nonDed_n_n :
    ¬ Valid (· = model) (fun M => AdvClass.all M) (Γ := []) []
      (.nonDed (one (nm Name.n)) (nm Name.n)) :=
  fun h => not_nonDed_of_forall_eq idMachine idMachine_mem
    (fun _ _ => (AdvMachine.appVals_eval _ _).trans (Machine.run_input _ _ _))
    (Form.holds_nonDed.1 (h model model_respectsLabels rfl Env.empty (by simp)))

/-- `h(h(n)) ⊬ n` fails in `model`, where `h` is the identity: the conclusion of the worked
derivation needs `n` fresh. -/
theorem not_valid_nonDed_hhn_n :
    ¬ Valid (· = model) (fun M => AdvClass.all M) (Γ := []) []
      (.nonDed (one (hT (hT (nm Name.n)))) (nm Name.n)) := fun h => by
  have hn := Form.holds_nonDed.1 (h model model_respectsLabels rfl Env.empty (by simp))
  exact not_nonDed_of_forall_eq idMachine idMachine_mem
    (fun _ _ => (AdvMachine.appVals_eval _ _).trans (Machine.run_input _ _ _)) hn

/-- `n ⊬ m`, by FreshR. -/
theorem valid_nonDed_n_m {R : Model decl → Prop} {C : ∀ M : Model decl, AdvClass M} :
    Valid R C (Γ := []) [] (.nonDed (one (nm Name.n)) (nm Name.m)) :=
  Valid.nonDed_freshR (D := decl) Name.m Fn.idx rfl fun M _ τ z => match τ, z with
    | _, .zero => nm_avoids (x := Name.m) (y := Name.n) nofun M

/-- `m ⊬ n`, by FreshR. -/
theorem valid_nonDed_m_n {R : Model decl → Prop} {C : ∀ M : Model decl, AdvClass M} :
    Valid R C (Γ := []) [] (.nonDed (one (nm Name.m)) (nm Name.n)) :=
  Valid.nonDed_freshR (D := decl) Name.n Fn.idx rfl fun M _ τ z => match τ, z with
    | _, .zero => nm_avoids (x := Name.n) (y := Name.m) nofun M

/-- **`⊬` is not transitive** (CCS26 §3.2, p. 6): `n ⊬ m` and `m ⊬ n` hold in `model` against
all machines, and `n ⊬ n` fails. -/
theorem nonDed_not_trans :
    Valid (· = model) (fun M => AdvClass.all M) (Γ := []) []
        (.nonDed (one (nm Name.n)) (nm Name.m)) ∧
      Valid (· = model) (fun M => AdvClass.all M) (Γ := []) []
        (.nonDed (one (nm Name.m)) (nm Name.n)) ∧
      ¬ Valid (· = model) (fun M => AdvClass.all M) (Γ := []) []
        (.nonDed (one (nm Name.n)) (nm Name.n)) :=
  ⟨valid_nonDed_n_m, valid_nonDed_m_n, not_valid_nonDed_n_n⟩

/-- **FreshL needs freshness.** `⊬ n`, with nothing on the left, holds by FreshR; adding `n`
itself on the left, which is not fresh in the right side, gives `n ⊬ n`, which fails. -/
theorem freshL_needs_freshness :
    Valid (· = model) (fun M => AdvClass.all M) (Γ := []) [] (.nonDed Env.empty (nm Name.n)) ∧
      ¬ Valid (· = model) (fun M => AdvClass.all M) (Γ := []) []
        (.nonDed (one (nm Name.n)) (nm Name.n)) :=
  ⟨Valid.nonDed_freshR (D := decl) Name.n Fn.idx rfl (fun _ _ _ z => nomatch z),
    not_valid_nonDed_n_n⟩

/-- The Boolean name is `true` with probability one half. -/
theorem prEvent_bT_eq_true (η : ℕ) :
    Pr{let ρ ← $ᵗ (model.Tape η)}[true = model.nameAt (D := decl) Name.b Fn.idx η ρ] = 2⁻¹ := by
  classical
  have h := prEvent_uniformSample_prod_update (β := model.TapeA η)
    (α := fun k : model.Slot η => model.Coin η k.1.2.1) (model.nameSlot (D := decl) Name.b Fn.idx η)
    fun ρ => true = model.nameAt (D := decl) Name.b Fn.idx η ρ
  simp only [Model.nameAt, Model.name, Function.update_self] at h
  refine h.symm.trans (((SampleableType.prEvent_uniformSample_prod
    (α := model.Coin η .bool) (β := model.Tape η)
    fun z => true = model.sample η .bool z.1).symm.trans
    (SampleableType.prEvent_uniformSample_fst (β := model.Tape η)
      fun c : model.Coin η .bool => true = model.sample η .bool c)).trans ?_)
  have hc : ∀ c : model.Coin η .bool, true = model.sample η .bool c ↔ c = fun _ => true :=
    fun c => ⟨fun h => funext fun i => (Subsingleton.elim (α := Fin 1) i 0) ▸ h.symm,
      fun h => h ▸ rfl⟩
  refine ((prEvent_congr _ _ _ hc).trans
    (SampleableType.prEvent_uniformSample_eq_singleton_natCard (α := model.Coin η .bool)
      fun _ => true)).trans ?_
  change ((Nat.card (Fin 1 → Bool) : ℕ) : ENNReal)⁻¹ = 2⁻¹
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, pow_one,
    Nat.cast_ofNat]

/-- **FreshR needs `large`.** The Boolean name `b` is fresh in the empty vector, and `⊬ b` fails
in `model` against all machines: the constant `true` guesses `b` with probability one half. -/
theorem freshR_needs_large :
    ¬ Valid (· = model) (fun M => AdvClass.all M) (Γ := []) [] (.nonDed Env.empty bT) := fun h => by
  have hn := Form.holds_nonDed.1 (h model model_respectsLabels rfl Env.empty (by simp))
    (Machine.const true) (AdvClass.all_mem_of_readsBelow_zero (Machine.readsBelow_const _))
  refine not_negligible_one (negligible_of_le (fun η => ?_)
    (negligible_const_mul hn (c := 2) ENNReal.ofNat_ne_top))
  change 1 ≤ 2 * Pr{let ρ ← $ᵗ (model.Tape η)}[true = model.nameAt (D := decl) Name.b Fn.idx η ρ]
  rw [prEvent_bT_eq_true, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

end SquirrelLogic.SecrecyExamples
