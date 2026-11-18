/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import SquirrelLogic.PRFExamples

/-!
# PRF.R in a model with a perfect PRF

Checks of PRF.R (CCS26 Fig. 4, `Valid.nonDed_prfR`) in `PRFExamples.pmodel`, where messages at
`η` are the bitstrings of length `η`, a key is a whole uniform function table and
`h(x, k) = k(x)`, so that every distinguisher has PRF advantage zero (`pmodel_prfAdv`).

* `chainWorked`, `chainWorked_sound`: the first two steps of CCS26 §2's hash chain with the
  oracle as the leakage, `ck₀ = s`, `ck₁ = h(s, k)`, `ck₂ = h(ck₁, k)`. FreshR gives
  `o_h^k ⊬ s`; PRF.R gives `o_h^k ⊬ h(s, k)`; PRF.R again, at the message `h(s, k)`, which is
  itself a hash, gives `o_h^k ⊬ h(h(s, k), k)`. The second step has two candidates (`h(s, k)` and
  `s`), and needs no `ψ_msg` of the message: `m = h(s, k)` is not asked to differ from `s`.
* `valid_chainWorked`: in `pmodel`, against all machines, every hypothesis of both PRF.R steps
  holds jointly (uniform messages, long tapes, polynomial bit blocks, read bounds, the label
  `large`, `[ψ_msg]` and the PRF assumption), so `o_h^k ⊬ h(h(s, k), k)` holds there. FreshR does
  not give it: the conclusion is not a name.
-/

public section

namespace SquirrelLogic.PRFOracleExamples

open IPFunctor IPFunctor.ScopedSignature PRFExamples

/-- The models over which the chain uses PRF.R: uniform messages, long tapes and polynomial bit
blocks for messages. -/
abbrev ChainR (M : Model decl) : Prop :=
  M.UniformSampler msg ∧ M.LongTapes ∧ M.PolyCoins msg

/-- The empty vector. -/
abbrev u₀ : OVec P [] [] := Env.empty

/-- The first link `h(s, k)`, with its call explicit. -/
@[expose] def ck₁ : OTerm P [] msg := OTerm.call (nmO Name.s)

/-- The first step of the chain: PRF.R at the message `s`. -/
@[expose] def inst₁ : PRFRInstance decl :=
  ⟨P, [], u₀, nmO Name.s, trivial, trivial, of_decide_eq_true rfl, of_decide_eq_true rfl⟩

/-- The second step of the chain: PRF.R at the message `h(s, k)`. -/
@[expose] def inst₂ : PRFRInstance decl :=
  ⟨P, [], u₀, ck₁, trivial, trivial, of_decide_eq_true rfl, of_decide_eq_true rfl⟩

/-- The hypothesis `[ψ_msg^{m,k}(∅)]`: the empty vector has no call, so it is `[true]`. -/
@[expose] def psiR (m : OTerm P [] msg) : Form decl [] := .box (P.psiMsgVec u₀ m)

/-- `[ψ_msg^{m,k}(∅)]` holds in every model. -/
theorem valid_psiR {R : Model decl → Prop} {C : ∀ M : Model decl, AdvClass M}
    {Θ : List (Form decl [])} (m : OTerm P [] msg) : Valid R C Θ (psiR m) := fun M _ _ env _ => by
  refine Form.holds_box.2 (negligible_of_zero fun η =>
    prEvent_eq_zero_of_forall_not _ _ fun ρ hρ => ?_)
  rw [Bool.eq_false_iff] at hρ
  exact hρ ((P.psiMsgVec_eq_true_iff _ u₀ m env ρ).2 fun t' ht' => absurd ht' List.not_mem_nil)

theorem keyFree_nmO (x : Name .bool msg) : P.KeyFree (nmO x) :=
  nmO_every x trivial (fun h => by cases h) trivial

theorem pptm_nmO (x : Name .bool msg) : P.Pptm (nmO x) :=
  nmO_every x trivial ⟨trivial, Nat.zero_le 1⟩ (Nat.zero_le 1)

theorem firstOrder_nmO (x : Name .bool msg) : P.FirstOrder (nmO x) :=
  nmO_every x trivial trivial trivial

theorem inst₁_syntactic : inst₁.Syntactic := by
  refine ⟨fun _ h => absurd h List.not_mem_nil, rfl, fun _ x => ?_, keyFree_nmO _, fun _ x => ?_,
    pptm_nmO _, fun _ x => ?_, firstOrder_nmO _⟩ <;> cases x

theorem inst₂_syntactic : inst₂.Syntactic := by
  refine ⟨fun _ h => absurd h List.not_mem_nil, rfl, fun _ x => ?_,
    ⟨trivial, fun _ => keyFree_nmO Name.s⟩, fun _ x => ?_,
    ⟨⟨trivial, trivial⟩, fun _ => pptm_nmO Name.s⟩, fun _ x => ?_,
    ⟨trivial, fun _ => firstOrder_nmO Name.s⟩⟩ <;> cases x

/-- The PRF assumption of the first step holds in `pmodel` against all machines: `h` is a perfect
PRF. -/
theorem inst₁_holds : inst₁.Holds (· = pmodel) (fun M => AdvClass.all M) := by
  intro M _ hM hU g _ t _
  subst hM
  exact negligible_of_zero fun η => pmodel_prfAdv η hU _

/-- The PRF assumption of the second step holds in `pmodel` against all machines. -/
theorem inst₂_holds : inst₂.Holds (· = pmodel) (fun M => AdvClass.all M) := by
  intro M _ hM hU g _ t _
  subst hM
  exact negligible_of_zero fun η => pmodel_prfAdv η hU _

/-- The hash oracle does not read the coordinate of `s(idx)`: it reads only the key's. -/
theorem hashOracle_avoids (M : Model decl) :
    FTerm.Avoids M (fun η k => k = M.nameSlot (D := decl) Name.s Fn.idx η)
      (P.hashOracle (Γ := [])) := fun η _ ρh ρh' hρ _ => by
  funext x
  change M.fn η Fn.h x (M.sample η keyT (ρh (P.keySlot M η))) =
    M.fn η Fn.h x (M.sample η keyT (ρh' (P.keySlot M η)))
  rw [hρ _ fun h => by cases h]

/-- **Two steps of a hash chain by PRF.R** (CCS26 §2.3, the lemma secrecy_base unrolled): FreshR
gives `o_h^k ⊬ s`, PRF.R gives `o_h^k ⊬ h(s, k)`, and PRF.R at the message `h(s, k)` gives
`o_h^k ⊬ h(h(s, k), k)`. -/
@[expose] def chainWorked :
    Derivation decl (fun _ => False) (fun e => e = .right inst₁ ∨ e = .right inst₂) ChainR
      (Γ := []) [psiR (nmO Name.s), psiR ck₁]
      (.nonDed inst₂.lhs (P.hashTerm (P.close ck₁)) inst₂.order) :=
  have hl : ∀ M, ChainR M → M.UniformSampler msg ∧ M.LongTapes ∧ M.PolyCoins msg := fun _ h => h
  have d₀ := (close_nmO Name.s).symm ▸ Derivation.nonDedFreshR
    (enc := fun _ => False) (prf := fun e => e = .right inst₁ ∨ e = .right inst₂) (R₀ := ChainR)
    (Θ := [psiR (nmO Name.s), psiR ck₁]) inst₁.lhs Name.s Fn.idx inst₁.orderM rfl
    fun M τ x => by
      cases x with
      | zero => exact hashOracle_avoids M
      | succ x => exact nomatch x
  have d₁ := Derivation.nonDedPRFR inst₁ (.inl rfl) inst₁_syntactic hl
    (fun _ _ _ _ _ _ => ⟨fun _ x => (nomatch x), ⟨0, fun _ _ _ _ _ => rfl⟩⟩)
    (.ax List.mem_cons_self) d₀
  Derivation.nonDedPRFR inst₂ (.inr rfl) inst₂_syntactic hl
    (fun _ _ _ _ _ _ => ⟨fun _ x => (nomatch x), ⟨0, fun _ _ _ _ _ => rfl⟩⟩)
    (.ax (List.mem_cons_of_mem _ List.mem_cons_self)) d₁

/-- The chain is valid over the models of `ChainR`, against every class under which both PRF.R
instances meet their PRF assumption. -/
theorem chainWorked_sound (R : Model decl → Prop) (C : ∀ M : Model decl, AdvClass M)
    (hR : ∀ M, R M → ChainR M) (h₁ : inst₁.Holds R C) (h₂ : inst₂.Holds R C) :
    Valid R C [psiR (nmO Name.s), psiR ck₁]
      (.nonDed inst₂.lhs (P.hashTerm (P.close ck₁)) inst₂.order) :=
  chainWorked.sound R C (fun _ h => h.elim) (fun e he => by
    rcases he with rfl | rfl
    · exact h₁
    · exact h₂) hR

/-- **Satisfiability of PRF.R.** In `pmodel`, against all machines, every hypothesis of both PRF.R
steps holds jointly, so `o_h^k ⊬ h(h(s, k), k)` holds there. -/
theorem valid_chainWorked :
    Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) []
      (.nonDed inst₂.lhs (P.hashTerm (P.close ck₁)) inst₂.order) :=
  have hc := chainWorked_sound (· = pmodel) (fun M => AdvClass.all M)
    (fun _ hM => hM ▸ ⟨pmodel_uniformSampler, pmodel_longTapes, pmodel_polyCoins⟩)
    inst₁_holds inst₂_holds
  (valid_psiR (Θ := []) ck₁).cut ((valid_psiR (Θ := [psiR ck₁]) (nmO Name.s)).cut hc)

end SquirrelLogic.PRFOracleExamples
