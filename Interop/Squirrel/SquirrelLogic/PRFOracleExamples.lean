/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import SquirrelLogic.PRFExamples

/-!
# PRF.R and PRF.L-sec in a model with a perfect PRF

Checks of PRF.R and PRF.L-sec (CCS26 Fig. 4 and §2.3, `Valid.nonDed_prfR`,
`Valid.nonDed_prfLSec`) in `PRFExamples.pmodel`, where messages at `η` are the bitstrings of
length `η`, a key is a whole uniform function table and `h(x, k) = k(x)`, so that every
distinguisher has PRF advantage zero (`pmodel_prfAdv`).

* `chainWorked`, `chainWorked_sound`: the first two steps of CCS26 §2's hash chain with the
  oracle as the leakage, `ck₀ = s`, `ck₁ = h(s, k)`, `ck₂ = h(ck₁, k)`. FreshR gives
  `o_h^k ⊬ s`; PRF.R gives `o_h^k ⊬ h(s, k)`; PRF.R again, at the message `h(s, k)`, which is
  itself a hash, gives `o_h^k ⊬ h(h(s, k), k)`. The second step has two candidates (`h(s, k)` and
  `s`), and needs no `ψ_msg` of the message: `m = h(s, k)` is not asked to differ from `s`.
* `valid_chainWorked`: in `pmodel`, against all machines, every hypothesis of both PRF.R steps
  holds jointly (uniform messages, long tapes, polynomial bit blocks, read bounds, the label
  `large`, `[ψ_msg]` and the PRF assumption), so `o_h^k ⊬ h(h(s, k), k)` holds there. FreshR does
  not give it: the conclusion is not a name.
* `leftWorked`, `valid_leftWorked`: PRF.R gives `o_h^k ⊬ h(s, k)`, FreshR gives `o_h^k ⊬ r`, and
  PRF.L-sec with the secret `h(s, k)` and the message `r` gives `o_h^k, h(r, k) ⊬ h(s, k)`; in
  `pmodel` every hypothesis of both steps holds jointly, `[s ≠ r]` (`valid_psiL`) because two
  independent messages collide with probability `2^{-η}`. A preview of CCS26 §2.3, where PRF.L-sec
  removes the corrupted key from the leakage.
* `prfLSec_needs_psiMsg`: with the secret `h(s, k)` and the message `s`, every hypothesis of
  PRF.L-sec but `[ψ_msg]` holds (the premise by PRF.R, `C_sec` by FreshR), `ψ_msg` is `s ≠ s`, and
  the conclusion `o_h^k, h(s, k) ⊬ h(s, k)` fails: the attacker returns the hash it is given.
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

/-! ## PRF.L-sec -/

/-- The hash oracle reads no coordinate of a message name at `idx`: it reads only the key's. -/
theorem hashOracle_avoids_name (M : Model decl) (x : Name .bool msg) :
    FTerm.Avoids M (fun η k => k = M.nameSlot (D := decl) x Fn.idx η)
      (P.hashOracle (Γ := [])) := fun η _ ρh ρh' hρ _ => by
  funext y
  change M.fn η Fn.h y (M.sample η keyT (ρh (P.keySlot M η))) =
    M.fn η Fn.h y (M.sample η keyT (ρh' (P.keySlot M η)))
  rw [hρ _ fun h => by cases h]

/-- `o_h^k ⊬ x(idx)` by FreshR, for a message name `x`. -/
@[expose] def freshMsg (x : Name .bool msg) {prf : PRFRule decl → Prop}
    {R₀ : Model decl → Prop} {Θ : List (Form decl [])} :
    Derivation decl (fun _ => False) prf R₀ Θ (.nonDed inst₁.lhs (P.close (nmO x)) inst₁.orderM) :=
  (close_nmO x).symm ▸ Derivation.nonDedFreshR inst₁.lhs x Fn.idx inst₁.orderM rfl
    fun M τ y => by
      cases y with
      | zero => exact hashOracle_avoids_name M x
      | succ y => exact nomatch y

/-- The first PRF.R step: `o_h^k ⊬ h(s, k)`, from `[ψ_msg^{s,k}(∅)]`. -/
@[expose] def step₁ {prf : PRFRule decl → Prop} (hprf : prf (.right inst₁))
    {Θ : List (Form decl [])} (hψ : psiR (nmO Name.s) ∈ Θ) :
    Derivation decl (fun _ => False) prf ChainR Θ
      (.nonDed inst₁.lhs (P.hashTerm (P.close (nmO Name.s))) inst₁.order) :=
  Derivation.nonDedPRFR inst₁ hprf inst₁_syntactic (fun _ h => h)
    (fun _ _ _ _ _ _ => ⟨fun _ x => (nomatch x), ⟨0, fun _ _ _ _ _ => rfl⟩⟩) (.ax hψ) (freshMsg _)

/-- PRF.L-sec with the secret `h(s, k)` and the message `r`. -/
@[expose] def inst₃ : PRFLInstance decl :=
  ⟨P, [], msg, u₀, ck₁, nmO Name.r, trivial, trivial, of_decide_eq_true rfl,
    of_decide_eq_true rfl, of_decide_eq_true rfl⟩

theorem inst₃_syntactic : inst₃.Syntactic := by
  refine ⟨fun _ h => absurd h List.not_mem_nil, trivial, fun _ x => ?_,
    ⟨trivial, fun _ => keyFree_nmO Name.s⟩, keyFree_nmO Name.r, fun _ x => ?_,
    ⟨⟨trivial, trivial⟩, fun _ => pptm_nmO Name.s⟩, pptm_nmO Name.r, fun _ x => ?_,
    ⟨trivial, fun _ => firstOrder_nmO Name.s⟩, firstOrder_nmO Name.r⟩ <;> cases x

/-- The PRF assumption of PRF.L-sec holds in `pmodel` against all machines. -/
theorem inst₃_holds : inst₃.Holds (· = pmodel) (fun M => AdvClass.all M) := by
  intro M _ hM hU g _
  subst hM
  exact ⟨negligible_of_zero fun η => pmodel_prfAdv η hU _,
    negligible_of_zero fun η => pmodel_prfAdv η hU _⟩

/-- The hypothesis `[ψ_msg^{r,k}(∅, h(s, k), r)]`: the one call is on `s`, so it is `[s ≠ r]`. -/
@[expose] def psiL : Form decl [] :=
  .box (P.psiMsg (Env.append u₀ (Env.cons ck₁ Env.empty)) (nmO Name.r))

/-- A message name at `idx` has no call. -/
theorem calls_nmO (x : Name .bool msg) : P.calls (nmO x) = [] :=
  rfl

/-- The arguments of the calls of `h(s, k)` and `r`: only `s`. -/
theorem calls_psiL (t' : OTerm P [] msg)
    (ht' : t' ∈ P.vecCalls (Env.append u₀ (Env.cons ck₁ Env.empty)) ++ P.calls (nmO Name.r)) :
    t' = nmO Name.s := by
  change t' ∈ P.vecCalls (Env.cons ck₁ Env.empty : OVec P [] [msg]) ++ P.calls (nmO Name.r) at ht'
  simp only [PRFSymbols.vecCalls_cons, PRFSymbols.vecCalls_nil, ck₁, PRFSymbols.calls_call,
    calls_nmO, List.append_nil, List.mem_singleton] at ht'
  exact ht'

/-- `[s ≠ r]` holds in `pmodel`: two independent uniform messages collide with probability at most
`2^{-η}` (`deduceAdv_nameAt_le`). -/
theorem valid_psiL {Θ : List (Form decl [])} :
    Valid (· = pmodel) (fun M => AdvClass.all M) Θ psiL := fun M _ hM env _ => by
  subst hM
  obtain ⟨c, hc, hle⟩ := pmodel_isLarge
  refine Form.holds_box.2 (negligible_of_le (fun η => ?_) (negligible_two_rpow_neg_mul hc))
  refine (prEvent_mono _ _ (fun ρ => (P.close (nmO Name.r)).denote
    (fullInterp pmodel (AdvClass.all pmodel)) env η ρ =
      pmodel.nameAt (D := decl) Name.s Fn.idx η ρ) fun ρ hρ => ?_).trans ?_
  · by_contra hne
    refine Bool.eq_false_iff.1 hρ ((P.psiMsg_eq_true_iff _ _ _ env ρ).2 fun t' ht' heq => hne ?_)
    rw [calls_psiL t' ht'] at heq
    rw [P.denote_close_apply _ _ env ρ]
    exact heq.symm
  · exact deduceAdv_nameAt_le (M := pmodel) (D := decl) Name.s Fn.idx (τs := [msg])
      (fun _ _ x => x)
      (u := fun η ρ => Env.cons ((P.close (nmO Name.r)).denote
        (fullInterp pmodel (AdvClass.all pmodel)) env η ρ) Env.empty)
      (fun η ρa ρh ρh' hρ => congrArg (Env.cons · _) (by
        change pmodel.sample η msg (ρh ⟨⟨_, _, Name.r⟩, pmodel.fn η Fn.idx⟩) =
          pmodel.sample η msg (ρh' ⟨⟨_, _, Name.r⟩, pmodel.fn η Fn.idx⟩)
        rw [hρ _ fun h => by cases h])) η (hle η)

/-- **PRF.R, then PRF.L-sec** (a preview of CCS26 §2.3's elimination of the corrupted key): PRF.R
gives `o_h^k ⊬ h(s, k)`; FreshR gives `o_h^k ⊬ r`; PRF.L-sec, with the secret `h(s, k)` and the
message `r`, gives `o_h^k, h(r, k) ⊬ h(s, k)`. -/
@[expose] def leftWorked :
    Derivation decl (fun _ => False) (fun e => e = .right inst₁ ∨ e = .left inst₃) ChainR
      (Γ := []) [psiR (nmO Name.s), psiL]
      (.nonDed (Vec.snoc inst₃.lhs (P.hashTerm (P.close (nmO Name.r)))) (P.close ck₁)
        inst₃.orderC) :=
  Derivation.nonDedPRFLSec inst₃ (.inr rfl) inst₃_syntactic
    (fun _ h => ⟨h.1, h.2.1, h.2.2, h.2.2⟩)
    (fun _ _ _ _ _ _ => ⟨fun _ x => (nomatch x), ⟨0, fun _ _ _ _ _ => rfl⟩,
      ⟨0, fun _ _ _ _ _ => rfl⟩⟩)
    (.ax (List.mem_cons_of_mem _ List.mem_cons_self)) (step₁ (.inl rfl) List.mem_cons_self)
    (freshMsg _)

/-- **Satisfiability of PRF.L-sec.** In `pmodel`, against all machines, every hypothesis of the
PRF.R step and of the PRF.L-sec step holds jointly, so `o_h^k, h(r, k) ⊬ h(s, k)` holds there.
FreshR does not give it: the secret is not a name. -/
theorem valid_leftWorked :
    Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) []
      (.nonDed (Vec.snoc inst₃.lhs (P.hashTerm (P.close (nmO Name.r)))) (P.close ck₁)
        inst₃.orderC) :=
  have hc := leftWorked.sound (· = pmodel) (fun M => AdvClass.all M) (fun _ h => h.elim)
    (fun e he => by
      rcases he with rfl | rfl
      · exact inst₁_holds
      · exact inst₃_holds)
    (fun _ hM => hM ▸ ⟨pmodel_uniformSampler, pmodel_longTapes, pmodel_polyCoins⟩)
  (valid_psiL (Θ := [])).cut ((valid_psiR (Θ := [psiL]) (nmO Name.s)).cut hc)

/-! ## PRF.L-sec needs `ψ_msg` -/

/-- PRF.L-sec with the secret `h(s, k)` and the message `s`: the secret's call is on the
message. -/
@[expose] def inst₄ : PRFLInstance decl :=
  ⟨P, [], msg, u₀, ck₁, nmO Name.s, trivial, trivial, of_decide_eq_true rfl,
    of_decide_eq_true rfl, of_decide_eq_true rfl⟩

/-- **PRF.L-sec needs `ψ_msg`.** With the secret `h(s, k)` and the message `s`: the syntactic
conditions and the PRF assumption hold, `o_h^k ⊬ h(s, k)` holds (PRF.R) and so does
`C_sec = o_h^k ⊬ s` (FreshR), but `ψ_msg`, which is `s ≠ s`, fails, and so does the conclusion
`o_h^k, h(s, k) ⊬ h(s, k)`: the attacker returns the hash it is given. -/
theorem prfLSec_needs_psiMsg :
    inst₄.Syntactic ∧ inst₄.Holds (· = pmodel) (fun M => AdvClass.all M) ∧
      Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) []
        (.nonDed inst₄.lhs (P.close inst₄.v) inst₄.order) ∧
      Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) []
        (.nonDed inst₄.lhs (P.close inst₄.m) inst₄.orderM) ∧
      ¬ Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) []
        (.box (P.psiMsg (Env.append inst₄.u (Env.cons inst₄.v Env.empty)) inst₄.m)) ∧
      ¬ Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) []
        (.nonDed (Vec.snoc inst₄.lhs (P.hashTerm (P.close inst₄.m))) (P.close inst₄.v)
          inst₄.orderC) := by
  refine ⟨?_, ?_, ?_, ?_, fun h => ?_, fun h => ?_⟩
  · refine ⟨fun _ h => absurd h List.not_mem_nil, trivial, fun _ x => ?_,
      ⟨trivial, fun _ => keyFree_nmO Name.s⟩, keyFree_nmO Name.s, fun _ x => ?_,
      ⟨⟨trivial, trivial⟩, fun _ => pptm_nmO Name.s⟩, pptm_nmO Name.s, fun _ x => ?_,
      ⟨trivial, fun _ => firstOrder_nmO Name.s⟩, firstOrder_nmO Name.s⟩ <;> cases x
  · intro M _ hM hU g _
    subst hM
    exact ⟨negligible_of_zero fun η => pmodel_prfAdv η hU _,
      negligible_of_zero fun η => pmodel_prfAdv η hU _⟩
  · exact (valid_psiR (Θ := []) (nmO Name.s)).cut
      ((step₁ (prf := (· = .right inst₁)) rfl List.mem_cons_self).sound _ _ (fun _ h => h.elim)
        (fun e he => he ▸ inst₁_holds)
        (fun _ hM => hM ▸ ⟨pmodel_uniformSampler, pmodel_longTapes, pmodel_polyCoins⟩))
  · exact (freshMsg (prf := fun _ => False) (R₀ := fun _ => True) (Θ := []) Name.s).sound _ _
      (fun _ h => h.elim) (fun _ h => h.elim) fun _ _ => trivial
  · have hb := Form.holds_box.1 (h pmodel pmodel_respectsLabels rfl Env.empty (by simp))
    refine not_negligible_one (negligible_of_le (fun η => le_of_eq ?_) hb)
    refine ((prEvent_congr _ _ (fun _ => True) fun ρ => iff_true_intro ?_).trans
      (OracleComp.prEvent_true_eq_one _)).symm
    refine Bool.eq_false_iff.2 fun hψ => (P.psiMsg_eq_true_iff _ _ _ _ ρ).1 hψ (nmO Name.s) ?_ rfl
    change nmO Name.s ∈ P.vecCalls (Env.cons ck₁ Env.empty : OVec P [] [msg]) ++
      P.calls (nmO Name.s)
    simp [ck₁, PRFSymbols.calls_call, calls_nmO]
  · have hN := Form.holds_nonDed.1 (h pmodel pmodel_respectsLabels rfl Env.empty (by simp))
    have h₁ := hN (Machine.input (M := pmodel)
      (τs := (([] ++ [Ty.arrow msg msg]) ++ [msg]) ++ msg.args) (.succ .zero) trivial)
      (AdvClass.all_mem_input (M := pmodel)
        (τs := (([] ++ [Ty.arrow msg msg]) ++ [msg]) ++ msg.args) (.succ .zero)
        (Ty.isGround_base ()))
    refine not_negligible_one (negligible_of_le (fun η => le_of_eq ?_) h₁)
    exact ((prEvent_congr _ _ (fun _ => True) fun ρ => iff_true_intro rfl).trans
      (OracleComp.prEvent_true_eq_one _)).symm

end SquirrelLogic.PRFOracleExamples
