/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import SquirrelLogic.Rules.Secrecy
public import SquirrelLogic.Avoids
import SquirrelLogic.ProductTape
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# A fresh name of a large type is secret (FreshR)

CCS26's FreshR (Fig. 11, p. 17): `u ⊬ n` when `large ∈ label(τ)` for the type `τ` of `n` and `n`
is fresh in `u`. CCS26 presents un-indexed names. Here a name `n : τ₀ → τ` is read at an honest
symbol `i : τ₀`, a closed index whose value at `η` is `⟦i⟧_η`, and freshness is about the one
coordinate of the honest tape that `n(i)` reads at each `η` (`Model.nameSlot`).

* `deduceAdv_nameAt_le` is the concrete statement: if `u` does not read that coordinate, every
  attacker function, admitted or not, computes `n(i)` from `u` with probability at most the
  largest probability of one value of the sampler. Overwriting the coordinate with a fresh coin
  leaves the tape uniform (`prEvent_uniformSample_prod_update`), and for each tape the coin hits
  the attacker's guess with that probability.
* `AdvClass.nonDed_nameAt` is its asymptotic form. With the label `large`
  (`Model.IsLarge`, LICS23 App. A) the bound is `2^{-cη}`, which is negligible
  (`negligible_two_rpow_neg_mul`). It needs no closure field: the bound holds against every
  function of the attacker tape.
* `Valid.nonDed_freshR_of_freshAt` is the rule with the freshness premise semantic, under the
  hypotheses `Θ`, as CCS26's premise `E; Θ ⊢ [ψ^n_fresh(u)]` is a judgment under `Θ`.
  `Valid.nonDed_freshR` is the rule for closed vectors whose terms avoid the coordinate
  (`FTerm.Avoids`) in every admitted model.

FreshL (`u ⊬ v ⟹ u, n ⊬ v` for `n` fresh in `u, v`) is not proved: its reduction must supply the
value of `n` from attacker randomness that the terms do not read (`notes/experiments.md`, M1 part
1; ledger rows L10 and L20).
-/

public section

namespace SquirrelLogic

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B} {M : Model D} {τs : List (Ty B)} {a b : Ty B}

/-- `2^{-cη}` is negligible for `c > 0`. -/
theorem negligible_two_rpow_neg_mul {c : ℝ} (hc : 0 < c) :
    negligible fun η : ℕ => (2 : ENNReal) ^ (-(c * η)) := by
  have hne : ∀ η : ℕ, (2 : ENNReal) ^ (-(c * η)) ≠ ⊤ := fun _ =>
    ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
  rw [negligible_iff_superpolynomialDecay_toReal hne]
  intro k
  have hr : |(2 : ℝ) ^ (-c)| < 1 := by
    rw [abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.2 hc)
  refine (tendsto_pow_const_mul_const_pow_of_abs_lt_one k hr).congr fun η => ?_
  simp only [← ENNReal.toReal_rpow, ENNReal.toReal_ofNat]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), neg_mul]

/-- The random variable of the name `n` read at the honest index `i`. -/
@[expose] def Model.nameAt (M : Model D) (n : D.Name a b) (i : D.Fn a) : RV M b :=
  fun η ρ => M.name η n (M.fn η i) ρ.2

/-- **FreshR at `η`.** If the vector `u` does not read the coordinate of `n(i)`, every attacker
function computes `n(i)` from `u` with probability at most a bound `ε` on the probability of each
value of the sampler. -/
theorem deduceAdv_nameAt_le (n : D.Name a b) (i : D.Fn a) (g : AttackerFn M (Ty.arrows τs b))
    {u : VecRV M τs} (hu : M.FreshAt (M.nameSlot n i) u) (η : ℕ) {ε : ENNReal}
    (hε : ∀ y, Pr{let r ← $ᵗ (M.Coin η b)}[M.sample η b r = y] ≤ ε) :
    deduceAdv g u (M.nameAt n i) η ≤ ε := by
  classical
  rw [deduceAdv, ← prEvent_uniformSample_prod_update (β := M.TapeA η)
    (α := fun k : M.Slot η => M.Coin η k.1.2.1) (M.nameSlot n i η)]
  have hev : ∀ (c : M.Coin η b) (ρ : M.Tape η),
      Ty.appVals (g η ρ.1) (u η (ρ.1, Function.update ρ.2 (M.nameSlot n i η) c)) =
          M.nameAt n i η (ρ.1, Function.update ρ.2 (M.nameSlot n i η) c) ↔
        Ty.appVals (g η ρ.1) (u η ρ) = M.sample η b c := fun c ρ => by
    rw [hu η ρ.1 _ ρ.2 fun k hk => Function.update_of_ne hk _ _]
    simp only [Model.nameAt, Model.name, Function.update_self]
  refine (prEvent_bind_congr_of_forall _ _ _ _ _ fun c =>
    prEvent_congr _ _ _ (hev c)).trans_le ?_
  refine (SampleableType.prEvent_uniformSample_prod (α := M.Coin η b) (β := M.Tape η)
    fun z => Ty.appVals (g η z.2.1) (u η z.2) = M.sample η b z.1).symm.trans_le ?_
  refine SampleableType.prEvent_uniformSample_prod_le_of_forall_snd _ fun ρ => ?_
  exact le_of_eq_of_le (prEvent_congr _ _ _ fun _ => eq_comm) (hε (Ty.appVals (g η ρ.1) (u η ρ)))

/-- **FreshR**, semantically: a name of a large type is secret from every vector that does not
read its coordinate, against every attacker function. -/
theorem AdvClass.nonDed_nameAt (C : AdvClass M) (n : D.Name a b) (i : D.Fn a)
    (hb : M.IsLarge b) {u : VecRV M τs} (hu : M.FreshAt (M.nameSlot n i) u) :
    C.NonDed u (M.nameAt n i) := fun g _ => by
  obtain ⟨c, hc, hle⟩ := hb
  exact negligible_of_le (fun η => deduceAdv_nameAt_le n i g hu η (hle η))
    (negligible_two_rpow_neg_mul hc)

namespace Valid

variable {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M}

/-- **FreshR** (CCS26 Fig. 11, p. 17), with a semantic freshness premise: `u⃗ ⊬ n(i)` when the
type of `n` is labelled `large` and, in every admitted model where `Θ` holds, the vector `u⃗` does
not read the coordinate of `n(i)`. -/
theorem nonDed_freshR_of_freshAt {Γ : List (Kind B)} {Θ : List (Form D Γ)} {u : Vec D Γ τs}
    (n : D.Name a b) (i : D.Fn a) (hlarge : b.HasLabel D.labels .large)
    (hfresh : ∀ M : Model D, M.RespectsLabels → R M → ∀ env,
      (∀ θ ∈ Θ, θ.Holds M (C M) env) → M.FreshAt (M.nameSlot n i) (u.rv M (C M) env)) :
    Valid R C Θ (.nonDed u (FTerm.name n (FTerm.fn i))) := fun M hl hR env hΘ =>
  Form.holds_nonDed.2 ((C M).nonDed_nameAt n i (M.isLarge_of_hasLabel hl hlarge)
    (hfresh M hl hR env hΘ))

/-- **FreshR** (CCS26 Fig. 11, p. 17), for a closed vector: `u⃗ ⊬ n(i)` when the type of `n` is
labelled `large` and, in every admitted model, every term of `u⃗` avoids the coordinate of
`n(i)`. -/
theorem nonDed_freshR {Θ : List (Form D [])} {u : Vec D [] τs} (n : D.Name a b) (i : D.Fn a)
    (hlarge : b.HasLabel D.labels .large)
    (hfresh : ∀ M, R M → ∀ τ x, (u τ x).Avoids M fun η k => k = M.nameSlot n i η) :
    Valid R C Θ (.nonDed u (FTerm.name n (FTerm.fn i))) :=
  nonDed_freshR_of_freshAt n i hlarge fun M _ hR env _ =>
    Vec.freshAt_rv (hfresh M hR) (C M) env

end Valid

end SquirrelLogic
