/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import SquirrelLogic.Global
import VCVio.OracleComp.EvalDist.Measure

/-!
# Satisfiability checks and a derived rule

* `Model.trivial D` interprets every base type as the single empty bitstring, over one-element
  tapes; it respects every label (`Model.trivial_respectsLabels`), so validity does not quantify
  over an empty class of models.
* `Valid.not_box_ff`: `[false]` is not valid, so validity is not trivial either.
* `Valid.all_inst`: instantiating a valid global universal, derived from G.Cut, G.L-∀̃ and
  G.Axiom.
-/

public section

namespace SquirrelLogic

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B}

/-- Every base type is the single empty bitstring, and the tapes have one element. Names,
honest and attacker symbols take arbitrary values. -/
noncomputable def Model.trivial (D : Decl B) : Model D where
  TapeA _ := Unit
  TapeH _ := Unit
  carrier _ _ := {[]}
  nonempty _ _ := Set.singleton_nonempty _
  name η n _ _ := Classical.choice ((D.nameCod n).nonempty_value
    (fun _ _ => Set.singleton_nonempty _) η)
  fn η f := Classical.choice ((D.fnTy f).nonempty_value (fun _ _ => Set.singleton_nonempty _) η)
  att η f _ := Classical.choice ((D.attTy f).nonempty_value
    (fun _ _ => Set.singleton_nonempty _) η)

/-- The trivial model meets every label: its carriers are finite and constant. -/
theorem Model.trivial_respectsLabels : (Model.trivial D).RespectsLabels
  | _, .finite, _ => fun _ => Set.finite_singleton _
  | _, .fixed, _ => fun _ _ => rfl

/-- The constant `1` is not negligible. -/
theorem not_negligible_one : ¬ negligible fun _ : ℕ => (1 : ENNReal) := fun h => by
  have h0 := h 0
  simp only [pow_zero, one_mul] at h0
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h0)

/-- `[false]` is not valid, whatever the adversary classes. -/
theorem Valid.not_box_ff (C : ∀ M : Model D, AdvClass M) :
    ¬ Valid (fun _ => True) C (Γ := []) [] (.box .ff) := fun h => by
  have hM := h (Model.trivial D) Model.trivial_respectsLabels trivial Env.empty (by simp)
  refine not_negligible_one (negligible_of_le (fun η => le_of_eq ?_) hM)
  exact (OracleComp.prEvent_eq_one_of_forall_mem_support _ _ fun _ _ => rfl).symm

/-- A valid global universal may be instantiated by any local term: G.Cut, G.L-∀̃, G.Axiom. -/
theorem Valid.all_inst {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M}
    {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τ : Ty B} {G : Form D (.loc τ :: Γ)}
    (t : FTerm D Γ τ) (h : Valid R C Θ (.all τ G)) : Valid R C Θ (G.substOne t) :=
  h.cut (all_left t (ax List.mem_cons_self))

end SquirrelLogic
