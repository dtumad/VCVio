/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.Rewinding.ExtractionCached
public import VCVio.CryptoFoundations.Rewinding.FixedTape
public import VCVio.CryptoFoundations.CoordinateFork.Finder
public import VCVio.CryptoFoundations.CoordinateFork.SpecialSoundness

/-!
# Coordinate-wise extraction against a frozen prover

Lemma 7.1 of Fenzi–Moghaddas–Nguyen at `μ = 1`, against frozen reruns of an interactive prover
(`Rewinding.fixedTape`) rather than a table of responses. The coordinate-wise finder
(`OracleComp.coordFinder`) looks for a coordinate-wise special sound set of accepting challenge
vectors. `Rewinding.recoverCached` recovers the transcripts of its members from the finder's own
runs, they share the commitment (`Rewinding.ResetPolicy.eagerTable_fst_eq`), and a coordinate-wise
special sound extractor turns them into a witness. A valid witness comes back with probability at
least the prover's acceptance probability minus `ℓ(k - 1)/|S|`, after at most `1 + ℓ(k - 1)`
complete runs in expectation.
-/

public section

open OracleComp OracleSpec Rewinding CoordinateWise
open scoped ENNReal

namespace VCVioTest.CoordinateExtraction

variable {Stmt Wit Commit St Resp : Type} {rel : Stmt → Wit → Bool}
  {ι S : Type} [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S] [Nonempty S]

/-- A malicious prover's complete run on a challenge vector: its commitment phase, then its
response. -/
@[expose] def proverRun (commit : ProbComp (Commit × St)) (respond : St → (ι → S) → ProbComp Resp)
    (c : ι → S) : ProbComp (Commit × Resp) :=
  commit >>= fun s => (s.1, ·) <$> respond s.2 c

/-- The size of a coordinate-wise special sound set. -/
abbrev starSize (ι : Type) [Fintype ι] (k : ℕ) : ℕ := Fintype.card ι * (k - 1) + 1

omit [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S] in
/-- The members of a set of challenge vectors in the order of its list, with a default past its
end. -/
@[expose] noncomputable def starPoints (k : ℕ) (X : Finset (ι → S)) :
    Fin (starSize ι k) → ι → S :=
  fun i => X.toList.getD i (Classical.arbitrary _)

omit [DecidableEq ι] [DecidableEq S] [Fintype S] in
theorem starPoints_eq (k : ℕ) (X : Finset (ι → S)) (i : Fin (starSize ι k))
    (hi : (i : ℕ) < X.toList.length) : starPoints k X i = X.toList[(i : ℕ)] := by
  simp only [starPoints, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some]

omit [DecidableEq ι] [DecidableEq S] [Fintype S] in
theorem starPoints_mem (k : ℕ) (X : Finset (ι → S)) (hX : X.card = starSize ι k)
    (i : Fin (starSize ι k)) : starPoints k X i ∈ X := by
  have hi : (i : ℕ) < X.toList.length := by rw [Finset.length_toList, hX]; exact i.isLt
  rw [starPoints_eq k X i hi]
  exact Finset.mem_toList.mp (List.getElem_mem hi)

omit [DecidableEq ι] [Fintype S] in
theorem image_starPoints (k : ℕ) (X : Finset (ι → S)) (hX : X.card = starSize ι k) :
    Finset.univ.image (starPoints k X) = X := by
  have hlen : ∀ i : Fin (starSize ι k), (i : ℕ) < X.toList.length := fun i => by
    rw [Finset.length_toList, hX]; exact i.isLt
  have hinj : Function.Injective (starPoints k X) := by
    intro i j hij
    rw [starPoints_eq k X i (hlen i), starPoints_eq k X j (hlen j)] at hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff (Finset.nodup_toList X)).mp hij)
  apply Finset.eq_of_subset_of_card_le
  · intro c hc
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hc
    exact starPoints_mem k X hX i
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, hX]

/-- The coordinate-wise extractor on the transcripts at the members of a set, with the commitment
of the first. -/
@[expose] noncomputable def coordExt [DecidableEq Resp]
    (ext : Stmt → Commit → Finset ((ι → S) × Resp) → ProbComp Wit) (x : Stmt) (k : ℕ)
    (X : Finset (ι → S)) (ts : Fin (starSize ι k) → Commit × Resp) : ProbComp Wit :=
  ext x (ts 0).1 (Finset.univ.image fun i => (starPoints k X i, (ts i).2))

/-- The extractor: the coordinate-wise finder against verdicts of complete reruns, recovery of the
transcripts from its runs, and the coordinate-wise extractor. -/
@[expose] noncomputable def coordRecover [SampleableType (ι → S)] [DecidableEq Resp]
    (σ : SigmaProtocol Stmt Wit Commit St (ι → S) Resp rel)
    (ext : Stmt → Commit → Finset ((ι → S) × Resp) → ProbComp Wit) (x : Stmt) (k : ℕ) :
    OracleComp (unifSpec + rerunSpec (ι → S) (Commit × Resp)) (Option Wit) :=
  recoverCached (fun c t => σ.verify x t.1 c t.2) (coordFinder (ι := ι) (S := S) k)
    (starPoints k) (coordExt ext x k)

/-- **Lemma 7.1 of Fenzi–Moghaddas–Nguyen at `μ = 1`, against a frozen prover.** A valid witness
comes back with probability at least the prover's acceptance probability, averaged over challenge
vectors, minus `ℓ(k - 1)/|S|`, after at most `1 + ℓ(k - 1)` complete runs in expectation. -/
theorem coord_recover [SampleableType (ι → S)] [DecidableEq Resp]
    (σ : SigmaProtocol Stmt Wit Commit St (ι → S) Resp rel)
    (ext : Stmt → Commit → Finset ((ι → S) × Resp) → ProbComp Wit) (x : Stmt) (k : ℕ)
    (hss : σ.CoordSpeciallySoundAt k ext x)
    (commit : ProbComp (Commit × St)) (respond : St → (ι → S) → ProbComp Resp) :
    (∑ c, Pr{let t ← proverRun commit respond c}[σ.verify x t.1 c t.2 = true]) /
          Fintype.card (ι → S) - (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S ≤
        Pr{let z ← fixedTape.attempt (proverRun commit respond) (coordRecover σ ext x k)}[
          ∃ w, z.1 = some w ∧ rel x w = true] ∧
      expectedCalls (fixedTape.attempt (proverRun commit respond) (coordRecover σ ext x k)) ≤
        1 + Fintype.card ι * (k - 1 : ℕ) := by
  have hcoins : ∀ c, (simulateQ (coins (S := Unit)) (proverRun commit respond c)).run' () =
      proverRun commit respond c := fun c => by simp [coins]
  have hb := fixedTape.recoverCached_bounds_sub (proverRun commit respond)
    (fun c t => σ.verify x t.1 c t.2) (isFinder_coordFinder (ι := ι) (S := S) k) (starPoints k)
    (fun _ X hX i => hX.2 _ (starPoints_mem k X hX.1.2 i)) (coordExt ext x k)
    (fun w => rel x w = true) ?_
  · simp only [pure_bind, hcoins] at hb
    exact hb
  · rintro F hF X ⟨hX, hacc⟩ w hw
    have hcommit : ∀ i, (F (starPoints k X i)).1 = (F (starPoints k X 0)).1 := fun i =>
      fixedTape.eagerTable_fst_eq (Q := ι → S) (S := Commit × St) (A := Commit) (B := Resp)
        commit Prod.fst (fun s c => respond s.2 c) hF _ _
    refine hss (F (starPoints k X 0)).1 _ ⟨?_, ?_⟩ w hw
    · intro p hp
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
      have h := hacc _ (starPoints_mem k X hX.2 i)
      simp only at h
      rw [hcommit i] at h
      exact h
    · have himage : (Finset.univ.image fun i => (starPoints k X i, (F (starPoints k X i)).2)).image
          Prod.fst = X := by
        rw [Finset.image_image]
        exact image_starPoints k X hX.2
      rw [himage]
      exact hX

end VCVioTest.CoordinateExtraction
