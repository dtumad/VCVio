/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import SquirrelLogic.Machine
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.EvalDist.ProbabilityBounds

/-!
# Query bounds and the guessing machine

CCS26's proof of Rw-Oracle (App. C.1, pp. 15–16) uses a polynomial `q(η)` bounding the number of
oracle calls of the adversary `A`, and a machine `B` that "samples `j` uniformly between `1` and
`q(η)`, independently of the randomness used by `A` (i.e. using a part of `ρa` further away)",
and runs `A_j`, which "simulates `A` until its `j`-th oracle call, and returns the input of that
call".

* **Query bounds.** `Machine.QueryBound A q`: on every path, at every `η`, `A` makes at most
  `q η` queries to its inputs (VCVio's `IsQueryBoundP`; tape reads are not counted). Each program
  construction keeps a bound (`Machine.QueryBound.rename`, `.subst`, …): a handler multiplies it
  by the number of queries its answers make (`OracleComp.isQueryBoundP_simulateQ`).
* **The guessing machine.** `Machine.guess off k ha A d` reads the `k η` bits of the tape from bit
  `off η` as a number `j < 2 ^ k η` (`bitsEquiv`), runs `A` logging its queries (VCVio's
  `withQueryLog`), and returns the argument of the `j`-th query to its first input, an oracle of
  type `a → b`, or `d`'s value if there is no such query (CCS26's "default value"). Running `A`
  to the end and reading its log gives the same output as stopping at the `j`-th call.
  `Machine.run_guess` says what it computes.
* **Identical until bad, on one path** (`Machine.run_cons_eq_of_firstArgs`): with the oracle
  `o₁` replaced by `o₂`, a run that queried `o₁` only where the two agree is unchanged.
* **Exact uniformity.** `k` bits spell a uniform number below `2 ^ k`, not below `q`. Rounding `q`
  up to a power of two (`k = ⌈log₂ q⌉`, `Nat.clog`) costs a factor below `2`.
  `sum_prEvent_eq_two_pow_mul` is the averaging step: when the events `E j` read the attacker
  tape only below `off`, the sum of their probabilities for `j < 2 ^ k` is `2 ^ k` times the
  probability of `E j` at the number the bits `[off, off + k)` spell. Its proof is one
  involution of (bits, tape), which swaps the drawn bits with that block.
* **The guessing bound** (`prEvent_faulty_le`): the probability that the run with `o` queries a
  point where `o` and `o'` differ is at most `2 ^ k` times the probability that the guessing
  machine outputs such a point. This is CCS26's step 2, with `2 ^ k` in place of `q(η)`.
-/

public section

namespace SquirrelLogic

open IPFunctor IPFunctor.ScopedSignature OracleComp OracleSpec

variable {B : Type} {D : Decl B} {M : Model D} {η : ℕ} {τs τs' : List (Ty B)} {a b β γ : Ty B}

/-! ## Query bounds -/

/-- At most `q η` queries to the inputs, on every path of the program, at every `η` (VCVio's
`IsQueryBoundP` at the input queries; tape reads are not counted). -/
@[expose] def Machine.QueryBound (A : Machine M τs β) (q : ℕ → ℕ) : Prop :=
  ∀ η, (A η).IsQueryBoundP (fun t => t.isRight = true) (q η)

/-- Every answer of the handler makes at most `k` queries to the inputs. -/
def Handler.QueryBound (H : Handler M η τs τs') (k : ℕ) : Prop :=
  ∀ τ x q, (H τ x q).IsQueryBoundP (fun t => t.isRight = true) k

namespace Machine

theorem isQueryBoundP_read (i n : ℕ) :
    (read (M := M) (η := η) (τs := τs) i).IsQueryBoundP (fun t => t.isRight = true) n :=
  (isQueryBoundP_query_iff (spec := M.Iface η τs) _ (.inl i) n).2 (by simp)

theorem isQueryBoundP_ask (q : M.InQuery η τs) :
    (ask q).IsQueryBoundP (fun t => t.isRight = true) 1 :=
  (isQueryBoundP_query_iff (spec := M.Iface η τs) _ (.inr q) 1).2 fun _ => Nat.one_pos

theorem isQueryBoundP_fetch (y : ScopedVar τs a) (ha : a.IsGround) :
    (fetch (M := M) (η := η) y ha).IsQueryBoundP (fun t => t.isRight = true) 1 := by
  rw [fetch, isQueryBoundP_map_iff]
  exact isQueryBoundP_ask _

theorem isQueryBoundP_readBits :
    ∀ n k : ℕ, (readBits (M := M) (η := η) (τs := τs) n k).IsQueryBoundP
      (fun t => t.isRight = true) 0
  | _, 0 => by rw [readBits]; simp
  | n, k + 1 => by
    rw [readBits]
    exact isQueryBoundP_bind_le (m := 0) (isQueryBoundP_read n 0) (fun _ =>
      isQueryBoundP_bind_le (m := 0) (isQueryBoundP_readBits (n + 1) k) (fun _ => by simp)
        (by omega)) (by omega)

theorem isQueryBoundP_fetchVals : ∀ {Ξ : List (Ty B)} (r : Renaming Ξ τs)
    (h : ∀ τ ∈ Ξ, τ.IsGround),
    (fetchVals (M := M) (η := η) r h).IsQueryBoundP (fun t => t.isRight = true) Ξ.length
  | [], _, _ => by rw [fetchVals]; simp
  | _ :: _, _, _ => by
    rw [fetchVals]
    exact isQueryBoundP_bind_le (isQueryBoundP_fetch _ _) (fun _ =>
      isQueryBoundP_bind_le (m := 0) (isQueryBoundP_fetchVals _ _) (fun _ => by simp) le_rfl)
        (by simp [Nat.add_comm])

end Machine

namespace Handler

theorem queryBound_fwd (r : Renaming τs τs') : (fwd r : Handler M η τs τs').QueryBound 1 :=
  fun _ _ _ => Machine.isQueryBoundP_ask _

theorem queryBound_ofVals (v : Vals M η τs) (k : ℕ) :
    (ofVals v : Handler M η τs τs').QueryBound k :=
  fun _ _ _ => trivial

theorem QueryBound.mono {H : Handler M η τs τs'} {k k' : ℕ} (h : H.QueryBound k) (hk : k ≤ k') :
    H.QueryBound k' :=
  fun τ x q => (h τ x q).mono hk

theorem QueryBound.cons {k : ℕ}
    {H : Vals M η a.args → OracleComp (M.Iface η τs') (a.res.Value M.carrier η)}
    {H' : Handler M η τs τs'} (h : ∀ q, (H q).IsQueryBoundP (fun t => t.isRight = true) k)
    (h' : H'.QueryBound k) : Handler.QueryBound (Env.cons H H' : Handler M η (a :: τs) τs') k := by
  intro _ x q
  cases x with
  | zero => exact h q
  | succ x => exact h' _ x q

theorem QueryBound.append {k : ℕ} {H₂ : Handler M η τs τs'} :
    ∀ {Ξ : List (Ty B)} {H₁ : Handler M η Ξ τs'}, H₁.QueryBound k → H₂.QueryBound k →
      Handler.QueryBound (Env.append H₁ H₂ : Handler M η (Ξ ++ τs) τs') k
  | [], _, _, h₂ => h₂
  | _ :: _, _, h₁, h₂ => by
    intro _ x q
    cases x with
    | zero => exact h₁ _ .zero q
    | succ x => exact QueryBound.append (fun _ y q => h₁ _ y.succ q) h₂ _ x q

/-- Interpreting a program through a handler multiplies its bound on input queries by the bound
on its answers. -/
theorem QueryBound.isQueryBoundP_simulateQ {k n : ℕ} {α : Type} {H : Handler M η τs τs'}
    (hH : H.QueryBound k) {oa : OracleComp (M.Iface η τs) α}
    (h : oa.IsQueryBoundP (fun t => t.isRight = true) n) :
    (simulateQ H.impl oa).IsQueryBoundP (fun t => t.isRight = true) (n * k) :=
  OracleComp.isQueryBoundP_simulateQ _ (fun t => by
    rcases t with i | ⟨τ, x, q⟩
    · exact Machine.isQueryBoundP_read (M := M) (η := η) (τs := τs') i _
    · exact hH τ x q) h

end Handler

namespace Machine

variable {q q' : ℕ → ℕ}

theorem QueryBound.mono {A : Machine M τs β} (h : A.QueryBound q) (hq : ∀ η, q η ≤ q' η) :
    A.QueryBound q' :=
  fun η => (h η).mono (hq η)

theorem QueryBound.handle {A : Machine M τs β} {H : ∀ η, Handler M η τs τs'} {k : ℕ → ℕ}
    (hA : A.QueryBound q) (hH : ∀ η, (H η).QueryBound (k η)) :
    (A.handle H).QueryBound fun η => q η * k η :=
  fun η => (hH η).isQueryBoundP_simulateQ (hA η)

theorem QueryBound.rename {A : Machine M τs β} (hA : A.QueryBound q) (r : Renaming τs τs') :
    (A.rename r).QueryBound q :=
  (hA.handle fun _ => Handler.queryBound_fwd r).mono fun _ => (Nat.mul_one _).le

theorem QueryBound.app {A : Machine M (b :: τs) β} (hA : A.QueryBound q) (ha : a.IsGround) :
    (A.app ha).QueryBound fun η => q η * 2 :=
  hA.handle fun _ => Handler.QueryBound.cons
    (fun _ => isQueryBoundP_bind_le (isQueryBoundP_fetch _ ha) (fun _ => isQueryBoundP_ask _)
      le_rfl)
    ((Handler.queryBound_fwd _).mono (by norm_num))

theorem QueryBound.fn {A : Machine M (a :: τs) β} (hA : A.QueryBound q) (f : D.Fn a) :
    (A.fn f).QueryBound q :=
  (hA.handle fun _ => Handler.QueryBound.cons (fun _ => by simp)
    (Handler.queryBound_fwd _)).mono fun _ => (Nat.mul_one _).le

theorem QueryBound.subst {as : List (Ty B)} {ρ : Ty B} {A : Machine M (Ty.arrows as ρ :: τs) β}
    {K : Machine M (as ++ (ρ.args ++ τs)) ρ.res} (hA : A.QueryBound q) (hK : K.QueryBound q') :
    (A.subst K).QueryBound fun η => q η * (q' η + 1) :=
  hA.handle fun η => Handler.QueryBound.cons
    (fun _ => (isQueryBoundP_map_iff _ _ _).2 ((Handler.QueryBound.isQueryBoundP_simulateQ
      ((Handler.queryBound_ofVals _ 1).append ((Handler.queryBound_ofVals _ 1).append
        (Handler.queryBound_fwd _))) (hK η)).mono (by omega)))
    ((Handler.queryBound_fwd _).mono (by omega))

theorem QueryBound.branch {x y : Machine M τs β} (hx : x.QueryBound q) (hy : y.QueryBound q') :
    (branch x y).QueryBound fun η => 1 + (q η + q' η) := fun η => by
  unfold Machine.branch
  refine isQueryBoundP_bind_le (isQueryBoundP_ask _) (fun c => ?_) le_rfl
  cases c
  · exact ((hy.rename _) η).mono (Nat.le_add_left _ _)
  · exact ((hx.rename _) η).mono (Nat.le_add_right _ _)

theorem queryBound_const (c : Bool) : (const c : Machine M τs .bool).QueryBound q :=
  fun _ => by unfold const; simp

theorem queryBound_input (y : ScopedVar τs a) (ha : a.IsGround) :
    (input y ha : Machine M τs a).QueryBound fun _ => 1 :=
  fun _ => isQueryBoundP_fetch y ha

theorem queryBound_eqTest (hβ : β.IsGround) :
    (eqTest hβ : Machine M [β, β] .bool).QueryBound fun _ => 2 := fun _ => by
  unfold eqTest
  exact isQueryBoundP_bind_le (isQueryBoundP_fetch _ hβ) (fun _ =>
    isQueryBoundP_bind_le (m := 0) (isQueryBoundP_fetch _ hβ) (fun _ => by simp) le_rfl)
      (show 1 + (1 + 0) ≤ 2 by omega)

theorem QueryBound.shift {A : Machine M τs β} (hA : A.QueryBound q) (off : ℕ → ℕ) :
    (A.shift off).QueryBound q := fun η =>
  (OracleComp.isQueryBoundP_simulateQ (k := 1) _ (fun t => by
    rcases t with i | q
    · exact isQueryBoundP_read (M := M) (η := η) (τs := τs) (off η + i) _
    · exact isQueryBoundP_ask q) (hA η)).mono (Nat.mul_one _).le

theorem queryBound_sampler (b : Ty B) (hb : b.order ≤ 1) :
    (sampler b hb : Machine M b.args b.res).QueryBound fun _ => b.args.length := fun _ => by
  unfold sampler
  exact isQueryBoundP_bind_le (isQueryBoundP_readBits _ _) (fun _ =>
    isQueryBoundP_bind_le (m := 0) (isQueryBoundP_fetchVals _ _) (fun _ => by simp) le_rfl)
      (by simp)

end Machine

/-! ## The guessing machine -/

/-- `k` bits as a number below `2 ^ k`, least significant bit first: a bijection. -/
@[expose] def bitsEquiv (k : ℕ) : (Fin k → Bool) ≃ Fin (2 ^ k) :=
  (Equiv.arrowCongr (Equiv.refl (Fin k)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- The arguments of a query to the first input; tape reads and queries to the other inputs have
none. -/
@[expose] def Model.firstArg (M : Model D) {η : ℕ} {σ : Ty B} {Γ : List (Ty B)} :
    ℕ ⊕ M.InQuery η (σ :: Γ) → Option (Vals M η σ.args)
  | .inr ⟨_, .zero, q⟩ => some q
  | _ => none

/-- The arguments of the queries to the first input in a query log, oldest first. -/
@[expose] def Model.firstArgs (M : Model D) {η : ℕ} {σ : Ty B} {Γ : List (Ty B)}
    (log : QueryLog (M.Iface η (σ :: Γ))) : List (Vals M η σ.args) :=
  log.filterMap fun e => M.firstArg e.1

theorem Model.isRight_of_firstArg {σ : Ty B} {Γ : List (Ty B)} :
    ∀ (t : ℕ ⊕ M.InQuery η (σ :: Γ)), (M.firstArg t).isSome → t.isRight = true
  | .inl _, h => absurd h (by simp [Model.firstArg])
  | .inr _, _ => rfl

/-- The guessing machine of CCS26's proof of Rw-Oracle (App. C.1, p. 15): read the `k η` bits of
the attacker tape from bit `off η` as a number `j < 2 ^ k η`; run `A`, logging its queries; and
return the argument of the `j`-th query to its first input, an oracle of type `a → b` with `a` a
Boolean or base type, or `d`'s value if `A` made at most `j` such queries. -/
@[expose] def Machine.guess {Γ : List (Ty B)} (off k : ℕ → ℕ) (ha : a.IsGround)
    (A : Machine M (.arrow a b :: Γ) γ) (d : Machine M (.arrow a b :: Γ) a.res) :
    Machine M (.arrow a b :: Γ) a.res := fun η => do
  let c ← readBits (off η) (k η)
  let r ← (A η).withQueryLog
  ((M.firstArgs r.2)[(bitsEquiv (k η) c : ℕ)]?).elim (d η)
    fun q => pure (Ty.apply (q _ .zero) (Ty.groundArgs ha))

namespace Machine

variable {Γ : List (Ty B)} {ρa : M.TapeA η}

/-- The guessing machine returns the argument of the `j`-th query to the first input of `A`'s run,
for the number `j` that the bits `[off η, off η + k η)` of the tape spell, or `d`'s value. -/
theorem run_guess (off k : ℕ → ℕ) (ha : a.IsGround) (A : Machine M (.arrow a b :: Γ) γ)
    (d : Machine M (.arrow a b :: Γ) a.res) (e : Vals M η (.arrow a b :: Γ)) :
    (A.guess off k ha d).run η ρa e =
      ((M.firstArgs (runLog (M.answer ρa e) (A η)))[(bitsEquiv (k η)
          (M.bitsAt ρa (off η) (k η)) : ℕ)]?).elim (d.run η ρa e)
        fun q => Ty.apply (q _ .zero) (Ty.groundArgs ha) := by
  rw [run, guess, evalWithAnswerFn_bind, evalWithAnswerFn_readBits, evalWithAnswerFn_bind]
  change evalWithAnswerFn _ (Option.elim ((M.firstArgs (runLog (M.answer ρa e) (A η)))[(bitsEquiv
    (k η) (M.bitsAt ρa (off η) (k η)) : ℕ)]?) _ _) = _
  cases (M.firstArgs (runLog (M.answer ρa e) (A η)))[(bitsEquiv (k η)
    (M.bitsAt ρa (off η) (k η)) : ℕ)]? <;> rfl

/-- A machine making at most `q η` input queries logs at most `q η` queries to its first input. -/
theorem QueryBound.length_firstArgs_le {σ : Ty B} {A : Machine M (σ :: Γ) γ} {q : ℕ → ℕ}
    (hA : A.QueryBound q) (ρa : M.TapeA η) (e : Vals M η (σ :: Γ)) :
    (M.firstArgs (runLog (M.answer ρa e) (A η))).length ≤ q η :=
  length_filterMap_runLog_le _ (fun e => M.firstArg e.1)
    (fun e he => M.isRight_of_firstArg e.1 he) (hA η)

/-- A machine reading below `bd` logs the same queries at two tapes that agree below `bd η`. -/
theorem ReadsBelow.runLog_eq {A : Machine M τs β} {bd : ℕ → ℕ} (hA : A.ReadsBelow bd)
    {ρa ρa' : M.TapeA η} (hρ : ∀ i < bd η, M.readBit ρa i = M.readBit ρa' i) (e : Vals M η τs) :
    runLog (M.answer ρa e) (A η) = runLog (M.answer ρa' e) (A η) :=
  (runLog_eq_of_allQueriesSatisfy _ (fun t ht => by
    rcases t with i | q
    · exact hρ i ht
    · rfl) (hA η)).1

/-- **Identical until bad, on one path** (CCS26 App. C.1, step 1): a machine whose first input is
the oracle `o₁` runs as with `o₂` in its place, when its run with `o₁` queries `o₁` only at points
where the two agree. -/
theorem run_cons_eq_of_firstArgs (A : Machine M (.arrow a b :: Γ) γ)
    {o₁ o₂ : (Ty.arrow a b).Value M.carrier η} {e : Vals M η Γ}
    (h : ∀ q ∈ M.firstArgs (runLog (M.answer ρa (Env.cons o₁ e)) (A η)),
      o₁ (q _ .zero) = o₂ (q _ .zero)) :
    A.run η ρa (Env.cons o₁ e) = A.run η ρa (Env.cons o₂ e) := by
  refine evalWithAnswerFn_eq_of_forall_mem_runLog _ (A η) fun ent hent => ?_
  obtain ⟨t, r⟩ := ent
  rcases t with i | ⟨τ, x, q⟩
  · rfl
  · cases x with
    | zero =>
      have hq : q ∈ M.firstArgs (runLog (M.answer ρa (Env.cons o₁ e)) (A η)) :=
        List.mem_filterMap.2 ⟨_, hent, rfl⟩
      change Ty.apply (o₁ (q _ .zero)) _ = Ty.apply (o₂ (q _ .zero)) _
      rw [h q hq]
    | succ x => rfl

end Machine

/-! ## Read and query bounds of the guessing machine -/

namespace Machine

variable {Γ : List (Ty B)}

theorem ReadsBelow.guess {A : Machine M (.arrow a b :: Γ) γ}
    {d : Machine M (.arrow a b :: Γ) a.res} {bd : ℕ → ℕ} (hA : A.ReadsBelow bd)
    (hd : d.ReadsBelow bd) (off k : ℕ → ℕ) (ha : a.IsGround) (hk : ∀ η, off η + k η ≤ bd η) :
    (A.guess off k ha d).ReadsBelow bd := fun η => by
  unfold Machine.guess
  refine allQueriesSatisfy_bind ((allQueriesSatisfy_readBits _ _).mono (tapeBelow_mono (hk η)))
    fun c => allQueriesSatisfy_bind (allQueriesSatisfy_withQueryLog (hA η)) fun r => ?_
  cases (M.firstArgs r.2)[(bitsEquiv (k η) c : ℕ)]? with
  | none => exact hd η
  | some q => exact allQueriesSatisfy_pure _ _

theorem QueryBound.guess {A : Machine M (.arrow a b :: Γ) γ}
    {d : Machine M (.arrow a b :: Γ) a.res} {q q' : ℕ → ℕ} (hA : A.QueryBound q)
    (hd : d.QueryBound q') (off k : ℕ → ℕ) (ha : a.IsGround) :
    (A.guess off k ha d).QueryBound fun η => q η + q' η := fun η => by
  unfold Machine.guess
  refine isQueryBoundP_bind_le (isQueryBoundP_readBits _ _) (fun c =>
    isQueryBoundP_bind_le (m := q' η) (isQueryBoundP_withQueryLog (hA η)) (fun r => ?_) le_rfl)
      (by simp)
  cases (M.firstArgs r.2)[(bitsEquiv (k η) c : ℕ)]? with
  | none => exact hd η
  | some q => simp

end Machine

/-! ## The uniform guess -/

/-- **Averaging over drawn bits.** Let the events `E j` depend on the attacker tape only through its
bits below `off`, and let the `k` bits from `off` fit on the tape. Over uniform tapes, the sum of
the probabilities of `E j` for `j < 2 ^ k` is `2 ^ k` times the probability of `E j` at the number
`j` that the bits `[off, off + k)` spell (`bitsEquiv`). The proof is the involution of (bits,
tape) that swaps the bits with that block of the tape. -/
theorem sum_prEvent_eq_two_pow_mul (off k : ℕ) (hk : off + k ≤ M.lenA η)
    (E : ℕ → M.Tape η → Prop)
    (hE : ∀ j ρa ρa' ρh, (∀ i < off, M.readBit ρa i = M.readBit ρa' i) →
      E j (ρa, ρh) → E j (ρa', ρh)) :
    ∑ j ∈ Finset.range (2 ^ k), Pr{let ρ ← $ᵗ (M.Tape η)}[E j ρ] =
      2 ^ k * Pr{let ρ ← $ᵗ (M.Tape η)}[E (bitsEquiv k (M.bitsAt ρ.1 off k)) ρ] := by
  let σf : (Fin k → Bool) × M.Tape η → (Fin k → Bool) × M.Tape η := fun x =>
    (M.bitsAt x.2.1 off k, (M.setBlock off x.2.1 x.1, x.2.2))
  have hσ : Function.Involutive σf := fun x => by
    simp only [σf, M.bitsAt_setBlock _ _ _ hk, Model.setBlock_setBlock, Model.setBlock_bitsAt]
  -- The joint probability of `E (j c) ρ`, with `c` drawn, is that of `E (j (bits of ρ)) ρ`.
  have h1 : Pr{let x ← $ᵗ ((Fin k → Bool) × M.Tape η)}[E (bitsEquiv k x.1) x.2] =
      Pr{let ρ ← $ᵗ (M.Tape η)}[E (bitsEquiv k (M.bitsAt ρ.1 off k)) ρ] := by
    rw [← SampleableType.prEvent_uniformSample_equiv (Function.Involutive.toPerm σf hσ)]
    refine (prEvent_congr _ _ (fun x => E (bitsEquiv k (M.bitsAt x.2.1 off k)) x.2)
      fun x => ⟨hE _ _ _ _ fun i hi => M.readBit_setBlock_of_lt _ _ hi,
        hE _ _ _ _ fun i hi => (M.readBit_setBlock_of_lt _ _ hi).symm⟩).trans ?_
    rw [SampleableType.prEvent_uniformSample_prod]
    dsimp only
    exact OracleComp.prEvent_bind_const ($ᵗ (Fin k → Bool)) _
  -- The joint probability is the average over the drawn bits.
  have h2 : Pr{let x ← $ᵗ ((Fin k → Bool) × M.Tape η)}[E (bitsEquiv k x.1) x.2] =
      ∑ c : Fin k → Bool, ((2 : ENNReal) ^ k)⁻¹ *
        Pr{let ρ ← $ᵗ (M.Tape η)}[E (bitsEquiv k c) ρ] := by
    rw [SampleableType.uniformSample_prod_eq_bind, prEvent_bind_eq_sum_fintype]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [SampleableType.prEvent_uniformSample_eq_singleton_natCard]
    congr 1
    · rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      push_cast
      rfl
    · rw [show (do let b ← $ᵗ (M.Tape η); pure (c, b) : ProbComp _) =
        Prod.mk c <$> ($ᵗ (M.Tape η)) from (map_eq_bind_pure_comp _ _ _).symm, prEvent_map]
  have h3 : ∑ j ∈ Finset.range (2 ^ k), Pr{let ρ ← $ᵗ (M.Tape η)}[E j ρ] =
      ∑ c : Fin k → Bool, Pr{let ρ ← $ᵗ (M.Tape η)}[E (bitsEquiv k c) ρ] := by
    rw [Finset.sum_range fun j => Pr{let ρ ← $ᵗ (M.Tape η)}[E j ρ]]
    exact (Equiv.sum_comp (bitsEquiv k)
      fun i : Fin (2 ^ k) => Pr{let ρ ← $ᵗ (M.Tape η)}[E i ρ]).symm
  rw [h3, ← h1, h2, ← Finset.mul_sum, ← mul_assoc,
    ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
    one_mul]

end SquirrelLogic
