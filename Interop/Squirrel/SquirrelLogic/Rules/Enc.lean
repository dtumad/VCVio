/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import SquirrelLogic.Global
public import SquirrelLogic.OneTimeGame
import SquirrelLogic.ProductTape
import VCVio.OracleComp.EvalDist.Measure

/-!
# Encryption from one-time IND-CPA

BC14's axiom EncCCA1 (§7, Fig. 2; sound by Prop. 3) where the secret key is never used to decrypt:
if an asymmetric encryption scheme is IND-CPA secure, the encryptions of two messages under a
fresh key and fresh coins are indistinguishable, next to the public key and a context that uses
the secret key only through the public key:

```
pk(nk), enc(m₀; r, pk(nk)), u⃗ ∼ pk(nk), enc(m₁; r, pk(nk)), u⃗
```

It differs from EncCCA1 in three ways. There is no decryption, so IND-CPA replaces IND-CCA1. The
messages are values of one type, and the scheme's message space is that whole type, so BC14's
equal-length guard `EQL(u, u′)` is not needed. Both sides use the same coin name, which is BC14's
pair `r, r′` up to name renaming. LICS23's G.CCA1 (Prop. 19) is the real-or-zero form of the same
rule, against `aenc (zero (len m))`.

* `EncSymbols D` names the scheme in a declaration: a key name `nk` and a coin name `r`, each at
  an honest constant index, and honest symbols `pkOf` and `encOf`.
* `EncSymbols.scheme E M η` is the scheme a model implements: key generation draws the key
  coordinate's coin and applies `pkOf` to its sample, and encryption draws the coin coordinate's
  coin and applies `encOf`.
* The messages and the context are terms with one free variable standing for the public key,
  closed by substituting `pk(nk)` (`EncSymbols.challenge`). This is BC14's constraint that the
  secret key occur only in decryption position, with no decryption: `nk` occurs only under `pk`.
  The freshness constraints are semantic (`EncSymbols.Avoids`): the values of the messages and the
  context do not depend on the key coordinate or the coin coordinate of the honest tape.
* `EncSymbols.encReduction` is the named reduction. Given the public key it draws both tapes
  itself, evaluates the messages and the context at the public key, and runs the distinguisher on
  the challenge ciphertext with the attacker tape it drew. It never inverts the public key.

`EncSymbols.advantage_challenge` is the concrete statement: at every `η` the distinguisher's
advantage between the two challenge vectors equals the one-time IND-CPA advantage of the
reduction, with factor one. The coupling is `prEvent_uniformSample_update_update`: the game's key
and coins, written into the reduction's own honest tape, give a uniform tape.

`Valid.equiv_enc` is the rule, from the IND-CPA hypothesis for the image of the class under the
reduction. The runtime `ProbCompRuntime.probComp` imposes no time or query bound, so the
hypothesis bounds every image of an admitted distinguisher, however slow: efficiency enters only
through the class `C`, as a hypothesis on the reductions of its members.
-/

public section

namespace SquirrelLogic

open IPFunctor IPFunctor.ScopedSignature AsymmEncAlg

variable {B : Type} {D : Decl B}

/-- The symbols of an asymmetric encryption scheme in a declaration: a key name and a coin name,
each at an honest constant index, the public key of a key, and the encryption of a message with
coins under a public key. -/
structure EncSymbols (D : Decl B) where
  /-- The index type of the key name. -/
  keyIdx : Ty B
  /-- The type of keys. -/
  keyTy : Ty B
  /-- The index type of the coin name. -/
  coinIdx : Ty B
  /-- The type of encryption coins. -/
  coinTy : Ty B
  /-- The type of public keys. -/
  pkTy : Ty B
  /-- The type of messages. -/
  msgTy : Ty B
  /-- The type of ciphertexts. -/
  cTy : Ty B
  /-- The key name `nk`. -/
  nk : D.Name keyIdx keyTy
  /-- The index at which the key name is read. -/
  ik : D.Fn keyIdx
  /-- The coin name `r`. -/
  nr : D.Name coinIdx coinTy
  /-- The index at which the coin name is read. -/
  ir : D.Fn coinIdx
  /-- The public key of a key. -/
  pkOf : D.Fn (.arrow keyTy pkTy)
  /-- Encryption of a message with coins under a public key. -/
  encOf : D.Fn (.arrow msgTy (.arrow coinTy (.arrow pkTy cTy)))

namespace EncSymbols

variable (E : EncSymbols D)

/-- The key name with its types. -/
abbrev keyName : (a : Ty B) × (b : Ty B) × D.Name a b := ⟨_, _, E.nk⟩

/-- The coin name with its types. -/
abbrev coinName : (a : Ty B) × (b : Ty B) × D.Name a b := ⟨_, _, E.nr⟩

/-- The coordinate of the honest tape that the key reads. -/
abbrev keySlot (M : Model D) (η : ℕ) : M.Slot η := ⟨E.keyName, M.fn η E.ik⟩

/-- The coordinate of the honest tape that the coins read. -/
abbrev coinSlot (M : Model D) (η : ℕ) : M.Slot η := ⟨E.coinName, M.fn η E.ir⟩

/-! ## Syntax -/

/-- The public key `pk(nk)`. -/
@[expose] def pkTerm : FTerm D [] E.pkTy :=
  FTerm.app (FTerm.fn E.pkOf) (FTerm.name E.nk (FTerm.fn E.ik))

/-- The coins `r`. -/
@[expose] def coinTerm : FTerm D [] E.coinTy := FTerm.name E.nr (FTerm.fn E.ir)

/-- The encryption of `m` with the coins `r` under `pk(nk)`. -/
@[expose] def encTerm (m : FTerm D [] E.msgTy) : FTerm D [] E.cTy :=
  FTerm.app (FTerm.app (FTerm.app (FTerm.fn E.encOf) m) E.coinTerm) E.pkTerm

/-- The challenge vector `pk(nk), enc(m{x ↦ pk(nk)}; r, pk(nk)), u⃗{x ↦ pk(nk)}`, for a message and
a context whose free variable `x` stands for the public key. -/
@[expose] def challenge {τs : List (Ty B)} (m : FTerm D [.loc E.pkTy] E.msgTy)
    (u : Vec D [.loc E.pkTy] τs) : Vec D [] (E.pkTy :: E.cTy :: τs) :=
  Env.cons E.pkTerm (Env.cons (E.encTerm (m.substOne E.pkTerm))
    fun _ x => (u _ x).substOne E.pkTerm)

/-! ## Semantics -/

/-- A term reads neither the key coordinate nor the coin coordinate of the honest tape: at every
value of its free variable, its value depends only on the attacker tape and the other honest
coordinates. -/
@[expose] def Avoids (M : Model D) {τ : Ty B} (t : FTerm D [.loc E.pkTy] τ) : Prop :=
  ∀ η ρa (ρh ρh' : M.TapeH η),
    (∀ k, k ≠ E.keySlot M η → k ≠ E.coinSlot M η → ρh k = ρh' k) →
      ∀ x, FTerm.evalAt M η (ρa, ρh) t x = FTerm.evalAt M η (ρa, ρh') t x

/-- The scheme a model implements at `η`: key generation draws a key coin and applies `pkOf` to
its sample, and encryption draws a coin and applies `encOf`. There is no secret key, and
decryption, which the IND-CPA game never runs, rejects every ciphertext. -/
@[expose] def scheme (M : Model D) (η : ℕ) :
    AsymmEncAlg ProbComp (E.msgTy.Value M.carrier η) (E.pkTy.Value M.carrier η) Unit
      (E.cTy.Value M.carrier η) where
  keygen := do
    let kc ← $ᵗ (M.Coin η E.keyTy)
    pure (M.fn η E.pkOf (M.sample η E.keyTy kc), ())
  encrypt pk m := do
    let rc ← $ᵗ (M.Coin η E.coinTy)
    pure (M.fn η E.encOf m (M.sample η E.coinTy rc) pk)
  decrypt _ _ := pure none

/-- **The reduction** from a distinguisher of the challenge vectors to a one-time IND-CPA
adversary. Given the public key, it draws both tapes, evaluates the two messages at the public
key and keeps the key and the tapes; given the ciphertext, it evaluates the context at the public
key and runs the distinguisher with the attacker tape it drew. -/
@[expose] noncomputable def encReduction {M : Model D} {τs : List (Ty B)}
    (m₀ m₁ : FTerm D [.loc E.pkTy] E.msgTy) (u : Vec D [.loc E.pkTy] τs)
    (A : Distinguisher M (E.pkTy :: E.cTy :: τs)) (η : ℕ) :
    IND_CPA_OneTime_Adversary (E.scheme M η) where
  State := E.pkTy.Value M.carrier η × M.Tape η
  chooseMessages pk := do
    let ρ ← $ᵗ (M.Tape η)
    pure (FTerm.evalAt M η ρ m₀ pk, FTerm.evalAt M η ρ m₁ pk, (pk, ρ))
  distinguish st c := pure (A η
    (Env.cons st.1 (Env.cons c fun _ x => FTerm.evalAt M η st.2 (u _ x) st.1)) st.2.1)

variable {E}

/-- The challenge vector at `(η, ρ)`: the public key of the key coordinate's sample, the
encryption of the message read at that public key with the coin coordinate's sample, and the
context read at that public key. -/
theorem rv_challenge {M : Model D} (C : AdvClass M) {τs : List (Ty B)}
    (m : FTerm D [.loc E.pkTy] E.msgTy) (u : Vec D [.loc E.pkTy] τs)
    (env : Env (Kind.Value M) []) (η : ℕ) (ρ : M.Tape η) :
    Vec.rv M C (E.challenge m u) env η ρ =
      Env.cons (M.fn η E.pkOf (M.sample η E.keyTy (ρ.2 (E.keySlot M η))))
        (Env.cons (M.fn η E.encOf
            (FTerm.evalAt M η ρ m (M.fn η E.pkOf (M.sample η E.keyTy (ρ.2 (E.keySlot M η)))))
            (M.sample η E.coinTy (ρ.2 (E.coinSlot M η)))
            (M.fn η E.pkOf (M.sample η E.keyTy (ρ.2 (E.keySlot M η)))))
          fun _ x => FTerm.evalAt M η ρ (u _ x)
            (M.fn η E.pkOf (M.sample η E.keyTy (ρ.2 (E.keySlot M η))))) := by
  funext τ x
  cases x with
  | zero => rfl
  | succ x =>
    cases x with
    | zero =>
      exact congrArg (fun y => M.fn η E.encOf y _ _)
        (FTerm.denote_substOne_apply M C m E.pkTerm env η ρ)
    | succ x => exact FTerm.denote_substOne_apply M C (u _ x) E.pkTerm env η ρ

/-- One branch of the game is an event of the uniform tape: the game's key coin and encryption
coin, written into the reduction's honest tape, make it uniform. -/
private theorem prEvent_branch (hkr : E.keyName ≠ E.coinName) {M : Model D} (C : AdvClass M)
    {τs : List (Ty B)} {m₀ m₁ : FTerm D [.loc E.pkTy] E.msgTy} {u : Vec D [.loc E.pkTy] τs}
    (hm₀ : E.Avoids M m₀) (hm₁ : E.Avoids M m₁) (hu : ∀ τ x, E.Avoids M (u τ x))
    (A : Distinguisher M (E.pkTy :: E.cTy :: τs)) (env : Env (Kind.Value M) []) (η : ℕ)
    (b : Bool) :
    Pr{let z ← IND_CPA_OneTime_Branch (E.scheme M η) (E.encReduction m₀ m₁ u A η) b}[z = true] =
      Pr{let ρ ← $ᵗ (M.Tape η)}[
        A η (Vec.rv M C (E.challenge (if b then m₀ else m₁) u) env η ρ) ρ.1 = true] := by
  classical
  have key := prEvent_uniformSample_update_update (β := M.TapeA η)
    (α := fun k : M.Slot η => M.Coin η k.1.2.1) (E.keySlot M η) (E.coinSlot M η)
    (fun ρ : M.Tape η => A η (Vec.rv M C (E.challenge (if b then m₀ else m₁) u) env η ρ) ρ.1 = true)
  refine Eq.trans ?_ key
  simp only [IND_CPA_OneTime_Branch, scheme, encReduction, prEvent_norm]
  refine congrArg prEvent (bind_congr fun kc => bind_congr fun ρ => ?_)
  refine congrArg (· <$> _) (funext fun rc => ?_)
  have hks : E.keySlot M η ≠ E.coinSlot M η := fun h => hkr (congrArg Sigma.fst h)
  have hk : Function.update (Function.update ρ.2 (E.keySlot M η) kc) (E.coinSlot M η) rc
      (E.keySlot M η) = kc := by
    rw [Function.update_of_ne hks, Function.update_self]
  have hr : Function.update (Function.update ρ.2 (E.keySlot M η) kc) (E.coinSlot M η) rc
      (E.coinSlot M η) = rc := Function.update_self _ _ _
  have hav : ∀ {τ : Ty B} {t : FTerm D [.loc E.pkTy] τ}, E.Avoids M t → ∀ x,
      FTerm.evalAt M η (ρ.1, Function.update (Function.update ρ.2 (E.keySlot M η) kc)
        (E.coinSlot M η) rc) t x = FTerm.evalAt M η ρ t x := fun ht x =>
    ht η ρ.1 _ ρ.2 (fun k h₁ h₂ => by rw [Function.update_of_ne h₂, Function.update_of_ne h₁]) x
  simp only [rv_challenge, hk, hr, hav (hu _ _)]
  cases b <;> simp [hav hm₀, hav hm₁]

/-- **The concrete statement.** At every `η`, a distinguisher's advantage between the two
challenge vectors is the one-time IND-CPA advantage of `encReduction`, with factor one. -/
theorem advantage_challenge (hkr : E.keyName ≠ E.coinName) {M : Model D} (C : AdvClass M)
    {τs : List (Ty B)} {m₀ m₁ : FTerm D [.loc E.pkTy] E.msgTy} {u : Vec D [.loc E.pkTy] τs}
    (hm₀ : E.Avoids M m₀) (hm₁ : E.Avoids M m₁) (hu : ∀ τ x, E.Avoids M (u τ x))
    (A : Distinguisher M (E.pkTy :: E.cTy :: τs)) (env : Env (Kind.Value M) []) (η : ℕ) :
    advantage A (Vec.rv M C (E.challenge m₀ u) env) (Vec.rv M C (E.challenge m₁ u) env) η =
      IND_CPA_OneTime_Advantage (E.scheme M η) ProbCompRuntime.probComp
        (E.encReduction m₀ m₁ u A η) := by
  rw [IND_CPA_OneTime_Advantage_probComp_eq_absDiff, prEvent_branch hkr C hm₀ hm₁ hu A env η,
    prEvent_branch hkr C hm₀ hm₁ hu A env η]
  rfl

end EncSymbols

/-- **Encryption from one-time IND-CPA** (BC14 §7, axiom EncCCA1 without decryption, Prop. 3;
LICS23 G.CCA1, Prop. 19, in left-or-right form):

```
pk(nk), enc(m₀; r, pk(nk)), u⃗ ∼ pk(nk), enc(m₁; r, pk(nk)), u⃗
```

where the messages and the context are closed by substituting `pk(nk)` for their free variable.

* The key and coin names are distinct (`hkr`), and in every admitted model the messages and the
  context read neither the key coordinate nor the coin coordinate (`hR`): `nk` occurs only under
  `pk`, and `r` is fresh.
* `hcpa` is the assumption, about the image of the class under the named reduction
  `EncSymbols.encReduction`: every admitted distinguisher becomes a one-time IND-CPA adversary of
  negligible advantage against the scheme the model implements.
* `ProbCompRuntime.probComp` imposes no time or query bound on the reduction, so `hcpa` asserts
  security against the reductions of every admitted distinguisher, however slow. Efficiency
  enters only through the class: `hcpa` is plausible only when `C` admits efficient machines and
  the reduction preserves efficiency.

The proof is `EncSymbols.advantage_challenge`, an equality at every `η`. -/
theorem Valid.equiv_enc (E : EncSymbols D) (hkr : E.keyName ≠ E.coinName)
    {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M} {Θ : List (Form D [])}
    {τs : List (Ty B)} {m₀ m₁ : FTerm D [.loc E.pkTy] E.msgTy} {u : Vec D [.loc E.pkTy] τs}
    (hR : ∀ M, R M → E.Avoids M m₀ ∧ E.Avoids M m₁ ∧ ∀ τ x, E.Avoids M (u τ x))
    (hcpa : ∀ M : Model D, M.RespectsLabels → R M →
      ∀ A : Distinguisher M (E.pkTy :: E.cTy :: τs), (C M).distinguishes A →
        negligible fun η => IND_CPA_OneTime_Advantage (E.scheme M η) ProbCompRuntime.probComp
          (E.encReduction m₀ m₁ u A η)) :
    Valid R C Θ (.equiv (E.challenge m₀ u) (E.challenge m₁ u)) := by
  intro M hl hRM env _
  obtain ⟨hm₀, hm₁, hu⟩ := hR M hRM
  exact Form.holds_equiv.2 fun A hA => negligible_of_le
    (fun η => (EncSymbols.advantage_challenge hkr (C M) hm₀ hm₁ hu A env η).le)
    (hcpa M hl hRM A hA)

/-! ## Instances, for derivations -/

/-- An instance of the encryption rule: the scheme's symbols, two messages and a context. -/
structure EncInstance (D : Decl B) where
  /-- The scheme's symbols. -/
  E : EncSymbols D
  /-- The types of the context. -/
  τs : List (Ty B)
  /-- The first message, with the public key free. -/
  m₀ : FTerm D [.loc E.pkTy] E.msgTy
  /-- The second message, with the public key free. -/
  m₁ : FTerm D [.loc E.pkTy] E.msgTy
  /-- The context, with the public key free. -/
  u : Vec D [.loc E.pkTy] τs

/-- The semantic hypotheses of `Valid.equiv_enc` for an instance: the side conditions in every
admitted model, and one-time IND-CPA security against the reductions of the admitted
distinguishers. -/
@[expose] def EncInstance.Holds (R : Model D → Prop) (C : ∀ M : Model D, AdvClass M)
    (e : EncInstance D) : Prop :=
  (∀ M, R M → e.E.Avoids M e.m₀ ∧ e.E.Avoids M e.m₁ ∧ ∀ τ x, e.E.Avoids M (e.u τ x)) ∧
    ∀ M : Model D, M.RespectsLabels → R M →
      ∀ A : Distinguisher M (e.E.pkTy :: e.E.cTy :: e.τs), (C M).distinguishes A →
        negligible fun η => IND_CPA_OneTime_Advantage (e.E.scheme M η) ProbCompRuntime.probComp
          (e.E.encReduction e.m₀ e.m₁ e.u A η)

end SquirrelLogic
