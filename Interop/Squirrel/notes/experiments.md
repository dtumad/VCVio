# Phase A experiments

Experiments A1 and A2 of the plan for a deep embedding of Squirrel's logic on PolyFun. They were
run on 2026-11-16 in `VCVio.wt/squirrel-logic`, on branch `dtumad/squirrel-logic` at base
`7b3bfe49d`, with PolyFun at VCVio's pin `ea3b297`. The source is LICS23, the author report
pinned in `../SOURCES.md`.

## Build and checks

- **Library.** `lakefile.lean` gains `lean_lib SquirrelLogic` with `srcDir := "Interop/Squirrel"`
  and `roots := #[`SquirrelLogic]`. It is not a default target, and CI is unchanged.
- **Build.** `LEAN_NUM_THREADS=4 lake build SquirrelLogic` succeeds from a clean touch of every
  file, with no warnings. Each module takes about 2 s.
- **Axioms.** `#print axioms` was run on 22 headline declarations; the list is in the table
  below. They use only `propext`, `Classical.choice` and `Quot.sound`. `Term.denote_inl` uses
  only `Quot.sound`.
- **Forbidden tactics.** There is no `sorry`, `stop` or `native_decide`.
- **Comment fences.** `scripts/check-comment-fences.py` passes.
- **Not run.** `lake lint`, the axiom sweep and the test drivers were not run. They cover the
  default targets only.

| File | Role | Lines | Code lines |
|---|---|---|---|
| `SquirrelLogic/Sum.lean` | Generic: sums of signatures over shared sorts | 72 | 39 |
| `SquirrelLogic/Syntax.lean` | A1: types, labels, declarations, sorts, `localSig` | 188 | 81 |
| `SquirrelLogic/Model.lean` | A1: models, the pointwise reading `interp`, β, congruence | 215 | 110 |
| `SquirrelLogic/RandomVariable.lean` | A2: the random-variable reading `rvInterp`, locality | 129 | 76 |
| `SquirrelLogic/Global.lean` | A2: global syntax, atoms, validity, the rules | 344 | 179 |
| `SquirrelLogic/Derivation.lean` | D2 probe: derivations as data, soundness | 72 | 37 |
| `SquirrelLogic/Examples.lean` | A satisfying model, a negative case, a derived rule | 67 | 34 |

"Code lines" excludes blank lines, comments and docstrings.

## A1: the local core

### Built

- **Types.** `Ty B` has the constructors `bool`, `base b` and `arrow`.
- **Labels.** `Label` has `finite` and `fixed`. `Ty.HasLabel` lifts labels along arrows, as
  LICS23 §II-B.1 does.
- **Declarations.** `Decl B` declares labels on base types; names `n : τ₀ → τ₁` with
  `nameDom_finite`; honest symbols; and attacker symbols.
- **Sorts.** `Kind B` is `loc τ | glob`.
- **Signature.** `localSig D : ScopedSignature (Kind B)` has application, λ (the only binder),
  `ite`, `tt`, `ff`, `=_τ`, `∀_τ`, `∃_τ`, names, honest symbols and attacker symbols. Smart
  constructors are in `LTerm`.
- **Models.** `Model D extends TapeModel`:
  - carriers are nonempty `Set (List Bool)` per base type and `η`;
  - tapes `TapeA η` and `TapeH η` carry `SampleableType` fields;
  - names are `dom → TapeH η → cod`;
  - honest symbols are values, one per `η`;
  - attacker symbols are `TapeA η → τ`.
- **Pointwise reading.** `interp M η ρ : Interpretation (localSig D) (Kind.PtValue M η)` reads
  `bool` as `Bool` and arrows as full function spaces. `=_τ`, `∀_τ` and `∃_τ` are `decide` of the
  proposition, with `Classical.propDecidable`. Names read `ρ.2`, and attacker symbols read `ρ.1`.
- **Theorems.**
  - `LTerm.denote_app_lam` (β):
    `(app (lam body) v).denote (interp M η ρ) env = (body.substOne v).denote (interp M η ρ) env`.
  - `LTerm.denote_substOne_congr`: in any interpretation, if `t` and `u` mean the same, then
    `C.substOne t` and `C.substOne u` mean the same. This is the semantic core of L.Rewrite.
  - `LTerm.denote_substOne_of_eq`: the same, from `⟦t = u⟧ = true`.
  - `LTerm.denote_eq_app_of_eq` (FA congruence): from `⟦f = g⟧` and `⟦t = u⟧`, conclude
    `⟦f t = g u⟧`.
  - `denote_eq_eq_true` and `denote_all_eq_true` give the intended meaning of `=_τ` and `∀_τ`.
  - `Ty.finite_value` and `Ty.value_eq_of_fixed` say what the labels give in a model that
    respects them.

### Success criterion: met

The criterion was at most about 300 lines and no new traversal.

- **Size.** Syntax and Model together have 191 code lines, or 403 lines with docstrings.
- **No term induction is written.**
  - β is `Term.denote_substOne` rewritten with two reading lemmas that hold by `rfl`.
  - The congruence lemmas are `denote_substOne` used twice.
  - The only inductions are over types (`nonempty_value`, `finite_value`, `value_eq_of_fixed`)
    and over lists, for environments (`evalEnv_append` in A2).

### Choices

- **`Bool`, not `Prop`, for `bool`.** There are three reasons:
  - LICS23 fixes `M_bool(η) = {0, 1}`;
  - a conditional needs a decidable test;
  - `[φ]` needs the event `φ = false` under a uniform measure.

  With `Prop`, every conditional would need classical choice, and the event would be the same.
  The cost is that `=_τ`, `∀_τ` and `∃_τ` range over function spaces, so they decide
  classically. `interp` is therefore noncomputable, and lemmas pass the instance explicitly.
- **Carriers are sets of bitstrings, not `Type`s per `η`.** `fixed` is equality of carriers
  across `η`, and `const` needs a value common to all `η`. Neither can be stated for unrelated
  `Type`s. LICS23 itself gives each domain an injective encoding into bitstrings.
- **Declared variables.** LICS23's declared variables are split, and the split is recorded as
  ledger row L15:
  - names, honest symbols (tape-independent) and attacker symbols (reading `ρa`) are
    constructors;
  - declared variables with no restriction are the free variables of a term.

### Problems hit

1. **The sort type is `Kind B`, not `Ty B`.** A sum of signatures needs one sort type.
   - Embedding a `Ty`-sorted local signature into the `Kind`-sorted sum would use
     `ScopedSignature.Hom` and `Term.map` along `Kind.loc`. Both exist at the pin.
   - That needs a `denote_map` law, which the pin lacks.
   - `Hom.toReindexing` proves its child equations with `rw [List.map_append, h.binders]`, so
     `IFreeM.fold_reindex` would leave propositional casts in every meaning.

   So the local signature is over `Kind B` from the start. The cost is an unused sort and
   `nomatch` cases at `glob`.
2. **`Fin.elim0` does not elaborate as an argument family.** Passing it as the argument family
   of a nullary constructor fails against the dependent type
   `(p : Arg op) → Term (binders op p ++ Γ) (sort op p)`. `fun p => nomatch p` works.
3. **`Term.fold` needs an annotated motive.** Without `fun j : Judgment S => …`, it fails with
   "Invalid projection: Type of j is not known".
4. **`decide_eq_true_iff` fails on a classical `decide`.** It cannot synthesize the instance; it
   needs `@decide_eq_true_iff _ (Classical.propDecidable _)`.
5. **The reading lemmas cross the PolyFun boundary by `rfl`.** These are `denote_app`,
   `denote_lam`, `denote_ite`, `FTerm.denote_ite` and `Form.holds_box`.
   - Each unfolds `Term.denote` to `IFreeM.fold`, and `Env.append` on `[]` and `[a]`.
   - PolyFun at the pin has `denote_node`, but no `Env.append` equation lemmas (`append_nil`,
     `append_single`) and no `denote` fusion lemma.
   - `Term.denote_inl` also relies on `denote` being definitionally a fold.

   So the rule "cross library boundaries with equation lemmas, never `rfl`" cannot be followed
   yet. This is a gap for PolyFun to fill.

### Not done

- **Name restrictions.** LICS23 asks for independent samplings and polynomial-time samplers.
  These are ledger row L12.
- **Other labels.** The `large` and `polynomial` labels.
- **Recursive definitions.** Definition 1 and Proposition 1.
- **Generalized subterms.** These belong to A3.

## A2: the global layer

### Built

- **`Sum.lean`** (generic) gives `ScopedSignature.sum`, `Interpretation.sum`, `Term.inl` and
  `Term.denote_inl : (inl t).denote (alg₁.sum alg₂) ρ = t.denote alg₁ ρ`. The last is one
  `IFreeM.fold_fusion`, with no casts: on `Sum.inl` the sum's binders and sorts reduce
  definitionally.
- **`RandomVariable.lean`.**
  - `RV M τ = (η : ℕ) → M.Tape η → τ.Value M.carrier η`.
  - `Kind.Value M` is `RV` at `loc τ` and `Prop` at `glob`.
  - `RV.constAt η a` is LICS23's `1^η_a`.
  - `rvInterp M` is the paper's semantics: λ reads its variable as `1^η_a`.
  - **Locality**, `eval_denote_rvInterp`:
    `s.eval M η ρ (t.denote (rvInterp M) env) = t.denote (interp M η ρ) (evalEnv M η ρ env)`.
  - `LTerm.denote_rvInterp_app_lam` is β for random variables, in 3 lines from locality.
- **`Global.lean`.**
  - Syntax: `GlobalOp` has ⊤, ⊥, ∧, ∨, ⇒, `all τ`, `ex τ` (binding `loc τ`), `box`, `const τ`,
    `adv τ` and `equiv τs` (vectors). `fullSig D` is `(localSig D).sum (globalSig B)`.
  - Atoms:
    - `Overwhelming T φ := negligible fun η => Pr{let ρ ← $ᵗ (T.Tape η)}[φ η ρ = false]`;
    - `RV.IsConst`;
    - `AdvClass M`, with `computes` and `distinguishes`, gives `AdvClass.Adv` and
      `AdvClass.Indist`. The latter uses `ENNReal.absDiff` of the two acceptance probabilities.
  - Semantics: `fullInterp M C` and `Form.Holds`.
  - Validity:
    - `Valid R C Θ F` holds iff for every `M` with `M.RespectsLabels` and `R M`, and every `env`,
      if every `θ ∈ Θ` holds then `F` holds;
    - `LValid R C Θ Γl φ := Valid R C Θ (box (imp (conj Γl) φ))`.
  - Rules: seven, in the table below.
  - `eval_denote_fullInterp`: locality for local terms inside global formulas.
- **`Derivation.lean`**, a D2 probe: `Derivation D : List (Form D Γ) → Form D Γ → Type`, one
  constructor per proved rule. `Derivation.sound R C : Derivation D Θ F → Valid R C Θ F` holds for
  every restriction and every class. `Derivation.allInst` is a worked derivation.
- **`Examples.lean`.**
  - `Model.trivial D` has every carrier `{[]}` and unit tapes. It respects every label
    (`Model.trivial_respectsLabels`), so `Valid` does not range over an empty set of models.
  - `Valid.not_box_ff`: `¬ Valid (fun _ => True) C [] (box ff)`, so validity is not trivial.
  - `Valid.all_inst` derives instantiation from G.Cut, G.L-∀̃ and G.Axiom.

### The sum, not `ScopedFamily`

The sum worked, and the fallback was not needed. Global quantifiers bind variables of a local
sort; `[·]`, `const`, `adv` and `∼` take local arguments without binders; no argument changes a
parameter context. So one sort type is enough. `ScopedFamily` would be needed for binders of
type variables, that is, for polymorphism.

### Success criterion: met (at most 10 lines per rule)

| Rule (LICS23 Fig. 7) | Lean | Proof lines | What the proof uses |
|---|---|---|---|
| G.Axiom | `Valid.ax` | 1 | membership |
| G.Weak | `Valid.weaken` | 1 | subset |
| G.Cut | `Valid.cut` | 1 | `List.forall_mem_cons` |
| G.L-∀̃ (instantiation by a local term) | `Valid.all_left` | 5 | `Term.denote_substOne` |
| G.R-∀̃ | `Valid.all_right` | 5 | `Term.denote_rename` (hypotheses weakened) |
| L.ByGlob | `Valid.byGlob` | 3 | `Overwhelming.mono` (`prEvent_mono`, `negligible_of_le`) |
| G.ByLoc | `Valid.byLoc` | 1 (`h`) | definitional: `cond true x true` reduces |

`Derivation.sound` takes one line per rule.

### Problems and friction

1. **One carrier per sort forces the random-variable reading on local constructors.**
   - `∀̃` binds local variables over random variables, and `fullInterp` is a single
     interpretation. So `Kind.Value M (loc τ)` must be `RV M τ`, and A1's pointwise algebra
     cannot be reused directly.
   - `rvInterp` lifts it constructor by constructor, reading bound variables as `1^η_a`. This is
     the paper's own definition, which it calls an "artificial complexity" kept for uniformity.
   - The cost: nonempty carriers, and a classical choice for the value at other `η`.
   - The payoff: locality, proved with `IFreeM.fold_rel` in about 20 lines plus
     `evalEnv_append` (a list induction). Every pointwise law then transfers.
   - This is the plan's `denote_pointwise` (A6a), as a Squirrel-specific instance: the embedding
     differs by sort (`constAt` at `loc`, `True` at `glob`).
2. **Locality on `localSig` terms is not enough.** G.L-∀̃ substitutes into global formulas, which
   produces `fullSig` terms outside the image of `Term.inl`, and there is no `subst_inl` law.
   `eval_denote_fullInterp` fixes this: it reads global constructors pointwise as `PUnit`, at
   about 20 more lines. The two locality proofs repeat the same node step, and a generic lemma
   would remove the repetition.
3. **Dot notation fails on interpretations.** `(rvInterp M).sum (globalInterp M C)` fails with
   "Function.sum", because `Interpretation` is an abbreviation for a `∀`-type. The fix is to write
   `Interpretation.sum a b`.
4. **`∼` and `adv` are declared, and no rule about them is proved.**
   - The spike's `AdvClass` does not fit. Its adversaries are `ℕ → α → ProbComp β` with fixed
     `α`, `β`, but here `⟦τ⟧_η` depends on `η`. So `AdvClass M` is per model, with
     `η`-indexed typed functions that read `ρa`.
   - The distinguishers are deterministic given `ρa`, as in LICS23. This makes ledger row L10
     concrete: it is now a statement to relate to VCVio's fresh coins (A4).
   - The distinguishers see typed values (Lean functions at arrow types) instead of encodings and
     handles. This is ledger row L14.
5. **`const` at arrow types** is a logical relation, `Ty.Same`. It agrees with LICS23's
   `⋂_η ⟦τ⟧_η` at base types and at arrows from fixed types, and differs otherwise. This is
   ledger row L13.
6. **No friction** with `Overwhelming` over `$ᵗ (T.Tape η)`: the product instance from the two
   `SampleableType` fields applies. `prEvent_mono` gave L.ByGlob directly.

### Not done

- **L.R-∀**, by the choice construction of Proposition 2. `eval_denote_fullInterp` now makes it
  possible. It is the first rule that uses the random-variable semantics nontrivially, and the
  natural next test of the 10-line criterion.
- **G.Rewrite**, the `const` rules (Fig. 4), the rules of Fig. 3 and L.R-∀-const
  (Proposition 4).
- **Any rule about `∼`.**

## A3: the heads a term uses, and no telepathy (PolyFun)

### Built

On the PolyFun fork, branch `dtumad/squirrel-generic`, commit `a4eced98`, upstream base `462edc16`:

- `PolyFun/IPFunctor/Scoped/Uses.lean`:
  - `Head` and `Term.heads`, the set of constructors a term uses, as a fold;
  - `heads_rename`, `heads_subset_heads_subst`, `heads_subst_subset` and `heads_substOne_subset`,
    all proved with `fold_rel`;
  - Boolean decision procedures for finitary signatures;
  - `Term.denote_congr_of_agreeOn_heads`: interpretations that agree on the heads a term uses give
    it the same meaning.
- `PolyFun/IPFunctor/Scoped/Measure.lean` and `ToCslib/MeasureTheory/Integral/Marginal.lean`: if
  the heads a term uses ignore coordinate `i` of a product tape, its meaning equals coordinate `i`
  with probability at most the largest point mass of that coordinate (`1/|X i|` when uniform).
  This is the FRESH shape (`Term.pi_setOf_denote_eq_apply_le_inv_card`).
- Consumers:
  - the scoped-programs tutorial: let elimination removes every `let` and keeps the meaning;
  - `PolyFunTest/IPFunctor/Scoped/{Uses,Measure}.lean`, with a negative case: a program that reads
    the coordinate hits it with probability one.

### Success criterion: met

The FRESH-shaped bounds and the tutorial's theorem each apply the congruence lemma once, with no
induction over terms.

### Friction

- **`Head` must be a structure.** As a sigma type, instances are indexed by `σ.Op`, which a
  concrete signature unfolds, and instance search fails.
- **`deriving DecidableEq` needs exposing.** A language's derived instance is not exposed under
  the module system, so `decide` on heads from another module needs `@[expose] public section`.
  Squirrel's signature will need the same.
- **One induction remains.** `fold_rel` cannot use a hypothesis about the tree, so the congruence
  lemma itself uses one `Term.inductionOn`. `IFreeM.fold_congr_of_nodesIn` would remove it, and is
  a #374 follow-up together with `IFreeM.fold_prod`.

The agent's full note is untracked at `PolyFun.wt/squirrel-generic/notes/squirrel-a3.md`.

## Implications for the decisions

- **D1, concrete first.** Keep the global semantics `Prop`-valued and asymptotic, as in LICS23,
  and work concretely in the rule proofs.
  - A `Prop`-valued global semantics is what made G.Cut, G.Weak and both `∀̃` rules one-liners.
  - Only L.ByGlob touches probability. Its proof is already concrete first: a per-`η` inequality
    `Pr[¬(∧Γ ⇒ φ)] ≤ Pr[¬φ]`, lifted by `negligible_of_le`.
  - So: prove each cryptographic rule as a per-`η` advantage inequality with a named reduction,
    and lift it to `Valid` with `negligible_of_le` and `negligible_add`.
  - A quantitative global semantics, such as CSF24's ε-judgements with the global sort read as
    error bounds, would be a separate reading. It was not tested, and it would change G.Cut and
    `∀̃`.
- **D2, derivations as data.** Data costs nothing extra here.
  - A `Type`-valued `Derivation` with soundness by structural recursion took 37 code lines, one
    line per rule, and no proof used proof irrelevance. `Nonempty (Derivation …)` recovers the
    `Prop` form.
  - The caveat is for M8: checking an imported derivation means comparing terms in the indices
    (`substOne`, `List.map weaken`). PolyFun's terms have no `DecidableEq` at the pin, so that is
    a prerequisite of import.
- **D5, monomorphic until M8.** Recommended.
  - Nothing in A1 or A2 needed type variables. The development is monomorphic in types and
    parametric in the declarations (`B`, names, symbols).
  - The pin has no `Stacked`.
  - Porting later would replace the `Kind`-sorted signatures, about 130 code lines across
    `Syntax` and the syntax part of `Global`. The rule proofs go through `denote_substOne` and
    `denote_rename`, so they port if the family versions of those laws exist. That was not
    checked.

## Suggested changes to the plan

1. **Signatures as sums.** Use sums over one shared sort type, with fold-defined embeddings
   (`Term.inl`, `denote_inl`), not sort-changing `Hom` embeddings, until PolyFun has `denote_map`.
   - The shared sort type must include every summand's sorts from the start, as `Kind B` does.
   - Splitting `LocalOp` further into Core, Names, Primitives and Adv summands would cost a few
     lines each with the same construction.
   - Candidates for PolyFun (A2a, A6a):
     - `ScopedSignature.sum` and its three companions;
     - `Env.append` equation lemmas;
     - "a pointwise map commutes with `Env.append`";
     - a generic locality lemma for an interpretation lifted from a family of interpretations
       through a per-sort evaluation and embedding pair (the two Squirrel proofs are instances);
     - `DecidableEq` for terms, for M8.
2. **Readings.** The pointwise and random-variable readings now exist, tied by locality. The
   global layer must use the random-variable reading, which is faithful to LICS23. The pointwise
   reading is where proofs compute. The distribution reading is next (A5).
3. **Security layer.** Generalize `AdvClass` to types that depend on `η` (indexed by model or by
   interface) before any `∼` rule. The spike's version fits only fixed types.
4. **Layout.** The library is `Interop/Squirrel/SquirrelLogic/{Sum, Syntax, Model,
   RandomVariable, Global, Derivation, Examples}.lean`. The plan's
   `Interop/Squirrel/{Syntax,Model,Global}.lean` sketch should be updated to match.
5. **Ledger.** `../OBLIGATIONS.md` gains the choice rows L12–L15 for this code.

## M0 start: indistinguishability, L.R-∀ and renaming

This work was done on top of `b7c103222`, with PolyFun still at `ea3b297`. Nothing here uses
A3's `Term.heads`.

### Build and checks

- **Build.** `LEAN_NUM_THREADS=4 lake build SquirrelLogic` succeeds from a clean touch of every
  file, with no warnings.
- **Axioms.** `#print axioms` was run on 46 headline declarations, the new ones and the A2
  rules. They use only `propext`, `Classical.choice` and `Quot.sound`.
- **Forbidden tactics.** There is no `sorry`, `stop` or `native_decide`.
- **Comment fences.** `scripts/check-comment-fences.py` passes.
- **Not run.** `lake lint`, the axiom sweep and the tests were not run, as for A1 and A2.

| File | Content | Lines | Code lines |
|---|---|---|---|
| `Indist.lean` (new) | distinguishers, named reductions, `advantage`, `AdvClass`, laws of `Indist` | 294 | 153 |
| `Rules/Local.lean` (new) | L.R-∀ | 91 | 57 |
| `Rules/Equiv.lean` (new) | structural `∼` rules | 120 | 66 |
| `Rules/Rename.lean` (new) | name renaming | 107 | 64 |
| `TwoTimePad.lean` (new) | the reused-randomness countermodel | 107 | 60 |
| `Global.lean` (changed) | vectors as environments, new local constructors, reading lemmas | 395 | 211 |
| `Derivation.lean` (changed) | 11 more constructors | 134 | 87 |
| `Syntax.lean`, `Model.lean`, `Examples.lean` (changed) | names indexed by types; satisfiability checks | | |

### L.R-∀

`Valid.local_all` (LICS23 Fig. 7, Proposition 2):

```
LValid R C (Θ.map (Term.weaken · (.loc τ))) (Γl.map (Term.weaken · (.loc τ))) φ →
  LValid R C Θ Γl (FTerm.all φ)
```

- **The proof** is the choice construction. A random variable `X` picks, at each parameter and
  tape, a counterexample to `φ` when one exists, and the premise is instantiated at `X`.
- **Locality is the step that matters.** `denote_cons_congr`, a corollary of
  `eval_denote_fullInterp`, identifies `φ` at `cons X env` with `φ` at
  `cons (RV.constAt η (X η ρ)) env`, which is the variable that local `∀` binds.
- **Size.** The proof has 25 lines, over the 10-line target for structural rules. The helper
  `FTerm.denote_conj_weaken` is a list induction.
- **Friction.** The classical `decide` of `∀_τ` needs `Classical.propDecidable` passed by hand,
  and `dif_pos` and `dite_cond_eq_true` are deprecated; `simp [X, hx]` unfolds the choice.

### The adversary class

- **Distinguishers see values of `⟦τ⟧_η`.** `Vals M η τs := Env (Ty.Value M.carrier η) τs` is a
  vector of values at `η`, so their type depends on `η`. `Distinguisher M τs` tests such a
  vector at each `η` and reads `ρa`.
- **Advantage.** `advantage A u v η` is
  `absDiff Pr_ρ[A η (u η ρ) ρ.1 = true] Pr_ρ[A η (v η ρ) ρ.1 = true]` over `$ᵗ (M.Tape η)`.
- **Indistinguishability.** `C.Indist u v := ∀ A, C.distinguishes A → negligible (advantage A u v)`.
- **`adv`.** `C.Adv X := ∃ g, C.computes g ∧ ∀ η ρ, X η ρ = g η ρ.1`. This is LICS23's definition
  of the atom's meaning; it is not a security statement.
- **One closure field per rule**, each a named reduction that changes the vector and then runs
  the given distinguisher:

| Field | Reduction | Used by |
|---|---|---|
| `app_mem` | `Distinguisher.app`: apply the first entry to the second | `Indist.app`, `Valid.equiv_app` (FA-App) |
| `fn_mem` | `Distinguisher.fn f`: prepend the value of an honest symbol | `Indist.fn`, `Valid.equiv_fn` (FA-Fn) |
| `adv_mem` | `Distinguisher.adv g`: prepend `g` run on the same `ρa` (needs `computes g`) | `Indist.adv`, `Valid.equiv_adv` (FA-Adv) |
| `tail_mem` | `Distinguisher.tail`: ignore the first entry | `Indist.tail`, `Valid.equiv_tail` (Restr) |
| `dup_mem` | `Distinguisher.dup`: duplicate the first entry | `Indist.dup`, `Valid.equiv_dup` (Dup) |
| `ite_mem` | `Distinguisher.ite`: the conditional of the first three entries | `Indist.ite`, `Valid.equiv_ite` (If) |

- **The per-`η` statements hold by `rfl`.** These are `advantage_app`, `advantage_fn`,
  `advantage_adv`, `advantage_tail`, `advantage_dup` and `advantage_ite`, for example
  `advantage A u.app v.app = advantage A.app u v`. Each reduction keeps the advantage exactly, at
  every `η`, which is the shape D1 asks for.
- **Class instances.** `AdvClass.all` admits every machine. The empty class also meets every
  field, and then `Indist` always holds.
- **The spike's `AdvClass` is not used.** Its adversaries have fixed types, and the types here
  depend on `η`.

### The shared tape (ledger row L10)

- **No rule needs a hypothesis about the shared tape.** This covers every structural rule proved
  here, the renaming rule and the countermodel; the last two change only the honest tape.
- **FA-Adv depends on the shared reading.** Its reduction `Distinguisher.adv g A` recomputes the
  added term by running `g` on the attacker tape it reads.
- **With fresh coins it would not go through.** A distinguisher drawing its own coins cannot
  recompute a term of `ρa`. The rule would then need `ρa` to be independent of the vectors, which
  fails as soon as they contain attacker symbols.
- **Still open.** Relating these distinguishers to VCVio's fresh-coin adversaries (A4). L10 is
  updated with this.

### Rules about `∼`

- **Vectors are environments.** `Form.equiv u v` takes `u v : Vec D Γ τs`, environments of
  terms. `GlobalOp.equiv τs` has the arguments `Bool × (τ : Ty B) × ScopedVar τs τ`, so rules
  extend and shorten vectors with `Env.cons` and `Vals.tail`.
- **Rules act on the first entries.** There is no permutation rule yet; one more closure field
  would add it.

| Rule | Theorem | Proof lines | Law used |
|---|---|---|---|
| Refl | `Valid.equiv_refl` | 1 | `absDiff_self` |
| Sym | `Valid.equiv_symm` | 1 | `absDiff_comm` |
| Trans | `Valid.equiv_trans` | 2 | `absDiff_triangle`, `negligible_add` |
| G.Equiv:FA-App | `Valid.equiv_app` | 4 | `app_mem` |
| FA-Fn | `Valid.equiv_fn` | 3 | `fn_mem` |
| G.Equiv:FA-Adv | `Valid.equiv_adv` | 3 | `adv_mem` |
| Restr | `Valid.equiv_tail` | 4 | `tail_mem` |
| Dup | `Valid.equiv_dup` | 4 | `dup_mem` |
| If | `Valid.equiv_ite` | 4 | `ite_mem` |
| Rewrite under `[t = t']` | `Valid.equiv_rewrite` | 9 | `advantage_le_add_prEvent_ne` |
| Name renaming | `Valid.equiv_renameNames` | 9, plus 19 in helpers | `prEvent_uniformSample_equiv` |

- **BC14's FA** for an honest symbol is `equiv_fn` followed by `equiv_app`.
- **Rewriting.**
  - `advantage_le_add_prEvent_ne` bounds the advantage at `u` by the advantage at `u'` plus
    `Pr[u ≠ u']`.
  - `Valid.equiv_rewrite` turns `[t = t']` and `t', u⃗ ∼ w⃗` into `t, u⃗ ∼ w⃗`.
  - LICS23's general G.Rewrite, for any formula `F[·]` whose hole is not under `const` or `adv`,
    needs that side condition checked on syntax. That is A3's `Term.heads`, not at either pin.
- **Non-vacuity.** `Valid.not_equiv_tt_ff`: `true ∼ false` fails against `AdvClass.all`.

### Name renaming

- **Names are indexed by their types.** `Decl.Name : Ty B → Ty B → Type` and
  `LocalOp.name {a b} (n : D.Name a b)`. A type-preserving `π` then maps constructors without
  casts, and `Term.renameNames π` is one fold whose algebra matches on the name constructor.
- **Semantics.** `denote_renameNames` (by `fold_fusion`) shows that, pointwise, renaming reads
  the honest tape through `σ`. `denote_renameNames_closed` lifts this to closed terms by
  locality.
- **The rule.** `Valid.equiv_renameNames (hR : ∀ M, R M → M.RenamesNames π) (u : Vec D [] τs) :
  Valid R C Θ (.equiv u (u.renameNames π))`.
  - `Model.RenamesNames π M` asks, at each `η`, for a bijection `σ` of honest tapes with
    `M.name η (π n) i ρh = M.name η n i (σ ρh)`.
  - The uniform tape is invariant under `σ` (`SampleableType.prEvent_uniformSample_equiv`), so
    every advantage is zero.
  - Vectors must be closed, because a free variable may read the honest tape.
- **Ledger.** This restriction is a modelling choice, ledger row L16.
- **Non-vacuity is weak.** `Model.trivial_renamesNames` holds because names there ignore the
  tape. A model with two independent names exchanged by a tape bijection was not built.

### Derivations (D2)

`Derivation` gains `localAll` and ten `∼` constructors, and `Derivation.sound` handles each in one
line. Renaming is left out, because it needs a restriction on models and derivations are
independent of the restriction.

### Encryption from IND-CPA: the countermodel only

`TwoTimePad.lean` has a declaration with one name, the pad `r : bool → bool`, and an honest
symbol `enc m r = m xor r`. Its model reads the pad from one uniform honest bit.

- `TwoTimePad.valid_fresh`: `enc false r ∼ enc true r` is valid for every class of
  distinguishers. Flipping the tape bit maps one side to the other.
- `TwoTimePad.not_valid_reuse`: `enc false r, enc false r ∼ enc true r, enc false r` fails
  against `AdvClass.all`. Testing the entries for equality has advantage one.

This shows that the freshness condition of the encryption rules is necessary, in a model where
the scheme is perfectly secure for one use. It is the first countermodel of the kind the plan
asks for.

The rule itself (`pk, enc(m₀; r) ∼ pk, enc(m₁; r)` from IND-CPA, with the reduction named) was not
done. Three things stand in the way:

1. **Side conditions.** The key must occur only under `pk`, and `r` must be fresh.
   - These are syntactic: they need A3's `Term.heads` on the new pin.
   - Alternatively they become semantic: the honest tape splits as a product of key slice, coin
     slice and the rest, and the other entries read only the rest and `ρa`.
2. **The reduction must sample.** Given `pk` and the challenge, the named reduction samples the
   rest of the tape and `ρa` itself, then runs the distinguisher. This needs the product split,
   and VCVio's IND-CPA game for a scheme whose key generation and encryption are `$ᵗ` over those
   slices.
3. **The class must map across.** The IND-CPA assumption has to hold for the image of `C` under
   the reduction. That is a hypothesis naming the reduction, not a closure field of `C`.

The estimate is 150 or more lines, mostly coupling uniform tape slices with the game's samplers.

### Problems hit

1. **Field binders.** In `AdvClass.all`, `fn_mem _ _ := trivial` bound the wrong binders; a field
   with an explicit binder after implicit ones needed `by intros; trivial`.
2. **Implicit reductions time out.** With the reduction left implicit (`h _ (C.app_mem hA)`),
   unification unfolded `Pr` and hit the 200000-heartbeat limit. Naming the reduction and stating
   `advantage_app … := rfl` fixed it, and that is also D1's statement shape.
3. **Dot notation fails** on `Vec`, an abbreviation of a `Π`-type, and on terms for functions in
   the `Term` namespace: `t.renameNames` resolves to `IFreeM.renameNames`. The fixes are
   `Vec.rv M C u env` and `Term.renameNames π t`.
4. **Concrete models need exposure.** Under the module system, `rfl` lemmas about a concrete
   model (`denote_enc`) need `@[expose]` on `decl`, `model`, `pad` and `enc`.
5. **Mathlib changes.** `add_le_add_left` changed its argument order (`add_le_add` used instead),
   and there is no `Equiv.boolNot`.
6. **Concrete tapes.** `model.TapeH η` is `Bool` only after unfolding. `simp` lemmas about `Bool`
   do not fire on it, and `decide` rejects goals with free variables; `cases` and
   `Bool.noConfusion` close them.

### Suggested changes to the plan

- **Cryptographic rules take their reduction as data.** Structural rules fit closure fields. A
  cryptographic rule should name its reduction to the VCVio game, and take the assumption for the
  image of `C` under it as a hypothesis, as above. Do not add a field to `AdvClass` per
  assumption.
- **Freshness.** The freshness and key-usage side conditions are where the encryption rule meets
  A3. Do that rule after the rebase onto the new PolyFun pin. Until then, the semantic product
  split of the honest tape is the fallback.
- **Small next items.**
  - a permutation rule for vectors;
  - general G.Rewrite, after `Term.heads`;
  - a two-name model satisfying `Model.RenamesNames` nontrivially;
  - FA for honest symbols as one derived rule. It needs `D.fnTy f = .arrow a b`, so it is a cast,
    or a declaration whose symbols are indexed by type, like names now.

## M0, part 2: tape slices, small rules, and the encryption rule's design

This work was done on top of `1b5bbe80f`, with PolyFun still at `ea3b297`.

### Build and checks

- **Build.** `LEAN_NUM_THREADS=4 lake build SquirrelLogic` succeeds from a clean touch, with no
  warnings.
- **Axioms.** `#print axioms` was run on 54 headline declarations, the earlier list plus the new
  ones. They use only `propext`, `Classical.choice` and `Quot.sound`.
- **Forbidden tactics.** There is no `sorry`, `stop` or `native_decide`.
- **Comment fences.** The check passes.

### The honest tape as slices (task 1)

- **The tape is a product.** `Model.TapeH M η := (k : M.Slot η) → M.Coin η k.1.2.1`, one coin
  per slot. A slot is a name with its types, and an index value.
- **The model supplies coins and samplers per type.** A model gives `Coin η b` (a
  `SampleableType`) and a sampler `sample η b : Coin η b → ⟦b⟧_η` for each type `b`.
- **Names are a definition.** `Model.name M η n i ρh := M.sample η b (ρh ⟨⟨a, b, n⟩, i⟩)`, no
  longer a field.
- **This is LICS23 §II-B.2, structurally.**
  - Distinct (name, index) pairs read distinct coordinates of a product of uniform coins, so they
    are independent.
  - Names of one type share a sampler, so they are identically distributed.
  - Each name extracts finitely many bits.
- **Declarations and models gain finiteness.** `Decl` gains `finite_names` (finitely many
  names). `Model` gains `finite_index` (finite index types in the model).
- **The attacker tape stays opaque**, a field with a `SampleableType` instance.
- **`$ᵗ` still works.** `Model.instSampleableTapeH` uses VCVio's
  `SampleableType.piOfFintype`, with `Fintype.ofFinite` on the slots and coins.
  `Model.toTapeModel` packages both tapes for `Overwhelming`.
- **Friction.**
  - `Model.toTapeModel` must be `noncomputable`, because of the instance.
  - Concrete models hit the structure-field binder problem again: a field `f _ n := …` binds the
    first implicit, and `f _ := fun n => …` is needed.
- **`RenamesNames` is a theorem.**
  - `Model.tapePerm M η π : M.TapeH η ≃ M.TapeH η` permutes coordinates along a type-preserving
    bijection `π : ∀ {a b}, D.Name a b ≃ D.Name a b`.
  - `Model.renamesNames M π : M.RenamesNames fun n => π n` then holds by `rfl`.
  - Hence `Valid.equiv_renameNames_of_equiv π u : Valid R C Θ (.equiv u (u.renameNames fun n =>
    π n))` holds in every model. Ledger row L16 is closed; its residue is closed vectors, as in
    LICS23.
- **Proof friction.** The inverse laws of `tapePerm` need `change` then
  `rw [π.apply_symm_apply]`. Neither `simp` nor a `congrArg` term elaborated through the
  dependent coordinate type.
- **Honest symbols are indexed by type.** `Decl.Fn : Ty B → Type`, like names, so an honest
  symbol of arrow type applies without a cast.

### Small items (task 3)

- **Perm.** The closure field is general:
  `rename_mem (r : Renaming τs' τs) : distinguishes A → distinguishes (A.rename r)`, with
  `Distinguisher.rename r A := fun η e ρa => A η (Env.rename r e) ρa`. The rule is
  `Valid.equiv_rename r : Valid R C Θ (.equiv u v) → Valid R C Θ (.equiv (Env.rename r u)
  (Env.rename r v))`, in one line.
  - PolyFun's `Renaming` (a map of positions that preserves types) gives permutation,
    projection and duplication at once.
  - `tail_mem` and `dup_mem` are now special cases, kept for their simpler statements.
- **A two-name model.** `TwoTimePad` has pads `r` and `s`, which read different coordinates.
  `TwoTimePad.valid_swap : Valid R C [] (.equiv [pad r] [pad s])` is the renaming rule at the
  exchange `swap`, in every model.
  - `Term.renameNames swap (pad r)` equals `pad s` only up to function extensionality on node
    arguments. So the proof compares random variables through `denote_renameNames_closed`
    instead.
- **BC14 FA.** `Valid.equiv_fa (f : D.Fn (.arrow a b))` turns `t, u⃗ ∼ s, v⃗` into
  `f t, u⃗ ∼ f s, v⃗`. Its proof is `(equiv_fn f h).equiv_app`.

### The encryption rule (task 2): not done; the design and what is missing

- **The VCVio target.** `AsymmEncAlg.IND_CPA_OneTime_Game` with `IND_CPA_OneTime_Advantage`,
  which is the `boolBias` of the game. `evalDist_boolBias_bind_coin`
  (`VCVio/EvalDist/Monad/Bool.lean`) turns a game of the shape
  `do b ← coin; z ← if b then real else rand; pure (b == z)` into
  `(𝒟[real]).boolDist 𝒟[rand]`.
- **The scheme induced by a model.** Fix a key name `nk` (index `ik`), a coin name `r`
  (index `ir`), and honest symbols `pkOf : D.Fn (kTy ⇒ pkTy)` and
  `encOf : D.Fn (msgTy ⇒ rTy ⇒ pkTy ⇒ cTy)`. At each `η`:
  - key generation is `do c ← $ᵗ (M.Coin η kTy); pure (pkOf (M.sample η kTy c), ())`;
  - encryption is `do c ← $ᵗ (M.Coin η rTy); pure (encOf m (M.sample η rTy c) pk)`.

  The assumption concerns the scheme the model implements.
- **The statement.** The context `u⃗` and the messages `m₀`, `m₁` are terms in the context
  `[loc pkTy]`, whose free variable stands for the public key; this is BC14's "`nk` occurs only
  under `pk`". The conclusion is

  ```
  pk(nk), enc(m₀{x ↦ pk(nk)}, r, pk(nk)), u⃗{x ↦ pk(nk)}
    ∼ pk(nk), enc(m₁{x ↦ pk(nk)}, r, pk(nk)), u⃗{x ↦ pk(nk)}
  ```

  - The semantic side conditions say that the values of `u⃗`, `m₀` and `m₁` at `(x := X, ρ)` do
    not change when the key slot or the coin slot of `ρh` is updated, which is A3's
    `denote_update_eq` shape.
  - The hypothesis is `∀ A, (C M).distinguishes A → negligible fun η => IND_CPA_OneTime_Advantage
    (scheme M η) runtime (encReduction A η)`.
- **The named reduction.**
  `encReduction : Distinguisher M (pkTy :: cTy :: τs) → (η : ℕ) →
  IND_CPA_OneTime_Adversary (scheme M η)`.
  - `chooseMessages pk` samples `ρa` and `ρh`, then returns the values of `m₀` and `m₁` at
    `(x := pk, ρ)` with the state `(pk, ρa, ρh)`.
  - `distinguish (pk, ρa, ρh) c` returns `A η (pk, c, u⃗ at (x := pk, ρ)) ρa`.
  - It needs no inversion of `pk`: the side conditions let it use its own key and coin
    coordinates.
- **What is missing: the per-`η` equality.** It is
  `advantage A left right η = IND_CPA_OneTime_Advantage (scheme M η) runtime (encReduction A η)`.
  It needs four pieces of about 20–40 lines each:
  1. Rewrite the game into the `coin / real / rand` shape (a `bind_congr` on the hidden bit),
     then apply `evalDist_boolBias_bind_coin`. The losslessness side conditions hold because
     everything is uniform sampling.
  2. A uniform-tape coupling. The map `(kc, rc, ρh) ↦ (ρh[key := kc][coin := rc], ρh key,
     ρh coin)` is a bijection of `Coin × Coin × TapeH`. So under `$ᵗ` the updated tape is
     uniform, and the discarded old coordinates marginalize away.
     `prEvent_uniformSample_pair_of_bijective` and `prEvent_uniformSample_equiv` are the tools.
  3. Use locality (`denote_cons_congr`) and `denote_substOne`, so the value of
     `u⃗{x ↦ pk(nk)}` at `ρ` is the value of `u⃗` at `(x := pk value, ρ)`. Then use the side
     conditions to move the key and coin coordinates.
  4. Lift: `negligible_of_le` and the hypothesis.
- **Non-vacuity, not yet done.** A scheme that leaks the message (`encOf m r pk := m`) makes the
  conclusion fail with advantage one, by the distinguisher "the second entry equals `true`". Its
  proof is like `TwoTimePad.not_valid_reuse`. The reuse countermodel `TwoTimePad.not_valid_reuse`
  stands.
- **The estimate** is a session's work. The coupling (piece 2) is the main risk, and it is
  generic: "updating finitely many coordinates of a uniform product tape with fresh uniform coins
  keeps it uniform" belongs beside A3's `Scoped/Measure.lean`.

### Ledger

- **L12** narrows to polynomial time: independence and identical distribution are structural.
- **L16** is closed.
- **L10** is unchanged.

## M0, part 3: one closure field per reduction shape, and the coupling

This work was done on top of `0652ca0e4`.

### Build and checks

- **Build.** `lake build SquirrelLogic` succeeds with no warnings.
- **Axioms.** `#print axioms` on the new and changed declarations shows only the standard three.
- **Forbidden tactics.** There is no `sorry`, `stop` or `native_decide`.
- **Comment fences.** The check passes.

### Fewer closure fields

`tail_mem` and `dup_mem` are gone, and with them `Distinguisher.tail`, `Distinguisher.dup`,
`advantage_tail` and `advantage_dup`. Restr and Dup now go through the reindexing field:

- `Indist.tail` is `h.rename fun _ x => .succ x`;
- `Indist.dup` is `rename` at `Env.cons .zero fun _ x => x`, after a pointwise identification of
  `VecRV.dup` with that reindexing (`funext` and `cases`).

`Valid.equiv_tail` and `Valid.equiv_dup` are unchanged. The class now carries five closure
fields, each one reduction shape, and fewer fields mean a weaker assumption on `C`:

| Field | Reduction | Used by |
|---|---|---|
| `app_mem` | `Distinguisher.app` | FA-App |
| `fn_mem` | `Distinguisher.fn f` | FA-Fn, and through it BC14 FA |
| `adv_mem` | `Distinguisher.adv g` (needs `computes g`) | FA-Adv |
| `ite_mem` | `Distinguisher.ite` | If |
| `rename_mem` | `Distinguisher.rename r` | Perm, Restr, Dup |

### The coupling (`ProductTape.lean`)

```
prEvent_uniformSample_update {ι} [DecidableEq ι] {α : ι → Type} [SampleableType (∀ i, α i)]
    (i₀ : ι) [SampleableType (α i₀)] (p : (∀ i, α i) → Prop) :
  Pr{let c ← $ᵗ (α i₀); let ρ ← $ᵗ (∀ i, α i)}[p (Function.update ρ i₀ c)] =
    Pr{let ρ ← $ᵗ (∀ i, α i)}[p ρ]
```

- **No Squirrel types.** The lemma holds for any `SampleableType` instances on the product and
  the coordinate, since all of them are uniform.
- **Proof.** `(c, ρ) ↦ (update ρ i₀ c, ρ i₀)` is a bijection, and
  `SampleableType.prEvent_uniformSample_pair_of_bijective` makes the pair uniform on product ×
  coordinate. Drawing the old coordinate first (`Equiv.prodComm`) and dropping it
  (`OracleComp.prEvent_bind_const`) marginalizes it away.
- **Friction.** `prEvent_bind_const` matches the normalized event (`simpa only [prEvent_norm]`),
  not the `Pr{…}` notation directly. It needs its lossless prefix stated at `ProbComp`, or the
  `AnswerMeasure` instance problem is stuck.
- **Use.** Applied twice, once at the key slot and once at the coin slot of `Model.TapeH`, it is
  piece 2 of the encryption rule's per-`η` equality.

### The encryption rule: still missing

The per-`η` equality
`advantage A left right η = IND_CPA_OneTime_Advantage (scheme M η) runtime (encReduction A η)`
was not reached in this session. `scheme`, `encReduction` and the rule are not yet in Lean. What
remains is pieces 1, 3 and 4 of part 2's plan, plus the definitions:

- `scheme M η : AsymmEncAlg ProbComp …` from the key and coin slots;
- `encReduction` as designed;
- rewriting `IND_CPA_OneTime_Game` into the shape of `evalDist_boolBias_bind_coin`;
- locality with `denote_substOne` for terms whose free variable stands for the public key;
- the lift.

On `runtime`, checked against VCVio's definitions: `IND_CPA_OneTime_Game` takes a
`ProbCompRuntime (OracleComp spec)`. At `spec := unifSpec` the honest choice is
`ProbCompRuntime.probComp`, under which `runtime.evalDist` is `𝒟`. It imposes no query or time
bound, so the reduction's running time is unconstrained by the game. Efficiency enters only
through the hypothesis on the image of `C M` under `encReduction`. That belongs in the rule's
docstring and in ledger row L14 when the rule lands.

The leaky-scheme check and the `Derivation` constructor wait for the rule.

### Ledger

No row changes in this part. The CCA1 row waits for the rule.

## M0, part 4: the encryption rule

This work was done on top of `bf694ae97`.

### Build and checks

- **Build.** `LEAN_NUM_THREADS=4 lake build SquirrelLogic` succeeds with no warnings.
- **Axioms.** `#print axioms`, from a scratch file outside the repository, on 32 declarations: the
  new ones below and the earlier rules and checks that the change to `Model.TapeH` reaches
  (renaming, `TwoTimePad`, `Valid.not_equiv_tt_ff`, `Valid.equiv_rewrite`, `Valid.local_all`).
  They use only `propext`, `Classical.choice` and `Quot.sound`; `Derivation.allInst` uses only
  `propext`.
- **Forbidden tactics.** There is no `sorry`, `stop` or `native_decide`.
- **Comment fences.** The check passes. No Lean line exceeds 100 characters.

| File | Content | Lines | Code lines |
|---|---|---|---|
| `OneTimeGame.lean` (new) | the game's shape, generic over `AsymmEncAlg` | 59 | 28 |
| `Rules/Enc.lean` (new) | `EncSymbols`, `scheme`, `encReduction`, the per-`η` equality, the rule, `EncInstance` | 304 | 150 |
| `EncExamples.lean` (new) | satisfiability, three countermodels, a derivation | 232 | 142 |
| `ProductTape.lean` (changed) | the coupling at two coordinates | 158 | 122 |
| `Global.lean` (changed) | `FTerm.name`, `FTerm.evalAt`, `FTerm.denote_substOne_apply` | 423 | 230 |
| `Model.lean` (changed) | `Model.TapeH` reducible | 272 | 142 |
| `Derivation.lean` (changed) | the parameter `enc` and the constructor `equivEnc` | 151 | 96 |

### The rule

```
Valid.equiv_enc (E : EncSymbols D) (hkr : E.keyName ≠ E.coinName)
    (hR : ∀ M, R M → E.Avoids M m₀ ∧ E.Avoids M m₁ ∧ ∀ τ x, E.Avoids M (u τ x))
    (hcpa : ∀ M : Model D, M.RespectsLabels → R M →
      ∀ A : Distinguisher M (E.pkTy :: E.cTy :: τs), (C M).distinguishes A →
        negligible fun η => IND_CPA_OneTime_Advantage (E.scheme M η) ProbCompRuntime.probComp
          (E.encReduction m₀ m₁ u A η)) :
  Valid R C Θ (.equiv (E.challenge m₀ u) (E.challenge m₁ u))
```

- **The symbols.** `EncSymbols D` bundles a key name `nk` and a coin name `nr`, each read at an
  honest constant index (`ik`, `ir`), and honest symbols `pkOf` and `encOf`. An honest constant
  index covers BC14's atomic names and any finite index type, and its value is the same on every
  tape. The slots are `E.keySlot M η` and `E.coinSlot M η`.
- **The vectors.** `E.challenge m u` is `pk(nk), enc(m{x ↦ pk(nk)}; r, pk(nk)),
  u⃗{x ↦ pk(nk)}`, for `m : FTerm D [.loc E.pkTy] E.msgTy` and `u : Vec D [.loc E.pkTy] τs`. The
  sequent is closed (`Θ : List (Form D [])`): a free variable of the ambient context would make
  the reduction depend on its value.
- **The side condition** `E.Avoids M t` says that `t`'s value, at every value of its free
  variable, agrees on honest tapes that agree outside the two slots. Agreement replaces
  "invariant under `Function.update`", so the statement needs no decidable equality on slots.
  `hR` states it in every admitted model, as a restriction, as renaming does.
- **The scheme.** `E.scheme M η` has `SK := Unit`: key generation draws the key coin and returns
  `pkOf` of its sample, and encryption draws the coin and applies `encOf`. Decryption rejects
  every ciphertext. The IND-CPA game never runs it.
- **The reduction** `E.encReduction m₀ m₁ u A η`. `chooseMessages pk` draws `ρ ← $ᵗ (M.Tape η)`
  and returns `(m₀ at (pk, ρ), m₁ at (pk, ρ), (pk, ρ))`. `distinguish (pk, ρ) c` runs
  `A η (pk, c, u⃗ at (pk, ρ)) ρ.1`. It never inverts `pk`.
- **The factor is one.** `EncSymbols.advantage_challenge`:

  ```
  advantage A (Vec.rv M C (E.challenge m₀ u) env) (Vec.rv M C (E.challenge m₁ u) env) η =
    IND_CPA_OneTime_Advantage (E.scheme M η) ProbCompRuntime.probComp (E.encReduction m₀ m₁ u A η)
  ```

  VCVio's advantage is the bias `|Pr[win] − Pr[lose]| = 2·|Pr[win] − ½|`, which is the distance
  between the two branches. BC14's Prop. 3 loses a factor of two only because its IND-CCA1
  advantage is `|Pr[win] − ½|`.

### The proof

1. **The game's shape** (`OneTimeGame.lean`, generic):
   `IND_CPA_OneTime_Advantage_probComp_eq_absDiff encAlg adv : IND_CPA_OneTime_Advantage encAlg
   ProbCompRuntime.probComp adv = absDiff Pr[branch true = true] Pr[branch false = true]`, with
   `IND_CPA_OneTime_Branch encAlg adv b` the game at a fixed hidden bit. The proof rewrites the
   game into the hidden-bit shape (`bind_congr`, `cases b`, `simp`), then applies VCVio's
   `evalDist_boolBias_bind_uniformBool` (`SecExp/Measure.lean`, the `ProbComp` form of
   `evalDist_boolBias_bind_coin`), `boolDist` and `prEvent_eq_evalDist_singleton`. It is 6 lines.
2. **Terms to values.** `FTerm.denote_substOne_apply`: a term with one free variable, closed by
   a closed term, means at `(η, ρ)` the open term read at the closed term's value (`denote_substOne`
   and `eval_denote_fullInterp`). `EncSymbols.rv_challenge` reads the challenge vector this way.
3. **The coupling.** `prEvent_uniformSample_update_update`: draw `c₀`, then `ρ ← $ᵗ (β × Π)`,
   then `c₁`, and overwrite the coordinates `i₀`, `i₁` of `ρ.2`; the pair is uniform. This is the
   game's order: key coin, the reduction's tapes, encryption coin. It needs no distinctness of
   the coordinates. The proof chains `EvalDistEq` steps: `EvalDistEq.bind_bind_swap`,
   `SampleableType.uniformSample_prod_eq_bind`, and the one-coordinate lemma twice, in
   distribution form (`update_uniformSample_evalDistEq`).
4. **One branch** (`prEvent_branch`, private): the game's branch is `Pr{kc; ρ; rc}[A … = true]`
   after unfolding, and pointwise its value is the challenge vector at
   `(ρ.1, update (update ρ.2 key kc) coin rc)`. This step uses `hkr` (the key slot survives the
   coin update) and the side conditions, then the coupling. It is 20 lines.
5. **The rule** is `negligible_of_le` with the per-`η` equality.

### Checks (`EncExamples.lean`)

The declaration is `TwoTimePad.decl`, with key name `s` (or `r`), coin name `r`, everything of
type `bool`, and `encModel enc` reading the public key of a key as the key.

| Check | Shows |
|---|---|
| `padInstance_holds`, `valid_enc_pad` | the one-time pad meets every hypothesis against `AdvClass.all`; its IND-CPA advantage is zero for every adversary (`pad_advantage_eq_zero`, from `pad_branch_evalDistEq`) |
| `not_valid_enc_leaky` | `enc m r pk = m`: side conditions and distinct names hold, the conclusion fails with advantage one. The IND-CPA hypothesis is needed |
| `not_valid_enc_keyIsCoin` | key name = coin name, one-time pad: side conditions and IND-CPA hold, the conclusion fails. `hkr` is needed |
| `not_valid_enc_coinReused` | the coin in the context, one-time pad: the conclusion fails. The freshness side condition is needed |
| `encDerivation`, `encDerivation_sound` | the rule as a derivation step; `Derivation.sound`'s hypothesis discharged by `padInstance_holds` |

The pad's zero advantage is proved on the VCVio side, independently of the per-`η` equality: in
each branch, `xor m <$> $ᵗ Bool =ᵈ $ᵗ Bool`, by
`SampleableType.map_uniformSample_evalDistEq_of_bijective`.

### Derivations

`Derivation D enc` gains a parameter `enc : EncInstance D → Prop`, the admitted instances of the
rule. `EncInstance` bundles the symbols, the messages and the context. The constructor `equivEnc`
takes `enc e` and the syntactic premise `hkr`. `Derivation.sound R C henc` takes
`henc : ∀ e, enc e → e.Holds R C`, where `EncInstance.Holds` is the pair `hR`, `hcpa`. With
`enc` empty this is the earlier fragment. A hypothesis over every instance would have been
unsatisfiable for any declaration with an insecure triple of symbols of the right types.

### Problems hit

1. **`Model.TapeH` had to become reducible.** The coupling lemma is stated over `∀ i, α i`. With
   `TapeH` semireducible, goals mixed `M.TapeH η` with the Π-type, were type-correct only at
   default transparency, and `rw` and `simp` failed ("not type-correct under the implicit
   transparency"). The fix was `@[expose, reducible]`; the docstring says why. `keySlot`, `coinSlot`
   are `abbrev`s for the same reason (`(E.keySlot M η).1.2.1` must reduce to `E.keyTy`), and so is
   the example's `encSymbols` (`(encSymbols nk).msgTy` must reduce to `.bool`).
2. **`decl.Name` is not `Name` at reducible transparency.** `encSymbols` takes
   `nk : TwoTimePad.Name .bool .bool`, not `decl.Name .bool .bool`, and the honest symbol `()`
   stays type-incorrect at instance transparency. So the countermodels close their goals with
   `refine`/`exact` (default transparency) and `change`, not `rw`.
3. **`rw` with a `rfl` argument.** In `rw [prEvent_congr _ _ _ fun _ => iff_true_intro rfl]` the
   `rfl` is elaborated before the predicate is known and unifies it with `?a = ?a`. Splitting the
   goal with `congrArg₂ ENNReal.absDiff` and using `exact` fixed it.
4. **`EvalDistEq` is not exposed**, so `fun p => …` does not prove `mx =ᵈ my`; use
   `EvalDistEq.of_forall_prEvent_eq` and `h.prEvent_eq p`.
5. **`do` blocks inside parentheses** do not mix `;` and newlines.
6. **Citations.** The part 2 design cited BC14 §4. The rule is BC14 §7, Fig. 2, axiom EncCCA1,
   sound by Prop. 3; its proof's reduction also draws every name except the key itself. LICS23's
   G.CCA1 is Prop. 19, in real-or-zero form. Both were checked in the pinned PDFs on 2026-11-16.

### Ledger

- **L17** (new): BC14's EncCCA1 without decryption, left-or-right, closed for this fragment.
  Still open there: decryption (IND-CCA1), the equal-length guard for messages of varying length,
  syntactic side conditions, and the real-or-zero form.
- **L7** notes the CCA1 part; it stays open.
- **L10**: the encryption reduction draws `ρa` itself and recomputes the whole vector, so for
  such rules the shared reading costs nothing.
- **L14**: `ProbCompRuntime.probComp` bounds nothing; efficiency enters only through the
  hypothesis on the image of the class.

### Suggested changes to the plan

- **M0's worked derivation is now in reach.** For `pk, enc(n), n ∼ pk, enc(0), n`, the side
  conditions for a name `n` other than `nk` and `r`, and for honest constants, hold in every
  model. Two generic lemmas would give them: a name at a constant index other than the two
  avoids both slots, and `Avoids` is closed under application. Then the derivation needs no
  restriction `R`, and only `hcpa` remains as a hypothesis.
- **Syntactic side conditions** replace `hR` once A3's `Term.heads` is at the pin: "no name but
  `nk` under `pkOf`, and no `nr`" implies `Avoids`.
- **The equal-length guard.** For message types whose values vary in length, the hypothesis
  quantifies over unequal pairs too, which real schemes do not meet. BC14's `EQL` guard, or a
  `fixed`-labelled message type, would remove that.
- **`OneTimeGame.lean`** is a candidate for VCVio core, beside `IND_CPA_OneTime_Advantage`.
