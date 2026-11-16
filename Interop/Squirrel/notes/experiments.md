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
