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

## M0, part 5: the length guard, side conditions by construction, the worked derivation

This work was done on top of `f6d7ea08f`.

### Build and checks

- **Build.** `LEAN_NUM_THREADS=4 lake build SquirrelLogic` succeeds with no warnings.
- **Axioms.** `#print axioms` on 33 declarations: the rule, `Derivation.sound`, the new lemmas and
  checks, and the earlier encryption checks. They use only `propext`, `Classical.choice` and
  `Quot.sound` (`Derivation.allInst` only `propext` and `Quot.sound`).
- **Forbidden tactics, comment fences, line length.** No `sorry`, `stop` or `native_decide`; the
  fence check passes; no Lean line exceeds 100 characters.

### The length guard

Without a guard, `hcpa` asks VCVio's unrestricted game about the reduction, which may submit
messages of different lengths. No scheme that leaks lengths meets that.
`WorkedEnc.lpad_advantage_unequalAdv` shows advantage one for the length-leaking pad.

- **The choice.** BC14's EncCCA1 guards the challenge with `if EQL(u, u′) then {u}ʳ else u″`.
  Here the guard is the side condition `EncSymbols.EqualLength M m₀ m₁`: at every tape the two
  messages, read at the tape's public key, have equal `lenOf`. The guard then always takes its
  first branch. LICS23's G.CCA1 gets equal lengths the same way: its second message
  `zero (len m)` has the length of the first in every model. The conditional form in the
  conclusion was not chosen. Recovering the unguarded worked example from it would need a rewrite
  under `[EQL]` at the second entry, and `Env.rename` is not definitionally the permuted `Env.cons`.
- **The symbol.** `EncSymbols` gains `lenTy` and `lenOf : D.Fn (msgTy ⇒ lenTy)`, an honest symbol
  that the model interprets freely.
- **The reduction** tests the lengths and submits `(m₀, m₀)` when they differ, so it always
  submits equal-length pairs (`EncSymbols.encReduction_equalLength`, stated with the generic
  `IND_CPA_OneTime_EqualLength` of `OneTimeGame.lean`). Under `EqualLength` the fallback never
  fires, and the per-`η` equality still has factor one.
- **The check** (`WorkedEnc.lean`). A message is a length bit and a payload bit, read as a
  function `bool → bool`. `lpad` masks the payload with the coin and copies the length bit.
  - `lpad_advantage_eq_zero`: every adversary that submits equal-length pairs has advantage zero.
  - `lpad_advantage_unequalAdv`: an adversary submitting unequal-length pairs has advantage one.
  - `valid_worked_lpad`: every hypothesis of the worked derivation holds in this model, against
    `AdvClass.all`.
  - `not_valid_leak`: for `leak m _ _ = m`, the conclusion fails for the equal-length messages
    `one` and `zero`, with advantage one.

### Side conditions by construction (`Rules/Enc.lean`)

`avoids_var`, `avoids_fn`, `avoids_tt`, `avoids_ff`, `Avoids.app`, `Avoids.ite`, `Avoids.eq`
and `Avoids.name` hold in every model. A name other than the key and coin names, at an avoiding
index, reads its own coordinate. Each proof is a `change` to the pointwise reading and a `rw`;
the reading of a constructor is definitional. A fold-based statement (one `fold_rel` over a
syntactic predicate on names) was not cheap. The relation would have to carry the predicate's
fold beside both readings, and binders need environments of any length, while `Avoids` is stated
for the one-variable context. A3's `Term.heads` is the syntactic route.

### The worked derivation

`WorkedEnc.workedDerivation : Derivation decl (· = workedInstance) [] (.equiv
(encSymbols.challenge nTerm ctx) (encSymbols.challenge zeroTerm ctx))` is
`pk(k), enc(n; r), n ∼ pk(k), enc(zero; r), n` in one step of `equivEnc`. Here `n` is a third
name and `zero` an honest constant, and the vectors are the rule's substitution instances.

`workedDerivation_sound` gets its validity from `Derivation.sound`. The side conditions are
discharged by the lemmas above in every model (`avoids_n`, `avoids_ctx`). The hypotheses left are
`hlen` (in every admitted model `n` and `zero` have equal length) and `hcpa`. In `model enc` the
length fact holds by computation (`equalLength_n_zero`), and is not assumed.

### Derivations

`Derivation` gains three constructors, each sound in one line:
- `equivEqSelf`: BC14's Eq1, `Valid.equiv_eq_self`, new in `Rules/Equiv.lean`.
- `equivRename`: Restr and Perm by reindexing, `Valid.equiv_rename`.
- `equivRenameNames`: renaming along a bijection of names, `Valid.equiv_renameNames_of_equiv`,
  which holds in every model since part 2.

The docstring's claim that renaming needs a restriction on models was stale; it is corrected.

### M0 against the plan

| Headline item | Status |
|---|---|
| `Base.sound` | met by `Derivation.sound`: every constructor of the fragment, with the encryption instances' hypotheses as the one parameter |
| worked `pk, enc(n), n ∼ pk, enc(0), n` | met: `workedDerivation`, `workedDerivation_sound`, `valid_worked_lpad` |
| countermodel with reused randomness | met: `TwoTimePad.not_valid_reuse`, `EncExamples.not_valid_enc_coinReused` |

Against BC14 Fig. 2 and the plan's M0 row:

- **Done:**
  - Refl, Sym, Trans.
  - Restr (with permutation), and name renaming.
  - Eq1.
  - EncCCA1 without decryption.
  - Indcong for a curried honest symbol: FA-Fn, then FA-App once per argument. This was not
    stated as one lemma.
- **Not done:**
  - **If1**, BC14's case split: `b, w⃗, x ∼ b, w⃗′, z ∧ b, w⃗, y ∼ b, w⃗′, z → w⃗, if b then x else
    y ∼ w⃗′, z`. `Valid.equiv_ite` is FA for `if` (LICS23's form), not If1. If1 needs its own
    reduction, which branches on `b` and flips a coin, and BC14's proof loses a factor of two.
    The plan's row says "If", and earlier notes listed `equiv_ite` under that name; that holds
    only for the FA form.
  - **EncKP** (key privacy) and EncCCA1 with decryption. They are not in the M0 row, but they are
    in Fig. 2.

### Ledger

- **L17** narrows: the length guard is in, and the open items are decryption, the guard as a
  conditional for lengths that differ on some tapes, syntactic side conditions, and the
  real-or-zero form.
- **L16** gains the derivation constructor as an anchor.

## M0, part 6: the case split (If1)

This work was done on top of `1479346bc`.

### Build and checks

- **Build.** `LEAN_NUM_THREADS=4 lake build SquirrelLogic` succeeds with no warnings.
- **Axioms.** `#print axioms`, from a scratch file outside the repository, on 21 declarations: the
  new ones below, `AdvClass.all`, `Derivation.sound`, and earlier rules and checks
  (`Valid.equiv_ite`, `Valid.equiv_enc`, `WorkedEnc.workedDerivation_sound`,
  `WorkedEnc.valid_worked_lpad`, `TwoTimePad.not_valid_reuse`, `Valid.not_equiv_tt_ff`). They use
  only `propext`, `Classical.choice` and `Quot.sound`.
- **Forbidden tactics, comment fences, line length.** No `sorry`, `stop` or `native_decide`; the
  fence check passes; no Lean line exceeds 100 characters.

| File | Content | Lines | Code lines |
|---|---|---|---|
| `CaseStudy.lean` (new) | a satisfying instance, a derivation, three countermodels, the field's independence | 222 | 135 |
| `Indist.lean` (changed) | `Distinguisher.guard`, `guard_mem`, the per-`η` bound, `Indist.caseStudy`, `Indist.if1` | 367 | 197 |
| `Rules/Equiv.lean` (changed) | `Valid.equiv_caseStudy`, `Valid.equiv_if1` | 177 | 101 |
| `Derivation.lean` (changed) | `equivCaseStudy`, `equivIf1` | 185 | 122 |

### The sources

All three were checked on 2026-11-16, the papers in the PDFs pinned in `../SOURCES.md`.

- **BC14's If1** (§7, Fig. 2, sound by Prop. 2) is
  `b, w⃗, x ∼ b, w⃗, z ∧ b, w⃗, y ∼ b, w⃗, z ⟶ w⃗, if b then x else y ∼ w⃗, z`. The condition and
  the context are the same on both sides. Part 5 quoted it with `w⃗′` on the right, which is not
  BC14's statement.
- **LICS23's G.Case-Study:ITE** (Fig. 8): from `u⃗l, bl, sl ∼ u⃗r, br, sr` and
  `u⃗l, bl, tl ∼ u⃗r, br, tr`, conclude `u⃗l, if bl then sl else tl ∼ u⃗r, if br then sr else tr`.
  Each side has its own condition. Prop. 11 calls the structural rules straightforward and refers
  to BC14 for their proofs; it gives none for this rule.
- **The tool's `cs φ`** (tactic `case_study`, `documentation/sphinx/source/proofs.rst` at
  `ebef0aca4f`) projects the conditionals on one pattern `φ` on both sides: from
  `equiv(if φ then t1 else t2, if φ then u1 else u2)` it leaves `equiv(φ, t1, u1)` and
  `equiv(φ, t2, u2)`.

### BC14's proof and the factor

- BC14 sets `p1 = Pr[A(w⃗, if b then x else y)]` and `p2 = Pr[A(w⃗, z)]`, and splits each on `b`:
  `p1 = p^x_{1,1} + p^y_{1,2}` and `p2 = p^z_{1,1} + p^z_{1,2}`.
- Its machine `B1` runs `A` when `b = 1` and otherwise flips a coin. BC14 gives its success
  probability as `1/4 + p^x_{1,1}`, which holds only when `Pr[b = 1] = 1/2`. In general the coin
  adds `Pr[b ≠ 1]/2` on both sides, and that cancels because `b` is the same on both sides. With
  different conditions, as in G.Case-Study:ITE, it does not cancel.
- Its inequality `|p1 − p2| ≤ |p^x_{1,1} − p^z_{1,1}| + |p^y_{1,2} − p^z_{1,2}|` has factor one.
  The factor two appears only in its conclusion, which names one of the two machines: one of them
  has advantage at least `ε/2`.
- Here the two reductions return `false` instead of flipping, and the bound keeps the sum. So the
  factor is one, and the conditions may differ:

  ```
  advantage_cons_cond_le (A : Distinguisher M (a :: τs)) (b b' : RV M .bool)
      (x y x' y' : RV M a) (u v : VecRV M τs) (η : ℕ) :
    advantage A (VecRV.cons (fun η ρ => cond (b η ρ) (x η ρ) (y η ρ)) u)
        (VecRV.cons (fun η ρ => cond (b' η ρ) (x' η ρ) (y' η ρ)) v) η ≤
      advantage (A.guard true) (VecRV.cons b (VecRV.cons x u))
          (VecRV.cons b' (VecRV.cons x' v)) η +
        advantage (A.guard false) (VecRV.cons b (VecRV.cons y u))
          (VecRV.cons b' (VecRV.cons y' v)) η
  ```

- **The proof.** `Pr[A(if b then x else y, u⃗)] = Pr[b ∧ A(x, u⃗)] + Pr[¬b ∧ A(y, u⃗)]`, by
  VCVio's `prEvent_eq_prEvent_and_add_prEvent_and_not` and a case split on `b` at each tape
  (private `prEvent_cons_cond`). Then `absDiff (a + b) (c + d) ≤ absDiff a c + absDiff b d`
  (private `absDiff_add_add_le`, 5 lines). `ToMathlib/Data/ENNReal/AbsDiff.lean` has no such
  lemma, and it belongs there.

### The rules

```
Valid.equiv_caseStudy
    (h₁ : Valid R C Θ (.equiv (Env.cons c (Env.cons t u)) (Env.cons c' (Env.cons s v))))
    (h₂ : Valid R C Θ (.equiv (Env.cons c (Env.cons t' u)) (Env.cons c' (Env.cons s' v)))) :
  Valid R C Θ (.equiv (Env.cons (FTerm.ite c t t') u) (Env.cons (FTerm.ite c' s s') v))

Valid.equiv_if1
    (h₁ : Valid R C Θ (.equiv (Env.cons c (Env.cons x u)) (Env.cons c' (Env.cons z v))))
    (h₂ : Valid R C Θ (.equiv (Env.cons c (Env.cons y u)) (Env.cons c' (Env.cons z v)))) :
  Valid R C Θ (.equiv (Env.cons (FTerm.ite c x y) u) (Env.cons z v))
```

- `Indist.caseStudy` is `negligible_of_le` at the per-`η` bound, with `negligible_add`.
  `Indist.if1` is the case split with both right-hand branches `z`, then `Bool.cond_self`. Each
  `Valid` rule takes 5 lines.
- **If1 is stated more generally than in BC14.** The right side's condition `c'` and context `v⃗`
  are free; BC14's rule is the instance `c' = c`, `v⃗ = u⃗`.
- **Positions.** As for every rule here, the entries acted on come first, where LICS23 and BC14
  put them last. Perm moves them.

### The closure field

`guard_mem (c : Bool) : distinguishes A → distinguishes (A.guard c)`, where
`Distinguisher.guard c A η e ρa := (e _ .zero == c) && A η e.tail ρa`. So `guard true` is
`D₁(b, v⃗) = b && D(v⃗)` and `guard false` is `D₂(b, v⃗) = !b && D(v⃗)`; one field with a
parameter covers both.

- **No derivation from the other fields.** `ite_mem` and `rename_mem` were tried first. Each of
  the five other reductions changes the input and then runs `A`, so it maps a constant
  distinguisher to a constant one. But `guard true` of the constant-`true` distinguisher returns
  `false` when the condition is `false`. `CaseStudy.guard_not_derivable` proves this: the
  constant-`true` distinguishers are closed under the five reductions and not under `guard true`.
- Any class of polynomial-time machines is closed under `guard`. `AdvClass.all` meets it by
  `by intros; trivial`.

| Field | Reduction | Used by |
|---|---|---|
| `app_mem` | `Distinguisher.app` | FA-App |
| `fn_mem` | `Distinguisher.fn f` | FA-Fn, and through it BC14 FA |
| `adv_mem` | `Distinguisher.adv g` (needs `computes g`) | FA-Adv |
| `ite_mem` | `Distinguisher.ite` | FA for `if` |
| `rename_mem` | `Distinguisher.rename r` | Perm, Restr, Dup |
| `guard_mem` | `Distinguisher.guard c`: test the rest when the Boolean first entry is `c`, else return `false` | G.Case-Study:ITE, If1 |

### Checks (`CaseStudy.lean`)

The model is `TwoTimePad.model`: the pads `r` and `s` are independent uniform bits,
`enc m = m xor r`, and the condition `parity` is `enc s`, which is `s xor r`.

| Check | Shows |
|---|---|
| `valid_flip` | `parity, r ∼ parity, enc true` for every class: flipping both tape bits keeps `parity` and maps `r` to `!r` |
| `valid_if1_flip`, `denote_ite_parity` | If1 with its first premise Refl and its second `valid_flip`: `if parity then enc true else r ∼ enc true`, whose sides are the different random variables `s` and `!r` |
| `if1Derivation`, `if1Derivation_sound` | the same as one derivation step from the hypothesis `flipForm`, closed by `Derivation.sound` and `valid_flip` |
| `caseStudy_needs_condition` | the tempting variant whose premises leave out the condition is unsound: `enc true ∼ enc false` and `enc false ∼ enc false` hold, and `if r then enc false else enc true ∼ enc false` fails with advantage one half, since its left side is always `true` and its right side is `r` |
| `if1_needs_second`, `if1_needs_first` | in every model of every declaration, each premise alone holds by Refl at an instance whose conclusion is `true ∼ false` |
| `guard_not_derivable` | `guard_mem` does not follow from the other five fields |

`caseStudy_needs_condition` never computes `Pr[r] = 1/2`. It shows `Pr[r] + Pr[r] = 1`, by the
flip and `prEvent_add_prEvent_not_eq_prEvent_true`, then `1 ≤ 2 · advantage`, and concludes with
`negligible_const_mul` and `not_negligible_one`.

### Derivations

`Derivation` gains `equivCaseStudy` and `equivIf1`, each sound in one line. `equivIf1` is not
derived from `equivCaseStudy`: that would rewrite `if c' then z else z` to `z`, and every rule of
the fragment that concludes a local formula `[φ]` needs one as a premise or a hypothesis.

### Problems hit

1. **`rfl` does not prove an `Iff`** whose sides agree only after `cond` reduces. After `cases`
   on the condition, `simp` and then `rfl` close it. `simp` leaves `true = true` stated at the
   coin type, and `decide` rejects such goals ("free variables").
2. **Field binders, again.** In `guard_not_derivable`, `fun _ h _ _ _` bound the implicit `A` to
   `h` after the explicit `f`. Writing every binder (`fun {_ _} _ {_} h _ _ _`) fixed it.
3. **Dot notation fails** on a lambda ascribed as a `Distinguisher`; `Distinguisher.guard true
   (fun …)` works.
4. **Elaboration order.** `Env.cons false Env.empty` needs the ascription
   `Vals model 0 [.bool]`.
5. **Deprecations.** `cond_true` and `cond_false` are deprecated for `Bool.cond_true` and
   `Bool.cond_false`.

### M0 against the plan

| Plan row item | Lean | Derivation constructor |
|---|---|---|
| FA | `Valid.equiv_fn`, `Valid.equiv_app`, `Valid.equiv_adv`; BC14's FA is `Valid.equiv_fa`; FA for `if` is `Valid.equiv_ite` | `equivFn`, `equivApp`, `equivAdv`, `equivIte` |
| Refl, Sym, Trans | `Valid.equiv_refl`, `Valid.equiv_symm`, `Valid.equiv_trans` | `equivRefl`, `equivSymm`, `equivTrans` |
| Restr | `Valid.equiv_tail`, `Valid.equiv_rename` (with Perm), `Valid.equiv_dup` | `equivTail`, `equivRename`, `equivDup` |
| If | `Valid.equiv_if1` (BC14's If1), `Valid.equiv_caseStudy` (LICS23) | `equivIf1`, `equivCaseStudy` |
| Eq | `Valid.equiv_eq_self` (Eq1) | `equivEqSelf` |
| Name renaming | `Valid.equiv_renameNames_of_equiv` | `equivRenameNames` |
| CCA1 without decryption | `Valid.equiv_enc` | `equivEnc` |

| Headline item | Status |
|---|---|
| `Base.sound` | met by `Derivation.sound`, which now covers the case split and If1 |
| worked `pk, enc(n), n ∼ pk, enc(0), n` | met (part 5) |
| countermodel with reused randomness | met (part 5) |

Every item of the M0 row is a constructor of `Derivation`, sound by `Derivation.sound`, with a
satisfiability check and a countermodel for each new rule family.

Still missing from BC14 Fig. 2:

- **EncKP** (key privacy).
- **EncCCA1 with decryption**: IND-CCA1, with the side conditions `sk ⋢d v⃗` (secret keys only in
  decryption position) and `nodec`.
- **EncCCA1's guard as a conditional** `if EQL(u, u′) then {u}ʳ else u″` in the conclusion. Here
  the guard is a side condition that must hold at every tape (L17).
- **Indcong** for a curried `n`-ary symbol is FA-Fn and then FA-App once per argument; it is not
  stated as one lemma.

### Ledger

- **L7** records that LICS23 omits the proof of G.Case-Study:ITE, and that BC14's proof of If1
  is sound for its form, with the slip in `B1`'s probability; the rule is proved for the
  first-order fragment with factor one. L7 stays open for `⊢pptm` and the other sketched proofs.
- No row is added: `guard_mem` is a closure field like the others, within L14.

## M1, part 1: the secrecy predicates `⊬` and `▷`

This work was done on top of `44ca7421d`. The source is CCS26, the authors' PDF pinned in
`../SOURCES.md`: §3.1 (p. 6) for the definitions, Fig. 3 (p. 7) for the core rules, Fig. 11 and
App. C.2 (pp. 16–17) for FreshL and FreshR; LICS23 App. A for the label `large`.

### The predicates are definitions

- **No new primitive.** `Form.nonDed u v` is `∀̃ f. adv(f) ⇒̃ [¬ (f(u⃗) = v)]` and `Form.ded u v`
  is `∃̃ f. adv(f) ∧̃ [f(u⃗) = v]`, built from `Form.all`, `Form.ex`, `Form.imp`, `Form.and`,
  `Form.adv`, `Form.box` and the local `FTerm.not`, `FTerm.eq`. `Global.lean` gains the smart
  constructors `Form.and`, `Form.ex`, `Form.bot`, `Form.not` and `FTerm.not`, with `holds`
  lemmas; `GlobalOp` is unchanged.
- **Tuples are curried (no products).** `Ty` has no product type, so the tuple `u₁, …, uₙ` on
  the left is a vector `Vec D Γ τs`, and `f` has the curried type `Ty.arrows τs β`, applied by
  `FTerm.apps` (syntax) and `Ty.appVals` (values). The right side is one term. A term in the
  middle of Trans or WeakL is on the right of a `▷`, so it is a single term, written as the
  vector `[v]`. Rw-Equiv's vectors `u⃗, v` are `Vec.snoc u v`, PolyFun's `Env.append`.
- **Semantics.** `Form.holds_nonDed` and `Form.holds_ded` read the formulas as
  `AdvClass.NonDed C u v` (every admitted `g` has negligible `deduceAdv g u v`) and
  `AdvClass.Ded C u v` (some admitted `g` has negligible `deduceErr g u v`), where
  `deduceAdv g u v η = Pr_ρ[g(ρa)(u(ρ)) = v(ρ)]` and `deduceErr` is the probability of `≠`.
- **Against the spike.** The spike's `deduceAdv uv f` (`Examples/SquirrelModel/Deduction.lean`)
  is the same probability for a VCVio adversary `f : α → ProbComp β` that draws fresh coins; here
  `g` reads the shared attacker tape `ρa` (L10). FreshL is where the two differ (below).

### The core rules (CCS26 Fig. 3)

Each rule is a `Valid` theorem in `Rules/Secrecy.lean` that applies one law of `Secrecy.lean`,
whose proof is an inequality at every `η` with the reduction named.

| Rule | Lean | Bound at `η` | Reduction |
|---|---|---|---|
| Neg1 | `Valid.not_ded`, `AdvClass.NonDed.not_ded` | `deduceAdv g u v + deduceErr g u v = 1` | the witness of `▷` |
| Neg2 | `Valid.not_nonDed`, `AdvClass.Ded.not_nonDed` | the same | the same |
| Ineq | `Valid.box_not_eq`, `AdvClass.NonDed.negligible_eq` | `Pr[v = w] ≤ deduceAdv g u v + deduceErr g u w` | the witness of `u ▷ w` |
| Trans | `Valid.ded_trans`, `AdvClass.Ded.trans` | `deduceErr (k.comp f) u w ≤ deduceErr f u v + deduceErr k [v] w` | `AttackerFn.comp` |
| WeakL | `Valid.nonDed_weakL`, `AdvClass.NonDed.weakL` | `deduceAdv g [v] w ≤ deduceAdv (g.comp f) u w + deduceErr f u v` | `AttackerFn.comp` |
| WeakR | `Valid.nonDed_weakR`, `AdvClass.NonDed.weakR` | `deduceAdv g u w ≤ deduceAdv (k.comp g) u v + deduceErr k [w] v` | `AttackerFn.comp` |
| Rw-Equiv | `Valid.nonDed_rwEquiv`, `AdvClass.NonDed.rwEquiv` | `deduceAdv g u₁ v₁ ≤ deduceAdv g u₂ v₂ + advantage (Distinguisher.deduce g) (u₁, v₁) (u₂, v₂)` | `Distinguisher.deduce` |

- `Valid.ded_apps` concludes `u⃗ ▷ f(u⃗)` from `adv(f)`: the definition of `▷` with its witness.
  The fragment has no other way to introduce `▷`.
- **Rw-Equiv at Boolean and base types only** (`Ty.IsGround`). Its distinguisher tests
  `f(u⃗) = v`, which no machine does at an arrow type. The closure field is asked only there, so
  that a polynomial-time class can meet it.
- Rw-Oracle and Pc-Oracle are not done: they need `adv` at order two.

### Closure fields

| Field | Reduction | Used by | Polynomial-time counterpart |
|---|---|---|---|
| `comp_mem` | `AttackerFn.comp k f`: `f` then `k`, both on the shared `ρa` | Trans, WeakL, WeakR | `IsPPTOn.bind`; uniform PPT has it |
| `eqTest_mem` | `Distinguisher.eqTest β` at ground `β` | Rw-Equiv, with `app_mem` and `adv_mem` | `decide_eq`; uniform PPT has it |

Both are operations a machine performs on its input and its tape, so they restate directly on
programs over a tape-reading interface. FreshR needs no field. Commit `0512ab73b` also added a
field for FreshL, fixing an argument of an attacker function to an `η`-indexed value; that closure
is non-uniform, and the next commit removes it (FreshL below).

Rw-Equiv's distinguisher is derived, not a field: `Distinguisher.deduce g` is
`((eqTest β).appArgs τs).adv g`, where `appArgs` applies `Distinguisher.app` once per argument
(`AdvClass.deduce_mem`).

### The label `large`

LICS23 App. A: if `large ∈ label(τ)`, then for every name `n : τ₀ → τ`, every `η`, `a` and `b`,
`Pr_ρh[⟦n⟧(η, a)(ρh) = b] ≤ 1/2^{c_τ·η}`, for some real `c_τ > 0`. Here `Label.large` is a label
of base types and `Model.IsLarge M τ` says `∃ c > 0, ∀ η y, Pr_coin[sample η τ coin = y] ≤
2^{-(c·η)}`: names of one type share a sampler, so the bound is on the sampler.

- **Lifting.** LICS23 lifts labels "in the natural way" without saying how `large` lifts. Here
  `Ty.HasLabel` lifts `finite` and `fixed` along arrows as before, and Booleans and arrow types
  are not `large`: the samplers of the parts do not determine the sampler of an arrow type, and a
  Boolean is guessed with probability at least one half.
- **Consequence.** `Model.trivial` respects every label but `large`. A type labelled `finite`,
  `fixed` and `large` has no model, so `Valid.not_box_ff`, `Valid.not_equiv_tt_ff` and the
  If1 countermodels now assume a declaration with no `large` base type.

### FreshR (CCS26 Fig. 11, p. 17)

```
Valid.nonDed_freshR (n : D.Name a b) (i : D.Fn a) (hlarge : b.HasLabel D.labels .large)
    (hfresh : ∀ M, R M → ∀ τ x, (u τ x).Avoids M fun η k => k = M.nameSlot n i η) :
  Valid R C Θ (.nonDed u (FTerm.name n (FTerm.fn i)))
```

- **Bound at `η`** (`deduceAdv_nameAt_le`): if `u` does not read the coordinate of `n(i)`, every
  attacker function, admitted or not, has `deduceAdv g u (n(i)) η ≤ ε`, where `ε` bounds the
  probability of each value of the sampler. The proof overwrites the coordinate with a fresh coin
  (`prEvent_uniformSample_prod_update`, new in `ProductTape.lean`), and for each tape the coin
  hits the attacker's guess with probability at most `ε`. With `large`, `ε = 2^{-cη}`, which is
  negligible (`negligible_two_rpow_neg_mul`).
- **Indexed names.** CCS26 presents un-indexed names. Here the name is read at an honest symbol
  `i`, a closed index, and freshness is for the one coordinate `M.nameSlot n i η` at each `η`.
- **Freshness is semantic.** `FTerm.Avoids M S t` (`Avoids.lean`) says that `t`'s pointwise value
  at every value of its free variables is the same at two honest tapes that agree outside the
  coordinates `S η`. The encryption rule's `EncSymbols.Avoids` is now its instance at the key and
  coin coordinates, and the constructor lemmas (`FTerm.avoids_var`, `avoids_fn`, `avoids_tt`,
  `avoids_ff`, `Avoids.app`, `.ite`, `.eq`, `.not`, `.name`) serve both rules. `Model.FreshAt`
  is the same condition on random variables, and `FTerm.Avoids.freshAt` passes from a closed term
  to its random variable.
- **Two forms.** `Valid.nonDed_freshR_of_freshAt` takes freshness of the random variables in every
  admitted model where `Θ` holds, for any context, as CCS26's premise `E; Θ ⊢ [ψ^n_fresh(u)]` is
  a judgment under `Θ`. `Valid.nonDed_freshR` is the closed-vector form with `FTerm.Avoids`; free
  variables range over all random variables, which may read the name, so the syntactic form needs
  a closed vector (CCS26's caption of Fig. 11 instead asks every declared variable to be a name
  or adversarial).
- The decidable side condition will be PolyFun's `Term.heads`, not at VCVio's pin `ea3b297`.

### FreshL: not proved

FreshL is `u ⊬ v ⟹ u, n ⊬ v` for `n` fresh in `u, v`. It is left open (L20), with a countermodel
showing the freshness condition is needed.

- **CCS26's proof** (App. C.2, p. 17) uses G.Equiv.Fresh, `u, n ∼ u, n_fresh` for a name
  `n_fresh` occurring nowhere, and a function `f′` that, on input `u`, "simulates the sampling of
  `n_fresh` from the adversarial randomness and then runs `f`". Rw-Equiv then moves from
  `n_fresh` to `n`.
- **Footnote 2** (p. 17): "we must ensure that `f′` has enough fresh randomness at its disposal in
  the adversarial tape. This can be done by defining `f′` in a new model in which we extended the
  size of the adversarial tape as needed. Then, since the secrecy property `u ⊬ v` is assumed to
  hold in any model, we can apply consider it in the extended model."
- **What it leaves out.** The premise is the judgment `E; Θ ⊢ u ⊬ v`, true in models of `Θ` only,
  and the footnote does not show that `Θ` holds in the extended model. Atoms whose meaning
  quantifies over machines, `∼` and `adv` and through them `⊬` and `▷`, are evaluated there
  against machines that read the longer tape. Whether a hypothesis true in the smaller model
  stays true is not argued; we have not settled it either way.
- **What bounds the bits the terms read.** LICS23 (§II-A.3) takes the tapes to be a pair
  `(ρa, ρh)` of finite bitstrings of model-chosen length, and its machines for `adv` and `∼`
  (§II-C.1, Fig. 2) have a randomness input tape for `ρa` and a query tape for higher-order
  arguments. The caption of CCS26 Fig. 11 asks every declared variable to be a name or
  adversarial (`E; Θ ⊢ adv(v)`): that is what bounds which bits of `ρa` the terms read, so that
  `f′` can sample from bits further along.
- **Here.** A model's attacker tape is a fixed finite type, possibly a single point, and the class
  of machines is chosen per model (`C : ∀ M, AdvClass M`), so there is no extended model to move
  to, nor a relation between the classes of two models. Averaging over the name's coin would
  bound the success by that of the attacker function with the name's argument fixed to a best
  value at each `η`, but admitting that function is a non-uniform closure (advice), which this
  development does not adopt. The route that follows the papers needs attacker functions as
  programs over a tape-reading interface, with the number of bits they read bounded, so that
  `f′` reads bits beyond them.
- **Check.** `SecrecyExamples.freshL_needs_freshness`: `⊬ n` with nothing on the left holds by
  FreshR, and `n ⊬ n`, which adds `n` although it is not fresh on the right, fails.

### Checks (`SecrecyExamples.lean`)

The declaration has one base type `msg` labelled `large`, names `k, m, n : bool → msg` and
`b : bool → bool`, the honest index `idx : bool` and `h : msg → msg`. In `model`, `msg` at `η` is
the bitstrings of length `η`, every name draws a uniform value of its type, and `h` is the
identity; `msg` is large with `c = 1` (`model_isLarge`, from `card_vector`).

| Check | Shows |
|---|---|
| `workedDerivation`, `workedDerivation_sound` | from `adv(h)`: FreshR gives `k ⊬ n`; `▷` from `adv` gives `k ▷ h(k)` and `h(k) ▷ h(h(k))`; Trans gives `k ▷ h(h(k))`; WeakL gives `h(h(k)) ⊬ n`, sound by `Derivation.sound` |
| `valid_advH`, `valid_worked` | the hypothesis holds in `model` against all machines, so the conclusion does |
| `not_valid_nonDed_hhn_n` | `h(h(n)) ⊬ n` fails in `model`: the conclusion is not trivially true |
| `nonDed_not_trans` | `n ⊬ m` and `m ⊬ n` hold, `n ⊬ n` fails (CCS26 §3.2, p. 6) |
| `freshL_needs_freshness` | `⊬ n` holds and `n ⊬ n` fails |
| `freshR_needs_large` | the Boolean name `b` is fresh in the empty vector, and `⊬ b` fails: the constant `true` guesses it with probability one half |

The rules of Fig. 3 have no countermodel of their own here: each is an inequality at every `η`
whose terms are all present.

### Derivations

`Derivation` gains `notDed`, `notNonDed`, `boxNotEq`, `dedTrans`, `nonDedWeakL`, `nonDedWeakR`,
`nonDedRwEquiv` (with the ground type of its right side as a premise), `dedApps` and
`nonDedFreshR` (with `large` and freshness in every model as premises), each sound in one line.
The type of `Derivation` is unchanged.

### Build and checks

- **Build.** `LEAN_NUM_THREADS=4 lake build SquirrelLogic` succeeds with no warnings.
- **Axioms.** `#print axioms` from a scratch file outside the repository on 40 declarations: the
  rules, their semantic laws and bounds, `Form.holds_nonDed`, `Form.holds_ded`,
  `prEvent_uniformSample_prod_update`, `negligible_two_rpow_neg_mul`, `AdvClass.all`,
  `Derivation.sound`, every check above and four M0 headlines. They use only `propext`,
  `Classical.choice` and `Quot.sound`.
- **Forbidden tactics, comment fences, line length.** No `sorry`, `stop` or `native_decide`; the
  fence check passes; no line exceeds 100 characters.

| File | Content |
|---|---|
| `Secrecy.lean` (new) | `deduceAdv`, `deduceErr`, `NonDed`, `Ded`, the bounds at `η`, `Distinguisher.deduce`, the laws |
| `Rules/Secrecy.lean` (new) | `FTerm.apps`, `Form.nonDed`, `Form.ded`, their readings, the `Valid` rules of Fig. 3, `Valid.ded_apps` |
| `Avoids.lean` (new) | `FTerm.Avoids`, its constructor lemmas, `Model.FreshAt` |
| `Rules/Fresh.lean` (new) | `negligible_two_rpow_neg_mul`, `Model.nameAt`, FreshR |
| `SecrecyExamples.lean` (new) | the model, the worked derivation, the countermodels |
| `Syntax.lean`, `Model.lean` | `Label.large`, `Ty.arrows`, `Ty.IsGround`, `Model.IsLarge`, `Ty.appVals`, `Ty.postcomp`, `Model.nameSlot` |
| `Indist.lean`, `Global.lean` | `AttackerFn.comp`, `Distinguisher.eqTest`, `comp_mem`, `eqTest_mem`; `Form.and`, `Form.ex`, `Form.bot`, `Form.not`, `FTerm.not`; `not_negligible_one` moves here |
| `Rules/Enc.lean` and its checks | `EncSymbols.Avoids` is an instance of `FTerm.Avoids` |

### Problems hit

1. **Implicit declarations.** A name of the example's own inductive type, passed where
   `Decl.Name ?D a b` is expected with `D` not yet known, makes elaboration time out; giving
   `(D := decl)` fixes it.
2. **`nomatch z, w`** parses as a match on two discriminants; a lambda ending in `nomatch` inside
   an anonymous constructor needs parentheses.
3. **Coin types.** `model.Coin η .bool` is `Bool` only up to unfolding, so `rw` with lemmas about
   `$ᵗ Bool` fails on the instance; `refine` with the type given explicitly works.
4. **`rw` through definitional unfolding.** `Nat.card_congr e` records `e`'s inferred type, not
   its ascription; the two types must be passed as named arguments.

### What remains

- **FreshL** (L20), after attacker functions become programs over a tape-reading interface.
- **Rw-Oracle and Pc-Oracle** need `adv` at order two (L2, L11).
- **Syntactic freshness** through `Term.heads`, after the PolyFun pin moves.
- **Part 2 (PRF rules).** CCS26's PRF rules (Fig. 4, Fig. 11, App. C.3) state the PRF assumption
  through named reductions whose distinguishers query an oracle `o_h^k = λx. h(x, k)`; the ψ
  conditions (`ψ_PRF,key`, `ψ_PRF,msg`) say the key occurs only as the key of `h` and that the
  message was never hashed before. Both need a reading of terms as programs that query the
  oracle, so that a reduction can answer the queries from its own game; the coupling and
  avoidance lemmas here carry over to the key's coordinate.

### Ledger

- **L10** records that `⊬` and `▷` read the shared tape and that FreshL is where it matters.
- **New rows**: L18 (the predicates as derived formulas, curried tuples), L19 (the label `large`),
  L20 (FreshL and CCS26's footnote 2), L21 (Rw-Equiv at ground types), L22 (FreshR's semantic
  side condition, closed for this fragment).

## M1, step 1b: machines over polynomial interfaces

This work was done on top of `f4c467596`, in commits `847b2002e` (tapes and machines),
`ce431975b` (the class over machines and the order bounds), `7b0504e02` (read bounds and long
tapes) and the commit that adds these notes. Sources: LICS23, the author report pinned in
`../SOURCES.md`; CCS26 §3.1 (p. 6) and App. C.2 (pp. 16–17); CSF24 App. A as cited in L11.

### Tapes as in LICS23

- **The attacker tape is a bitstring.** `Model.TapeA M η := Fin (M.lenA η) → Bool`, uniform, with
  `Model.readBit` returning `false` past its end. LICS23 §II-B (p. 5): `T^a_{M,η}` and
  `T^h_{M,η}` are "finite set[s] of bit-strings of the same length called random tapes".
- **Names read bit blocks.** A name of type `τ` reads `Model.Coin M η τ := Fin (M.coinLen η τ) →
  Bool` and runs `M.sample η τ` on it. LICS23 p. 6: "a name value requires at most a finite
  number of bits from `ρh`", so a model with "large enough honest tapes for names to draw their
  randomness" exists. The honest tape is still the product of one block per name and index, so
  independence stays structural (L12) and the coupling lemmas of `ProductTape.lean` apply
  unchanged. A machine that reads `coinLen` bits of its own tape and runs the sampler produces a
  name's distribution: this is what FreshL's reduction will do.
- **Examples.** Every example model has `lenA = 0`. Names read one bit in `TwoTimePad`,
  `EncExamples` and `WorkedEnc` (abbreviations `TwoTimePad.bit`, `EncExamples.encBit`), `η` bits
  for `msg` in `SecrecyExamples` (the sampler is `List.ofFn`, injective, so `msg` is `large` with
  `c = 1` as before; `model_isLarge` is re-proved from `Fintype.card_fun`), and none in
  `Model.trivial`.

### Machines (`Machine.lean`)

- **Interfaces are polynomial functors.** `Model.Iface M η τs := tapeSpec + M.inSpec η τs`, VCVio's
  sum of oracle specifications. A tape query `i` returns bit `i`; a query to an input of type `τ`
  carries values for all of `τ`'s arguments (`Ty.args τ`) and is answered by a value of
  `Ty.res τ`. A Boolean or base input is queried with no arguments. LICS23 Fig. 2 and §II-C.2
  (p. 7): base values are written on input tapes as encodings, functions are given by handles
  that the machine queries "using its query tape", and "handles are similar to oracles". Here
  every input is an oracle; LICS23's handles for partial applications are not modelled, since a
  query supplies all arguments, which suffices for inputs of order at most one.
- **Machines are free programs.** `Machine M τs β := (η : ℕ) → OracleComp (M.Iface η τs) (β.Value
  …)`, and `Machine.run A η ρa e` interprets the interface at `Id` by `Model.answer ρa e` (VCVio's
  `evalWithAnswerFn`, that is `simulateQ`). Machines are families over `η`; uniformity is the
  class's business.
- **Deep and shallow, in the small.** The function-level types stay as the semantics:
  `Machine.test : Machine M τs .bool → Distinguisher M τs` and `AdvMachine.eval : AdvMachine M τs β
  → AttackerFn M (Ty.arrows τs β)`, where `AdvMachine M τs β := Machine M (τs ++ β.args) β.res`
  takes the tuple and `β`'s arguments as inputs and is curried by `Ty.curryVals` and `Ty.curry`.
  Advantages, `deduceAdv` and every bound at `η` are still computed on functions; machines enter
  only through `run` lemmas (`Machine.test_app : (A.app ha).test = A.test.app`, …,
  `AdvMachine.eval_comp'`), so the M0 and part-1 proofs changed by one rewrite each.
- **Handlers.** Every construction is `Machine.handle H A := fun η => simulateQ (H η).impl (A η)`
  for a handler of the input interface into programs over another interface (PolyFun's `liftM`,
  VCVio's `closeHandler`). All `run` lemmas go through one fact, `Handler.EvalsTo.
  evalWithAnswerFn_simulateQ`: a handler that answers as the values `e'` turns a run at `e` into a
  run at `e'`. The constructions: `rename` (forward each query along a renaming), `app` (answer an
  input of type `b` by querying the input of type `a → b` at the value of the input of type `a`),
  `fn` (answer by an honest symbol), `subst` (answer the first input, of type `as → ρ`, by running
  a machine on the query's arguments and the remaining inputs), and, outside the handler form,
  `branch`, `const`, `eqTest` and `input`. The reductions of the rules are built from them:
  `ite`, `guard`, `adv`, `AdvMachine.comp` and `deduce`.
- **Problems hit.** `Ty.args (Ty.arrows τs β)` is stuck for a variable `τs`, so the substitution
  splits the arguments by recursion on `as` (`Ty.splitArgs`, `Ty.resArrows`,
  `Ty.apply_curryVals_curry`) rather than by a cast. Terms that are type-correct only up to
  unfolding `Ty.arrows [] β` or `Ty.args` defeat `rw` ("not type-correct under the implicit
  transparency"); the proofs chain `Eq.trans` instead. Dot notation puts the receiver at the first
  explicit argument of type `Machine`, so `subst` and `adv` take the outer machine first.

### The class (`Indist.lean`)

`AdvClass M` is a predicate `mem` on machines with these fields:

| Field | Construction | Rules | Polynomial-time counterpart |
|---|---|---|---|
| `rename_mem` | `Machine.rename` | Perm, Restr, Dup; inside FA-Adv, If, the case split, Trans, WeakL, WeakR, Rw-Equiv | `closeHandler` with a forwarding dispatcher of constant cost |
| `subst_mem` | `Machine.subst` | FA-Adv (`adv_mem`), Trans, WeakL, WeakR (`comp_mem`), Rw-Equiv (`deduce_mem`) | `closeHandler` with a `HandlerCertificate`; `IsOraclePPTBy.bind` |
| `app_mem` | `Machine.app` | FA-App | a handler making two queries per query |
| `fn_mem` | `Machine.fn` | FA-Fn, BC14's FA | honest symbols are polynomial-time (LICS23); `PureCertificate` |
| `branch_mem` | `Machine.branch` | If (`ite_mem`), the case split (`guard_mem`) | `IsOraclePPTBy.bind` with a two-way continuation |
| `const_mem` | `Machine.const` | the case split | `PureCertificate` of a constant |
| `eqTest_mem` | `Machine.eqTest` (ground types) | Rw-Equiv | bitstring equality (cslib-frontier's `decide_eq`) |
| `readBound_mem` | — | none yet; FreshL | a machine reading `ρa` from a tape in time `t` reads below `t`; `AllQueriesSatisfy` |

- **Why not one substitution field.** A substitution whose handlers are member machines receives
  the query's arguments as inputs; a handler that forwards a query (relabelling) or adds an
  argument to it (FA-App) would have to read those inputs back, which needs them to be Boolean or
  base values, and cannot forward a higher-order argument at all. So relabelling and querying an
  input at another input stay fields; they are the shapes the task named. `subst` takes over the
  old `adv_mem` and `comp_mem`, and `branch` with `const` the old `ite_mem` and `guard_mem`; the
  number of reduction fields goes from eight to seven, each one program construction.
- **Rw-Equiv no longer needs `app`.** Its reduction runs `g` with the left part of the vector
  forwarded (`subst` and `rename`) and compares with the last entry, so it never reads a
  higher-order entry.
- **`guard_not_derivable` is retired.** It showed that `guard` did not follow from five
  reductions that only change the input. `guard` is now derived (`AdvClass.guard_mem` from
  `branch_mem` and `const_mem`), so the statement no longer separates fields. It is replaced by
  `CaseStudy.guard_changes_output`, which records why the case split needs a construction that
  changes the output.
- **`AdvClass.all`** admits every machine with a polynomial read bound; each construction preserves
  a common bound (`Machine.ReadsBelow.rename`, `.subst`, `.branch`, …), so it meets every field.
  Every countermodel's machine reads no tape bit (`AdvClass.all_mem_of_readsBelow_zero`).
- **Semantics.** `C.Adv X` holds when an admitted `AdvMachine` evaluates to `X` everywhere;
  `C.Indist u v` quantifies over admitted machines returning a Boolean; `NonDed` and `Ded`
  quantify over admitted `AdvMachine`s. `⊬` and `▷` remain derived formulas.

### The order bounds

- **In the syntax.** `GlobalOp.adv τs β (h : Ty.AdvOrder τs β)` and `GlobalOp.equiv τs (h :
  Ty.IndistOrder τs)`, so an atom outside the fragment cannot be written; `Form.nonDed` and
  `Form.ded` carry `Ty.SecrecyOrder τs β` (entries and right side of order at most one), from which
  the bound of their `adv` follows (`Ty.SecrecyOrder.advOrder`). CCS26 §3.1 (p. 6): "the predicate
  `adv(·)` is only defined for terms of order at most 2, and therefore `u` and `v` must in turn be
  of order at most 1". Each constructor takes the bound as a last argument whose default,
  `of_decide_eq_true rfl`, proves it by evaluation for concrete types (`decide` refuses the free
  base-type variable of generic declarations).
- **The semantics stays total.** Machines exist for inputs of every type; the bounds are needed
  where a reduction reads an input: FA-App's argument is a Boolean or base type
  (`Ty.IndistOrder.isGround_app`), as `Machine.app` fetches it.
- **Rules.** A rule's conclusion carries the bound derived from its premise's (`.tail`, `.app`,
  `.ite`, `.dup`, `.rename`); a rule that adds an entry or has no premise (Refl, FA-Fn, FA-Adv,
  Eq1, name renaming, `ded_apps`, FreshR) takes the conclusion's bound. `equiv_fa` takes the bound
  of its intermediate vector explicitly, since FA-Fn's added symbol must have a ground argument.
  `EncInstance` has a field `order`.

### Read bounds and long tapes (`TapeBounds.lean`)

- `Machine.ReadsBelow A b`: every tape query of `A`, on every path, is below `b η` (VCVio's
  `AllQueriesSatisfy`). `Machine.ReadsBelow.run_eq` and `AdvMachine.eval_eq_of_readsBelow`: the
  run depends on `ρa` only through those bits.
- `RV.ReadsBelow X b`: `X` depends on `ρa` only through its bits below `b η`.
  `RV.readsBelow_of_eval` and `AdvClass.Adv.readsBelow`: an `adv` term has a polynomial bound,
  its machine's.
- `Model.LongTapes M`: `∀ p : Polynomial ℕ, ∀ᶠ η in atTop, p.eval η < M.lenA η`. LICS23 p. 17:
  random tapes are infinite in the base logic and finite here, which "is, however, not
  restrictive", since one can build "a model in our sense with long enough finite tapes (for each
  `η`)". CCS26's footnote 2 extends the tape "as needed". Not imposed anywhere.
- **Checks.** `Machine.readsBelow_readZero_one` and `Machine.not_readsBelow_readZero_zero`: the
  machine reading bit `0` reads below `1` and not below `0`.

### Statements that changed

- Every `∼`, `adv`, `⊬` and `▷` formula carries its order bound, so formulas outside the fragment
  of CSF24 and CCS26 are gone; the rules hold for every formula that can be written. `⊬` and `▷`
  previously existed at every type.
- `AdvClass.Indist.app` takes `a.IsGround`; `AdvClass.Indist.adv` and `Valid.equiv_adv` take a term
  of type `Ty.arrows τs₀ β` (every type is one, with `τs₀ = []`).
- `deduceAdv_le_add_advantage` takes `β.IsGround` and an `AdvMachine`, and bounds by the advantage
  of `(Machine.deduce hβ g).test`; `Distinguisher.appArgs`, `Distinguisher.deduce` and
  `AdvClass.appArgs_mem` are gone.
- `Valid.equiv_enc`, `EncInstance.Holds` and `WorkedEnc.workedDerivation_sound` state the IND-CPA
  hypothesis for every admitted machine, at the reduction `EncSymbols.encReduction … A.test`. The
  reduction still draws `ρa` itself, now a uniform bitstring, and is named.
- `CaseStudy.guard_not_derivable` is replaced by `CaseStudy.guard_changes_output` (above).
- `SecrecyExamples.not_nonDed_of_forall_eq` takes an admitted machine instead of a function; the
  countermodels use `SecrecyExamples.idMachine`, `hMachine`, `EncExamples.xorMachine`,
  `Machine.input`, `Machine.eqTest` and `Machine.const`.

### What FreshL needs

- **Definitions.** `Machine.ReadsBelow`, `RV.ReadsBelow`, `AdvClass.Adv.readsBelow`,
  `AdvClass.readBound_mem`, `Model.LongTapes`, and `ProductTape.lean` for the coupling.
- **The reduction.** From an admitted `g : AdvMachine M (τs ++ [b]) β` against `u, n ⊬ v`, build
  `g' : AdvMachine M τs β` that answers the input `n` (`Machine.subst` at `as = []`) by a machine
  reading the bits `[B η, B η + coinLen η b)` and running `M.sample η b`, with `B` a polynomial
  above the read bounds of `g` and of the terms. Over uniform `ρa`, those bits are independent of
  the bits below `B η`, so `g'` against `u ⊬ v` succeeds as `g` does against `u, n_fresh ⊬ v`;
  `G.Equiv.Fresh` and Rw-Equiv move from `n_fresh` to `n` (CCS26 App. C.2).
- **Missing pieces.** A closure field admitting the sampling machine (reading bits at a polynomial
  offset and running the sampler); polynomial `coinLen` and polynomial-time samplers as model
  conditions (L12); `LongTapes` as a hypothesis on `R`, so that `B η + coinLen η b ≤ lenA η`
  eventually; read bounds for the terms `u`, `v`: `adv` terms have them, names read no `ρa`, but
  attacker symbols (`Model.att`) are arbitrary functions of `ρa` and need a model condition or the
  side condition of CCS26 Fig. 11's caption; and a satisfiability model with `LongTapes`.

### Build and checks

- **Build.** `LEAN_NUM_THREADS=4 lake build SquirrelLogic` succeeds with no warnings.
- **Axioms.** A scratch file outside the repository prints the axioms of 113 headlines (every
  rule, `Derivation.sound`, the worked derivations, the satisfiability models and countermodels,
  the `run` and read-bound lemmas) and sweeps all 1599 declarations of the library's modules: only
  `propext`, `Classical.choice` and `Quot.sound` occur.
- **Forbidden tactics, comment fences, line length.** No `sorry`, `admit`, `stop` or
  `native_decide`; the fence check passes; no line exceeds 100 characters.

### Ledger

L10, L11, L12, L14 and L20 are updated, and L23 (long tapes) is new.

## M1, part 1c: FreshL

This work was done on top of `ed54b8aa9`, in commits `9ab692cb4` (the machines and class fields),
`2d582319d` (read bounds of terms), `234d97931` (FreshL and the derivation constructor),
`bc2e8ca21` (the long-tape model and the uses of part 1's rules), `879297cd5` (the countermodel)
and the commit that adds these notes. Sources: CCS26 Fig. 11 and App. C.2 (pp. 16–17), the
authors' PDF pinned in `../SOURCES.md`; LICS23 §II-A.3, §II-B.2 (p. 6), §II-C.1 and p. 17.

### The reduction, as a machine

- **Pieces.** `Machine.shift off A` runs `A` with every tape read moved `off η` bits along: the
  handler `Machine.shiftImpl` of the tape interface, applied by `simulateQ`, with
  `Machine.run_shift` (the run at `ρa` is the run at `Model.shiftTape (off η) ρa`).
  `Machine.sampler b hb` reads the first `coinLen η b` bits of the tape (`Machine.readBits`),
  fetches `b`'s arguments (`Machine.fetchVals`; they are Boolean or base since `b` has order at
  most one, `Ty.isGround_of_mem_args`), and returns the model's sampler applied to them
  (`Machine.run_sampler`).
- **The reduction.** `AdvMachine.freshL off hb g` answers `g`'s input for the fresh name, the last
  entry of its tuple, by `(Machine.sampler b hb).shift off`, through `Machine.subst` after the
  relabelling `Machine.lastFirst` that moves that input first. `AdvMachine.appVals_eval_freshL`:
  it computes `g` applied to `u` and the sampler's value on the bits `[off η, off η + coinLen η b)`
  (`Model.coinAt`). FreshL takes `off` to be a polynomial `p`, the sum of the read bounds of `g`
  and of the terms.

### Class and model conditions

| Condition | Kind | Used for | Polynomial-time counterpart |
|---|---|---|---|
| `shift_mem p` | closure field, `p` a polynomial | the offset of the sampler | computing `p(η)` from `1^η` and adding it to each tape index: a tape handler of polynomial cost (`closeHandler`, `HandlerCertificate`) |
| `sampler_mem hb` | closure field, given `Model.PolyCoins b` | drawing the fresh name | LICS23 §II-B.2 makes names polynomial-time samplings; `PureCertificate` for the sampler (cslib-frontier's `IsPPTOn`) after the tape reads, by `IsOraclePPTBy.bind`; a model–class compatibility condition like `fn_mem` |
| `readBound_mem` | closure field (from step 1b) | the bound `p` above `g`'s reads | a machine running in time `t` reads below `t` |
| `Model.PolyCoins M b` | model condition, hypothesis on `R` | the field's premise, and room on the tape | a polynomial-time sampling reads polynomially many bits |
| `Model.LongTapes M` | model condition, hypothesis on `R` | room above `p` at every large `η` | LICS23's "long enough finite tapes" (p. 17) |

- **Uniformity.** No field admits an `η`-indexed constant: offsets are polynomials, and the only
  values the fields supply are Booleans, honest symbols and samplers. `AdvClass.all` meets both new
  fields (a shifted machine reads below `p + q`; the sampler below `coinLen`).
- **Why the premise on `sampler_mem`.** With `Model.PolyCoins` as a premise of the field rather
  than a condition on `AdvClass.all`, the information-theoretic class stays a function of the
  model alone, and no existing satisfiability model or countermodel changes.
- `AdvClass.freshL_mem`: the reduction is admitted, from `subst_mem`, `rename_mem`, `shift_mem` and
  `sampler_mem`.

### What the terms read of ρa

- `VecRV.ReadsBelow` (every entry), `RV.ReadsBelow.mono`, `VecRV.exists_readsBelow` (finitely many
  polynomial bounds give one, their sum).
- `FTerm.ReadsPoly M C t env`: the random variable of `t` at `env` reads below a polynomial.
  Constructor lemmas: `readsPoly_fn`, `readsPoly_tt`, `readsPoly_ff` (nothing), `ReadsPoly.name` (a
  name reads only what its index reads), `ReadsPoly.app`, `.ite`, `.eq`, `.not` (the sum), and
  `readsPoly_of_adv` (a term computed by an admitted machine has its bound).
- **Choice (L24).** Free variables and attacker symbols get their bounds from `adv` hypotheses
  (`Valid.readsPoly_of_adv`), not from a model condition. CCS26's caption of Fig. 11 asks every
  declared variable to be a name or adversarial, and LICS23 (p. 17) adds `adv(g)` for every
  attacker symbol; the worked derivation uses `adv(a)` for its attacker symbol `a`. A model
  condition on `Model.att` would have restricted the models without the paper asking it. λ and the
  local quantifiers are not covered: their bodies are read at every value of the bound variable,
  and a bound uniform in that value is not built.
- `FTerm.att` (smart constructor), `FTerm.denote_att`, `FTerm.avoids_att` are new.

### The proof

- **At one `η`** (`deduceAdv_freshL_eq`): if `g`, `u` and `v` read below `p` and `n(i)` is fresh in
  `u` and `v`, then at every `η` with `p(η) + coinLen η b ≤ lenA η`,
  `deduceAdv (g.freshL p hb).eval u v η = deduceAdv g.eval (u, n(i)) v η`. The map that swaps the
  bit block `[p(η), p(η) + coinLen η b)` of ρa with the honest coordinate of `n(i)` is an
  involution of the tapes, so it preserves the uniform distribution
  (`prEvent_uniformSample_equiv`). After the swap the reduction reads the name's old coordinate,
  while `g`, `u` and `v` see the same bits below `p(η)` and the same honest tape outside the
  coordinate.
- **Not through G.Equiv.Fresh.** CCS26 goes through `u, n ∼ u, n_fresh` and Rw-Equiv. That needs a
  name occurring nowhere, which a fixed declaration may not have, and Rw-Equiv is proved only at
  ground types (L21); the single bijection gives equality directly, for every type of order at most
  one.
- **Asymptotically** (`AdvClass.NonDed.freshL`): `LongTapes` at `p + pc`, with `pc` bounding
  `coinLen`, gives the condition for all large `η`, and `negligible_of_eventuallyLE` transfers
  negligibility. `Valid.nonDed_freshL_of_readsPoly` (any context, side conditions under `Θ`) and
  `Valid.nonDed_freshL` (closed vectors, freshness by `FTerm.Avoids`) are the rules.
- **Footnote 2.** No model is extended: the premise is applied in the model where the conclusion
  is evaluated, and the bits the reduction needs are there by `LongTapes`. The question whether `Θ`
  holds in an extended model (L20) does not arise.
- `Model.longTapes_of_two_pow_le`: tapes of at least `2^η` bits are long, since `p(η)·2^{-η}` is
  negligible (`negligible_polynomial_mul`).

### Derivations

`Derivation D enc R₀` gains the parameter `R₀`, the restriction on models its rules assume.
`nonDedFreshL` takes as premises that `R₀` gives `LongTapes` and `PolyCoins b`, the read bounds in
every model of `R₀` and `Θ` and every class, and freshness by `FTerm.Avoids`;
`Derivation.sound` takes `hR : ∀ M, R M → R₀ M`. Derivations without FreshL take `R₀` to be every
model (`fun _ => True`); the four existing derivations changed by one argument each, and
`SecrecyExamples.freshR` and `workedDerivation` are polymorphic in `R₀`.

### Checks

| Check | Shows |
|---|---|
| `FreshLExamples.longModel_longTapes`, `longModel_polyCoins`, `longModel_respectsLabels` | the model with tapes of `2^η` bits meets FreshL's model conditions |
| `FreshLExamples.valid_advA` | `adv(a)` holds there: the attacker symbol is the sampler of messages on the tape |
| `FreshLExamples.freshLDerivation`, `freshLDerivation_sound` | from `adv(h)`, `adv(a)`: FreshR, `▷` twice, Trans, WeakL give `h(h(a)) ⊬ n`, and FreshL adds `m`; the read bound of `a` comes from `adv(a)` |
| `FreshLExamples.valid_freshLWorked` | all of FreshL's hypotheses hold jointly with `AdvClass.all`, and `h(h(a)), m ⊬ n` holds |
| `FreshLExamples.not_valid_freshL_n` | `h(h(a)), n ⊬ n` fails: the conclusion depends on freshness |
| `SecrecyExamples.freshL_needs_freshness` | unchanged: `⊬ n` holds and `n ⊬ n` fails |
| `FreshLCountermodel.freshL_needs_longTapes` | with an empty attacker tape, against the class generated by the closure fields, `[] ⊬ m` holds, `n ⊬ m` fails, and every other hypothesis of FreshL holds |

- **The countermodel.** `Gen M` is the least predicate closed under the constructions of the
  closure fields and containing their base machines and the input projections (`Machine.input`,
  which every polynomial-time class contains; without it the generated class has no identity and
  `n ⊬ m` would hold). `Gen.mem_all` gives the read bounds, so `genClass M` is an `AdvClass`. In
  `cmodel` a message is `[true]` except with probability `2^{-(η+1)}`, and the empty tape gives the
  sampler the all-`false` block, whose value is `[false]`. `Gen.clean`, by induction over `Gen`: on
  inputs without `[true]`, no machine outputs `[true]`. So no machine without inputs guesses `m`
  beyond probability `2^{-(η+1)}`, while the identity on `n` computes `m` with probability at least
  `1 − 2·2^{-(η+1)}` (a union bound over the marginals, `prEvent_nameAt`, new in
  `Rules/Fresh.lean`). The construction uses one likely value instead of two values sharing the mass: two would need
  the independence of the two names, and the class's inability to produce the value is the same.

### Part 1's rules, used

`SecrecyExamples` uses Neg1 (`valid_neg1`: `¬ (k ▷ n)`), Neg2 (`valid_neg2`: `¬ (k ⊬ h(k))`),
Ineq (`valid_ineq`: `[n ≠ h(k)]`), Rw-Equiv (`valid_rwEquiv`: `k ⊬ h(h(n))` from
`k, h(h(n)) ∼ k, n`, valid in `model` where `h` is the identity, `valid_equiv_k_hhn`) and WeakR
(`valid_weakR`: `k ⊬ h(n)` from `k ⊬ h(h(n))` and `h(n) ▷ h(h(n))`). Checks that premises are
needed: `neg1_needs_nonDed` (`¬ (k ▷ h(k))` fails), `ineq_needs_nonDed` (`[h(k) ≠ h(k)]` fails
while `k ▷ h(k)` holds), `rwEquiv_needs_equiv` (`k ⊬ n` holds and `k ⊬ k` fails, so neither
Rw-Equiv nor WeakR passes between them without its second premise). The declaration gains an
attacker symbol of type `msg`, constant in `model`; `hMachine`, `idMachine`, `valid_advH` and
`not_nonDed_of_forall_eq` are stated for every model.

### Problems hit

1. **`simp` on membership of formulas.** `advA ∈ [advH, advA]` by `simp` timed out at `whnf`,
   deciding the equality of two formulas; `List.mem_cons_of_mem _ List.mem_cons_self` is instant.
2. **Binder types from arithmetic.** In `fun j => M.readBit ρa (n + j)` with `j : Fin k` expected,
   `n + j` elaborated `j` as a natural number; the binder needs its type.
3. **`renameInl` unification.** In `rename renameInl` with target `[] ++ (Ξ ++ Γ)`, Lean solved
   `Ξ := []`; the block is given explicitly, `renameInl (Γ := …)`.
4. **Dot notation on function types.** `Vec`, `VecRV` and `CleanVals` unfold to function types, so
   `u.ReadsPoly` and `he.append` fail; the full names work.
5. **`dif_pos` is deprecated** at this toolchain; `split_ifs` with `omega` replaces it.
6. **`nomatch x, y`** again parsed as two discriminants inside an anonymous constructor.

### Build and checks

- **Build.** `LEAN_NUM_THREADS=4 lake build SquirrelLogic` succeeds with no warnings.
- **Axioms.** The scratch file of step 1b, extended by 55 headlines of this part, prints the axioms
  of 167 declarations and sweeps all 1922 declarations of the library's modules: only `propext`,
  `Classical.choice` and `Quot.sound` occur.
- **Forbidden tactics, comment fences, line length.** No `sorry`, `admit`, `stop` or
  `native_decide`; the fence check passes; no line exceeds 100 characters, and no file 1500 lines.

| File | Content |
|---|---|
| `Machine.lean` | `Model.shiftTape`, `Model.coinAt`, `Machine.shift`, `readBits`, `fetchVals`, `sampler`, `lastFirst`, `AdvMachine.freshL`, their `run` lemmas and read bounds |
| `Indist.lean` | `Model.PolyCoins`, `shift_mem`, `sampler_mem`, `AdvClass.freshL_mem` |
| `TapeBounds.lean` | `VecRV.ReadsBelow`, `FTerm.ReadsPoly` and its constructor lemmas, `Valid.readsPoly_of_adv` |
| `Rules/FreshL.lean` (new) | `Model.longTapes_of_two_pow_le`, `deduceAdv_freshL_eq`, `AdvClass.NonDed.freshL`, the rules |
| `Derivation.lean` | the parameter `R₀`, `nonDedFreshL` |
| `FreshLExamples.lean`, `FreshLCountermodel.lean` (new) | the checks above |

### What remains

- **Read bounds under binders** (L24): λ and the local quantifiers.
- **Syntactic side conditions**: freshness through PolyFun's `Term.heads`, after the pin moves.
- **FreshL for open vectors in derivations**: the semantic rule covers them; the constructor takes
  closed vectors, as FreshR's does.
- **Polynomial time itself**: the class is still a parameter (L14); the new fields name their
  polynomial-time counterparts but no polynomial-time class is built.

### Ledger

L20 is closed for this fragment, with the replacement of footnote 2 recorded; L23 is closed
(satisfiable and needed); L12 is closed as stated conditions; L10, L14 and L18 are updated; L24
(the read-bound side condition and its choice for free variables and attacker symbols) is new.

## M1, part 2: PRF

This work was done on top of `4eaa47a1b`, in commits `13554120c` (the compiled reading and its
adequacy), `eef60ea51` (G.PRF), `1f6f9af9b` (PRF-Simple and the derivation constructor),
`3376c0b6b` (the checks), `87c6bf70b` (decidability, placement, the ledger) and the commit that adds
these notes. Sources: LICS23, the author report pinned in `../SOURCES.md` (G.PRF and the `ψ`
conditions, p. 29; generalised subterms, Fig. 1, p. 4; `⊢pptm`, Fig. 10, p. 27, and its machine,
p. 28); CCS26 Fig. 4 and §3.3–3.4 (pp. 7–8), Fig. 11 and p. 17 (PRF-Simple and its derivation),
App. C.3 (pp. 18–19, the PRF reduction).

### Terms with calls

- **The calls are syntax.** CCS26's reduction evaluates the terms "calling the hash oracle when a
  hash with key `k` is needed". A fold cannot recognise the pattern `h(t, k)`, which spans five
  nodes, so the hashes with key `k` are explicit: `PRFSymbols.oSig P` is the local signature with
  one more constructor, `call t`, CCS26's `o_h^k(t)`, and its terms are `OTerm P Γ τ`.
  `PRFSymbols.close` replaces each `call t` by `h(t, k)` (a fold), and `denote_close` says that a
  closed-up term means its calls read as hashes at the key of the honest tape.
- **ψ_key** (`PRFSymbols.KeyFree`) is the fold `Term.Every` of "this constructor is not the key
  name". In a closed-up term the key then occurs only as the key of `h`: that is CCS26's
  `ψ^k_PRF,key`, context-sensitive on the closed-up terms and context-free on the terms with calls.
  It is decidable when names have decidable equality (`Term.decidableEvery`), and
  `ointerp_eq_of_keyFree` is what it gives: the reading ignores every coordinate of the key name.
- **ψ_msg** (`PRFSymbols.psiMsg`) is the conjunction, over the arguments `t′` of the calls of
  `u⃗` and `m`, of `t′ ≠ m`, generated by the fold `PRFSymbols.calls`, which rebuilds the syntax
  beside the list (a fold into pairs, so no recursion on terms is written by hand).
  `psiMsg_eq_true_iff` reads it pointwise. The challenge is not a call of `u⃗` or `m`.
- **First order.** Calls are collected only in terms without abstraction (`PRFSymbols.FirstOrder`),
  so every argument lives in the term's own context; LICS23's generalised subterms would carry
  the bound variables. The conditions of enclosing conditionals are dropped, which strengthens
  `ψ_msg` and keeps the rule sound. Both are recorded (L26).

### The compiled reading (`MonadicReading.lean`, `Compile.lean`)

- **The generic part** (`MonadicReading.lean`, no Squirrel import beyond `Sum.lean`, both bound
  for PolyFun): a call-by-value algebra `CBVAlgebra σ m V` receives each argument as a computation
  of the argument's value from the values of its bound variables; `Term.cbv` is the fold of
  `Term.denote` with variables returned by `pure`. `Term.cbv_rel` is the fundamental lemma of a
  logical relation between a plain reading and the call-by-value one, for any relation between
  values and between values and computations, over the terms of a fragment `Term.Every ok`; its
  proof is one induction. `Term.denote_eq_of_every` is the congruence of the plain reading.
- **The instance.** Values are Kleisli values (`Ty.KVal`): Booleans and base values as they are,
  `a → b` as `a → OracleComp _ b`. The interface `PRFSymbols.Iface P M η` is the sum of the honest
  coins (query a slot, receive its bit block), the attacker tape, and the hash oracle `Dom →ₒ Rng`.
  `PRFSymbols.cbvAlg` evaluates application function first, then argument, then runs the function;
  an abstraction is a closure; a conditional runs only its branch; a name queries the coin of its
  slot and runs the sampler; an attacker symbol queries the tape; `call t` evaluates `t` and queries
  the oracle.
- **Adequacy** (`PRFSymbols.cbv_adequate`, `lower_evalWithAnswerFn_cbv`): running the compiled
  term with `PRFSymbols.answer M η ρ kv`, the tapes' coins and tape and hashes keyed by `kv`, gives
  the ordinary reading at `ρ` with calls hashed under `kv`. The relation `CRel` is equality at
  Boolean and base types and "related arguments give related runs" at arrows.
- **Tracking the hashes** (`PRFSymbols.cbv_guard`): the same relation carries `HashOK ans Q`, every
  hash query of the run satisfies `Q`. The ordinary reading is paired with a proposition
  (`guardInterp`), `Q` of every call argument, under an abstraction at every value of the bound
  variable. One application of `Term.cbv_rel` gives both; adequacy is the case `Q = True`, whose
  proposition always holds (`snd_denote_guardInterp_true`). For first-order terms the proposition
  is `ψ_msg`'s conjunction (`snd_denote_guardInterp_iff`).
- **The fragment** (`PRFSymbols.Pptm`, L25) mirrors LICS23's `⊢pptm`: variables, application,
  abstraction, names at Boolean or base indices with results of order at most one, honest and
  attacker symbols of order at most one, conditionals, Boolean constants, equality at Boolean and
  base types, and calls on Boolean or base types. Local quantifiers are out: PT.Quant enumerates a
  polynomial type, which the reading does not do. Equality at arrow types is out because Kleisli
  arrows are not compared; higher-order symbols are out because their values cannot be passed to a
  Kleisli arrow.

**How it realises App. C.3.** CCS26's `A₁` and `A₂` "recursively evaluate the terms", reading the
honest tape for names other than `k(t)` and calling the hash oracle "when a hash with `k(t)` is
needed" (p. 18). Here that machine is `Term.cbv` of `cbvAlg`, a free program over coins, tape and
hash; the recursion is the fold. The reduction runs it by a handler (`PRFSymbols.fwd`) that answers
coins and the tape from the tapes it drew and forwards the hash to its PRF oracle; the real and
ideal experiments are further handlers. CCS26's assumption that the machines never ask for the key
is ψ_key: a key-free term never queries a coordinate of the key name.

**What the polynomial-functor reading buys.** Terms become free programs over an interface, the
reduction is handler composition (`simulateQ (fwd ρ)` then `prfRealQueryImpl` or `romImpl`), and
every fact about the reduction is a fact about a fold: adequacy and the hash invariant are one
logical relation (`Term.cbv_rel`); the real world is one induction on free programs
(`simulateQ_prfRealQueryImpl_fwd`); the log is VCVio's `withQueryLog`; the ideal world is one
induction on the program against the lazily sampled random function
(`eq_none_of_mem_support_run`). No machine is written by hand.

### G.PRF (`Rules/PRF.lean`)

```
Valid.equiv_prf P u m nn i hg hmg hku hkm hpu hpm hfu hfm hnk hR hprf hmsg :
  Valid R C Θ (.equiv (Vec.snoc (P.closeVec u) (P.hashTerm (P.close m)))
    (Vec.snoc (P.closeVec u) (FTerm.name nn (FTerm.fn i))) ho)
```

for a closed vector `u⃗ : OVec P [] τs` and message `m`, with entries and message of Boolean or base
type (`hg`, `hmg`), ψ_key (`hku`, `hkm`), `⊢pptm` (`hpu`, `hpm`), first order (`hfu`, `hfm`), `n`
not the key name (`hnk`), `[ψ_msg]` (`hmsg`), and in every model of `R` uniform names of the hash
type and `n(i)` fresh in `u⃗` and `m` (`hR`). `hprf` is the assumption: for every admitted machine
`A`, `P.prfAdv M η hU (P.hashReduction η u m A.test)` and the same for `freshReduction` are
negligible.

- **The PRF.** `PRFSymbols.scheme P M η`: the key is the bit block of the key name, drawn
  uniformly; `eval kc x = h(x, k)` at the key's sample. `P.prfAdv` is VCVio's `prfAdvantage` with
  the random function's values drawn by `Model.uniformSampler`, the sampler of the hash type, which
  is uniform by `Model.UniformSampler`.
- **The reductions** (`hashReduction`, `freshReduction`, instances of `reductionWith`): draw both
  tapes, run `PRFSymbols.prog` (the compiled vector, then the message) logged by `withQueryLog`
  through `fwd`, then take the challenge (the oracle at the message, or a fresh draw of the hash
  type's sampler), and return the distinguisher's output, or `false` if the log hashes the
  message.
- **The bound** (`PRFSymbols.advantage_le`): at every `η`, advantage ≤ `prfAdv (hashReduction)`
  + `prfAdv (freshReduction)` + `Pr[ψ_msg = false]`.
- **Hop 1 and 3, the real side** (`prEvent_prfRealExperiment_hashReduction`, `…_freshReduction`):
  the reductions' outputs are the events of the conclusion where the message was not hashed, over
  the key's coin, the tapes and the challenge's bits. `prEvent_uniformSample_update_update` couples
  them with a uniform tape whose key coordinate is the key and whose `n` coordinate is the
  challenge; `close_apply_couple` reads the terms there (freshness, then `denote_close`, then
  ψ_key).
- **Hop 2, the ideal world** (`prEvent_prfIdealExperiment_hashReduction`): the two reductions agree
  exactly. `eq_none_of_mem_support_run`: on every possible run, the random function's cache is
  empty at every message the log does not hash. So where the guard passes, the oracle's answer is a
  fresh uniform draw, the same as the second reduction's challenge.
- **The bad event**: where `ψ_msg` holds at the tape with the key overwritten, the compiled run
  hashes no copy of the message (`cbv_guard` with `Q = (· ≠ m)`, transported along ψ_key by
  `guardInterp_eq_of_keyFree`). The split `Pr[p] − Pr[q] ≤ |Pr[p ∧ ¬bad] − Pr[q ∧ ¬bad]| + Pr[bad]`
  charges the guard once, not twice.
- **Why two PRF reductions and not three.** CCS26 bounds the bad event in the ideal world by a third
  PRF game. Here both reductions carry the guard, so the ideal hop is an equality and the bad event
  is only ever bounded in the real world, by `Pr[¬ψ_msg]`.
- `PRFSymbols.prfAdv_eq_zero_of_bijective`: if the hash under a uniform key is a uniform function
  on a finite domain, every distinguisher has PRF advantage zero
  (`OracleComp.evalDist_simulateQ_romImpl_run'_eq_completeTable` for the ideal side).

### PRF-Simple

```
Valid.nonDed_prf P u v m nn i … (h : Valid R C Θ (.nonDed (P.closeVec u) (P.close v) ho)) :
  Valid R C Θ (.nonDed (Vec.snoc (P.closeVec u) (P.hashTerm (P.close m))) (P.close v) ho')
```

derived as CCS26 derives it (p. 17): G.PRF on the vector `u⃗, v` gives `u⃗, v, h(m, k) ∼ u⃗, v, n`;
Perm (`swapLast`, `rename_swapLast`) moves `v` last; FreshL turns `u⃗ ⊬ v` into `u⃗, n ⊬ v`;
Rw-Equiv, for a secret of Boolean or base type, concludes. Its hypotheses are the three rules':
G.PRF's at `u⃗, v` (with `[ψ_msg(u⃗, v, m)]`, CCS26's premise), FreshL's long tapes, polynomial bit
blocks and read bounds, and `n` fresh in `u⃗`, `v` and `m`. `Derivation.nonDedPRF` builds the same
derivation from the constructors, with casts along `closeVec_append` and `rename_swapLast`.

### Derivations

`Derivation D enc prf R₀` gains the parameter `prf : PRFInstance D → Prop` and the constructor
`equivPRF`, with `PRFInstance.Syntactic` and a derivation of `[ψ_msg]` as premises;
`Derivation.sound` takes `PRFInstance.Holds R C` for each admitted instance. The existing
derivations change by one argument each, and their soundness corollaries by one.

### Checks (`PRFExamples.lean`)

The declaration has a base type `msg` labelled `large`, keys of type `msg → msg`, the key name
`k`, message names `n`, `s`, `r`, the index `idx`, a constant `c` and `h : msg → (msg → msg) → msg`.
In `pmodel` messages at `η` are bitstrings of length `η`, a key is a uniform function table read
from `η · 2^η` bits through a bijection (`keyEquiv`), `h(x, k) = k(x)`, and the attacker tape has
`2^η` bits.

| Check | Shows |
|---|---|
| `pmodel_prfAdv` | `h` is a perfect PRF: every distinguisher has PRF advantage zero |
| `pmodel_uniformSampler`, `pmodel_isLarge`, `pmodel_longTapes`, `pmodel_polyCoins` | the model conditions of G.PRF and FreshL |
| `inst_syntactic`, `inst_holds`, `valid_psiH`, `valid_gprf` | every hypothesis of G.PRF holds jointly at an instance, against `AdvClass.all`, and `s, h(r, k) ∼ s, n` holds |
| `prfWorked`, `prfWorked_sound`, `valid_prfWorked` | a derivation ending with PRF-Simple: FreshR gives `⊬ s`, PRF-Simple adds `h(r, k)`; sound by `Derivation.sound`; all hypotheses hold jointly in `pmodel` |
| `gprf_needs_psiMsg` | with `u⃗ = h(c, k)`, `m = c`: ψ_key and the PRF hypothesis hold, `[ψ_msg]` fails, and `h(c, k), h(c, k) ∼ h(c, k), n` fails |
| `gprf_needs_psiKey` | with `u⃗ = k(c)`, `m = c`: `[ψ_msg]` and the PRF hypothesis hold, ψ_key fails, and `k(c), h(c, k) ∼ k(c), n` fails |

Both countermodels are the equality test (`not_indist_eq_name`): on the left the two entries are
equal, on the right the second is a fresh name, equal to the first with probability at most
`2^{-η}` (`deduceAdv_nameAt_le`).

### Problems hit

1. **Pattern matching through a fold.** `h(t, k)` cannot be recognised by `Term.denote`; explicit
   call syntax and `close` replace a paramorphism with casts between sorts.
2. **Three PRF games.** Bounding the bad event in the ideal world needs a third reduction; moving
   the guard into both reductions makes the ideal hop an equality (above).
3. **`nomatch x, y`** again parsed as two discriminants inside anonymous constructors.
4. **Instances in statements.** `prfAdvantage` needs `DecidableEq` on the domain and a sampler of
   the range; both are fixed in `PRFSymbols.prfAdv` (`Classical.decEq`, `Model.uniformSampler`),
   and the ideal-world lemma is stated for any instances whose sampler is the hash type's.
5. **Reducibility in examples.** With `P` a `def`, `OTerm P [] msg` and `P.oSig.Term [] (.loc
   P.msgTy)` differ at reducible transparency and `rw` fails; `P` is an `abbrev`.
6. **Closed-up terms are not syntactically the logic's terms.** `close (OTerm.name x i)` and
   `FTerm.name x (close i)` differ in their empty argument functions; `close_name`, `close_fn` and
   `close_app` are propositional, and derivations are cast along them.

### Build and checks

- **Build.** `LEAN_NUM_THREADS=3 lake build SquirrelLogic` succeeds with no warnings.
- **Axioms.** The scratch file of step 1b, extended by 50 headlines of this part, prints the axioms
  of 217 declarations and sweeps all 2430 declarations of the library's modules: only `propext`,
  `Classical.choice` and `Quot.sound` occur.
- **Forbidden tactics, comment fences, line length.** No `sorry`, `admit`, `stop` or
  `native_decide`; the fence check passes; no line exceeds 100 characters, and no file 1500 lines.

| File | Content |
|---|---|
| `MonadicReading.lean` (new) | `CBVAlgebra`, `Term.cbv`, `Env.Rel`, `Term.Every` and its decidability, `Term.cbv_rel`, `Term.denote_eq_of_every` |
| `OracleTerm.lean` (new) | `PRFSymbols`, `oSig`, `OTerm`, `close`, `KeyFree`, `Pptm`, `FirstOrder`, `calls`, `psiMsg` and their lemmas |
| `Compile.lean` (new) | the interface, `Ty.KVal`, `cbvAlg`, `answer`, `HashOK`, `CRel`, `guardInterp`, `cbv_guard`, `cbv_adequate`, `prog` |
| `Rules/PRF.lean` (new) | `Model.UniformSampler`, `scheme`, `prfAdv`, the reductions, the hops, `advantage_le`, `Valid.equiv_prf`, `Valid.nonDed_prf`, `PRFInstance` |
| `Derivation.lean` | the parameter `prf`, `equivPRF`, `Derivation.nonDedPRF` |
| `Machine.lean` | `Env.forall_append`, `Env.append_renameInl`, `swapLast` |
| `PRFExamples.lean` (new) | the checks above |

### What remains (part 3)

- **The oracle on the left.** PRF.R, PRF.L-sec, Rw-Oracle and Pc-Oracle put `o_h^k = λx. h(x, k)`
  in the vector, and the attacker queries it through an input handle. The compiled reading already
  covers abstraction (`cbv_guard` holds for the `⊢pptm` fragment with `λ`), so the oracle compiles
  to a Kleisli arrow that queries the hash; the distinguisher must then be a machine whose input
  queries are answered by running that arrow (handler composition with `Machine.handle`), rather
  than a function of values. Rw-Oracle and Pc-Oracle need `adv` at order two (L2, L11).
- **ψ_msg with binders**: LICS23's generalised subterms with the bound variables and the
  conditions above an occurrence, for higher-order entries (L26).
- **Higher-order entries** in G.PRF, which need the distinguisher as a machine (above).
- **Key occurrences at other indices**, which LICS23 admits when `t₀ ≠ t`.

### Ledger

L3 is closed for this fragment; L6, L7, L10 and L14 are updated; L25 (the `⊢pptm` fragment of the
compiled reading) and L26 (`ψ_msg` for first-order terms) are new.

## M1, part 3a: oracle rules

This work was done on top of `2a91b5f30`, in commits `02c81e97e` (reductions run machines),
`7e401e139` (query bounds and the guess), `d5e9fe222` (Rw-Oracle and Pc-Oracle), `cf96da92d` (a
docstring), `d017751fe` (the checks) and the commit that adds these notes. Sources: CCS26 Fig. 3
(p. 7) and App. C.1 (pp. 15–16), the authors' PDF pinned in `../SOURCES.md`; LICS23 §II-C.

### Reductions run machines

- **What changed.** `EncSymbols.encReduction` and `PRFSymbols.reductionWith` (so `hashReduction`
  and `freshReduction`) take the admitted machine itself, not its denotation, and run its program:
  `Machine.simulate A η ρa H := simulateQ (M.answerIn ρa H) (A η)`, where `Model.answerIn` answers
  tape reads from the tape the reduction drew and input queries by `H : InputImpl M η τs m`, a
  computation per input in the reduction's own oracle computations. Ground inputs are answered from
  the values the reduction computed (`InputImpl.ofVals`); an order-1 input can be answered by a
  computation that queries the reduction's oracle, such as a compiled Kleisli arrow.
- **Fusion.** `Machine.simulateQ_simulate`: if the reduction's oracle `impl` runs every answer of
  `H` as the values `e` answer it, `simulateQ impl (A.simulate η ρa H) = pure (A.run η ρa e)`. The
  value case is `Machine.simulate_ofVals`, from `OracleComp.simulateQ_pure_comp` (the monad
  morphism `pure` commutes with the fold). `EncSymbols.encReduction_distinguish` is the encryption
  reduction's last step. The existing proofs carry over by adding `Machine.simulate_ofVals` to
  their `simp` sets; `A.test` replaces `A` in the bounds.
- **Hypotheses.** `hcpa` (`Valid.equiv_enc`, `EncInstance.Holds`, `WorkedEnc.workedDerivation_sound`)
  and `hprf` (`Valid.equiv_prf`, `Valid.nonDed_prf`, `PRFInstance.Holds`) quantify over
  `encReduction … A η` and `hashReduction η u m A` for admitted machines `A`.
- **Why this is the polynomial-functor point.** A machine is a free program over the polynomial
  interface `tapeSpec + inSpec`; a reduction is the substitution of handlers into it (`simulateQ`,
  PolyFun's `liftM`), and its semantics is a fold, so every fact about a reduction is a fact about
  handler composition (`QueryImpl.simulateQ_compose`) and its fusion with an evaluation. Efficiency
  is closure of the class under that substitution: a polynomial-time instance certifies a reduction
  by a certificate for each handler (VCVio's `closeHandler`, `HandlerCertificate`), which needs the
  adversary's program inside the reduction, not its denotation. The same reading gives the guess
  below: a logging handler substituted into the attacker's program.

### Query bounds and the guess

- **The field.** `Machine.QueryBound A q`: on every path, at every `η`, at most `q η` queries to
  the inputs (VCVio's `IsQueryBoundP` at `Sum.isRight`; tape reads are not counted). Counting all
  inputs together is equivalent, up to the number of inputs, to a bound per input.
  `AdvClass.queryBound_mem` asks a polynomial bound of every member; its polynomial-time
  counterpart is that time bounds query count. Every construction keeps a bound: a handler whose
  answers make at most `k` input queries multiplies a bound by `k`
  (`OracleComp.isQueryBoundP_simulateQ`), so `rename` keeps `q`, `app` gives `2q`, `subst` gives
  `q·(q_K + 1)`, `branch` `1 + q_x + q_y`.
- **The guess.** `Machine.guess off k ha A d` reads `k η` bits of the tape from `off η` as a number
  `j < 2^{k η}` (`bitsEquiv`, a bijection), runs `A` logging its queries (`withQueryLog`), and
  returns the argument of the `j`-th query to its first input, an oracle `a → b` with `a` Boolean or
  base, or `d`'s value (`Machine.run_guess`). Running `A` to the end and reading the log gives the
  output of CCS26's `A_j`, which stops at the `j`-th call. `AdvClass.guess_mem` admits it at
  `off = p(η)`, `k = ⌈log₂ q(η)⌉` for polynomials `p`, `q`: a uniform closure, since both are
  computed from finite objects. Its polynomial-time counterpart is a logging handler of constant
  cost per query (`closeHandler`), which forwards answers rather than copying them (L2).
- **Exact uniformity.** `sum_prEvent_eq_two_pow_mul`: if the events `E j` read ρa only below `off`
  and `off + k ≤ lenA`, then `Σ_{j < 2^k} Pr[E j] = 2^k · Pr[E (the j that the bits [off, off+k)
  spell)]`. The proof is one involution of (bits, tape), `(c, ρa) ↦ (bits of ρa, ρa with the block
  set to c)`, as FreshL's swap. `two_pow_clog_le`: `2^⌈log₂ n⌉ ≤ 2n + 1`.
- **The bound** (`prEvent_faultyAt_le`): `Pr[the run with o makes a faulty query] ≤ 2^⌈log₂ q(η)⌉ ·
  Pr[the guess, run with o, returns a point where o and o′ differ]`, at every `η` with
  `p(η) + ⌈log₂ q(η)⌉ ≤ lenA η`, where `p` bounds the reads of the attacker machine and the terms.
  This is CCS26's step 2 with `2^⌈log₂ q⌉` in place of `q`; the bound on the guess is
  `Pr[guess hits] ≥ Pr[some query hits] / 2^⌈log₂ q(η)⌉ ≥ Pr[some query hits] / (2q(η) + 1)`.
- **No non-uniform guess.** `j` is read from the tape inside the machine; no `j` is chosen per `η`.
- **The default.** CCS26's `A_j` returns "a default value empty". Carriers need not contain the
  empty bitstring and no field supplies an `η`-indexed constant, so the reduction draws its default
  with the model's sampler for `a` (`Machine.sampler`), admitted under `Model.PolyCoins a` (L28).

### Rw-Oracle and Pc-Oracle (`Rules/Oracle.lean`)

```
Valid.nonDed_rwOracle_of ha hβ (hoβ : oβ = o₁ ∨ oβ = o₂) hR hread
    (h : Valid R C Θ (.nonDed (Vec.snoc u o₂) v ho₂))
    (hagree : Valid R C Θ (Form.oracleAgree u oβ o₁ o₂ hd)) :
  Valid R C Θ (.nonDed (Vec.snoc u o₁) v ho₁)
```

with `Form.oracleAgree u oβ o₁ o₂ = ∀̃ m. (u⃗, oβ ▷ m) ⇒̃ [o₁(m) = o₂(m)]`, `hR : ∀ M, R M →
M.LongTapes ∧ M.PolyCoins a`, and `hread`: `u⃗`, `o₁`, `o₂` read ρa below a polynomial under `Θ`.
`Valid.nonDed_rwOracle` is Fig. 3's case `oβ = o₁`.

- **Per `η`** (`AdvClass.NonDed.rwOracle`): `deduceAdv g (u⃗, o₁) v η ≤ deduceAdv g (u⃗, o₂) v η +
  2^⌈log₂ q(η)⌉ · Pr[o₁(m) ≠ o₂(m)]`, at every `η` where the bits fit, with `m` the output of the
  named reduction `AdvMachine.rwGuess p q ha hβ g` run on `u⃗, oβ`, `p` the sum of the read bounds and
  `q` the attacker machine's query bound. Asymptotically `(2q + 1)·negl` is negligible.
- **Step 1** (`deduceAdv_le_add_faulty`): on each tape, the machine with the oracle first
  (`AdvMachine.withOracleFirst`) runs the same with `o₁` and `o₂` unless the run with `oβ` queries a
  point where they differ (`Machine.run_cons_eq_of_firstArgs`, from
  `OracleComp.evalWithAnswerFn_eq_of_forall_mem_runLog`). Identical until bad is pointwise here: a
  machine's only randomness is ρa, so no `AgreeUntilBad` coupling is needed. One faulty event, that
  of the run with `oβ`, bounds both directions, which is the double rule.
- **Step 2** is the guessing bound; the premise, at `m := rwGuess(u⃗, oβ)`, for which `u⃗, oβ ▷ m`
  holds with the reduction as witness, makes its success negligible.
- **Ground right side.** `v` is Boolean or base: a deduction of a function is an equality at every
  argument, and the guess cannot know which argument's run is faulty (as for Rw-Equiv, L21).
- **Shared tape.** The guess draws `j` above the reads of `g` and of `u⃗`, `o₁`, `o₂`, so the terms
  need read bounds and the tapes must be long: FreshL's conditions (L20, L24). CCS26 says only "a
  part of `ρa` further away".
- **Pc-Oracle** (`AdvClass.NonDed.pcOracle`, `Valid.nonDed_pcOracle`) is derived from `β = 2` as
  App. C.1 derives it: with `o′ = λx. if x ≠ m then o(x) else w` (`FTerm.puncture`, the paper's
  λ-term; `FTerm.denote_puncture` reads it as `RV.puncture`), a message deducible from `u⃗, o′` is
  not `m` by Ineq from `u⃗, o′ ⊬ m`, and `o`, `o′` agree away from `m`.

### L2: answer sizes

The reduction never computes `o₁` or `o₂`. It runs the attacker machine through a handler that
forwards each oracle query to its own oracle input and keeps the argument; answers are typed values
the handler passes on. So no premise on answer sizes, and no `⊢pptm` premise on the oracles, is
needed: the efficiency obligation is the closure field `guess_mem`, whose polynomial-time
counterpart charges a constant per forwarded query. In the paper's machine model `A_j` copies each
answer onto `A`'s tape, which is where answer sizes enter; a class that charges for copying would
meet `guess_mem` only under a size premise. L2 is closed with that reading.

### Derivations

`Derivation` gains `nonDedRwOracle` (the double rule, over models where `R₀` gives long tapes and
`PolyCoins a`, with the read bounds as premises) and `nonDedPcOracle`. Pc-Oracle is a constructor:
deriving it from `nonDedRwOracle` concludes the agreement premise by Ineq under the hypothesis
`u⃗, o′ ▷ m`, and the fragment has no rule to introduce a hypothesis under `⇒̃`.

### Checks (`OracleExamples.lean`)

In `FreshLExamples.longModel` (tapes of `2^η` bits, `h` the identity), with `hideO = λx. if x ≠ m
then h(x) else n` and `leakO = λx. if x ≠ a then h(x) else n`:

| Check | Shows |
|---|---|
| `valid_rwOracleWorked` | Rw-Oracle at `β = 2`: from `h ⊬ n` (FreshR) and the agreement at every message deducible from `h` (FreshR `h ⊬ m`, Ineq), `hideO ⊬ n`; every hypothesis holds jointly against `AdvClass.all`, and FreshR does not give the conclusion, since `hideO` reads `n` |
| `valid_rwOracleFig3` | Fig. 3's form: from `hideO ⊬ k` and the agreement at every message deducible from `h`, `h ⊬ k` |
| `rwOracle_needs_agree` | with `leakO`, `h ⊬ n` and every side condition hold, `leakO ⊬ n` fails (`queryAtA` queries the oracle at `a` and gets `n` on every tape), so the agreement premise fails at both `β`: the oracles differ at a deducible point |
| `valid_pcOracleWorked` | Pc-Oracle with `o′ = λx. if x ≠ m then hideO(x) else m`, the identity: FreshR gives `o′ ⊬ n` and `o′ ⊬ m`, and Pc-Oracle gives `hideO ⊬ n` |
| `queryBound_input`, `not_queryBound_input_zero` | the query bound counts: the input projection meets it at `1` and not at `0` |

`AdvClass.all` meets `queryBound_mem` and `guess_mem` (it is an `AdvClass`), so the fields are
satisfiable jointly with every other field. The FreshL countermodel's generated class
(`FreshLCountermodel.genClass`) is closed under the guess too; its invariant now also says that on
clean inputs every query has clean arguments (`Gen.clean_argsClean`), since the guess returns an
argument.

### Statements that changed

- `encReduction`, `reductionWith`, `hashReduction`, `freshReduction`, `outcome` and
  `PRFSymbols.advantage_le` take a machine; `advantage_challenge` bounds `advantage A.test`.
- `AdvClass` has two more fields; `AdvClass.all` asks read and query bounds;
  `all_mem_of_readsBelow_zero` takes a query bound, and `AdvClass.all_mem_input` is new.
- `Handler` is `InputImpl` at the machine's own interface; `Handler.EvalsTo` is exposed.
- `PRFSymbols.runLog` and its lemmas are now `OracleComp.runLog` (`RunLog.lean`).
- FreshL's tape-block operations are `Model.setBlock` and `Model.bitsAt` in `Machine.lean`.

### Candidates for VCVio core

`RunLog.lean` is interface-independent: `OracleComp.runLog`, `runLog_bind`, `runLog_query`,
`simulateQ_pure_comp`, `evalWithAnswerFn_eq_of_forall_mem_runLog` (identical until bad on a path),
`length_filterMap_runLog_le`, `forall_mem_runLog_simulateQ`, `runLog_eq_of_allQueriesSatisfy`,
`isQueryBoundP_simulateQ`, `isQueryBoundP_withQueryLog`, `allQueriesSatisfy_withQueryLog`,
`isQueryBoundP_bind_le`. From the spike, `GuessQuery.lean`'s `guessQuery` is the ProbComp analogue
of `Machine.guess`; its sum over query positions is `prEvent_exists_finset_le` here, and
`OracleRules.lean`'s identical-until-bad through `AgreeUntilBad` is not needed for deterministic
runs. `sum_prEvent_eq_two_pow_mul` is generic in the tape model up to the block operations.

### Problems hit

1. **Classical decisions in rewrites.** `FTerm.eq` reads as `@decide _ (Classical.propDecidable P)`
   with `P` fixed at elaboration; `simp`'s definitional steps change the decided proposition but not
   the instance, after which `rw` fails ("motive is not type correct"). Rewriting `cond (cond
   (decide P) false true) t e` into `ite` first (`cond_cond_decide`) and splitting with `split_ifs`
   works.
2. **`nomatch x, y`** inside anonymous constructors again parsed as two discriminants.
3. **Implicit declarations** again: `Valid.nonDed_freshR x …` with the example's own `Name` timed
   out until given `(D := decl)`.
4. **Unexposed definitions.** `Handler.EvalsTo` had to be exposed to be applied in another module.
5. **Elaboration order.** Bounds of sequenced programs need the continuation's bound given
   (`isQueryBoundP_bind_le (m := …)`), and handler lemmas need the program unfolded first
   (`unfold Machine.app Machine.handle`) so the handler is known.

### Build and checks

- **Build.** `LEAN_NUM_THREADS=3 lake build SquirrelLogic` succeeds with no warnings.
- **Axioms.** The scratch file of step 1b, extended by 54 headlines of this part, prints the axioms
  of 271 declarations and sweeps all 2687 declarations of the library's modules: only `propext`,
  `Classical.choice` and `Quot.sound` occur.
- **Forbidden tactics, comment fences, line length.** No `sorry`, `admit`, `stop` or
  `native_decide`; the fence check passes; no line exceeds 100 characters, and no file 1500 lines.

| File | Content |
|---|---|
| `RunLog.lean` (new) | the run log, fusion, identical until bad, query bounds through handlers and logs |
| `Guess.lean` (new) | `Machine.QueryBound` and its construction lemmas, `Machine.guess`, `run_guess`, `sum_prEvent_eq_two_pow_mul` |
| `Rules/Oracle.lean` (new) | `rwGuess`, steps 1 and 2, `AdvClass.NonDed.rwOracle`, `.pcOracle`, `Form.oracleAgree`, `FTerm.puncture`, the rules |
| `OracleExamples.lean` (new) | the checks above |
| `Machine.lean` | `InputImpl`, `Model.answerIn`, `Machine.simulate` and fusion, `Model.bitsAt`, `Model.setBlock` |
| `Indist.lean` | `queryBound_mem`, `guess_mem`, `AdvClass.all` with query bounds |
| `Rules/Enc.lean`, `Rules/PRF.lean` | the reductions run machines |
| `Derivation.lean` | `nonDedRwOracle`, `nonDedPcOracle` |
| `FreshLCountermodel.lean` | `Gen.guess`, `Gen.clean_argsClean` |

### What remains (part 3b)

PRF.R and PRF.L-eq/sec/⊤ (CCS26 Fig. 4, App. C.3, pp. 18–20) put `o_h^k = λx. h(x, k)` on the left.
They need:

- **The oracle as a compiled arrow.** The reduction answers the attacker machine's queries to the
  oracle input by running `o_h^k`'s compiled Kleisli arrow (`Compile.lean`), which queries the PRF
  oracle: an `InputImpl` into `PRFOracleSpec` built from `simulateQ (fwd ρ)`, and its fusion
  through `Machine.simulateQ_simulate` with `simulateQ_prfRealQueryImpl_fwd` and `CRel` at the
  arrow type (Kleisli application of a related arrow to embedded ground arguments).
- **ψ_msg for the attacker's queries.** The challenge must not be hashed by the attacker's own
  oracle queries, which happen after the challenge is fixed: in the ideal world those queries
  make the challenge's value consistent, so PRF.L needs the bad event "the attacker queries `m`",
  bounded by a guessing reduction as here (the guess's log of oracle arguments is the query log),
  with `u⃗, o_h^k ⊬ m` as the premise that bounds it.
- **Higher-order entries in G.PRF** and `ψ_msg` with binders (L26), for the oracle term `λx. h(x, k)`.
- **The bound** will carry a factor `2^⌈log₂ q(η)⌉` from the guess, as Rw-Oracle's does.

### Ledger

L2 is closed with the efficiency obligation in `guess_mem`; L10, L11, L14 and L18 are updated; L27
(the uniform guess and its factor), L28 (the default value and `PolyCoins a`) and L29 (the double
rule, ground right side, Pc-Oracle as a constructor) are new.

## M1, part 3b: the hash oracle on the left

This work was done on top of `c89509a87`, in commits `ecdece14c` (the oracle input and PRF.R),
`fc9d85615` (PRF.R's derivation constructor and checks), `c6e7206e0` (notes), `5076aca16`
(PRF.L-sec), `cd4829c71` (PRF.L-sec's constructor, checks and countermodel) and the commit that
updates these notes.
Sources: CCS26 Fig. 4 and §3.4 (pp. 7–8), §2.3 (pp. 5–6), App. C.3.1 (pp. 18–21) and App. C.3.2
(pp. 22–25), the authors' PDF pinned in `../SOURCES.md`.

### The oracle as an input (`Rules/PRFOracle.lean`)

- **The terms.** `PRFSymbols.hashOracle` is `o_h^k = λx. h(x, k)`; `PRFSymbols.callOracle` is the
  term with calls `λx. call x`, which closes up to it (`close_callOracle`, by `rfl`).
- **The handler.** `PRFSymbols.kapp M η o x` Kleisli-applies the compiled reading of a closed arrow
  `o` (`Term.cbv` of `cbvAlg`) to `x`; `PRFSymbols.arrowIn M η o e` answers a machine whose first
  input is `o` by `kapp` and its other inputs from the values `e`. For `λx. call x`, `kapp` is one
  hash query (`kapp_callOracle`), which the reduction's `fwd` sends to the PRF oracle.
- **Fusion.** `evalWithAnswerFn_kapp` is adequacy at an arrow (`cbv_adequate`, `CRel` at `a → b`
  applied to an embedded ground argument); `evalWithAnswerFn_simulate_arrowIn` is the instance of
  `Machine.simulateQ_simulate`: with the keyed hash's answers the machine's run inside the
  reduction is its run with the oracle's reading as its first input. In the PRF game's real world
  that reading is the true function `h(·, k)` (`simulateQ_prfRealQueryImpl_simulate_callOracle`).
- **The attacker's hashes are its oracle queries** (`exists_firstArgs_of_hashed`, from
  `OracleComp.forall_mem_runLog_simulateQ`): a hash query of the simulated run is the argument of a
  query to the first input on the run with the true function.
- **Ad hoc, as in CCS26.** No condition is generated from the oracle: it is a fixed term, answered
  by the rule's reductions (L30).

### PRF.R

```
Valid.nonDed_prfR P u m hg hmg hh hlarge hku hkm hpu hpm hfu hfm hR hread hprf hmsg h :
  Valid R C Θ (.nonDed (Vec.snoc (P.closeVec u) P.hashOracle) (P.hashTerm (P.close m)) ho)
```

from `h : u⃗, o_h^k ⊬ m` and `hmsg : [ψ^{m,k}_msg(u⃗)]` (`PRFSymbols.psiMsgVec`, the calls of `u⃗`
only), for a first-order `⊢pptm` vector of Boolean or base entries and message, without the key
name, a `large` hash type, and in every model of `R` uniform names of the hash type, long tapes and
polynomial bit blocks for messages; the terms read the attacker tape below a polynomial under `Θ`.
`hprf` is the PRF assumption on the named reductions `PRFSymbols.rightReduction η hmg hh u t g`, one
for each candidate `t ∈ m :: calls m`.

- **Per `η`** (`PRFSymbols.rightAdvantage_le`): at every `η` where the guess's bits fit,
  `deduceAdv g (u⃗, o_h^k) h(m, k) ≤ Pr[ψ_msg(u⃗) = false] + 2^⌈log₂ q(η)⌉ · deduceAdv (rwGuess g)
  (u⃗, o_h^k) m + Σ_{t ∈ m :: calls m} (prfAdv (rightReduction t g) + ε)`, with `ε` a bound on each
  value of the hash type's sampler (`2^{-cη}` for a `large` type).
- **The events.** On the conclusion's tapes the attacker wins; either the vector hashes `m`
  (bounded by `¬ψ_msg`, through `cbvVec_spec` at `Q = (· ≠ m)`), or the attacker queries its oracle
  at `m` (bounded by the uniform guess, `prEvent_exists_firstArgs_le`, a generalisation of
  Rw-Oracle's guessing bound to any event on the queried point), or neither. In the last case the
  descent (`exists_unhashed`) gives a candidate `t` with `m`'s value that its own run does not
  hash, and `rightReduction t` succeeds in the real world.
- **The reduction** (`rightReduction`, program `rightProg`): draw both tapes, run the compiled
  vector, then the attacker with its oracle answered by `arrowIn`, then the compiled candidate,
  all logged and forwarded to the PRF oracle; query the oracle at the candidate's value; succeed
  if the attacker's output is the answer and the value was not hashed before. Real world:
  `prEvent_prfRealExperiment_rightReduction` and `rightRun_eq`. Ideal world
  (`prEvent_prfIdealExperiment_rightReduction_le`): the answer is a fresh draw, so the success is at
  most `ε`.
- **Why candidates, not a guess of `A₂`'s call.** App. C.3.2 guesses which oracle call of the
  message's machine is on its output (factor `q(η)`), and drops the machine's continuation. A
  first-order message's hashes are values of its call arguments (`exists_mem_calls_of_hashed`, the
  contrapositive of `cbv_guard`), and a call argument of a call argument is a call argument with
  fewer calls (`calls_infix`), so the descent on the number of calls stops at a candidate that its
  own run does not hash. One reduction per candidate replaces the guess (L31).
- **Why the attacker runs before the candidate.** CCS26's `B` runs the message first. Run last,
  the challenge is the last query of the reduction, and in the ideal world a fresh draw
  independent of the attacker's output; no lazy-sampling argument about the attacker's view is
  needed (L31).

### PRF.L-sec (`Rules/PRFLeft.lean`)

```
Valid.nonDed_prfLSec P u v m hg hβ hmg hh hku hkv hkm hpu hpv hpm hfu hfv hfm hR hread hprf
    hmsg h hsec :
  Valid R C Θ (.nonDed (Vec.snoc (Vec.snoc (P.closeVec u) P.hashOracle)
    (P.hashTerm (P.close m))) (P.close v) ho')
```

from `h : u⃗, o_h^k ⊬ v`, `hsec : u⃗, o_h^k ⊬ m` (`C_sec`) and `hmsg : [ψ^{m,k}_msg(u⃗, v, m)]`
(`PRFSymbols.psiMsg` at the vector `u⃗, v`), under PRF.R's conditions for `u⃗`, `v` and `m`, with
polynomial bit blocks also for hashes. `hprf` is the PRF assumption on `leftReduction` and
`leftFreshReduction`.

- **Per `η`** (`PRFSymbols.leftAdvantage_le`): `deduceAdv g (u⃗, h(m, k), o_h^k) v ≤ Pr[¬ψ_msg] +
  prfAdv (leftReduction) + prfAdv (leftFreshReduction) + deduceAdv (freshL (swapLast g)) (u⃗,
  o_h^k) v + 2^⌈log₂ q(η)⌉ · deduceAdv (freshL (swapLast (rwGuess g))) (u⃗, o_h^k) m`, at every `η`
  where the guess's bits fit above the fresh draw's block. The rule swaps the conclusion's last two
  entries into CCS26's order (`AdvClass.NonDed.swapLast`).
- **The reductions.** Phase one compiles `u⃗`, `v` and `m`, logged; the challenge is the oracle at
  the message (`leftReduction`) or a fresh draw (`leftFreshReduction`); phase two runs the attacker
  on the values and the challenge, its oracle input answered by the compiled `λx. call x` except
  at the message, where the challenge answers (`interceptIn`). Success: the attacker computes the
  secret or queries the message, unless the message was hashed in phase one.
- **Real worlds.** With the hash as challenge, the intercepting oracle is the keyed hash
  (`evalWithAnswerFn_simulate_interceptIn`, `reprogram_self`), so the first reduction's success
  covers the conclusion where `ψ_msg` holds. With a fresh challenge, the reprogrammed oracle runs
  as the keyed hash until the message is queried (`Machine.run_cons_eq_of_firstArgs`), and a query
  at the message is one with either oracle (`mem_firstArgs_iff_of_agree`).
- **The ideal hop is an equality of distributions.** Where the message was not hashed in phase
  one its value is a fresh draw, and phase two never queries the hash there
  (`allQueriesSatisfy_interceptIn`), so the cache entry that the first reduction leaves at the
  message does not matter (`fst_run_evalDistEq_of_avoids`, an induction on the forwarded program).
  This is where the interception pays: without it the two ideal worlds differ after the attacker
  queries the message, and an identical-until-bad argument on the stateful lazy sampler is needed.
- **The fresh draw from the tape.** `update_coin_evalDistEq` moves the key's coordinate and the
  fresh coin into place; `prEvent_coin_eq_coinAt` reads the coin from a block of the attacker
  tape above what the attacker and the terms read (FreshL's swap). The attacker with that draw is
  `freshL (swapLast g)`, a machine on `u⃗, o_h^k`; its queries at the message are bounded by the
  guess (`prEvent_exists_firstArgs_le` at the vector `u⃗, n`), which is
  `freshL (swapLast (rwGuess g))` against `u⃗, o_h^k ⊢ m`.
- **Form (L32).** `ψ_msg` includes `m`'s calls, as in §2.3; Fig. 4 drops them, which App. C.3.1
  pays for by guessing `A₂`'s call on the message. PRF.L-eq and PRF.L-⊤ are not done.

### Derivations

`Derivation`'s parameter `prf` now ranges over `PRFRule D`, the instances of G.PRF (`.gprf`),
PRF.R (`.right`, `PRFRInstance`) and PRF.L-sec (`.left`, `PRFLInstance`), with `PRFRule.Holds`.
`nonDedPRFR` and `nonDedPRFLSec` are the constructors: syntactic side conditions, model conditions
on `R₀` and read bounds are premises, as for FreshL. `PRFExamples` changes by one constructor
name.

### Checks (`PRFOracleExamples.lean`)

| Check | Shows |
|---|---|
| `chainWorked`, `chainWorked_sound` | FreshR gives `o_h^k ⊬ s`; PRF.R gives `o_h^k ⊬ h(s, k)`; PRF.R at the message `h(s, k)` (two candidates, `h(s, k)` and `s`) gives `o_h^k ⊬ h(h(s, k), k)`: two steps of CCS26 §2's `secrecy_base` |
| `valid_chainWorked` | in `pmodel` (a perfect PRF), against `AdvClass.all`, every hypothesis of both PRF.R steps holds jointly, so `o_h^k ⊬ h(h(s, k), k)` holds; FreshR does not give it |
| `inst₁_holds`, `inst₂_holds` | the PRF assumption of both instances, from `pmodel_prfAdv` |
| `hashOracle_avoids`, `hashOracle_avoids_name` | the oracle reads only the key's coordinate |
| `leftWorked`, `valid_leftWorked` | PRF.R gives `o_h^k ⊬ h(s, k)`, FreshR `o_h^k ⊬ r`, and PRF.L-sec (secret `h(s, k)`, message `r`) gives `o_h^k, h(r, k) ⊬ h(s, k)`; every hypothesis of both steps holds jointly in `pmodel`, `[s ≠ r]` by `valid_psiL` |
| `prfLSec_needs_psiMsg` | with secret `h(s, k)` and message `s`: syntactic conditions, PRF assumption, premise (PRF.R) and `C_sec` (FreshR) hold, `ψ_msg` (`s ≠ s`) fails, and `o_h^k, h(s, k) ⊬ h(s, k)` fails (the attacker returns its last input) |

No countermodel to `C_sec` exists: without it the rule is PRF.L-⊤, which App. C.3.1 proves sound
at a polynomial loss. A countermodel to PRF.R without `ψ_msg` (`u⃗ = h(m, k)`) needs the
one-wayness of the oracle, `h(m, k), o_h^k ⊬ m`, and is not built (L32).

### Statements that changed

- `prEvent_faultyAt_le` is derived from `prEvent_exists_firstArgs_le` (statement unchanged).
- `Derivation`'s parameter `prf : PRFInstance D → Prop` is now `prf : PRFRule D → Prop`;
  `equivPRF` takes `prf (.gprf e)`, and `Derivation.sound` takes `PRFRule.Holds`.
- `Derivation.lean` imports `Rules/PRFLeft.lean`, which holds `PRFRule`.

### Build and checks

- **Build.** `LEAN_NUM_THREADS=3 lake build SquirrelLogic` succeeds with no warnings.
- **Axioms.** The scratch file of step 1b, extended by 40 headlines of this part, prints the axioms
  of 310 declarations and sweeps all 3006 declarations of the library's modules: only `propext`,
  `Classical.choice` and `Quot.sound` occur.
- **Forbidden tactics, comment fences, line length.** No `sorry`, `admit`, `stop` or
  `native_decide`; the fence check passes; no line exceeds 100 characters, and no file 1500 lines.

| File | Content |
|---|---|
| `Rules/PRFOracle.lean` (new) | the oracle terms, `kapp`, `arrowIn`, fusion, PRF.R's reductions, the bound, `Valid.nonDed_prfR`, `PRFRInstance` |
| `Rules/PRFLeft.lean` (new) | `AdvMachine.swapLast`, `prEvent_coin_eq_coinAt`, `update_coin_evalDistEq`, `interceptIn`, `fst_run_evalDistEq_of_avoids`, PRF.L-sec's reductions, the bound, `Valid.nonDed_prfLSec`, `PRFLInstance`, `PRFRule` |
| `PRFOracleExamples.lean` (new) | the checks above |
| `OracleTerm.lean` | `calls_infix`, `mem_calls_of_mem_calls`, `length_calls_lt`, `every_of_mem_calls`, `psiMsgVec` |
| `Compile.lean` | `exists_mem_calls_of_hashed`, `exists_unhashed` |
| `Rules/Oracle.lean` | `prEvent_exists_firstArgs_le` |
| `Derivation.lean` | `PRFRule` as the parameter, `nonDedPRFR` |

### Candidates for VCVio core

`fst_run_evalDistEq_of_avoids` is a fact about VCVio's lazily sampled random function, stated here
for the forwarded programs of the compiled reading: a program that never queries a point gives the
same output distribution from two caches that differ only there. The private
`runLog_eq_of_forall_mem_runLog` (answers agreeing on a run's queries give the same log) belongs
beside `OracleComp.evalWithAnswerFn_eq_of_forall_mem_runLog` in `RunLog.lean`.

### What part 4 needs

CCS26 §2's toy hash chain for a fixed trace: `frame ⊬ ck` through the simulation lemma
(`leakage ▷ frame`, then WeakL), `secrecy_base` by unrolled PRF.R steps (`chainWorked` is two of
them), PRF.L-sec to remove the corrupted key `C = h(⟨ck(pred Corrupt), input⟩, k)` from
`leakage = (o_h^k, C)` (`leftWorked` is the shape), and WeakL.

- **Messages are pairs.** The chain hashes `⟨ck, input⟩`; the declaration needs a pairing symbol
  of order at most one, and `input` is an attacker symbol of the frame (`att`), which the compiled
  reading answers from the attacker tape.
- **`ψ_msg` of the message in PRF.L-sec.** Removing `C` needs `[ψ_msg(∅, ck(τ), v)]` with
  `v = ⟨ck(pred Corrupt), input⟩`, whose calls are the earlier links' messages: their inequality
  with `v` is CCS26's non-collision lemmas, provable for a fixed trace in a model where the links
  are distinct overwhelmingly (a derivation of `[t′ ≠ v]` from the secrecy of the links by Ineq,
  or semantically). Fig. 4's form, without `m`'s calls, would avoid this (L32).
- **The simulation lemma** `leakage ▷ frame` needs a deduction of the frame's hashes through the
  oracle (`ded_apps` with the oracle applied), and the frame's attacker inputs.
- **WeakL** exists (`Valid.nonDed_weakL`).

### Ledger

L6, L26 and L28 are updated; L30 (the oracle as a compiled input, handled by the rule), L31
(PRF.R's candidates and order) and L32 (PRF.L-sec's form, its proof, the variants not done, and
the countermodels) are new.
