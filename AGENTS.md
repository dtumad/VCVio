# VCVio — AI Agent Guide

Machine-checked cryptographic proofs in Lean, built on Mathlib.

## Fast Start

1. Run `lake exe cache get && lake build`.
2. Read `Examples/OneTimePad/Basic.lean` for a compact modern proof (correctness and privacy).
3. Choose the work area by task: use `VCVio/` for oracle/probability/program-logic work, `LatticeCrypto/` for lattice schemes and reductions, and `LatticeCryptoTest/` for vectors or differential tests.
4. If `𝒟` lemmas fail unexpectedly, check for `[OracleSpec.AnswerMeasure spec]`
   and a measurable space on the result type; oracle answer types need none. The
   concrete `unifSpec` and `coinSpec` have global uniform-measure instances; other
   specs need a chosen interpretation.

`AGENTS.md` is the canonical guide. `CLAUDE.md` is a symlink to this file.

## Further Reading

Before working in a specific area, read the relevant guide:

- **Interaction runtime and UC integration**: [`docs/agents/interaction.md`](docs/agents/interaction.md)
- **Interop with Rust verification frontends (hax, aeneas)**: [`docs/agents/interop.md`](docs/agents/interop.md)
- **LatticeCrypto layout and workflows**: [`docs/agents/lattice.md`](docs/agents/lattice.md)
- **OracleComp / SubSpec / SimSemantics**: [`docs/agents/oracle-comp.md`](docs/agents/oracle-comp.md)
- **Query tracking / weighted cost / expected runtime**: [`docs/agents/query-tracking.md`](docs/agents/query-tracking.md)
- **Honest computational-complexity design and implementation status**:
  [`docs/design/computational-complexity.md`](docs/design/computational-complexity.md)
- **SLH-DSA general-`d` formalization, FIPS 205 conformance, KAT, and security stack plan**:
  [`docs/design/slh-dsa-fips205-generalization.md`](docs/design/slh-dsa-fips205-generalization.md)
- **SLH-DSA implementation status, stale-plan corrections, and remaining slices**:
  [`docs/design/slh-dsa-status-and-roadmap.md`](docs/design/slh-dsa-status-and-roadmap.md)
- **SLH-DSA classical random-oracle bound, its accounting, and leanVM's 127-bit proof**:
  [`docs/design/slh-dsa-classical-rom-bound.md`](docs/design/slh-dsa-classical-rom-bound.md)
- **Probability reasoning (EvalDist, ProbComp)**: [`docs/agents/probability.md`](docs/agents/probability.md)
- **Converting code written against the removed discrete `Pr[…]` API**: [`docs/agents/probability-migration.md`](docs/agents/probability-migration.md)
- **Crypto primitives and reductions**: [`docs/agents/crypto.md`](docs/agents/crypto.md)
- **End-to-end crypto examples**: [`docs/agents/end-to-end-examples.md`](docs/agents/end-to-end-examples.md)
- **Program logic tactics**: [`docs/agents/program-logic.md`](docs/agents/program-logic.md)
- **All notation**: [`docs/agents/notation.md`](docs/agents/notation.md)
- **Proof workflows (game-hopping, reductions)**: [`docs/agents/proof-workflows.md`](docs/agents/proof-workflows.md)
- **Gotchas and troubleshooting**: [`docs/agents/gotchas.md`](docs/agents/gotchas.md)
- **Module visibility and the PolyFun façade**: [`docs/agents/module-system.md`](docs/agents/module-system.md)
- **Upstream alignment ledger (what Mathlib/core/cslib/PolyFun already own, with verdicts)**:
  [`docs/reading/upstream-alignment.md`](docs/reading/upstream-alignment.md)
- **CI gates and their baselines**: [`docs/agents/ci-gates.md`](docs/agents/ci-gates.md)

## Attribution, Headers, And Docstrings

Follow [`CONTRIBUTING.md`](CONTRIBUTING.md) for the repo's explicit attribution policy.

- New Lean files should use the standard copyright / license / authors header and a module docstring.
- For ordinary Lean source files, use the standard prologue layout: header, blank line, `module`, public imports, blank line, module docstring.
- Docstrings must be intrinsic and descriptive. Cross-reference live sibling definitions when helpful, but do not mention removed or renamed declarations, change history, or use reactive wording such as "replaces" or "renamed from".
- Preserve existing headers on routine edits.
- Only rewrite attribution when a file is genuinely new or materially replaced.
- Do not add a separate AI-attribution line.
- For inline section breaks within a Lean file, use Mathlib-style doc-comment headers `/-! ## Title -/` (or the multi-line `/-! ## Title \n\n explanation -/` form). **Do not use ASCII banners** such as `-- ====...===` flanking a `-- § Title` line. The `/-!` form is rendered by `doc-gen4`; ASCII banners are not, and they make the file feel artificially partitioned. If a section is large enough to want a loud header, it is usually large enough to want its own `namespace` or its own file. See *Section Headers Within A File* in [`CONTRIBUTING.md`](CONTRIBUTING.md).

## Module Scopes

Active Lean libraries and tests use Lean's module system. Put declarations in a `public section`;
use `public meta section` for tactic and elaborator code. Existing ordinary source files use
`@[expose] public section` so pre-migration downstream definitional equalities remain available; new
files use plain `public section` and expose individual definitions with `@[expose]` where unfolding
is part of the intended API. The per-library count of broadly exposed files is a ceiling
(`scripts/check-expose-boundary.sh`, baseline `scripts/expose_boundary_baseline.tsv`): converting a
file lowers it, and raising it needs an explicit baseline change under review. Executable and
runtime implementation modules should use opaque `public section` when callers do not need to
unfold their definitions.

- Use `public import` for dependencies that form part of the module's transitive public surface and
  `public meta import` for exported tactic/elaborator dependencies.
- Use plain `import` for implementation-only dependencies. A proof module may use `import all` to
  access an unexposed implementation from the same dependency when proving its public API.
- Do not enable `backward.privateInPublic` or `backward.proofsInPublic`; resolve visibility and
  proof-metavariable issues directly.
- Keep the dormant `Interop` library outside this policy until it is migrated separately.

Section `variable` lines carry an instance assumption only when the theorems in scope share it:
Lean auto-includes an instance-implicit section variable in every theorem mentioning its types,
so a section-wide `[Fintype Chal] [Inhabited Chal] [SampleableType Chal]` that most theorems
ignore turns into an `omit [...] in` line before each of them. Put such assumptions on the
declarations that use them, or open a `section` around the block that shares them; never declare
one that another in scope implies (`[Finite X]` beside `[SampleableType X]`). `omit` is for a
genuine one-off. See *Section Variables* in [`CONTRIBUTING.md`](CONTRIBUTING.md) and gotcha 31.

## What This Project Is

VCVio is a framework for formal cryptographic proofs built around `OracleComp spec α`, the free monad on the polynomial functor induced by an oracle signature `OracleSpec ι := ι → Type`. Its universal fold `simulateQ impl : OracleComp spec α → r α` is the unique monad morphism extending any `impl : QueryImpl spec r` to the free monad. For `OracleComp`, `support` is the set of possible outputs, equal to the fold into `SetM` that answers every query with `Set.univ`. Its probability semantics `evalDist` / `𝒟[…]` is a successful-output Mathlib `Measure`, the fold of the answer measures chosen by `[OracleSpec.AnswerMeasure spec]`; missing mass is failure. Events are written `Pr{let x ← oa}[p x]`, whose braces take any `do` sequence with its sugar (a single output is `Pr{let x ← oa}[x = a]`), the failure probability is `prFail oa`, and distributional equality is `oa =ᵈ ob`. Uniform answer measures are `[OracleSpec.UniformAnswerMeasure spec]`. `ProbComp α := OracleComp unifSpec α` specializes to computations whose only oracle is uniform selection.

The repo also includes a first-class lattice cryptography library under `LatticeCrypto/`, built on top of the `VCVio` framework. That layer contains generic lattice algebra plus ML-DSA, ML-KEM, and Falcon specifications, security statements, concrete implementations, and tests; the native FFI bridges live in the separate `Extern/` library.

## Repo Map

See the [repository ownership map](docs/design/repository-layout.md) for placement rules,
build boundaries and the staged consolidation.

- `VCVio/`: generic oracle-computation framework, program logic, crypto abstractions, and generic reductions.
- `VCVio/Algorithms/` contains shared pure SHA-2, HMAC, MGF1, SHA-3 and SHAKE implementations;
  their independent regressions run with `lake exe algorithm_tests`.
- `ToMathlib/`: local Mathlib-facing utilities and lemmas intended to remain below the framework layer.
- `Extern/`: native FFI surface — the `@[extern]` bindings (SHA-3/SHAKE, ML-KEM, ML-DSA, Falcon) and the FFI-backed concrete instances that reach them. No proof library may import it; the backing `extern_lib`s become empty stubs when `third_party/` submodules are absent.
- `LatticeCrypto/`: lattice-specific algebra, hardness assumptions, scheme definitions, security theorems, and concrete implementations.
- `HashSig/`: hash-based signatures: SLH-DSA (SPHINCS+, FIPS 205) specifications, FIPS
  conformance, and SUF-CMA bounds in the classical random-oracle model, including the specialized
  `HashSig/SLHDSA/SHAKE128s/` subtree. Theorem index, scope and open items:
  [status](docs/design/slh-dsa-status-and-roadmap.md),
  [bound](docs/design/slh-dsa-classical-rom-bound.md) and
  [SHAKE-128s](docs/design/slh-dsa-shake128s-suf-cma.md). Peer of `LatticeCrypto/`; depends on
  `VCVio`/`ToMathlib` but nothing in those imports it back.
- `LatticeCryptoTest/`: ACVP vectors, executable regression tests, and cross-checks against native backends.
- `VCVioTest/`: framework smoke tests and test support modules.
- `VCVioWidgets/`: optional widget experiments and visualizations.
- `VCVioCslib/`: optional cslib-backed non-uniform P/poly certificates and security-game adapters,
  a separate Lake library so core `VCVio` remains backend-neutral. It stays outside the default
  library graph but participates in repository validation.
- `VCVioComplexity/`: optional isolated Lake package for the complexitylib-backed exact-machine
  substrate; it is not part of VCVio's default dependency graph.
- `Examples/`: compact framework examples such as OneTimePad, ElGamal, Schnorr, and program-logic tactic walkthroughs.
- `Interop/`: experimental bridges to Rust verification frontends (hax, aeneas). **Strict TCB isolation**: nothing in core VCVio depends on it. See `docs/agents/interop.md`.
- `csrc/`: C FFI shims used for differential testing against native ML-DSA, ML-KEM, and Falcon code.
- `third_party/`: native backends as git submodules; when they are not checked out (fresh clones, Lake dependency checkouts), the native `extern_lib` targets build as empty stub archives.

## Placement policy

The [repository ownership map](docs/design/repository-layout.md) defines current roots and
planned migration slices. Shared pure implementations belong in `VCVio/Algorithms/`, named
constructions and their proofs in `VCVio/Schemes/`, and cryptographic interfaces, assumptions,
games and generic reduction theory in `VCVio/CryptoFoundations/`. Examples are instructional
consumers. Existing HashSig and LatticeCrypto peers migrate only in dependency-complete slices.
Keep implementations unique, preserve the FFI/test boundary, and add a separate library only
for a dependency, trust or build-isolation requirement. The import guards enforce pure-algorithm independence,
optional interop isolation and the FFI boundary; other placement rules guide review.

## Module Layering

For `VCVio/`:

```
ToMathlib → Prelude → EvalDist/Defs → OracleComp core → EvalDist bridge
  → {SimSemantics, QueryTracking, Constructions, Coercions, ProbComp}
  → {ProgramLogic, CryptoFoundations, CryptoFoundations/Asymptotics} → Examples
```

New files must respect this DAG. `EvalDist/` must never import from `OracleComp/`.

For `LatticeCrypto/`, the rough dependency direction is:

```
{Ring/*, DiscreteGaussian}
  → HardnessAssumptions
  → {MLDSA, MLKEM, Falcon}
  → Concrete implementations / security wrappers
  → Extern (FFI bindings + FFI-backed instances)
  → LatticeCryptoTest
```

Scheme-specific code in `LatticeCrypto/` may depend on `VCVio/CryptoFoundations`, but not the other way around.

The native FFI surface lives in `Extern/`: it may import `VCVio`, `LatticeCrypto`,
and `ToMathlib`, but no proof library (`VCVio/`, `ToMathlib/`, `LatticeCrypto/`,
`HashSig/`, `Examples/`, `VCVioWidgets/`, `Interop/`) may import `Extern.…`. That
keeps every proof library — and any downstream Lake project requiring VCVio —
link-safe when the `third_party/` submodules are absent. Enforced by
`scripts/check-extern-isolation.sh` on every PR.

For `Interop/`, the dependency contract is one-way:

```
Interop/{Hax,Aeneas,Rust}/  →  VCVio/, ToMathlib/, (Hax.…), (Aeneas.…)
```

`Interop/**` may **never** be imported from `VCVio/`, `LatticeCrypto/`,
`LatticeCryptoTest/`, `Examples/`, `ToMathlib/`, `Extern/`, `VCVioWidgets/`,
or `VCVioTest/`. This contract is enforced by
`scripts/check-interop-isolation.sh` and the
`Interop TCB Isolation` GitHub workflow on every PR.

## Critical Gotchas

1. **Probability assumptions are explicit for arbitrary specs.** `support` on `OracleComp spec` works without a probability interpretation. Direct `evalDist` / `𝒟[…]` and `Pr{…}[…]` need `[OracleSpec.AnswerMeasure spec]` and, for `𝒟[…]`, an ambient `MeasurableSpace` on the result. Oracle answer measures live on the discrete σ-algebra, so answer types take no `MeasurableSpace` hypotheses; continuous answers belong at the `PFunctor.FreeM` level. Uniform-measure instances are global for `unifSpec` and `coinSpec`; for another spec, uniform answers are `[OracleSpec.UniformAnswerMeasure spec]`, built by `UniformAnswerMeasure.ofFiniteNonempty` from `Finite`/`Nonempty` answer types as a local instance on the component spec (sums get theirs from `UniformAnswerMeasure.add`). There are no bundled `spec.Fintype` / `spec.Inhabited` / `spec.DecidableEq` classes: data on answer types are ordinary hypotheses on `spec.Range t` (see gotcha 12).
2. **`autoImplicit = false` is set globally in `lakefile.lean`**. Do not add `set_option autoImplicit false` in individual files. Every variable must be explicitly declared.
3. **`𝒟[oa]` IS the measure fold** `PFunctor.FreeM.denote` of the answer measures, definitionally, and `Pr{…}[…]` is `prEvent` of that measure. `support` is PolyFun's `MonadAttach` support, equal to the fold into `SetM` that answers every query with `Set.univ` by `PFunctor.FreeM.support_eq_liftM_univ`. The definitional identities are internal to `VCVio/EvalDist/**` and `VCVio/OracleComp/**`: code outside those directories crosses them through the public equation lemmas (`PFunctor.FreeM.evalDist_eq_denote`, `prEvent_def`). Existing downstream `rfl` uses are grandfathered; new proofs use the public equations.
4. **`++ₒ` is dead** — use `+` for combining oracle specs.
5. **Commented-out code is legacy** — follow only uncommented code. Use `Examples/OneTimePad/Basic.lean` as canonical reference.
6. **Preserve partial proofs** with `stop` instead of deleting large proof blocks.
7. **Do not disable linters to silence errors**. Do not use `set_option linter.* false`, `set_option weak.linter.* false`, or add repo-level `leanOptions` that turn lints off to dodge a fixable issue. Fix the root cause instead. (The one deliberate, documented exception is `weak.linter.unicodeLinter, false` in `lakefile.lean`, off so FIPS-204 math notation and diacritics in cited author names are allowed.)
8. **Interop TCB isolation is mandatory**. Core VCVio (`VCVio/`, `ToMathlib/`, `LatticeCrypto/`, `Examples/`, `LatticeCryptoTest/`, `Extern/`, `VCVioWidgets/`, `VCVioTest/`) must never `import Interop.…`, `import Hax.…`, or `import Aeneas.…`. CI fails the PR if it does. See `docs/agents/interop.md`.
9. **Extern link-safety isolation is mandatory**. Proof libraries (`VCVio/`, `ToMathlib/`, `LatticeCrypto/`, `HashSig/`, `Examples/`, `VCVioWidgets/`, `Interop/`) must never `import Extern.…`: the native backends behind it are built as empty stubs whenever the `third_party/` submodules are absent — always the case for Lake dependency checkouts — so importing `Extern` would break downstream executable links. Test libraries may import it. Enforced by `scripts/check-extern-isolation.sh` in CI.

10. **Probability is `Measure`/`Kernel`, never `PMF`.** Semantic code uses `𝒟[…]`, `Pr{…}[…]`, `=ᵈ`, Mathlib measures and kernels. Mathlib owns `PMF`, so VCVio cannot deprecate it; the environment linter `ToMathlib.Lint.usesPMF` reports any declaration that uses it directly, and `scripts/nolints.json` holds no exceptions for it. Code written against VCVio's removed discrete API (`SPMF`, `Pr[= x | mx]`, `IsUniformSpec`, …) converts with the codemod and guide in [`docs/agents/probability-migration.md`](docs/agents/probability-migration.md). See `docs/reading/denotational-probability-semantics.md`.

11. **Name the reduction in security theorems.** Write `bound ≤ Pr{let b ← exp (myReduction adv)}[b = true]`, never `∃ B, bound ≤ Pr{let b ← exp B}[b = true]`. Adversary types such as `X → ProbComp W` carry no resource bound, and `Classical.choice` can pick a witness directly, so the existential form holds for every scheme and passes the axiom sweep. The same applies to simulators (`∃ sim ζ, HVZK sim ζ` holds with `ζ := 1`), extractors, and distinguishers. If the reduction does not exist yet, use a named `sorry` definition or a warned placeholder instead. See [`docs/agents/crypto.md`](docs/agents/crypto.md#name-the-reduction-in-the-theorem-statement).

12. **No global instance may conclude `C spec.Domain` or `C (spec.Range t)` for a generic `spec`.** `Domain` and `Range` are reducible, so such an instance is indexed as `C ι`, respectively `C (?spec ?t)`, and becomes a candidate for every `C _` goal with `spec` undetermined; search then invents a specification through `ofFn` and either times out or routes ordinary `DecidableEq`/`Fintype`/`Inhabited` instances through oracle data (#772). Write `[DecidableEq ι]` for index equality and `[DecidableEq (spec.Range t)]`, `[Fintype (spec.Range t)]`, `[Inhabited (spec.Range t)]` (quantified over `t` only when a statement ranges over arbitrary queries) for answer types; concrete specifications reduce to their answer types. `VCVioTest/OracleComp/SpecInstanceSearch.lean` guards this.

For the full list, see `docs/agents/gotchas.md`.

## Naming Conventions

Follow Mathlib convention: `{head_symbol}_{operation}_{rhs_form}`.
Examples: `prEvent_bind_eq_lintegral`, `support_pure`, `simulateQ_map`.
Structures use UpperCamelCase: `SecurityGame`, `SymmEncAlg`, `RelTriple`.
Security-notion names may begin with an underscore-separated acronym:
`IND_CPA_Advantage`, `SM_DT_UD_Adversary`, `IND_CPA_OneTime_Game`, `OW_CPA_oracleSpec`.
`scripts/lint.py` accepts a `defsWithUnderscore` finding without a `nolints.json` entry when
each underscored name component starts with an acronym of two or more capitals or digits and
every later segment except the last starts with a capital.
Security notions, experiments, games, and advantages follow
[`docs/agents/crypto.md`](docs/agents/crypto.md#naming).

## Canonical Examples

- Compact modern crypto proof: `Examples/OneTimePad/Basic.lean`
- ElGamal IND-CPA via the generic one-time DDH lift: `Examples/ElGamal/Basic.lean`
- Schnorr sigma protocol (completeness, soundness, HVZK): `VCVio/Schemes/Schnorr/SigmaProtocol.lean`
- Concrete transcript and commitment walkthroughs: `Examples/Schnorr/Basic.lean`,
  `Examples/Pedersen.lean`
- Oracle computation core: `VCVio/OracleComp/OracleComp.lean`
- Probability lemmas: `VCVio/EvalDist/ProbabilityNotation.lean`, `VCVio/EvalDist/ProbabilityBounds.lean`, `VCVio/OracleComp/EvalDist/Measure.lean`
- Equality in distribution across monads (`mx =ᵈ my`): `VCVio/EvalDist/EvalDistEq.lean`
- SubSpec / coercions: `VCVio/OracleComp/Coercions/SubSpec.lean`
- `QueryImpl` instrumentation primitives (`preInsert` / `postInsert` and their bridge lemmas): `VCVio/OracleComp/SimSemantics/QueryImpl/Constructions/Core.lean`. Prefer these (or their downstream wrappers `withTraceBefore` / `withTrace` / `withCost` / `withLogging`) when wrapping a `QueryImpl` with a per-query side effect, so the generic theory in that file applies.
- DLog / CDH / DDH via HHS: `VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean`
- Cost model / polynomial time: `VCVio/OracleComp/QueryTracking/CostModel.lean`
- Query cost / weighted expected cost: `VCVio/OracleComp/QueryTracking/QueryCost.lean`, `VCVio/OracleComp/QueryTracking/WriterCost.lean`
- Quantitative realizability, syntactic resource traces, and generic polynomial resource
  certificates:
  `PolyFun/Realizability/Quantitative.lean`,
  `PolyFun/Realizability/Quantitative/Resource.lean`
- Strict backend-relative oracle PPT crypto facade:
  `VCVio/CryptoFoundations/Asymptotics/ComputationalComplexity.lean`
- Proof-bearing oracle-handler closure seam:
  `VCVio/CryptoFoundations/Asymptotics/OracleClosure.lean`
- Conservative PPT certificate lookup:
  `VCVio/CryptoFoundations/Asymptotics/ComplexityTactics.lean`
- Syntactic ElGamal complexity canary:
  `Examples/ElGamal/ComputationalComplexity.lean`
- Optional exact complexitylib machine substrate:
  `VCVioComplexity/VCVioComplexity/Backend/TuringMachine.lean`
- Complexitylib polynomial adapter and end-to-end pure canary:
  `VCVioComplexity/VCVioComplexity/Backend/Polynomial.lean`,
  `VCVioComplexity/VCVioComplexityTest/Backend/PureCanary.lean`
- End-to-end complexitylib canary with one enabled fair-coin query:
  `VCVioComplexity/VCVioComplexityTest/Backend/OracleCanary.lean`
- Asymptotic security games: `VCVio/CryptoFoundations/Asymptotics/Security.lean`
- Negligible function algebra: `VCVio/CryptoFoundations/Asymptotics/Negligible.lean`
- Query enforcement: `VCVio/OracleComp/QueryTracking/Enforcement.lean`
- Seeded (Bellare-Neven) forking lemma: `VCVio/CryptoFoundations/SeededFork.lean`
- Replay-based forking lemma: `VCVio/CryptoFoundations/ReplayFork.lean`
- Independent products of computations: `VCVio/EvalDist/IndepProduct.lean`
- Drawing without replacement and its expected draw count: `VCVio/OracleComp/Constructions/WithoutReplacement.lean`, `ToMathlib/Probability/NegativeHypergeometric.lean`
- Expected values of `ℝ≥0∞`-valued functionals (`wp` and `∫⁻` against `𝒟[mx]`): `VCVio/ProgramLogic/Unary/HoareTriple.lean`
- Fischlin transform: `VCVio/CryptoFoundations/Fischlin/` (`Defs`, `CostAccounting`, `Completeness`, `KnowledgeSoundness`)
- Interaction type tree and path: `PolyFun/Interaction/Basic/TypeTree.lean`
- Two-party roles and strategies: `PolyFun/Interaction/TwoParty/Strategy.lean`
- Two-party composition and factorization: `PolyFun/Interaction/TwoParty/Compose.lean`
- Multiparty local views: `PolyFun/Interaction/Multiparty/Core.lean`
- Concurrent specs and frontiers: `PolyFun/Interaction/Concurrent/Spec.lean`, `PolyFun/Interaction/Concurrent/Frontier.lean`
- Concurrent processes and execution: `PolyFun/Interaction/Concurrent/Process.lean`
- Open systems (interfaces, composition): `PolyFun/Interaction/Open/OpenTheory.lean`
- Open processes (boundary traffic, UC bridge): `PolyFun/Interaction/Open/OpenProcess.lean` (monad-parametric `OpenProcess m Party Δ` with intrinsic `stepSampler` field and `OpenStep.boundaryTrace`)
- Concrete open-theory model: `PolyFun/Interaction/Open/OpenProcessModel.lean` (`openTheory Party m schedulerSampler` threads `TypeTree.Sampler` through `map` / `par` / `wire` / `plug`)
- UC emulation and security: `PolyFun/Interaction/Open/Emulates.lean`
- Computational UC observation layer: `VCVio/Interaction/UC/Computational.lean`
- Per-node samplers as data (`TypeTree.Sampler m tree` = `Decoration (fun X => m X) tree`): `PolyFun/Interaction/Basic/Sampler.lean`
- `TypeTree.Fintype` / `TypeTree.Nonempty` ornaments + canonical uniform sampler: `PolyFun/Interaction/Basic/TypeTreeFintype.lean`, `VCVio/Interaction/UC/Runtime.lean`
- Oracle-aware runtime semantics (monad-parametric process execution, `processSemanticsOracle`): `VCVio/Interaction/UC/Runtime.lean` (no `sampler` argument; pulled from `process.stepSampler`)
- Observation-interface `ObservedCompEmulates 0` smoke test: `Examples/OneTimePad/UC.lean`
- Reactive single-use OTP execution and simulation with private environment state:
  `Examples/OneTimePad/Reactive.lean`, `Examples/OneTimePad/Reactive/Security.lean`
- Semantic counterexamples (plaintext leakage, wrong decoding, key reuse, delivery and fuel):
  `Examples/OneTimePad/Reactive/Separation.lean`, `VCVioTest/ReactiveNetworkAdversarial.lean`
- Interaction examples: `PolyFunTest/Interaction/TwoParty/Examples.lean`, `PolyFunTest/Interaction/Multiparty/Examples.lean`, `PolyFunTest/Interaction/Concurrent/Examples.lean`
- Program logic tactics: `VCVio/ProgramLogic/Tactics.lean`
- Program logic tactic walkthroughs: `Examples/ProgramLogic/`
- Generic lattice ring layer: `LatticeCrypto/Ring/Core.lean`, `LatticeCrypto/Ring/Kernel.lean`, `LatticeCrypto/Ring/VectorBackend.lean`, `LatticeCrypto/Ring/Transform.lean`, `LatticeCrypto/Ring/NTTCert.lean` (matrix and structural butterfly-stage certificates), `LatticeCrypto/Ring/Norms.lean`, `LatticeCrypto/Ring/Rounding.lean`
- ML-DSA proof-level IDS: `LatticeCrypto/MLDSA/Scheme.lean`
- ML-DSA FIPS signing layer: `LatticeCrypto/MLDSA/Signature.lean`
- ML-KEM internal deterministic core: `LatticeCrypto/MLKEM/Internal.lean`
- ML-KEM top-level KEM wrapper: `LatticeCrypto/MLKEM/KEM.lean`
- Falcon GPV instantiation: `LatticeCrypto/Falcon/Scheme.lean`
- Lattice hardness assumptions: `LatticeCrypto/HardnessAssumptions/LearningWithErrors.lean`, `LatticeCrypto/HardnessAssumptions/ShortIntegerSolution.lean`
- Differential and vector tests: `LatticeCryptoTest/`
- Rust verification interop (hax / aeneas): `Interop/Rust/Common.lean`, `Interop/README.md`, `scripts/check-interop-isolation.sh`

## Program Logic Tactics

For new program-logic proofs, import `VCVio.ProgramLogic.Tactics`.
`VCVio.ProgramLogic.Notation` holds the notation; `Tactics.lean` is the canonical
interactive proof mode.

For the tactic reference, proof-mode entry points, and workflow details, see
[`docs/agents/program-logic.md`](docs/agents/program-logic.md). The two
`@[vcspec]` and `@[wpStep]` registries are indexed via
`Lean.Meta.Sym.Pattern` / `Lean.Meta.Sym.DiscrTree`. `Sym.*` is under active
development in core Lean; see the *Internal Architecture* and *SymM
Stability Note* sections of that doc for the churn classes to watch at each
toolchain bump; the `@[wpStep]` rewrites already run through
`Sym.Simp.mkTheoremFromDecl` and `Sym.simpGoal`.

## Building

```bash
lake exe cache get && lake build
```

`lake build` builds the seven proof libraries (the default targets); `lake build VCVio` is
the fast path for framework-only work. `./scripts/validate.sh` runs the fast per-PR CI checks
locally in CI's order (including the optional `VCVioCslib` facade; build and warning budget, umbrella check, remaining boundary checks, style
linters, agent-docs checks); `--lint` adds Batteries' environment linters, one process per
proof library as in CI. `lake lint` runs both source-style and environment checks;
`-- --style-only` and `-- --env-only` select either pass, and `-- --no-build` requires existing
proof oleans. Findings must exactly match `scripts/nolints.json`: obsolete entries and unlisted
findings fail. After fixing findings, `lake lint -- --prune-baseline` safely removes obsolete
entries across all eight checked libraries and refuses additions. PR CI also checks that the baseline
only shrinks against the merge base.
`--test` adds `lake test` (the three test libraries, the smoke test,
and the SLH-DSA test executables), `--ffi` adds the native ML-KEM / ML-DSA / Falcon
executables to `--test`, and `--axioms` adds the axiom sweep. The eager-initialisation
ratchet runs in the default pass, after the boundary ratchets, since it reads the oleans
the build just produced; `--test` runs it a second time over `VCVioTest` and
`LatticeCryptoTest`, whose oleans `lake test` has just built.

CI also runs these gates, each with its baseline in `scripts/`; the reasons for each rule and
what each gate does not reach are in [`docs/agents/ci-gates.md`](docs/agents/ci-gates.md):
- the axiom sweep (`lake exe axiomsweep --check` against `scripts/axiom_baseline.json`): new
  `sorryAx` or non-standard axioms fail; after intentionally adding or closing a `sorry`, run
  `lake exe axiomsweep --update-baseline` and commit the diff. Native trust (`native_decide`) is
  zero-debt outside `grandfatheredNativeTrust` in `scripts/AxiomSweep.lean`;
- `python3 ./scripts/check-comment-fences.py`: a block comment that begins its line must be the
  last thing on the line where it ends;
- the init sweep (`lake exe initsweep --check` against `scripts/init_sweep_baseline.json`): no
  top-level constant may build an enumeration (`Fintype`, `FinEnum`) when its module loads; route
  finiteness through `Fintype.ofFinite` instead. Marking the instance `noncomputable` is not a fix.

After adding new `.lean` files: `./scripts/update-lib.sh` (CI's `scripts/check-imports.sh`
fails when a regenerated umbrella would differ from the committed one).

Lean toolchain and Mathlib must stay in sync (both currently `v4.35.0`); the bump procedure
is in `CONTRIBUTING.md`. Mathlib's file-length linter is enabled at 1500 lines. Split
files by responsibility before crossing that limit; retain an import façade when an existing
module path forms part of the public API.
