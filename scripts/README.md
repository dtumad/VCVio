# Repository scripts

`./scripts/validate.sh` is the entry point for local validation. It runs CI's checks in CI's order,
and `--lint`, `--test`, `--ffi` and `--axioms` add the slower ones. The tables below say what each
file does and which CI job runs it. A file named `test-<name>` tests the matching check with fixtures.

A new rule starts as a Lean linter with no exceptions where it can, as
`ToMathlib/Lint/UsesPMF.lean` does. A baseline is for a time-limited cleanup with a stated end.

## Everyday commands

| File | What it does | CI job |
|---|---|---|
| `validate.sh` | Runs the checks below locally | |
| `update-lib.sh` | Regenerates the library umbrella modules; run it after adding Lean files | |

## Trust

| File | What it does | CI job |
|---|---|---|
| `AxiomSweep.lean`, `test-axiomsweep.sh` | Kernel-level `sorry` and axiom accounting | `Build Project` |
| `axiom_baseline.json` | The `sorry` debt the sweep accepts | `Build Project` |
| `VCVioAxiomSweepTestFixtures/` | Synthetic taint for the sweep's tests | `Build Project` |
| `InitSweep.lean`, `test-initsweep.sh` | Flags constants that build an enumeration when their module loads | `Build Project` |
| `init_sweep_baseline.json` | The constants the init sweep accepts | `Build Project` |
| `VCVioInitSweepTestFixtures/` | Hazard modules for the init sweep's tests | `Build Project` |
| `check-warning-log.py` | Fails on warnings in a build log, apart from `sorry` warnings | `Build Project` |

## Library structure

| File | What it does | CI job |
|---|---|---|
| `check-imports.sh`, `test-check-imports.py` | Umbrella modules match the source tree | `Check Library File Imports` |
| `check-polyfun-boundary.sh`, `test-polyfun-boundary.sh` | VCVio's use of PolyFun stays public | `Check Library File Imports` |
| `check-expose-boundary.sh`, `test-expose-boundary.sh` | Broad `@[expose]` counts stay under their ceiling | `Check Library File Imports` |
| `count-expose-boundary.py` | Counts broadly exposed files for that check | `Check Library File Imports` |
| `expose_boundary_baseline.tsv` | The ceiling per library | `Check Library File Imports` |
| `check-complexity-backend-isolation.sh`, `test-complexity-backend-isolation.sh` | The optional complexity backend stays isolated | `Check Library File Imports` |
| `check-interop-isolation.sh`, `test-interop-isolation.py` | Nothing in core imports `Interop` | `Check Interop TCB Isolation` |
| `check-extern-isolation.sh` | Proof libraries don't import `Extern` | `Check Interop TCB Isolation` |
| `CheckImports.lean` | Import parser behind the two isolation checks | `Check Interop TCB Isolation` |
| `test-validation.py` | `validate.sh` reports failures correctly | `Check Library File Imports` |

## Style

| File | What it does | CI job |
|---|---|---|
| `lint.py`, `test-lint.py` | The `lake lint` driver | `Lint`, `Lint Style` |
| `nolints.json` | Exceptions to the environment linters; may only shrink | `Lint` |
| `nolints-style.txt` | Exceptions to the text linters | `Lint Style` |
| `check-comment-fences.py`, `test-comment-fences.sh` | No code after a block comment that opens a line | `Check Library File Imports` |

## Documentation

| File | What it does | CI job |
|---|---|---|
| `check-agent-docs.py`, `test-agent-docs.py` | Local links and paths in the docs resolve | `Check Agent Documentation` |
| `doc_refs.py` | Shared helpers for that check | `Check Agent Documentation` |
| `extract-doc-fragments.py` | Generated doc fragments are current | `Check Agent Documentation` |
| `check-doc-names.py`, `test-docnames.sh` | Docs cite real declarations and no retired names | `Check Agent Documentation`, `Build Project` |
| `DocNames.lean` | Resolves cited names for that check | `Build Project` |
| `doc_names_allowlist.txt` | Cited names allowed to stay unresolved | `Build Project` |

## Probability migration

These stay until downstream code and open PRs have left the removed discrete API.

| File | What it does | CI job |
|---|---|---|
| `migrate-native-probability.py`, `test-migrate-native-probability.py` | Rewrites code against the removed API | `Check Library File Imports` (tests) |
| `migration-dry-run.sh` | Tries the migration on open PRs | Manual |
| `classify-migration-errors.py`, `test-classify-migration-errors.py` | Sorts a dry run's errors by kind | `Check Library File Imports` (tests) |

## CI support

| File | What it does | CI job |
|---|---|---|
| `free-ci-disk-space.sh`, `test-ci-disk-space.py` | Removes unused SDKs from hosted runners | `Build Project`, `Lint`, `Downstream Consumer Build` |
| `build_timing_report.sh`, `module_times.py` | Build timing report and per-module times | `Build Project` |
| `add-api-consumer-fixtures.py` | Adds public-API fixtures to the scratch consumer | `Downstream Consumer Build` |

## Tests and evidence

| File | What it does | CI job |
|---|---|---|
| `AlgorithmTests.lean`, `OracleCostTests.lean` | Roots of two test executables | `Build Project` (`lake test`) |
| `check-slh-dsa-bound-table.py` | Compares the SLH-DSA bound table with exact arithmetic | `Build Project` (`lake test`) |
| `check-slh-dsa-byte-vectors.py` | Checks byte-model fixtures against a local NIST corpus | Manual |
