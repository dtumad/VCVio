# CI gates

What the per-PR gates check, why each rule has the shape it has, and what each gate does not
reach. [`AGENTS.md`](../../AGENTS.md) lists the commands; `./scripts/validate.sh` runs them locally
in CI's order.

CI runs the timed build on the non-test Lean libraries:
`ToMathlib`, `VCVio`, `VCVioCslib`, `LatticeCrypto`, `Extern`, `HashSig`, `Examples`,
and `VCVioWidgets`. The dormant `Interop` target remains excluded.
Test libraries and test executables are not part of the timed build; CI only
times the smoke module separately with `lake env lean VCVioTest/Smoke.lean`.

CI keeps two caches: `.lake/packages`, keyed by `lean-toolchain` and `lake-manifest.json`, and
the project's own `.lake/build`, which every `main` run saves and every run restores. Only `main`
saves, so pull-request code never publishes a cache another run loads. The `Lint` job restores the
same caches and builds the changed modules itself, so it runs alongside `Build Project`. Lake
rebuilds a module when the content hash of its source or imports
changes, so a restored build only saves work; it never changes a verdict. Lake replays the stored
messages of modules it does not rebuild, so the warning budgets still see every warning. The
nightly scheduled run, and a manual run with `clean_build`, skips the build cache.

Because an incremental build's wall time depends on what the change invalidated, the timing report
compares modules instead: `scripts/module_times.py` keeps the latest `Built <module> (<time>)` for
every module in `.lake/build/vcvio-module-times.json`, which travels with the build cache. The
report lists the modules this run rebuilt against those times, and the table's sum before and after
estimates clean-build compile time.

After the build, CI runs `./scripts/test-axiomsweep.sh` and then
`lake exe axiomsweep --check`: kernel-level axiom/`sorry` accounting for every
declaration in the non-test libraries, gated against the committed baseline
`scripts/axiom_baseline.json`. It fails on *new* `sorryAx` or non-standard-axiom
taint; after intentionally adding or closing a `sorry`, run
`lake exe axiomsweep --update-baseline` and commit the diff. `Interop` (the
declared TCB) is excluded — its boundary is enforced by the import-isolation
gate instead.

The baseline is an allowlist for `sorryAx` debt only. Native trust
(`native_decide`, which mints per-declaration `._native.` axioms) is held to a
zero-debt rule: anything outside the explicit `grandfatheredNativeTrust` list in
`scripts/AxiomSweep.lean` fails `--check` and cannot be greened by editing the
baseline, since accepting it would widen the trusted computing base. The
`VCVioAxiomSweepTestFixtures` library carries synthetic taint for the tool's own
tests and is deliberately excluded from every aggregate.

`python3 ./scripts/check-comment-fences.py` enforces one rule over every Lean source the
repository tracks or would track — tracked files plus untracked ones that are not ignored, the
vendored `third_party/` tree excluded and both lakefiles included: a block comment that begins
its line must be the last thing on the line where it ends. A declaration written after the `-/`
of the docstring that documents it parses, builds and runs, and a reader scanning the left
margin does not see it. Two passes miss that, for two different reasons, and they are easy to
confuse. `lake lint -- --style-only` runs Mathlib's four text-based linters, none of which has
any notion of a comment. `linter.style.whitespace` is not part of that pass at all: it is a
syntax linter that runs during elaboration under the package's `weak.linter.mathlibStandardSet`,
and its warnings fail CI through the build log and `scripts/check-warning-log.py`. It does
reject a command that does not start at the beginning of a line, and it does report the `/-`
and `/-!` forms of this shape — but it is silent on the `/--` form, because a doc comment is
part of the command it documents, so the command starts at the `/--`, at column 0. So this gate
is the only thing that sees the doc-comment form anywhere; over the seven proof and three test
libraries it deliberately repeats for the other forms what the whitespace linter already says;
and in four further places it is the only check that can *fail* on any form of the shape, for
three different reasons. `lakefile.lean` and `VCVioComplexity/lakefile.lean` are elaborated by
Lake from `import Lake`, with no Mathlib linter registered. `Interop/` is not a default target
and no job builds it. `scripts/` is built on every pull request, but nothing there imports
Mathlib, so the `weak.` option is silently dropped and the linter is never registered — one
Mathlib import in one axiom-sweep fixture would flip that. `VCVioComplexity/` sets
`linter.style.whitespace` explicitly in its own lakefile and the blocking `complexity_backend`
job builds it, so there the linter does run and does warn — what is missing is not the linter
but the gate, since `check-warning-log.py` is invoked only with the proof- and test-library
prefixes and `VCVioComplexity/scripts/test.sh` pipes its log nowhere. A block comment that
opens part-way into a line is untouched however many lines it spans — that is an annotation
inside an expression, a field or a tactic block, and wrapped field docstrings of that shape are
common here. The rule is positional, so it also rejects five shapes that hide nothing: a
comment at column 0 in front of a term, a structure field, a tactic or a list element, each of
which Lean lets begin at column 0 when the enclosing indentation has run out, and a comment at
column 0 whose line ends inside a second, still-open comment. Those five are clean Lean and are
asserted, as rejections, in the fixture matrix. Not covered: a declaration indented on its own
line, which the whitespace linter reports in the built libraries *unless* a margin docstring
precedes it, in which case nothing reports it anywhere; a comment that starts mid-line; two
declarations on one line; and a declaration after the closing quote of a multi-line string,
which is the same hiding with a different delimiter and which `lakefile.lean`, a user of
multi-line strings, could grow. The baseline is zero with no exception list;
`scripts/test-comment-fences.sh` carries the fixtures, including the shapes the rule knowingly
does not reach.

`./scripts/test-initsweep.sh` and `lake exe initsweep --check` are the companion
gate for what the *binary* does rather than what the kernel accepted. A top-level
constant of non-function type is evaluated when its module is loaded, before any
`main` runs, so

```lean
instance : Fintype limitedPrimitives.Y := inferInstanceAs (Fintype (Bytes 16))
```

builds a `Finset` of `2 ^ 128` vectors at start-up in every executable that
imports the module — while elaborating cleanly and passing the build, the
linters, every boundary ratchet and the axiom sweep. `lake exe initsweep --check`
flags a constant when the module initialiser evaluates something for it (its own
value, because the compiled declaration takes no parameters, or an `initialize`
body registered for it) and that value either names one of the enumeration entry
points listed in `scripts/InitSweep.lean` or names a *builder* of an enumeration
class (`Fintype`, `FinEnum`) — an instance constructor or an instance that takes
arguments, as opposed to an already-materialised nullary instance such as
`Bool.fintype`, which costs a pointer copy and is deliberately not counted. The
second disjunct is what makes the check a class test: writing the instance the
elaborator would have found (`:= Pi.instFintype`) names none of the entry points
and builds the same enumeration. The same sweep also walks the compiler-generated
declarations the module initialiser assigns beside its constants, because a
parameterless *specialisation* lifted out of a function is initialised at load and
has no environment constant to read; those are tested by what the functions in
their mangled name consume.

Marking the instance `noncomputable` is *not* a fix: it removes the instance's
own compiled code and leaves the compiled auxiliary that carries the enumeration,
which is the constant the gate names. Adding a parameter is not reliably a fix
either — `def cardY (_u : Unit) : Nat := Fintype.card T` still enumerates `T` at
load, through the specialisation the compiler lifts out of it. Route the
finiteness argument through `Fintype.ofFinite` instead, whose `Prop`-valued
`Finite` argument leaves nothing compiled at all.

The baseline `scripts/init_sweep_baseline.json` is a list of accepted constant
names — the allowlist idea `scripts/axiom_baseline.json` uses, with a scope
attached — rather than a per-library ceiling: accepting one benign instance costs
exactly that name and leaves every other constant of its library at zero. It
holds nine rows today; `scripts/InitSweep.lean` lists what each one does at load,
read off the emitted C, including the two that turn out not to be initialised at
all. A row is scoped to one constant under one library, so the same name flagged
under another root, or gaining a new entry point, is still a regression. Adding a
row is the escape hatch and needs an argument in review;
`lake exe initsweep --update-baseline` writes it and preserves the rows of
libraries the run did not sweep. `VCVioInitSweepTestFixtures` carries seven
hazard modules, one per route by which loading a module can build an enumeration,
one negative control per clause of the predicate, and the baseline's accept /
drop / narrow / widen / re-scope / preserve behaviour; like the axiom-sweep
fixtures it is kept out of every aggregate.

The gate cannot see how *large* an enumeration is, and it does not look at values
whose size is an argument rather than a type (`List.range n`,
`Array.replicate n x`); `scripts/InitSweep.lean` lists what that leaves open,
with the occurrences of each in the current tree.
