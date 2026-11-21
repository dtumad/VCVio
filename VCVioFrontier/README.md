# VCVioFrontier

VCVioFrontier connects VCVio security experiments to the finite-control probabilistic
multi-tape Turing machines in cslib-frontier. A polynomial functor specifies the requests and
their response types. A program is a tree of those requests. PolyFunFrontier certifies its
typed local functions and handler calls under explicit encodings. For a family of programs with these proofs, closing the requests with the chosen handler
gives a finite machine with one polynomial clock on encoded input lengths. The construction
chooses the machine noncomputably from Frontier’s existence theorem. The
probability bridge identifies the output measure of this computation with VCVio's
`evalDist` on every measurable event. `MachineRealization.output_measure` states that law for
the same witness that supplies the halting proof.
[Measure bridge](VCVioFrontier/OracleComp/Measure.lean) ·
[Machine realization](VCVioFrontier/OracleComp/Realization.lean)

## One-time pad

The program draws one coin per message bit. Words encode VCVio bitvectors least-significant
bit first, so the first draw remains the first bit. XOR is the interpretation of a two-variable
PolyFun term. Its machine certificate uses Samuel Schlesinger's `polytime` automation. The
explicit key sampler takes `n + 1` transitions on a unary input of width `n`.

- Install `tapeBits` in `encryptWord` and it reads a caller-supplied key.
  `encryptWord_tapeBits` proves exactly which ciphertext and unused tape suffix it returns.
  Install the fair-coin handler in the same program and the machine samples the key.
  [Program and handler laws](VCVioFrontier/Examples/OneTimePad/Words.lean)
- `encryptMachine_rows` proves equality of the complete ciphertext distributions of any two
  messages of the same width. This includes the empty message.
- `xorMachine_decrypt` proves decryption at every caller-supplied key.
  `roundTripMachine_correct` proves that sampling a key and reusing it returns the original word
  with probability one. The machines halt on every supported branch at the stated clock.
  [Definitions and theorems](VCVioFrontier/Examples/OneTimePad/Machine.lean)

## Build

The nested package follows PolyFunFrontier's immutable pins. At this revision it uses Lean
4.36.0-rc2 and the root packages use stable 4.36.0. Use a separate worktree for the nested
build, since the path dependency on VCVio writes into the parent directory's `.lake/build`.

```sh
cd VCVioFrontier
lake exe cache get
python3 ./scripts/check-pins.py
lake build VCVioFrontier VCVioFrontierTest
lake exe mk_all --lib VCVioFrontier --module --check
lake exe axiomsweep --root VCVioFrontier --baseline ../scripts/axiom_baseline.json --check
```

The pin check requires Python 3.11 or newer. After publishing a new PolyFun revision, run
`python3 ./scripts/check-pins.py --sync-from /path/to/PolyFun <commit>` here to update the
two PolyFun dependencies, Frontier, CSLib, Mathlib and the toolchain together.
