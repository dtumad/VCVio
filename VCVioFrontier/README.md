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

## ElGamal

The typed VCVio reduction and the word implementation share one program parameterized by its
operations. It calls the adversary to choose messages, flips a coin, then calls the
adversary to guess using the saved state and challenge ciphertext. A realization gives two
uniform word procedures with polynomial-time certificates, an encoding for the saved state, and
agreement of each call on encoded inputs. The choice law preserves both messages and the state
jointly. VCVio uses the first message on `true`, so the representation exchanges the two message
positions at that boundary.

- `AdversaryRealization.exists_halting_machine` realizes the existing
  `IND_CPA_OneTime_DDHReduction_openOracle` after the adversary and coin handlers are installed.
  Its clock is polynomial in encoded input length and covers malformed words as well.
  `AdversaryRealization.advantage_eq` identifies the exact-exponent one-time IND-CPA advantage
  with twice the DDH advantage of this same distinguisher. The assumption uses a specified
  prime-order group family and a point setup at each security parameter.
  [Machine and security theorems](VCVioFrontier/Examples/ElGamal/Security.lean)
- Key generation, encryption and decryption are free programs over an exponent request.
  Installing fixed exponents proves decryption for every secret and nonce. A state handler runs
  the whole round trip and exposes both draws and the unused suffix.
  [Programs and handler laws](VCVioFrontier/Examples/ElGamal/HonestPrograms.lean) ·
  [State regression](VCVioFrontierTest/Examples/ElGamal/State.lean)
- Installing the bounded sampler in these programs gives the honest word scheme. It samples bounded fair-coin exponents for key generation and encryption.
  Decryption recovers every honestly encrypted group-element word on every supported execution.
  When selecting the group description is polynomial time, key generation, encryption, and
  decryption have uniform polynomial-time certificates. For each fixed challenge bit the
  implemented game incurs advantage at most `2 / 2^n` relative to exact exponents.
  [Honest algorithms and sampling bound](VCVioFrontier/Examples/ElGamal/Honest.lean)
- `AdversaryRealization.wordGame_advantage_le` combines the two sampling errors. For the same
  realized adversary and its own DDH distinguisher, the implemented advantage is bounded by
  `2 * AdvDDH + 4 / 2^n`. The bound holds at each parameter. Uniform machine DDH then implies
  negligible advantage for the bounded-coin implementation in VCVio's native one-time IND-CPA
  experiment (`implemented_secureAgainst`).
  [Implemented security bound](VCVioFrontier/Examples/ElGamal/Bound.lean)

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
