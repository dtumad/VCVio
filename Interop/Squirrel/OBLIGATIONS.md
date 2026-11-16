# Obligations

Each row is a point where the sources leave something unproved, informal or unsound, or where the
formalization makes a modelling choice or assumes a hypothesis. A row is closed only by a Lean
theorem (or a countermodel, for an unsound rule) named in the last column. Source keys are those
of `SOURCES.md`.

Kinds: **gap** (the sources omit or sketch a proof), **unsound** (the rule as stated is false),
**informal** (a definition is not given precisely), **choice** (a modelling decision), **assumed**
(a hypothesis carried by our theorems), **out of scope**.

| Id | Kind | Source anchor | Obligation | Status | Lean anchor |
|---|---|---|---|---|---|
| L1 | informal | SP21 p. 6; tool `declarations.rst`; SIG 1044–1051 | The translation from processes to actions is never formally defined (only BC14 §5 proves one, for finite transition systems). | open | |
| L2 | gap | CCS26 Fig. 3, App. C.1 | Rw-Oracle has no premise bounding the size of oracle answers, yet its proof assumes them polynomial. | open | |
| L3 | informal | CCS26 Fig. 11, App. C.3 | The PRF side conditions ψ_key, ψ_msg (with the oracle excluded) are not defined formally. | open | |
| L4 | gap | CCS26 App. C (Fig. 12) | The soundness proofs of CDH, GDH and EUF-sign are omitted. | open | |
| L5 | unsound | LICS23 Fig. 8; CSF24 §III-C, Remark 2 | Global induction without `const` is unsound (counterexample X_i(η) = max(η − i, 0)); CSF24 gives the corrected rule. | open | |
| L6 | gap | SP21 App. C | The rules lifted from the base logic (CCA1, ENC-KP, DDH, PRF, INT-CTXT) have no detailed proofs. | open | |
| L7 | gap | LICS23 Props. 11, 17, 19 | Proofs of the FA/structural rules, `⊢pptm` soundness and CCA1 are sketched or omitted. | open | |
| L8 | assumed | tool `theories/Logic.sp`, `Classic.sp`, `Deduction.sp` | The tool's 31 user-space axioms (e.g. polymorphic `lt_wf`) and its polymorphism are outside the published theory (SIG 600). | open | |
| L9 | out of scope | CCS26 §3.5; CCS24 | The OCaml tactics are trusted; our theorems cover the rules as published, not the tool's implementation of them. | open | |
| L10 | choice | LICS23 p. 5; spike `Asymptotic.lean` | Adversaries read the shared attacker tape ρ_a in the papers, while VCVio adversaries draw fresh coins; relate the two or record the gap. The distinguishers of `SquirrelLogic` read ρ_a as in the papers, and no structural `∼` rule needs a further hypothesis; FA-Adv depends on the shared reading, since its reduction reruns the attacker computation on the distinguisher's own ρ_a. Relating these distinguishers to VCVio's fresh-coin adversaries remains open. | open | `SquirrelLogic.Distinguisher.adv`, `SquirrelLogic.AdvClass.Indist.adv` |
| L11 | choice | LICS23 p. 7; CSF24 App. A; CCS26 §3.1 | `∼` at arbitrary order (LICS23) versus order ≤ 1 for `∼` and order ≤ 2 for `adv` (CSF24, CCS26). | open | |
| L12 | choice | LICS23 §II-B.2 | Names read the honest tape, which is a product with one uniform coin per name and index; a name reads its own coordinate, and names of one type share a sampler. Independence and identical distribution are therefore structural. That samplers run in polynomial time is not a restriction yet. | open (narrowed to polynomial time) | `SquirrelLogic.Model.TapeH`, `SquirrelLogic.Model.name` |
| L13 | choice | LICS23 Fig. 2 | `const t` at arrow types is read as a logical relation (`Ty.Same`). LICS23 asks for a value in `⋂_η ⟦τ⟧_η`; the two agree at base types and at arrows from fixed types, and differ when the domain varies with `η`. | open | `SquirrelLogic.RV.IsConst` |
| L14 | choice | LICS23 §II-C.1, §II-C.2 | The machines of `adv` and the distinguishers of `∼` are a class parameter receiving typed values. LICS23's machines receive bitstring encodings and query higher-order values through handles. | open | `SquirrelLogic.AdvClass` |
| L15 | choice | LICS23 §II-A, §II-B | LICS23's declared variables are split into constructors (names, honest symbols with tape-independent values, attacker symbols reading `ρa`, `=_τ`, `∀_τ`, `∃_τ`) and free variables, which range over all random variables. | open | `SquirrelLogic.Decl`, `SquirrelLogic.localSig` |
| L16 | choice | BC14 (α-renaming of names); LICS23 §II-B.2 | Renaming names in a closed vector is sound along any type-preserving bijection of names, in every model: the renaming is the permutation `Model.tapePerm` of the honest tape's coordinates. The residue is the restriction to closed vectors, which LICS23's rule shares (free variables range over all random variables, which may read the tape). | closed | `SquirrelLogic.Model.renamesNames`, `SquirrelLogic.Valid.equiv_renameNames_of_equiv` |
