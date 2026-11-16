# Squirrel's logic: pinned sources

The development formalizes the logic of the Squirrel prover as published in the papers below, at
the versions listed. The tool is a secondary reference; where the tool and a paper differ, the
paper is the target and the difference is an obligation in `OBLIGATIONS.md`. Sources are re-pinned
only at a milestone boundary.

| Key | Source | Version read | Used for |
|---|---|---|---|
| BC14 | Bana, Comon-Lundh, "A computationally complete symbolic attacker for equivalence properties", CCS 2014 ([PDF](https://www.lsv.ens-paris-saclay.fr/Publis/PAPERS/PDF/BC-ccs14.pdf)) | published version | base logic: first-order terms, `∼`, Fig. 2 axioms, §5 folding |
| SP21 | Baelde, Delaune, Jacomme, Koutsos, Moreau, "An Interactive Prover for Protocol Verification in the Computational Model", S&P 2021 ([long version](https://adrienkoutsos.fr/papers/metabc_long.pdf)) | long version | meta-logic, actions, macros, FRESH, EUF-CMA, INDUCTION, lifted rules (App. C) |
| CSF22 | Baelde, Delaune, Koutsos, Moreau, "Cracking the Stateful Nut", CSF 2022 ([PDF](https://adrienkoutsos.fr/papers/state-squirrel.pdf)) | author PDF | state, macros (Fig. 2), bi-systems, bi-deduction |
| LICS23 | Baelde, Koutsos, Lallemand, "A Higher-Order Indistinguishability Logic for Cryptographic Reasoning", LICS 2023 ([author report](https://people.irisa.fr/Joseph.Lallemand/files/papers/lics23-report.pdf), [ho-squirrel.pdf](https://adrienkoutsos.fr/papers/ho-squirrel.pdf)) | author report (30 pp.); the published HAL version was not reachable | higher-order terms, models, validity, Figs. 3, 4, 7–11 |
| CSF24 | Baelde, Fontaine, Koutsos, Scerri, Vignon, "A Probabilistic Logic for Concrete Security", CSF 2024 ([long version](https://adrienkoutsos.fr/papers/concrete-long.pdf)) | long version | `det`, `blen`, ε-versions, `adv` at order ≤ 2, corrected induction (§III-C) |
| CCS24 | Baelde, Koutsos, Sauvage, "Foundations for Cryptographic Reductions in CCSA Logics", CCS 2024 (local `~/Documents/ref/papers/baelde2024bideduction/`) | long version | bi-deduction (Thm 1), the `crypto` tactic's game language |
| CCS26 | Hérouard, Jacomme, Koutsos, Lallemand, "Secrecy in Squirrel and the Post-Compromise Security of a Ratchet", CCS 2026 ([ePrint 2026/1912](https://eprint.iacr.org/2026/1912); local `~/Documents/ref/papers/herouard2026ratchet/`) | authors' PDF of 2026-09-07 | `⊬`/`▷`, Figs. 3, 4, 10, 11, App. C |
| SIG | Baelde, Delaune, Jacomme, Koutsos, Lallemand, "The Squirrel Prover and its Logic", SIGLOG News 2024 (local `~/Documents/ref/papers/baelde2024squirrelsiglog/`) | text copy | overview; fixed traces (lines 536–555) |
| Tool | [squirrel-prover](https://github.com/squirrel-prover/squirrel-prover) | master `ebef0aca4f` (2026-09-29) | `theories/*.sp`, `documentation/sphinx/source/*.rst`, `examples/secrecy-ccs-2026/` |

All links accessed 2026-11-16.
