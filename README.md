# Following a Six-State Busy Beaver Candidate for 97 Quadrillion Steps

[![Zenodo DOI for software v1.0.0](https://zenodo.org/badge/DOI/10.5281/zenodo.24371839.svg)](https://doi.org/10.5281/zenodo.24371839)

**Darryl Novotny · SyncQutrit Research Group, LLC.**

Read the [published preprint](https://doi.org/10.5281/zenodo.24370902) or the [included PDF](paper/pass1.pdf). Its subtitle is *Certified Tape Rules, Cross-Library Proofs, and Two Open Endings*. The paper follows AppC 8 through **97,311,884,181,777,598 completed steps** from a blank tape. Two families of tape endings still lack a general return proof. For AppC 7, the paper combines exact halting times on prepared tapes with an existing upstream proof to show that the blank run can never reach those tapes.

## Find the evidence

| If you want to… | Start here |
|---|---|
| Read, typeset, or cite the paper | [LaTeX manuscript](paper/pass1.tex) · [Bibliography](paper/references.bib) · [Citation metadata](CITATION.cff) |
| Inspect the exact blank-run count | [Checkpoint proof](lean_interop/BB6Interop/AppC8TerminalCheckpoints.lean) · [Certified continuation](docs/audits/2026-11-18-appc8-terminal-grammar/continuation.json) |
| Work on one of the two open cases | [Formal return predicates](lean_interop/BB6Interop/AppC8GeneratedSuffix.lean) · [Open questions and search limits](docs/audits/2026-11-18-appc8-terminal-grammar/proof-obligations.json) |
| Trace the AppC 7 argument | [Gate-halting proof](lean_phase4/CryptidSolvePhase4/AppC7RawGate.lean) · [Transfer to the upstream machine](lean_interop/BB6Interop/AppC7.lean) |
| Explore the counter models, finite simulations, or timings | [Evidence by paper topic](docs/EVIDENCE.md) |
| Repeat the checks | [Reproduction instructions](REPRODUCE.md) · [Release file checksums](SHA256SUMS) |

The six-state machine labels follow Dos Santos et al. The interoperability build fetches the pinned Google DeepMind **cryptids** repository. The bibliography gives the original papers and credits. [Upstream proof sources](https://github.com/google-deepmind/cryptids/tree/3647718b5df22e1a61462dec0376bd204526285a)

## Cite the paper or software

**Paper.** Novotny, D. (2026). *Following a Six-State Busy Beaver Candidate for 97 Quadrillion Steps: Certified Tape Rules, Cross-Library Proofs, and Two Open Endings* [Preprint]. Zenodo. [Published edition](https://doi.org/10.5281/zenodo.24370902) · [All versions](https://doi.org/10.5281/zenodo.24370901)

**Software.** Novotny, D. (2026). *Supporting proofs and experiments for Following a Six-State Busy Beaver Candidate for 97 Quadrillion Steps* (v1.0.0) [Software]. Zenodo. [10.5281/zenodo.24371839](https://doi.org/10.5281/zenodo.24371839)

## Licensing

The original software in this repository, including the Lean proofs, Python verifiers, and C benchmarks, is licensed under [Apache License 2.0](LICENSE). The published paper and its manuscript source carry [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). External dependencies retain their respective licenses.
