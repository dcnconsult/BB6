# Evidence for the paper

For the current AppC 8 result, start with the [terminal-grammar proof obligations](audits/2026-11-18-appc8-terminal-grammar/proof-obligations.json). Each dated audit directory records a stage of the work. An open obligation or shorter checkpoint in an earlier directory describes what was known at that stage.

| Paper topic | Sources and evidence |
|---|---|
| Six-state tables and counter models | [Core proofs](../lean/CryptidSolve/), [theorem and claim ledger](audits/2026-11-17-revision/claim-ledger.json), [executed Phase 3 counts](audits/2026-11-17-revision/logs/phase3-counts.json) |
| AppC 7 gate halting and unreachability | [Raw gate proof](../lean_phase4/CryptidSolvePhase4/AppC7RawGate.lean), [gate evidence](audits/2026-11-17-appc7-proof/), [upstream integration record](audits/2026-11-18-interoperability-proof/build-result.json) |
| AppC 8 shuttle, clean rule, and first blank checkpoints | [Shuttle audit](audits/2026-11-17-appc8-proof/), [clean rule](audits/2026-11-18-appc8-clean-proof/), [blank entry](audits/2026-11-18-appc8-blank-proof/), [odd case](audits/2026-11-18-appc8-odd-proof/), [clean input reached from blank](audits/2026-11-18-appc8-mod2-proof/) |
| Longer blank run and return families | [Continuation checkpoints](audits/2026-11-18-appc8-continuation/certified-checkpoints.json), [run-list frontier](audits/2026-11-18-appc8-run-lists/frontier-chain.json), [halting counterexample](audits/2026-11-18-appc8-residual-tape/boundary-counterexample.json), [restricted trajectory](audits/2026-11-18-appc8-restricted-invariant/trajectory.json) |
| Current endpoint and the two open cases | [Lean checkpoint](../lean_interop/BB6Interop/AppC8TerminalCheckpoints.lean), [conditional closure proof](../lean_interop/BB6Interop/AppC8GeneratedSuffix.lean), [audited statements](audits/2026-11-18-appc8-terminal-grammar/CheckStatements.lean), [full-tape checks](audits/2026-11-18-appc8-terminal-grammar/differential-tests.json) |
| Related algebraic examples and the bouncer | [Phase 4 proofs](../lean_phase4/CryptidSolvePhase4/), [exact-arithmetic verifier](../scripts/verify_phase4_beyond_collatz.py) |
| Finite comparisons with upstream rules | [Pinned upstream identity records](research/2026-11-18-interoperability/source-manifest.json), [comparison code and results](research/2026-11-18-interoperability/) |
| Specialized loop benchmarks | [C kernels and runner](../benchmarks/), [compiler-specific summaries](audits/2026-11-17-revision/benchmark-summary.json), [GCC measurements](audits/2026-11-17-revision/logs/benchmarks-gcc-paper.log), [MSVC measurements](audits/2026-11-17-revision/logs/benchmarks-windows.log) |

The historical build records list the inputs to the original audits. For the public copy, the [source hash mapping](source-hash-changes.json) records editorial changes to nine Lean header comments, one Python module docstring, and two Dockerfile comments. The [distribution manifest](../SHA256SUMS) identifies the files supplied here.

## Verification of the release copy

The two Lean 4.16.0 libraries rebuilt from the distributed source inside an empty, offline build workspace. The standard six-part Docker verification run passed, including the kernel audits, Python suites, and GCC bit-exactness benchmark. The separate Lean 4.35.0-rc4 build fetched the pinned dependencies and checked the edited release sources. Its [new build record](audits/2026-11-19-release/build-result.json) contains their release hashes and both negative-control results. The [frontier test counts](audits/2026-11-19-release/phase3-counts.json) and [terminal-grammar checks](audits/2026-11-19-release/terminal-grammar-checks.json) were also regenerated from this copy.

The manuscript checker resolved all 24 bibliography keys and 28 distinct cross-reference targets. A clean four-command LaTeX and BibTeX build reproduced the distributed PDF's 23 pages with identical extracted text in page order.
