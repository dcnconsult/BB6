# BB6 interoperability proofs

This directory adds a Lean library to the pinned upstream cryptids checkout. The [build command](../REPRODUCE.md) installs the upstream toolchain and Mathlib cache, copies nine required local source modules, builds the required upstream dependencies and the integration library, and tests the axiom audit with two invalid proofs.

| Question | Source |
|---|---|
| How do the two representations of a tape agree after each step? | [Zipper adapter](BB6Interop/Zipper.lean) |
| Where does the AppC 7 blank-run classification enter? | [AppC 7](BB6Interop/AppC7.lean) |
| How are AppC 8 exact-time rules transported? | [AppC 8](BB6Interop/AppC8.lean) |
| Which larger return family has a halting counterexample? | [Residual tape](BB6Interop/AppC8ResidualTape.lean) |
| Which returns hold uniformly? | [Terminal grammar](BB6Interop/AppC8TerminalGrammar.lean) |
| Which two premises would complete the nonhalting argument? | [Generated suffixes](BB6Interop/AppC8GeneratedSuffix.lean) |
| Where is the last certified blank configuration? | [Terminal checkpoints](BB6Interop/AppC8TerminalCheckpoints.lean) |

The toolchain is Lean 4.35.0-rc4. The upstream commit is `3647718b5df22e1a61462dec0376bd204526285a`. The [terminal-grammar build record](../docs/audits/2026-11-18-appc8-terminal-grammar/build-result.json) records the historical source inputs and the allowed transitive axioms. The [source hash mapping](../docs/source-hash-changes.json) identifies release-header edits.
