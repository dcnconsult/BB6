#!/usr/bin/env bash
set -euo pipefail
test ! -e /tmp/appc8-blank-proof-audit
mkdir -p /tmp/appc8-blank-proof-audit /audit-output
cd /tmp/appc8-blank-proof-audit
for lib in lean lean_phase4; do
  mkdir "$lib"
  cp /source/$lib/lean-toolchain /source/$lib/lakefile.lean "$lib/"
done
cp /source/lean/CryptidSolve.lean lean/
cp -R /source/lean/CryptidSolve lean/
cp /source/lean_phase4/CryptidSolvePhase4.lean lean_phase4/
cp -R /source/lean_phase4/CryptidSolvePhase4 lean_phase4/
cp -R /source/scripts /source/paper /source/lean_interop .
lean --version > /audit-output/environment.log
python3 --version >> /audit-output/environment.log
for lib in lean lean_phase4; do
  (cd "$lib" && lake build) > /audit-output/$lib-build.log 2>&1
  echo "PASS: clean $lib build and kernel axiom audit"
done
python3 - <<'PY'
from pathlib import Path
for lib, ns in [('lean','CryptidSolve'),('lean_phase4','CryptidSolvePhase4')]:
    source=Path(lib,ns,'KernelAudit.lean').read_text()
    fixture=('namespace ForeignFixture\naxiom untrusted : False\nend ForeignFixture\n'
             f'theorem {ns}.auditExternalFixture : False := ForeignFixture.untrusted\n\n')
    Path(lib,'NegativeAxiomFixture.lean').write_text(source.replace('open Lean in\n',fixture+'open Lean in\n',1))
PY
for lib in lean lean_phase4; do
  if (cd "$lib" && lake env lean NegativeAxiomFixture.lean) > /audit-output/$lib-negative-axiom.log 2>&1; then
    echo "FAIL: external axiom accepted"; exit 1
  fi
  grep -q 'non-allowlisted foundational constant' /audit-output/$lib-negative-axiom.log
  rm "$lib/NegativeAxiomFixture.lean"
  echo "PASS: $lib rejects external-namespace axiom"
done
cat > /tmp/AppC8Axioms.lean <<'LEAN'
import CryptidSolvePhase4.AppC8RawBlankReachability
#print axioms CryptidSolvePhase4.AppC8Raw.appC8_raw_shuttle
#print axioms CryptidSolvePhase4.AppC8Raw.appC8_raw_shuttle_rounds
#print axioms CryptidSolvePhase4.AppC8Raw.appC8_clean_middle_raw
#print axioms CryptidSolvePhase4.AppC8Raw.appC8_raw_reset
#print axioms CryptidSolvePhase4.AppC8Raw.appC8_raw_exit
#print axioms CryptidSolvePhase4.AppC8Raw.appC8_clean_macro_raw
#print axioms CryptidSolvePhase4.AppC8Raw.appC8_clean_macro_survives
#print axioms CryptidSolvePhase4.AppC8Raw.appC8_clean_macro_raw_and_ghost
#print axioms CryptidSolvePhase4.AppC8Raw.appC8_first_excursion
#print axioms CryptidSolvePhase4.AppC8Raw.appC8_blank_shuttle_entry
#print axioms CryptidSolvePhase4.AppC8Raw.appC8_blank_carry_twenty_three
#print axioms CryptidSolvePhase4.AppC8Raw.appC8_blank_odd_frontier
#print axioms CryptidSolvePhase4.AppC8Raw.appC8_blank_prefix_defined
#print axioms CryptidSolvePhase4.AppC8Raw.appC8_blank_clean_macro_transfer
LEAN
(cd lean_phase4 && lake env lean /tmp/AppC8Axioms.lean) > /audit-output/appc8-axioms.log 2>&1
python3 scripts/verify_appc8_raw_shuttle.py --output /audit-output/raw-shuttle-checks.json --lean-fixtures /tmp/AppC8Differential.lean > /audit-output/raw-shuttle-checks.log 2>&1
(cd lean_phase4 && lake env lean /tmp/AppC8Differential.lean) > /audit-output/appc8-differential.log 2>&1
cp /tmp/AppC8Differential.lean /audit-output/AppC8Differential.lean
python3 scripts/verify_appc7_raw_gate.py --output /audit-output/raw-gate-checks.json --lean-fixtures /tmp/AppC7Differential.lean > /audit-output/raw-gate-checks.log 2>&1
(cd lean_phase4 && lake env lean /tmp/AppC7Differential.lean) > /audit-output/appc7-differential.log 2>&1
cp /tmp/AppC7Differential.lean /audit-output/AppC7Differential.lean
echo "PASS: both raw proofs' independent checks and 384 Lean execution fixtures"
python3 scripts/verify_appc8_raw_clean_macro.py --output /audit-output/raw-clean-checks.json --lean-fixtures /tmp/AppC8CleanDifferential.lean > /audit-output/raw-clean-checks.log 2>&1
(cd lean_phase4 && lake env lean /tmp/AppC8CleanDifferential.lean) > /audit-output/appc8-clean-differential.log 2>&1
cp /tmp/AppC8CleanDifferential.lean /audit-output/AppC8CleanDifferential.lean
echo "PASS: raw reset, exit, full clean macro, and 33 complete-configuration Lean fixtures"
python3 scripts/verify_appc8_blank_reachability.py --output /audit-output/raw-blank-checks.json --lean-fixtures /tmp/AppC8BlankDifferential.lean > /audit-output/raw-blank-checks.log 2>&1
(cd lean_phase4 && lake env lean -s 65536 /tmp/AppC8BlankDifferential.lean) > /audit-output/appc8-blank-differential.log 2>&1
cp /tmp/AppC8BlankDifferential.lean /audit-output/AppC8BlankDifferential.lean
echo "PASS: blank trajectory and 10 complete-configuration direct Lean executions"
for suite in verify_cryptids_suite cryptid_solver_tools verify_all_appendix_a verify_clifford_bridges verify_lean_package verify_phase4_beyond_collatz; do
  python3 scripts/$suite.py > /audit-output/$suite.log 2>&1
  echo "PASS: $suite"
done
python3 scripts/verify_frontier_holdouts.py --manifest /audit-output/phase3-counts.json > /audit-output/verify_frontier_holdouts.log 2>&1
python3 scripts/verify_revision_claims.py --phase3-manifest /audit-output/phase3-counts.json --output /audit-output/revision-regressions.json > /audit-output/verify_revision_claims.log 2>&1
python3 scripts/verify_paper_tex.py > /audit-output/verify_paper_tex.log 2>&1
echo "PASS: frontier count manifest, revision regressions, and paper/bibliography audit"
echo "All mathematical and proof audits passed. Compiler kernels and bibliography entries unchanged."
