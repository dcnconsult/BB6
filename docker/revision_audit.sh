#!/usr/bin/env bash
set -euo pipefail
test ! -e /tmp/bb6-audit-clean
mkdir -p /tmp/bb6-audit-clean /audit-output
# The host source mount is read-only. Both Lean libraries start without .lake.
for lib in lean lean_phase4; do
  mkdir -p /tmp/bb6-audit-clean/$lib
  cp /source/$lib/lean-toolchain /source/$lib/lakefile.lean /tmp/bb6-audit-clean/$lib/
done
cp /source/lean/CryptidSolve.lean /tmp/bb6-audit-clean/lean/
cp -R /source/lean/CryptidSolve /tmp/bb6-audit-clean/lean/
cp /source/lean_phase4/CryptidSolvePhase4.lean /tmp/bb6-audit-clean/lean_phase4/
cp -R /source/lean_phase4/CryptidSolvePhase4 /tmp/bb6-audit-clean/lean_phase4/
cp -R /source/scripts /source/benchmarks /source/paper /source/lean_interop /tmp/bb6-audit-clean/
cd /tmp/bb6-audit-clean
lean --version > /audit-output/environment.log
gcc --version >> /audit-output/environment.log
python3 --version >> /audit-output/environment.log
for lib in lean lean_phase4; do
  (cd "$lib" && lake build) > /audit-output/$lib-build.log 2>&1
  echo "PASS: fresh $lib build"
done
# Regression fixture: an axiom outside the library namespace must be rejected.
python3 - <<'PY'
from pathlib import Path
for lib, ns in [('lean', 'CryptidSolve'), ('lean_phase4', 'CryptidSolvePhase4')]:
    original = Path(lib, ns, 'KernelAudit.lean').read_text()
    fixture = ('namespace ForeignFixture\naxiom untrusted : False\nend ForeignFixture\n'
               f'theorem {ns}.auditExternalFixture : False := ForeignFixture.untrusted\n\n')
    modified = original.replace('open Lean in\n', fixture+'open Lean in\n', 1)
    Path(lib, 'NegativeAxiomFixture.lean').write_text(modified)
PY
for lib in lean lean_phase4; do
  if (cd "$lib" && lake env lean NegativeAxiomFixture.lean) > /audit-output/$lib-negative-axiom.log 2>&1; then
    echo "FAIL: external axiom accepted in $lib"; exit 1
  fi
  grep -q 'non-allowlisted foundational constant' /audit-output/$lib-negative-axiom.log
  rm "$lib/NegativeAxiomFixture.lean"
  echo "PASS: $lib rejects external-namespace axiom"
done
for suite in verify_cryptids_suite cryptid_solver_tools verify_all_appendix_a verify_clifford_bridges verify_lean_package verify_phase4_beyond_collatz verify_paper_tex; do
  python3 scripts/$suite.py > /audit-output/$suite.log 2>&1
  echo "PASS: $suite"
done
python3 scripts/verify_frontier_holdouts.py --manifest /audit-output/phase3-counts.json > /audit-output/verify_frontier_holdouts.log 2>&1
echo "PASS: frontier suite and executed-count manifest"
python3 scripts/verify_revision_claims.py --phase3-manifest /audit-output/phase3-counts.json --output /audit-output/revision-regressions.json > /audit-output/verify_revision_claims.log 2>&1
echo "PASS: mathematical regression witnesses"
python3 scripts/verify_appc7_raw_gate.py --output /audit-output/appc7-raw-gate.json --lean-fixtures /tmp/AppC7Differential.lean > /audit-output/appc7-raw-gate.log 2>&1
(cd lean_phase4 && lake env lean /tmp/AppC7Differential.lean) > /audit-output/appc7-differential.log 2>&1
echo "PASS: AppC7 raw-gate checks and independent Lean fixtures"
python3 scripts/verify_appc8_raw_shuttle.py --output /audit-output/appc8-raw-shuttle.json --lean-fixtures /tmp/AppC8Differential.lean > /audit-output/appc8-raw-shuttle.log 2>&1
(cd lean_phase4 && lake env lean /tmp/AppC8Differential.lean) > /audit-output/appc8-differential.log 2>&1
echo "PASS: AppC8 raw-shuttle checks and independent Lean fixtures"
python3 scripts/verify_appc8_raw_clean_macro.py --output /audit-output/raw-clean-checks.json --lean-fixtures /tmp/AppC8CleanDifferential.lean > /audit-output/raw-clean-checks.log 2>&1
(cd lean_phase4 && lake env lean /tmp/AppC8CleanDifferential.lean) > /audit-output/appc8-clean-differential.log 2>&1
cp /tmp/AppC8CleanDifferential.lean /audit-output/AppC8CleanDifferential.lean
echo "PASS: raw reset, exit, full clean macro, and 33 complete-configuration Lean fixtures"
python3 scripts/verify_appc8_blank_reachability.py --output /audit-output/raw-blank-checks.json --lean-fixtures /tmp/AppC8BlankDifferential.lean > /audit-output/raw-blank-checks.log 2>&1
(cd lean_phase4 && lake env lean -s 65536 /tmp/AppC8BlankDifferential.lean) > /audit-output/appc8-blank-differential.log 2>&1
cp /tmp/AppC8BlankDifferential.lean /audit-output/AppC8BlankDifferential.lean
echo "PASS: blank trajectory and 10 complete-configuration direct Lean executions"
python3 scripts/verify_appc8_odd_sector.py --output /audit-output/raw-odd-checks.json --lean-fixtures /tmp/AppC8OddDifferential.lean > /audit-output/raw-odd-checks.log 2>&1
(cd lean_phase4 && lake env lean -s 65536 /tmp/AppC8OddDifferential.lean) > /audit-output/appc8-odd-differential.log 2>&1
cp /tmp/AppC8OddDifferential.lean /audit-output/AppC8OddDifferential.lean
echo "PASS: universal odd-family samples, extended blank trajectory, and 22 direct Lean fixtures"
python3 scripts/verify_appc8_mod2_sector.py --output /audit-output/raw-mod2-checks.json --lean-fixtures /tmp/AppC8Mod2Differential.lean > /audit-output/raw-mod2-checks.log 2>&1
(cd lean_phase4 && lake env lean -s 65536 /tmp/AppC8Mod2Differential.lean) > /audit-output/appc8-mod2-differential.log 2>&1
cp /tmp/AppC8Mod2Differential.lean /audit-output/AppC8Mod2Differential.lean
echo "PASS: residue refinements, actual clean entry, six blank checkpoints, and 22 direct Lean fixtures"
python3 benchmarks/run_benchmarks.py > /audit-output/benchmarks-gcc.log 2>&1
echo "PASS: GCC C11 bit-exact suite and timings"
echo "All revision checks passed."
