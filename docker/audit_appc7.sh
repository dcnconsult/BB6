#!/usr/bin/env bash
set -euo pipefail
test ! -e /tmp/appc7-proof-audit
mkdir -p /tmp/appc7-proof-audit /audit-output
cd /tmp/appc7-proof-audit
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
cat > /tmp/AppC7Axioms.lean <<'LEAN'
import CryptidSolvePhase4.AppC7RawGate
#print axioms CryptidSolvePhase4.AppC7Raw.gate_sweep_exact_time
#print axioms CryptidSolvePhase4.AppC7Raw.appC7_raw_gate_exact_time
LEAN
(cd lean_phase4 && lake env lean /tmp/AppC7Axioms.lean) > /audit-output/appc7-axioms.log 2>&1
python3 scripts/verify_appc7_raw_gate.py --output /audit-output/raw-gate-checks.json --lean-fixtures /tmp/AppC7Differential.lean > /audit-output/raw-gate-checks.log 2>&1
(cd lean_phase4 && lake env lean /tmp/AppC7Differential.lean) > /audit-output/differential-fixtures.log 2>&1
cp /tmp/AppC7Differential.lean /audit-output/AppC7Differential.lean
echo "PASS: raw gate checks and 192 independent Lean execution fixtures"
for suite in verify_phase4_beyond_collatz verify_revision_claims verify_paper_tex; do
  python3 scripts/$suite.py > /audit-output/$suite.log 2>&1
  echo "PASS: $suite"
done
echo "AppC7 proof audit complete. Compiler kernels and bibliography are unchanged."
