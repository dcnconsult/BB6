#!/usr/bin/env bash
set -euo pipefail

echo "======================================================================"
echo " BB(6) Cryptids + Phase-4 Beyond-Collatz Transfers — Verification"
echo "======================================================================"
echo "Lean toolchain : $(lean --version)"
echo "C compiler     : $(gcc --version | head -n 1)"
echo "Python runtime : $(python3 --version)"
echo "----------------------------------------------------------------------"

echo "[1/6] Lean 4 Kernel Build & Axiom Audit (Phase 1-3: lean/CryptidSolve)..."
cd /workspace/lean
lake build
lake env lean CryptidSolve/KernelAudit.lean
echo "      -> PASS: CryptidSolve lake build & kernel axiom audit succeeded."

echo "[2/6] Lean 4 Kernel Build & Axiom Audit (Phase 4: lean_phase4/CryptidSolvePhase4)..."
cd /workspace/lean_phase4
lake build
lake env lean CryptidSolvePhase4/KernelAudit.lean
echo "      -> PASS: CryptidSolvePhase4 lake build & kernel axiom audit succeeded."

echo "[3/6] Phase 1-3 Raw 6-State TM & Algebraic Verification Suites (scripts/)..."
cd /workspace
python3 scripts/verify_cryptids_suite.py
python3 scripts/cryptid_solver_tools.py
python3 scripts/verify_all_appendix_a.py
python3 scripts/verify_frontier_holdouts.py
python3 scripts/verify_clifford_bridges.py
python3 scripts/verify_lean_package.py
python3 scripts/verify_paper_tex.py
python3 scripts/verify_revision_claims.py

echo "[4/6] Phase 4 Zero-Float Beyond-Collatz Toolkit & Raw-TM Suite (scripts/)..."
python3 scripts/verify_phase4_beyond_collatz.py
python3 scripts/verify_appc7_raw_gate.py
python3 scripts/verify_appc8_raw_shuttle.py
python3 scripts/verify_appc8_raw_clean_macro.py
python3 scripts/verify_appc8_blank_reachability.py
python3 scripts/verify_appc8_odd_sector.py
python3 scripts/verify_appc8_mod2_sector.py

echo "[5/6] C11 + Python CLZ/CTZ Hardware Benchmark & Bit-Exactness Suite..."
python3 benchmarks/run_benchmarks.py

echo "[6/6] ALL PHASE 1-4 VERIFICATION PILLARS PASSED (EXIT 0)."
