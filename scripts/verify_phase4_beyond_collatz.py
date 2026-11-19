"""
End-to-End Verification Suite for BB6 Phase 4: Beyond-Collatz Algebraic Transfers
=================================================================================
Audits:
  0. Strict `PC-5` Zero-Float AST Audit on both Phase-4 Python modules (`0` float literals,
     `0` `/` division operators, `0` floating-point functions/imports).
  1. Transfer 1: Non-Abelian Matrix Monoid Lifts & Raw `AppC_7` Multi-Defect Separation.
  2. Transfer 2: Exact Rational `LDL^T` Putinar SOS Barriers & Raw `AppC_7` `16b^2+28b+15` Gate.
  3. Transfer 3: `Q(sqrt 5)` / `Q(sqrt 2)` Galois Norm Barriers vs. `63/63` Modular Sieve Failure.
  4. Transfer 4: `[7,4,3]` Hamming Coset, Block-Width Scanner, & Raw `AppC_8` `(3/2)`-Ghost Law.
  5. Transfer 5: 2D Discrete Stokes Cohomology, 3-Cell NFA Failure, & Raw 6-State Bouncer Proof.
  6. Transfer 6: Reynolds/Molien Degree Routing & Zero-Float Berlekamp-Massey Walk Classifiers.
  7. Transfer 7: Multi-Prime `{2,3}` & `{3,7}` Portal Sieves & Antihydra Mod-`2^k` Kirchhoff `L^+`.
  8. Static Audit of `lean_phase4/` (`0` sorry/admit/axiom, delimiter balance, toolchain lock).
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys
from fractions import Fraction
from typing import Dict, List

THIS_DIR = pathlib.Path(__file__).resolve().parent
if str(THIS_DIR) not in sys.path:
    sys.path.insert(0, str(THIS_DIR))

from phase4_beyond_collatz_toolkit import (  # noqa: E402
    MatInt,
    MolienAndWalkZetaClassifier,
    MultiPrimeAndKirchhoffAnalyzer,
    NonAbelianMatrixMonoidEngine,
    QuadElem,
    QuadraticPisotRingEngine,
    RationalPutinarSOSSolver,
    SpaceTimePlaquetteCohomologyDecider,
    WreathBlockGaugeSynthesizer,
    analyze_3cell_local_nfa,
    audit_zero_float_ast,
    parse_tm,
    simulate_tm,
)

APPC7_CODE = "1RB1RC_1LC0LE_0RA1RD_1RF1LB_1LD0LA_---0RC"
APPC8_CODE = "1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---"
BOUNCER_COHOM_CODE = "1RB0RF_0RE0RE_1RF1LD_0LC0LA_0LD1RF_0LA---"


def _word_to_tape(bits: str) -> Dict[int, int]:
    return {idx: 1 for idx, ch in enumerate(bits) if ch == "1"}


def _tape_word(tape: Dict[int, int]) -> str:
    if not tape:
        return ""
    lo = min(tape.keys())
    hi = max(tape.keys())
    return "".join(str(tape.get(i, 0)) for i in range(lo, hi + 1))


def strip_lean_comments(src: str) -> str:
    """Strip nested `/- ... -/` block comments and `-- ...` line comments."""
    out: List[str] = []
    i = 0
    n = len(src)
    depth = 0
    in_str = False
    while i < n:
        if depth == 0 and not in_str and i + 1 < n and src[i : i + 2] == "/-":
            depth = 1
            i += 2
            continue
        if depth > 0:
            if i + 1 < n and src[i : i + 2] == "/-":
                depth += 1
                i += 2
            elif i + 1 < n and src[i : i + 2] == "-/":
                depth -= 1
                i += 2
            else:
                if src[i] == "\n":
                    out.append("\n")
                i += 1
            continue
        if not in_str and i + 1 < n and src[i : i + 2] == "--":
            while i < n and src[i] != "\n":
                i += 1
            continue
        if src[i] == '"':
            in_str = not in_str
            out.append(src[i])
            i += 1
            continue
        if in_str and src[i] == "\\" and i + 1 < n:
            out.append(src[i : i + 2])
            i += 2
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


def audit_0_pc5_zero_float() -> None:
    toolkit_path = THIS_DIR.joinpath("phase4_beyond_collatz_toolkit.py")
    verifier_path = pathlib.Path(__file__).resolve()
    for path in (toolkit_path, verifier_path):
        ok, issues = audit_zero_float_ast(path.read_text(encoding="utf-8"), label=path.name)
        if not ok:
            raise AssertionError(f"PC-5 Zero-Float AST violation in {path.name}: {issues}")
    print("[PASS] Audit 0 (PC-5 Zero-Float AST): 0 float literals, 0 `/` ops in toolkit & verifier.")


def audit_1_non_abelian_matrix_monoid() -> None:
    mat_t = MatInt(((1, 1), (0, 1)))
    mat_d = MatInt(((17, 7), (0, 4)))
    engine = NonAbelianMatrixMonoidEngine({"T": mat_t, "D": mat_d})

    comm = mat_t.commutator(mat_d)
    assert comm == MatInt(((0, -13), (0, 0))), f"Unexpected commutator: {comm}"

    w1 = ["T", "T", "T", "T", "D", "D"]
    w2 = ["D", "D", "T", "T", "T", "T"]
    assert engine.parikh_counts(w1) == engine.parikh_counts(w2) == {"D": 2, "T": 4}
    m1 = engine.lift_word(w1)
    m2 = engine.lift_word(w2)
    assert m1 == MatInt(((289, 211), (0, 16)))
    assert m2 == MatInt(((289, 1303), (0, 16)))
    assert m1 != m2

    assert engine.certify_rewrite_cone_step(["T", "D"], ["D", "T", "T", "T", "T"])

    appc7 = parse_tm(APPC7_CODE)

    def condense_appc7(sym_word: List[str]) -> tuple[int, int]:
        raw = "100" + "".join("10" if s == "T" else "11100" for s in sym_word)
        tape = _word_to_tape(raw)
        head = len(raw)
        lo = 0
        hi = len(raw)
        st = "A"
        for step in range(1, 5000):
            act = appc7[(st, tape.get(head, 0))]
            assert act is not None
            w, d, st = act
            if w == 0:
                tape.pop(head, None)
            else:
                tape[head] = w
            head += d
            if head < lo:
                lo = head
            if head > hi:
                hi = head
                if st == "A":
                    tw = "".join(str(tape.get(p, 0)) for p in range(lo, head)).lstrip("0")
                    if tw.startswith("100") and len(tw) > 3:
                        rem = tw[3:]
                        if len(rem) % 2 == 0 and all(
                            rem[i : i + 2] == "10" for i in range(0, len(rem), 2)
                        ):
                            return (step, len(rem) // 2)
        raise AssertionError("AppC_7 condensation did not reach clean R_A(k)")

    s1, k1 = condense_appc7(w1)
    s2, k2 = condense_appc7(w2)
    assert (s1, k1) == (1227, 31), f"Expected (1227, 31), got {(s1, k1)}"
    assert (s2, k2) == (656, 22), f"Expected (656, 22), got {(s2, k2)}"

    for a in range(7):
        steps_a, k_a = condense_appc7(["T"] * a + ["D", "T", "T"])
        assert steps_a == 8 * a + 79 and k_a == a + 8

    print(
        f"[PASS] Audit 1 (Transfer 1 Matrix Monoid): T^4 D^2 -> R_A({k1}) ({s1} steps) "
        f"!= D^2 T^4 -> R_A({k2}) ({s2} steps); single-defect 8a+79 verified (a=0..6)."
    )


def audit_2_putinar_sos_and_appc7_gate() -> None:
    b_para = {(0, 2): Fraction(1), (1, 0): Fraction(-1), (0, 0): Fraction(1)}
    res_para = RationalPutinarSOSSolver.verify_putinar_barrier(
        barrier=b_para,
        init_pt=(2, 0),
        step_x={(1, 0): Fraction(1), (0, 1): Fraction(2), (0, 0): Fraction(1)},
        step_y={(0, 1): Fraction(1), (0, 0): Fraction(1)},
        guard_g={(0, 1): Fraction(4), (1, 0): Fraction(-1), (0, 0): Fraction(-3)},
        monomials_0=[(0, 0), (0, 1)],
        gram_0=[[Fraction(4), Fraction(-2)], [Fraction(-2), Fraction(1)]],
        monomials_1=[(0, 0)],
        gram_1=[[Fraction(1)]],
        step_neg_monomials=[(0, 0)],
        step_neg_gram=[[Fraction(0)]],
    )
    assert res_para["certified"] is True

    b_cpl = {(0, 2): Fraction(1), (0, 1): Fraction(1), (1, 0): Fraction(-1), (0, 0): Fraction(2)}
    res_cpl = RationalPutinarSOSSolver.verify_putinar_barrier(
        barrier=b_cpl,
        init_pt=(3, 0),
        step_x={(1, 0): Fraction(1), (0, 1): Fraction(2), (0, 0): Fraction(2)},
        step_y={(0, 1): Fraction(1), (0, 0): Fraction(1)},
        guard_g={(0, 1): Fraction(4), (1, 0): Fraction(-1), (0, 0): Fraction(-1)},
        monomials_0=[(0, 0), (0, 1)],
        gram_0=[[Fraction(3), Fraction(-3, 2)], [Fraction(-3, 2), Fraction(1)]],
        monomials_1=[(0, 0)],
        gram_1=[[Fraction(1)]],
        step_neg_monomials=[(0, 0)],
        step_neg_gram=[[Fraction(0)]],
    )
    assert res_cpl["certified"] is True
    ldlt0 = res_cpl["ldlt_0"]
    assert ldlt0.D == [Fraction(3, 1), Fraction(1, 4)]
    assert ldlt0.L[1][0] == Fraction(-1, 2)
    assert ldlt0.cleared_scale == 4

    appc7 = parse_tm(APPC7_CODE)
    gate_steps: List[int] = []
    for b in range(6):
        bits = "00" + ("1110" * b) + "11"
        halt_t, _, _, _ = simulate_tm(appc7, max_steps=1000, init_tape=_word_to_tape(bits), init_head=-1)
        expected = 16 * b * b + 28 * b + 15
        assert halt_t == expected, f"AppC_7 gate b={b}: got {halt_t}, expected {expected}"
        gate_steps.append(halt_t)

    print(
        f"[PASS] Audit 2 (Transfer 2 Putinar SOS): 1-pivot & 2-pivot rational LDL^T (D={ldlt0.D}) "
        f"certified; AppC_7 gate steps {gate_steps} == 16b^2+28b+15."
    )


def audit_3_pisot_quadratic_rings() -> None:
    sieve_res = QuadraticPisotRingEngine.test_modular_sieves_fibonacci(max_modulus=64)
    assert sieve_res["all_failed"] is True and sieve_res["failed_count"] == 63

    phi = QuadraticPisotRingEngine.phi()
    assert phi.is_positive() is True
    assert (phi * phi - phi - QuadElem(Fraction(1), Fraction(0), 5)).norm() == 0

    x, y = 3, 2
    for n in range(30):
        z = QuadElem(Fraction(x), Fraction(0), 5) - QuadElem(Fraction(y), Fraction(0), 5) * phi
        expected_norm = Fraction(-1) if n % 2 == 0 else Fraction(1)
        assert z.norm() == expected_norm
        x, y = x + y, x

    px, py = 3, 2
    for step_i in range(25):
        pz = QuadElem(Fraction(px), -Fraction(py), 2)
        assert pz.norm() == (Fraction(1) if step_i % 2 == 0 else Fraction(-1))
        px, py = px + 2 * py, px + py

    print(
        "[PASS] Audit 3 (Transfer 3 Pisot Quadratic Rings): 63/63 modular sieves fail (M=2..64); "
        "Q(sqrt 5) & Q(sqrt 2) Galois norm barriers verified exact."
    )


def audit_4_wreath_block_gauge_and_appc8() -> None:
    coset = WreathBlockGaugeSynthesizer.verify_fano_hamming743_coset()
    assert coset["codeword_count"] == 16
    assert coset["weight_dist"] == {0: 1, 3: 7, 4: 7, 7: 1}
    assert coset["anchor_coset"] == [8, 15, 17, 22, 34, 37, 59, 60, 67, 68, 90, 93, 105, 110, 112, 119]

    rates = WreathBlockGaugeSynthesizer.scan_block_widths(APPC8_CODE, widths=(1, 2, 3, 4, 5, 6))
    best_w = min(rates.keys(), key=lambda w: rates[w])
    assert best_w == 3, f"Expected width w=3 to minimize AppC_8 block defect, got {rates}"
    assert rates[3] * 5 < rates[1] and rates[3] * 8 < rates[2], f"Unexpected rates: {rates}"

    appc8 = parse_tm(APPC8_CODE)
    for k in range(0, 6):
        for m in range(5, 11):
            bits = "10" + ("110" * k) + ("1" * m)
            halt_t, tape, head, st = simulate_tm(
                appc8, max_steps=12 * k + 26, init_tape=_word_to_tape(bits), init_head=-1
            )
            assert halt_t is None and st == "A" and head == min(tape.keys()) - 1
            assert _tape_word(tape) == "10" + ("110" * (k + 2)) + ("1" * (m - 4))

    macro_steps: List[int] = []
    for q in range(5):
        c = 4 * (q + 1)
        c_next = 6 * q + 8
        duration = 108 * q * q + 332 * q + 238
        bits = "10" + ("100" * c) + "1"
        halt_t, tape, head, st = simulate_tm(
            appc8, max_steps=duration, init_tape=_word_to_tape(bits), init_head=len(bits), init_state="E"
        )
        assert halt_t is None and st == "E" and head == max(tape.keys()) + 1
        assert _tape_word(tape) == "10" + ("100" * c_next) + "1"
        assert 2 * (c_next + 4) == 3 * (c + 4)
        macro_steps.append(duration)

    print(
        f"[PASS] Audit 4 (Transfer 4 Wreath Block Gauge): [7,4,3] coset verified; AppC_8 min defect "
        f"at w={best_w} ({rates[3]}); (3/2)-ghost steps {macro_steps} verified."
    )


def audit_5_spacetime_cohomology() -> None:
    jx = [[(2 * x - t + 1) for x in range(5)] for t in range(5)]
    jt = [[(x * t - 3) for x in range(6)] for t in range(4)]
    stokes_ok, bulk, bdry = SpaceTimePlaquetteCohomologyDecider.verify_stokes_on_grid(jx, jt)
    assert stokes_ok and bulk == bdry

    phi = [[(x * x - 3 * x * t + 2 * t * t) for x in range(6)] for t in range(5)]
    d0_x = [[phi[t][x + 1] - phi[t][x] for x in range(5)] for t in range(5)]
    d0_t = [[phi[t + 1][x] - phi[t][x] for x in range(6)] for t in range(4)]
    exact_ok, zero_bulk, zero_bdry = SpaceTimePlaquetteCohomologyDecider.verify_stokes_on_grid(d0_x, d0_t)
    assert exact_ok and zero_bulk == 0 and zero_bdry == 0

    bouncer = parse_tm(BOUNCER_COHOM_CODE)
    nfa_info = analyze_3cell_local_nfa(bouncer)
    assert nfa_info["halt_reachable"] is True
    assert nfa_info["visited_count"] == 26
    assert len(nfa_info["shortest_halt_path"]) - 1 == 3

    cocycle_res = SpaceTimePlaquetteCohomologyDecider.decide_bipartite_sublattice_nonhalting(
        BOUNCER_COHOM_CODE
    )
    assert cocycle_res["certified_nonhalting"] is True
    assert cocycle_res["even_states"] == ["A", "C", "E"]
    assert cocycle_res["odd_states"] == ["B", "D", "F"]

    halt_t, tape, _, _ = simulate_tm(bouncer, max_steps=5000)
    assert halt_t is None
    assert len(tape) >= 20
    assert all(pos % 2 == 0 for pos in tape.keys())

    print(
        f"[PASS] Audit 5 (Transfer 5 Space-Time Cohomology): Stokes & d1∘d0=0 verified; "
        f"3-cell NFA hits Halt in 3 steps ({nfa_info['visited_count']}/48 patches), "
        f"sublattice 1-cocycle proves unconditional raw-TM non-halting."
    )


def audit_6_molien_and_walk_series() -> None:
    pin2_swap = [((1, 0), (0, 1)), ((0, 1), (1, 0))]
    central_inv = [((1, 0), (0, 1)), ((-1, 0), (0, -1))]
    dihedral_d4 = [
        ((1, 0), (0, 1)),
        ((-1, 0), (0, 1)),
        ((1, 0), (0, -1)),
        ((-1, 0), (0, -1)),
        ((0, 1), (1, 0)),
        ((0, -1), (1, 0)),
        ((0, 1), (-1, 0)),
        ((0, -1), (-1, 0)),
    ]
    assert MolienAndWalkZetaClassifier.invariant_dims_2d(pin2_swap, max_deg=3)[1] == 1
    dims_inv = MolienAndWalkZetaClassifier.invariant_dims_2d(central_inv, max_deg=3)
    assert dims_inv[1] == 0 and dims_inv[2] == 3
    dims_d4 = MolienAndWalkZetaClassifier.invariant_dims_2d(dihedral_d4, max_deg=4)
    assert dims_d4[1] == 0 and dims_d4[2] == 1 and dims_d4[3] == 0 and dims_d4[4] == 2

    seq_cyc = [(n // 3) * 5 + (1 if n % 3 == 0 else (2 if n % 3 == 1 else 4)) for n in range(16)]
    _, q_cyc = MolienAndWalkZetaClassifier.berlekamp_massey_exact(seq_cyc)
    assert MolienAndWalkZetaClassifier.classify_denominator(q_cyc) == "CYCLOTOMIC_TRANSLATED_CYCLER(period=3)"

    seq_appc7 = [16 * b * b + 28 * b + 15 for b in range(10)]
    _, q_appc7 = MolienAndWalkZetaClassifier.berlekamp_massey_exact(seq_appc7)
    assert MolienAndWalkZetaClassifier.classify_denominator(q_appc7) == "PARABOLIC_POLYNOMIAL_BOUNCER"

    seq_fib = [2, 3]
    for _ in range(10):
        seq_fib.append(seq_fib[-1] + seq_fib[-2])
    _, q_fib = MolienAndWalkZetaClassifier.berlekamp_massey_exact(seq_fib)
    assert MolienAndWalkZetaClassifier.classify_denominator(q_fib) == "PISOT_IRRATIONAL_SUBSTITUTIVE"

    seq_a5 = [5 * (1 << j) - j - 6 for j in range(10)]
    _, q_a5 = MolienAndWalkZetaClassifier.berlekamp_massey_exact(seq_a5)
    assert MolienAndWalkZetaClassifier.classify_denominator(q_a5) == "MIXED_COLLATZ_PORTAL"

    print(
        "[PASS] Audit 6 (Transfer 6 Molien & Walk Series): Reynolds ranks (coordinate swap, Z_2, D_4) & "
        "exact Berlekamp-Massey Q(t) verified across all 4 BB(6) regimes."
    )


def audit_7_multiprime_and_kirchhoff() -> None:
    p1 = MultiPrimeAndKirchhoffAnalyzer.verify_multiprime_portal(
        portal_fn_mod=lambda j, m: (pow(2, j, m) + 3 * j) % m,
        target_residue=1,
        composite_mod=6,
        period_len=6,
        prime_powers=(8, 9),
        j_min=1,
    )
    assert p1["all_single_primes_fail"] and p1["composite_eliminated"]
    assert p1["single_prime_witnesses"] == {8: 3, 9: 2}

    p2 = MultiPrimeAndKirchhoffAnalyzer.verify_multiprime_portal(
        portal_fn_mod=lambda j, m: (pow(2, j, m) + 7 * j) % m,
        target_residue=15,
        composite_mod=21,
        period_len=9,
        prime_powers=(9, 49),
        j_min=0,
    )
    assert p2["all_single_primes_fail"] and p2["composite_eliminated"]
    assert p2["single_prime_witnesses"] == {9: 7, 49: 12}

    p3 = MultiPrimeAndKirchhoffAnalyzer.verify_multiprime_portal(
        portal_fn_mod=lambda j, m: (pow(2, j, m) + pow(3, j, m)) % m,
        target_residue=7,
        composite_mod=21,
        period_len=6,
        prime_powers=(9, 49),
        j_min=1,
    )
    assert p3["all_single_primes_fail"] and p3["composite_eliminated"]
    assert p3["single_prime_witnesses"] == {9: 4, 49: 9}

    k8 = MultiPrimeAndKirchhoffAnalyzer.antihydra_mod_2k_kirchhoff(3)
    k16 = MultiPrimeAndKirchhoffAnalyzer.antihydra_mod_2k_kirchhoff(4)
    k32 = MultiPrimeAndKirchhoffAnalyzer.antihydra_mod_2k_kirchhoff(5)
    assert k8["projector_ok"] and k8["lcm_den"] == 48 and k8["r_eff_3_7"] == Fraction(29, 48)
    assert k16["projector_ok"] and k16["r_eff_3_7"] == Fraction(31, 60)
    assert k32["projector_ok"] and k32["r_eff_3_7"] == Fraction(703, 960)

    print(
        f"[PASS] Audit 7 (Transfer 7 Multi-Prime & Kirchhoff): 3 multi-prime CRT sieves verified; "
        f"Antihydra R_eff(3<->7) Mod-8={k8['r_eff_3_7']}, Mod-16={k16['r_eff_3_7']}, Mod-32={k32['r_eff_3_7']}."
    )


def audit_8_lean_phase4_static(lean_dir: pathlib.Path) -> None:
    assert lean_dir.is_dir(), f"Required Lean directory missing: {lean_dir}"

    toolchain = lean_dir.joinpath("lean-toolchain").read_text(encoding="utf-8").strip()
    assert toolchain == "leanprover/lean4:v4.16.0", f"Unexpected toolchain: {toolchain}"

    lakefile = lean_dir.joinpath("lakefile.lean").read_text(encoding="utf-8")
    assert "require" not in strip_lean_comments(lakefile), "External Lake dependency detected!"

    lean_files = sorted(
        (p for p in lean_dir.rglob("*.lean") if ".lake" not in p.parts),
        key=lambda p: p.relative_to(lean_dir).as_posix(),
    )
    rel_names = [p.relative_to(lean_dir).as_posix() for p in lean_files]
    expected_files = sorted(
        [
            "lakefile.lean",
            "CryptidSolvePhase4.lean",
            "CryptidSolvePhase4/Basic.lean",
            "CryptidSolvePhase4/AppC7RawGate.lean",
            "CryptidSolvePhase4/AppC8RawShuttle.lean",
            "CryptidSolvePhase4/AppC8RawCleanMacro.lean",
            "CryptidSolvePhase4/AppC8RawBlankReachability.lean",
            "CryptidSolvePhase4/AppC8RawOddSector.lean",
            "CryptidSolvePhase4/AppC8RawMod2Sector.lean",
            "CryptidSolvePhase4/Transfer1MatrixMonoid.lean",
            "CryptidSolvePhase4/Transfer2PutinarSOS.lean",
            "CryptidSolvePhase4/Transfer3PisotQuadratic.lean",
            "CryptidSolvePhase4/Transfer4WreathBlockGauge.lean",
            "CryptidSolvePhase4/Transfer5SpaceTimeCohomology.lean",
            "CryptidSolvePhase4/Transfer6MolienAndWalkSeries.lean",
            "CryptidSolvePhase4/Transfer7MultiPrimeKirchhoff.lean",
            "CryptidSolvePhase4/KernelAudit.lean",
        ]
    )
    assert rel_names == expected_files, f"Lean file list mismatch:\n  got={rel_names}\n  exp={expected_files}"

    thm_total = 0
    pairs = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
    closers = {v: k for k, v in pairs.items()}

    for lf in lean_files:
        raw = lf.read_text(encoding="utf-8")
        clean = strip_lean_comments(raw)
        for bad in (r"\bsorry\b", r"\badmit\b", r"\baxiom\b"):
            if re.search(bad, clean):
                raise AssertionError(f"Forbidden token {bad} in {lf}")
        thm_total += len(re.findall(r"\b(?:theorem|lemma)\b", clean))

        stack: List[str] = []
        in_str = False
        idx = 0
        while idx < len(clean):
            ch = clean[idx]
            if ch == '"':
                in_str = not in_str
                idx += 1
                continue
            if in_str and ch == "\\" and idx + 1 < len(clean):
                idx += 2
                continue
            if not in_str:
                if ch in pairs:
                    stack.append(ch)
                elif ch in closers:
                    if not stack or stack[-1] != closers[ch]:
                        raise AssertionError(f"Unbalanced delimiter '{ch}' in {lf}")
                    stack.pop()
            idx += 1
        if stack:
            raise AssertionError(f"Unclosed delimiters {stack} in {lf}")

    assert thm_total >= 40, f"Expected >= 40 Phase-4 theorems, found {thm_total}"
    print(
        f"[PASS] Audit 8 (Lean Phase-4 Static Audit): {len(lean_files)} files, {thm_total} theorems, "
        f"0 sorry/admit/axiom, toolchain={toolchain}."
    )


def main() -> None:
    parser = argparse.ArgumentParser(description="Verify BB6 Phase-4 Beyond-Collatz Transfers")
    default_lean = THIS_DIR.parent.joinpath("lean_phase4")
    parser.add_argument("--lean-dir", type=pathlib.Path, default=default_lean)
    args = parser.parse_args()

    print("=" * 78)
    print("BB6 PHASE 4 — BEYOND-COLLATZ ALGEBRAIC TRANSFERS VERIFICATION SUITE")
    print("=" * 78)
    audit_0_pc5_zero_float()
    audit_1_non_abelian_matrix_monoid()
    audit_2_putinar_sos_and_appc7_gate()
    audit_3_pisot_quadratic_rings()
    audit_4_wreath_block_gauge_and_appc8()
    audit_5_spacetime_cohomology()
    audit_6_molien_and_walk_series()
    audit_7_multiprime_and_kirchhoff()
    audit_8_lean_phase4_static(args.lean_dir)
    print("=" * 78)
    print("ALL PHASE-4 AUDITS PASSED (ZERO FLOATS, ZERO SORRY, EXACT RAW-TM MATCH)")
    print("=" * 78)


if __name__ == "__main__":
    main()
