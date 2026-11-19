"""Regression tests for the mathematical and audit-boundary corrections of 2026-11-17.

Finite checks here deliberately do not claim universal raw-to-macro refinement.
"""
from pathlib import Path
from fractions import Fraction
import argparse
import contextlib
import io
import json
import re
import tempfile

from verify_lean_package import lean_epochStepA11, lean_stepBMO8, lean_stepT315, audit_lean_files
from cryptid_solver_tools import LeftNullspaceSynthesizer
from verify_paper_tex import audit_paper
from verify_phase4_beyond_collatz import audit_8_lean_phase4_static

ROOT = Path(__file__).resolve().parent.parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    parser.add_argument('--phase3-manifest', type=Path)
    args = parser.parse_args()
    result = {}

    # F01: independently derive the contraction-run result and compare the model.
    for r in range(1, 91):
        a, b = 3**r - 1, 1
        for i in range(r):
            a, b = lean_stepT315(a, b)
            assert a == 3**(r-i-1)-1
        assert (a, b) == (0, 3**r+r)
        assert (lean_stepT315(a, b) is None) == (r % 3 == 0)
    for initial in range(1, 501):
        a, b = initial, 1
        while a % 3 == 2:
            a, b = lean_stepT315(a, b)
        immediate = a == 0 and lean_stepT315(a, b) is None
        assert immediate == any(initial == 3**(3*m)-1 for m in range(1, 4))
    later = {}
    for initial in [14, 20]:
        state = (initial, 1)
        for steps in range(100):
            nxt = lean_stepT315(*state)
            if nxt is None:
                later[initial] = {'defined_steps': steps, 'halt_state': state}
                break
            state = nxt
        else:
            raise AssertionError('Expected later-branch halting witness')
    result['T315'] = {'power_cases': 90, 'initial_interval': [1, 500], 'later_branch_witnesses': later}

    # F02: constant drift does not imply conservation or a quotient dimension.
    synthesis = LeftNullspaceSynthesizer.synthesize([[[1, 0], [0, 1]]])
    assert synthesis['left_nullspace_dim'] == 2
    assert synthesis['return_dimension'] is None
    assert 'conditional_d_ret' not in synthesis
    assert Fraction(1, 2) == Fraction(2, 4)
    assert Fraction(2, 3) != Fraction(3, 5)
    result['nullspace'] = {'ambient_dimension': 2, 'nullity': 2, 'return_dimension': None,
                           'normalized_successors': ['2/3', '3/5']}

    # F03/F07: finite A11 result plus the counterexample to c monotonicity.
    assert lean_epochStepA11(20, 5, 6) == (65, 3, 3)
    state = (16, 0, 3)
    for expected in [(12, 6, 3), (12, 24, 3), (20, 1138, 3)]:
        state = lean_epochStepA11(*state)
        assert state == expected
    z = 20
    for _ in range(569):
        z = 3*z//2
    c4 = (3*(z//2)-19)//2
    assert len(str(z)) == 102 and z % 8 == 7 and c4 % 16 == 1
    result['A11'] = {'Z3': str(z), 'c4': str(c4), 'Z3_mod8': z % 8, 'c4_mod16': c4 % 16,
                     'decreasing_c_witness': [[20, 5, 6], [65, 3, 3]],
                     'epoch4_completion': 'not established'}

    # F06: test the full domain and all three rays, including excluded endpoints.
    checked = 0
    for a in range(201):
        for c in range(201):
            domain = a+c >= 8 and c >= 2 and (a % 3 == 0 or c % 3 == 2)
            if not domain:
                continue
            gates = ((a >= 3 and a % 3 == 0 and c == 2*a-1)
                     or (a >= 2 and a % 3 == 2 and c == 2*a-2)
                     or (a >= 6 and a % 3 == 0 and c == 2*a-2))
            assert (lean_stepBMO8(a, c) is None) == gates, (a, c)
            checked += 1
    assert lean_stepBMO8(3, 4) is None and 3+4 < 8
    result['BMO8'] = {'domain_cases': checked, 'omitted_domain_counterexample': [3, 4]}

    # F08: arbitrary initial residues and translations obey a smaller annihilator.
    for initial in [(0, 1, 2), (4, -2, 9), (0, 0, 0)]:
        for d in [-3, 0, 3, 7]:
            def u(n):
                return initial[n % 3] + (n//3)*d
            for n in range(100):
                assert u(n+6)-2*u(n+3)+u(n) == 0
                assert u(n+4)-u(n+3)-u(n+1)+u(n) == 0
    for n in range(100):
        assert (n+2)-2*(n+1)+n == 0
    result['translated_sequences'] = {'minimality_counterexample': 'u(n)=n',
                                       'general_annihilator': '(S-1)(S^3-1)'}

    # F13: a missing or empty requested Lean directory must never silently pass.
    with tempfile.TemporaryDirectory() as tmp:
        for missing in [Path(tmp)/'missing', Path(tmp)]:
            try:
                with contextlib.redirect_stdout(io.StringIO()):
                    audit_paper(ROOT/'paper', [ROOT/'lean', missing])
            except AssertionError as e:
                assert 'Required Lean directory missing' in str(e) or 'No Lean source files' in str(e)
            else:
                raise AssertionError('Static auditor accepted a missing or empty library')
        for audit in [audit_lean_files, audit_8_lean_phase4_static]:
            try:
                audit(Path(tmp)/'missing')
            except AssertionError as e:
                assert 'Required Lean directory missing' in str(e)
            else:
                raise AssertionError('Library auditor silently skipped missing sources')
    source_counts = {}
    for lib in ['lean', 'lean_phase4']:
        source_counts[lib] = sum(len(re.findall(r'^\s*theorem\s+', p.read_text(encoding='utf-8'), re.M))
                                 for p in (ROOT/lib).rglob('*.lean') if '.lake' not in p.parts)
    assert source_counts == {'lean': 103, 'lean_phase4': 213}, source_counts
    result['source_theorems'] = source_counts
    result['missing_source_negative_tests'] = 4

    if args.phase3_manifest:
        manifest = json.loads(args.phase3_manifest.read_text(encoding='utf-8'))
        assert list(manifest['counts'].values()) == [1375, 670, 1085, 42, 118, 961, 1020]
        assert manifest['total'] == sum(manifest['counts'].values()) == 5271
        result['phase3_manifest_verified'] = manifest
    audit_paper(ROOT/'paper', [ROOT/'lean', ROOT/'lean_phase4', ROOT/'lean_interop'])
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(result, indent=2))
    print('[PASS] Revision mathematical witnesses, source counts, and fail-closed checks')


if __name__ == '__main__':
    main()
