"""
Phase 4 Beyond-Collatz Algebraic Toolkit
=====================================================================
Zero-float (`PC-5` strict AST-auditable: `int` and `fractions.Fraction` only;
zero `float`/`complex` literals, zero `/` division operators, zero floating-point
imports) implementation of the 7 Beyond-Collatz mathematical engines:

  1. NonAbelianMatrixMonoidEngine       (Transfer 1: `Mat_n(Z)` monoid lifts & cone monotonicity)
  2. RationalPutinarSOSSolver           (Transfer 2: Exact `Fraction` `LDL^T` Putinar SOS barriers)
  3. QuadraticPisotRingEngine           (Transfer 3: Exact `Q(sqrt d)` / `Z[phi]` Galois norm barriers)
  4. WreathBlockGaugeSynthesizer        (Transfer 4: `[7,4,3]` Hamming coset & width-`w` block scanner)
  5. SpaceTimePlaquetteCohomologyDecider(Transfer 5: 2D Stokes cohomology & sublattice cocycle decider)
  6. MolienAndWalkZetaClassifier        (Transfer 6: Exact Reynolds rank & `Fraction` Berlekamp-Massey)
  7. MultiPrimeAndKirchhoffAnalyzer     (Transfer 7: Multi-prime CRT sieves & exact `L_G^+` Kirchhoff)

Epistemic Guardrails (`[+1] / [0] / [-1]`):
  - `[+1]` Verified theorems and pure Lean 4 Core (`v4.16.0`) certificates.
  - `[0]`  Algebraic examples validated by exact zero-float computation.
  - `[-1]` Rice's theorem / Halting Problem undecidability: no engine is a universal BB(6) decider;
           finite Mod-`2^k` Kirchhoff resistances are strictly finite-quotient diagnostics.
"""

from __future__ import annotations

import ast
import math
from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Dict, Iterable, List, Optional, Sequence, Set, Tuple

# ---------------------------------------------------------------------------
# Zero-Float (`PC-5`) Exact Rational Helpers & AST Auditor
# ---------------------------------------------------------------------------


def fdiv(num: Fraction, den: Fraction) -> Fraction:
    """Exact `Fraction` division without using Python's `/` (`ast.Div`) operator."""
    if den == 0:
        raise ZeroDivisionError("Exact Fraction division by zero")
    return Fraction(num.numerator * den.denominator, num.denominator * den.numerator)


def fpow(base: Fraction, exp: int) -> Fraction:
    """Exact non-negative integer power of a `Fraction` without `**` float fallback."""
    if exp < 0:
        raise ValueError("Negative exponent disallowed without explicit fdiv")
    acc = Fraction(1, 1)
    b = Fraction(base)
    e = exp
    while e > 0:
        if e % 2 == 1:
            acc = acc * b
        b = b * b
        e = e // 2
    return acc


def audit_zero_float_ast(source_code: str, label: str = "<module>") -> Tuple[bool, List[str]]:
    """
    Strict `PC-5` AST auditor verifying zero floating-point constructs:
      - Zero `float` or `complex` literals (`ast.Constant`),
      - Zero `ast.Div` (`/`) operators anywhere in the AST,
      - Zero references to `float`, `complex`, `Decimal`, `numpy`, `scipy`, `cmath`.
    """
    tree = ast.parse(source_code, filename=label)
    violations: List[str] = []
    banned_names = {"float", "complex", "Decimal", "numpy", "scipy", "cmath"}
    allowed_math_attrs = {"gcd", "lcm", "isqrt", "comb", "factorial"}

    for node in ast.walk(tree):
        lineno = getattr(node, "lineno", 0)
        if isinstance(node, ast.Constant) and type(node.value).__name__ in banned_names:
            violations.append(f"{label}:{lineno}: floating constant {node.value!r}")
        elif isinstance(node, ast.Div):
            violations.append(f"{label}:{lineno}: `/` (ast.Div) operator forbidden under strict PC-5")
        elif isinstance(node, ast.Name) and node.id in banned_names:
            violations.append(f"{label}:{lineno}: banned identifier `{node.id}`")
        elif isinstance(node, ast.Import):
            for alias in node.names:
                root = alias.name.split(".")[0]
                if root in banned_names:
                    violations.append(f"{label}:{lineno}: banned import `{alias.name}`")
        elif isinstance(node, ast.ImportFrom):
            root = (node.module or "").split(".")[0]
            if root in banned_names:
                violations.append(f"{label}:{lineno}: banned from-import `{node.module}`")
        elif isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
            if node.value.id == "math" and node.attr not in allowed_math_attrs:
                violations.append(f"{label}:{lineno}: non-integer math attribute `math.{node.attr}`")

    return (len(violations) == 0, violations)


# ---------------------------------------------------------------------------
# Raw 6-State Turing Machine & 3-Cell Local Window NFA Utilities
# ---------------------------------------------------------------------------

TMTransition = Optional[Tuple[int, int, str]]
TMTable = Dict[Tuple[str, int], TMTransition]


def parse_tm(code: str) -> TMTable:
    """Parse standard TNF string like `1RB1RC_1LC0LE_0RA1RD_1RF1LB_1LD0LA_---0RC`."""
    blocks = code.strip().split("_")
    table: TMTable = {}
    for s_idx, blk in enumerate(blocks):
        st = chr(ord("A") + s_idx)
        for bit in (0, 1):
            tok = blk[3 * bit : 3 * bit + 3]
            if tok == "---":
                table[(st, bit)] = None
            else:
                w = int(tok[0])
                d = 1 if tok[1] == "R" else -1
                nst = tok[2]
                table[(st, bit)] = (w, d, nst)
    return table


def simulate_tm(
    table: TMTable,
    max_steps: int,
    init_tape: Optional[Dict[int, int]] = None,
    init_head: int = 0,
    init_state: str = "A",
) -> Tuple[Optional[int], Dict[int, int], int, str]:
    """Run raw TM for up to `max_steps`. Returns `(halt_step_or_None, tape, head, state)`."""
    tape: Dict[int, int] = {}
    if init_tape is not None:
        for k, v in init_tape.items():
            if v != 0:
                tape[k] = v
    head = init_head
    st = init_state
    for step in range(1, max_steps + 1):
        bit = tape.get(head, 0)
        act = table[(st, bit)]
        if act is None:
            return (step, tape, head, st)
        w, d, nst = act
        if w == 0:
            tape.pop(head, None)
        else:
            tape[head] = w
        head += d
        st = nst
    return (None, tape, head, st)


def analyze_3cell_local_nfa(table: TMTable) -> Dict[str, object]:
    """
    Explore the 48-state translation-invariant 3-cell local window NFA `(state, bl, bc, br)`
    from blank initial patch `('A', 0, 0, 0)`.
    """
    init_patch = ("A", 0, 0, 0)
    visited: Set[Tuple[str, int, int, int]] = {init_patch}
    parent: Dict[Tuple[str, int, int, int], Tuple[Tuple[str, int, int, int], int]] = {}
    queue: List[Tuple[str, int, int, int]] = [init_patch]
    halt_patches: List[Tuple[str, int, int, int]] = []
    q_idx = 0

    while q_idx < len(queue):
        cur = queue[q_idx]
        q_idx += 1
        st, bl, bc, br = cur
        act = table[(st, bc)]
        if act is None:
            halt_patches.append(cur)
            continue
        w, d, nst = act
        for wild in (0, 1):
            nxt = (nst, w, br, wild) if d == 1 else (nst, wild, bl, w)
            if nxt not in visited:
                visited.add(nxt)
                parent[nxt] = (cur, wild)
                queue.append(nxt)

    shortest_halt_path: List[Tuple[str, int, int, int]] = []
    if halt_patches:
        node = halt_patches[0]
        rev = [node]
        while node in parent:
            node, _ = parent[node]
            rev.append(node)
        shortest_halt_path = list(reversed(rev))

    return {
        "visited_count": len(visited),
        "halt_patches": halt_patches,
        "halt_reachable": len(halt_patches) > 0,
        "shortest_halt_path": shortest_halt_path,
    }


# ---------------------------------------------------------------------------
# Engine 1: Non-Abelian Matrix Monoid Engine (`Mat_n(Z)` Word Lifts)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class MatInt:
    """Exact immutable `n × n` matrix over `Z`."""

    rows: Tuple[Tuple[int, ...], ...]

    @staticmethod
    def identity(n: int) -> "MatInt":
        return MatInt(tuple(tuple(1 if i == j else 0 for j in range(n)) for i in range(n)))

    @property
    def dim(self) -> int:
        return len(self.rows)

    def __mul__(self, other: "MatInt") -> "MatInt":
        n = self.dim
        if other.dim != n:
            raise ValueError("Matrix dimension mismatch")
        return MatInt(
            tuple(
                tuple(sum(self.rows[i][k] * other.rows[k][j] for k in range(n)) for j in range(n))
                for i in range(n)
            )
        )

    def __sub__(self, other: "MatInt") -> "MatInt":
        n = self.dim
        return MatInt(
            tuple(tuple(self.rows[i][j] - other.rows[i][j] for j in range(n)) for i in range(n))
        )

    def commutator(self, other: "MatInt") -> "MatInt":
        return (self * other) - (other * self)

    def is_zero(self) -> bool:
        return all(v == 0 for row in self.rows for v in row)

    def is_upper_nonneg(self, strict_offdiag: bool = False) -> bool:
        n = self.dim
        for i in range(n):
            for j in range(n):
                val = self.rows[i][j]
                if i > j and val != 0:
                    return False
                if i <= j and val < 0:
                    return False
        if strict_offdiag and n >= 2:
            return self.rows[0][n - 1] > 0
        return True

    def eval_projective_affine(self, x: Fraction) -> Fraction:
        """For upper-triangular `2 × 2` `[a, b; 0, d]`, evaluate `(a*x + b) / d`."""
        if self.dim != 2:
            raise ValueError("Projective affine action requires 2x2 matrix")
        a, b = self.rows[0]
        _, d = self.rows[1]
        return fdiv(Fraction(a) * x + Fraction(b), Fraction(d))


class NonAbelianMatrixMonoidEngine:
    """Word homomorphism `mu : Sigma^* -> Mat_n(Z)` for variable-arity multi-defect TMs."""

    def __init__(self, generators: Dict[str, MatInt]) -> None:
        if not generators:
            raise ValueError("At least one generator required")
        dims = {m.dim for m in generators.values()}
        if len(dims) != 1:
            raise ValueError("All generators must share the same matrix dimension")
        self.dim = next(iter(dims))
        self.generators = dict(generators)

    def lift_word(self, word: Iterable[str]) -> MatInt:
        acc = MatInt.identity(self.dim)
        for sym in word:
            acc = acc * self.generators[sym]
        return acc

    def parikh_counts(self, word: Iterable[str]) -> Dict[str, int]:
        counts = {k: 0 for k in sorted(self.generators.keys())}
        for sym in word:
            counts[sym] = counts.get(sym, 0) + 1
        return counts

    def certify_rewrite_cone_step(
        self, lhs: Sequence[str], rhs: Sequence[str], strict_offdiag: bool = True
    ) -> bool:
        diff = self.lift_word(rhs) - self.lift_word(lhs)
        return diff.is_upper_nonneg(strict_offdiag=strict_offdiag)


# ---------------------------------------------------------------------------
# Engine 2: Exact Rational `LDL^T` Putinar SOS Barrier Solver (`Stage 3c`)
# ---------------------------------------------------------------------------

Poly2D = Dict[Tuple[int, int], Fraction]


def poly_clean(p: Poly2D) -> Poly2D:
    return {k: v for k, v in p.items() if v != 0}


def poly_add(p: Poly2D, q: Poly2D, scale_q: Fraction = Fraction(1)) -> Poly2D:
    out = dict(p)
    for m, coeff in q.items():
        out[m] = out.get(m, Fraction(0)) + scale_q * coeff
    return poly_clean(out)


def poly_mul(p: Poly2D, q: Poly2D) -> Poly2D:
    out: Poly2D = {}
    for (i1, j1), c1 in p.items():
        for (i2, j2), c2 in q.items():
            key = (i1 + i2, j1 + j2)
            out[key] = out.get(key, Fraction(0)) + c1 * c2
    return poly_clean(out)


def poly_eval(p: Poly2D, x: Fraction, y: Fraction) -> Fraction:
    total = Fraction(0)
    for (i, j), coeff in p.items():
        total = total + coeff * fpow(x, i) * fpow(y, j)
    return total


def poly_compose(p: Poly2D, tx: Poly2D, ty: Poly2D) -> Poly2D:
    """Exact polynomial composition `p(tx(x, y), ty(x, y))`."""
    total: Poly2D = {}
    for (i, j), coeff in p.items():
        term: Poly2D = {(0, 0): coeff}
        for _ in range(i):
            term = poly_mul(term, tx)
        for _ in range(j):
            term = poly_mul(term, ty)
        total = poly_add(total, term)
    return poly_clean(total)


def gram_to_poly(monomials: Sequence[Tuple[int, int]], gram: Sequence[Sequence[Fraction]]) -> Poly2D:
    """Expand `v(x, y)^T * Gram * v(x, y)` into an exact `Poly2D`."""
    m = len(monomials)
    out: Poly2D = {}
    for r in range(m):
        ir, jr = monomials[r]
        for c in range(m):
            ic, jc = monomials[c]
            key = (ir + ic, jr + jc)
            out[key] = out.get(key, Fraction(0)) + Fraction(gram[r][c])
    return poly_clean(out)


@dataclass(frozen=True)
class LDLTResult:
    is_psd: bool
    L: List[List[Fraction]]
    D: List[Fraction]
    cleared_scale: int


class RationalPutinarSOSSolver:
    """Exact Cholesky-free rational `LDL^T` Gram factorization and Putinar barrier auditor."""

    @staticmethod
    def exact_ldlt(gram_in: Sequence[Sequence[Fraction]]) -> LDLTResult:
        """
        Exact symmetric `LDL^T` factorization over `Fraction` (handles positive and zero pivots).
        Returns `is_psd = True` iff `gram == L * diag(D) * L^T` and every `D[k] >= 0`.
        """
        n = len(gram_in)
        A = [[Fraction(gram_in[i][j]) for j in range(n)] for i in range(n)]
        for i in range(n):
            for j in range(n):
                if A[i][j] != A[j][i]:
                    return LDLTResult(False, [], [], 1)

        L = [[Fraction(1 if i == j else 0) for j in range(n)] for i in range(n)]
        D = [Fraction(0) for _ in range(n)]

        for k in range(n):
            piv = A[k][k]
            if piv < 0:
                return LDLTResult(False, L, D, 1)
            if piv == 0:
                for i in range(k + 1, n):
                    if A[i][k] != 0:
                        return LDLTResult(False, L, D, 1)
                D[k] = Fraction(0)
            else:
                D[k] = piv
                for i in range(k + 1, n):
                    L[i][k] = fdiv(A[i][k], piv)
                for i in range(k + 1, n):
                    for j in range(k + 1, n):
                        A[i][j] = A[i][j] - L[i][k] * piv * L[j][k]

        # Exact algebraic reconstruction check `L * diag(D) * L^T == gram_in`
        for i in range(n):
            for j in range(n):
                recon = sum(L[i][k] * D[k] * L[j][k] for k in range(n))
                if recon != Fraction(gram_in[i][j]):
                    return LDLTResult(False, L, D, 1)

        lcm_scale = 1
        for k in range(n):
            lcm_scale = math.lcm(lcm_scale, D[k].denominator)
            for i in range(n):
                lcm_scale = math.lcm(lcm_scale, L[i][k].denominator)

        return LDLTResult(True, L, D, lcm_scale)

    @classmethod
    def verify_putinar_barrier(
        cls,
        barrier: Poly2D,
        init_pt: Tuple[int, int],
        step_x: Poly2D,
        step_y: Poly2D,
        guard_g: Poly2D,
        monomials_0: Sequence[Tuple[int, int]],
        gram_0: Sequence[Sequence[Fraction]],
        monomials_1: Sequence[Tuple[int, int]],
        gram_1: Sequence[Sequence[Fraction]],
        step_neg_monomials: Sequence[Tuple[int, int]],
        step_neg_gram: Sequence[Sequence[Fraction]],
    ) -> Dict[str, object]:
        """
        Certify Prajna-Jadbabaie + Putinar SOS barrier `B(x, y)` in zero floats:
          1. `B(x_0, y_0) < 0`,
          2. `-(B(T(x, y)) - B(x, y)) = w_step^T * Q_step * w_step` (`Q_step >= 0`),
          3. `B(x, y) = v_0^T * Q_0 * v_0 + g(x, y) * (v_1^T * Q_1 * v_1)` (`Q_0, Q_1 >= 0`).
        """
        init_val = poly_eval(barrier, Fraction(init_pt[0]), Fraction(init_pt[1]))
        init_ok = init_val < 0

        b_next = poly_compose(barrier, step_x, step_y)
        neg_delta = poly_add(barrier, b_next, scale_q=Fraction(-1))
        sos_step_poly = gram_to_poly(step_neg_monomials, step_neg_gram)
        ldlt_step = cls.exact_ldlt(step_neg_gram)
        step_ok = ldlt_step.is_psd and (neg_delta == sos_step_poly)

        sigma_0 = gram_to_poly(monomials_0, gram_0)
        sigma_1 = gram_to_poly(monomials_1, gram_1)
        putinar_rhs = poly_add(sigma_0, poly_mul(guard_g, sigma_1))
        ldlt_0 = cls.exact_ldlt(gram_0)
        ldlt_1 = cls.exact_ldlt(gram_1)
        putinar_ok = ldlt_0.is_psd and ldlt_1.is_psd and (poly_clean(barrier) == putinar_rhs)

        return {
            "certified": init_ok and step_ok and putinar_ok,
            "init_val": init_val,
            "ldlt_0": ldlt_0,
            "ldlt_1": ldlt_1,
            "ldlt_step": ldlt_step,
        }


# ---------------------------------------------------------------------------
# Engine 3: Irrational Quadratic / Pisot Ring Engine (`Q(sqrt d)`)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class QuadElem:
    """Exact element `a + b * sqrt(d)` in `Q(sqrt d)` (`d > 1` squarefree integer)."""

    a: Fraction
    b: Fraction
    d: int

    def _check(self, other: "QuadElem") -> None:
        if self.d != other.d:
            raise ValueError(f"Mismatched quadratic radicands {self.d} vs {other.d}")

    def __add__(self, other: "QuadElem") -> "QuadElem":
        self._check(other)
        return QuadElem(self.a + other.a, self.b + other.b, self.d)

    def __sub__(self, other: "QuadElem") -> "QuadElem":
        self._check(other)
        return QuadElem(self.a - other.a, self.b - other.b, self.d)

    def __mul__(self, other: "QuadElem") -> "QuadElem":
        self._check(other)
        return QuadElem(
            self.a * other.a + Fraction(self.d) * self.b * other.b,
            self.a * other.b + self.b * other.a,
            self.d,
        )

    def conj(self) -> "QuadElem":
        return QuadElem(self.a, -self.b, self.d)

    def norm(self) -> Fraction:
        """Exact Galois norm `N_{Q(sqrt d)/Q}(a + b sqrt(d)) = a^2 - d * b^2`."""
        return self.a * self.a - Fraction(self.d) * self.b * self.b

    def is_positive(self) -> bool:
        """Exact zero-float sign test for `a + b * sqrt(d) > 0` (`d > 0`)."""
        if self.a == 0 and self.b == 0:
            return False
        if self.a >= 0 and self.b >= 0:
            return True
        if self.a <= 0 and self.b <= 0:
            return False
        lhs = self.a * self.a
        rhs = Fraction(self.d) * self.b * self.b
        if self.a > 0 and self.b < 0:
            return lhs > rhs
        return rhs > lhs


class QuadraticPisotRingEngine:
    """Galois norm barriers & Pisano modular-sieve failure analyzer for Pisot TMs."""

    @staticmethod
    def phi() -> QuadElem:
        """Golden ratio `(1 + sqrt(5)) / 2` in `Q(sqrt 5)`."""
        return QuadElem(Fraction(1, 2), Fraction(1, 2), 5)

    @staticmethod
    def sqrt2_pisot() -> QuadElem:
        """Silver Pisot unit `1 + sqrt(2)` in `Q(sqrt 2)`."""
        return QuadElem(Fraction(1, 1), Fraction(1, 1), 2)

    @staticmethod
    def test_modular_sieves_fibonacci(max_modulus: int = 64) -> Dict[str, object]:
        """
        Test Stage-1 modular reachability on `(x, y) -> (x + y, x)` from `(3, 2)`
        against halting ray `G = {(2k, k) : k >= 2}` across all `M in 2..max_modulus`.
        """
        failed_moduli: List[int] = []
        for mod in range(2, max_modulus + 1):
            cur = (3 % mod, 2 % mod)
            vis = {cur}
            while True:
                nxt = ((cur[0] + cur[1]) % mod, cur[0])
                if nxt in vis:
                    break
                vis.add(nxt)
                cur = nxt
            guard_hit = any(((2 * k) % mod, k % mod) in vis for k in range(2, mod + 3))
            if guard_hit:
                failed_moduli.append(mod)
        return {
            "tested_count": max_modulus - 1,
            "failed_count": len(failed_moduli),
            "all_failed": len(failed_moduli) == (max_modulus - 1),
        }


# ---------------------------------------------------------------------------
# Engine 4: Wreath-Product Block-Coding & `[7,4,3]` Hamming Gauge Synthesizer
# ---------------------------------------------------------------------------


class WreathBlockGaugeSynthesizer:
    """`[7,4,3]` Fano Hamming gauge verifier & automated macro-block width scanner."""

    CANONICAL_FANO_LINES: Tuple[Tuple[int, int, int], ...] = (
        (1, 2, 3),
        (1, 4, 5),
        (1, 6, 7),
        (2, 4, 6),
        (2, 5, 7),
        (3, 4, 7),
        (3, 5, 6),
    )

    @classmethod
    def verify_fano_hamming743_coset(cls) -> Dict[str, object]:
        codewords: List[int] = []
        weight_dist: Dict[int, int] = {0: 0, 3: 0, 4: 0, 7: 0}
        for m in range(128):
            bits = [(m >> i) & 1 for i in range(7)]
            s0 = (bits[3] + bits[4] + bits[5] + bits[6]) % 2
            s1 = (bits[1] + bits[2] + bits[5] + bits[6]) % 2
            s2 = (bits[0] + bits[2] + bits[4] + bits[6]) % 2
            if s0 == 0 and s1 == 0 and s2 == 0:
                codewords.append(m)
                wt = sum(bits)
                weight_dist[wt] = weight_dist.get(wt, 0) + 1
        anchor_coset = sorted(8 ^ c for c in codewords)
        return {
            "codeword_count": len(codewords),
            "weight_dist": weight_dist,
            "anchor_coset": anchor_coset,
        }

    @staticmethod
    def scan_block_widths(
        tm_code: str, widths: Sequence[int] = (1, 2, 3, 4, 5, 6), steps: int = 15000
    ) -> Dict[int, Fraction]:
        """
        Collect extremal left-head `<A:0>` return words on a raw TM and compute
        the minimal coboundary block-transition defect density across widths `w`.
        """
        table = parse_tm(tm_code)
        tape: Dict[int, int] = {}
        head = 0
        st = "A"
        lo = 0
        hi = 0
        snapshots: List[str] = []

        for _ in range(1, steps + 1):
            act = table[(st, tape.get(head, 0))]
            if act is None:
                break
            wbit, d, st = act
            if wbit == 0:
                tape.pop(head, None)
            else:
                tape[head] = wbit
            head += d
            if head > hi:
                hi = head
            if head < lo:
                lo = head
                if st == "A":
                    word = "".join(str(tape.get(p, 0)) for p in range(head + 1, hi + 1)).rstrip("0")
                    if len(word) >= 18:
                        snapshots.append(word)

        defect_rates: Dict[int, Fraction] = {}
        for w in widths:
            tot_defects = 0
            tot_adj = 0
            for word in snapshots:
                best_tr: Optional[int] = None
                best_adj = 1
                for offset in range(w):
                    rem = word[offset:]
                    n_blk = len(rem) // w
                    if n_blk < 2:
                        continue
                    blocks = [rem[i * w : (i + 1) * w] for i in range(n_blk)]
                    defects = sum(1 for i in range(n_blk - 1) if blocks[i] != blocks[i + 1])
                    if best_tr is None or defects < best_tr:
                        best_tr = defects
                        best_adj = n_blk - 1
                if best_tr is not None:
                    tot_defects += best_tr
                    tot_adj += best_adj
            defect_rates[w] = Fraction(tot_defects, tot_adj) if tot_adj > 0 else Fraction(1, 1)

        return defect_rates


# ---------------------------------------------------------------------------
# Engine 5: 2D Space-Time Plaquette Cohomology & Sublattice Decider
# ---------------------------------------------------------------------------


class SpaceTimePlaquetteCohomologyDecider:
    """Verifies 2D Discrete Stokes' Theorem & decides `Z/2Z` space-time sublattice cocycles."""

    @staticmethod
    def verify_stokes_on_grid(
        jx: Sequence[Sequence[int]], jt: Sequence[Sequence[int]]
    ) -> Tuple[bool, int, int]:
        """
        Verify `sum_{t=0..T-1} sum_{x=0..W-1} curl(x, t) == bottom + right - top - left`
        for horizontal 1-cochain `jx[t][x]` (`(T+1) x W`) and vertical `jt[t][x]` (`T x (W+1)`).
        """
        t_len = len(jt)
        w_len = len(jx[0])
        bulk = 0
        for t in range(t_len):
            for x in range(w_len):
                curl = jx[t][x] + jt[t][x + 1] - jx[t + 1][x] - jt[t][x]
                bulk += curl
        bottom = sum(jx[0][x] for x in range(w_len))
        top = sum(jx[t_len][x] for x in range(w_len))
        right = sum(jt[t][w_len] for t in range(t_len))
        left = sum(jt[t][0] for t in range(t_len))
        bdry = bottom + right - top - left
        return (bulk == bdry, bulk, bdry)

    @staticmethod
    def decide_bipartite_sublattice_nonhalting(tm_code: str) -> Dict[str, object]:
        """
        Check whether a 6-state TM admits an exact `Z/2Z` space-time sublattice zero-occupation
        1-cocycle invariant from blank `('A', head=0)` that globally blocks all `---` transitions.
        """
        table = parse_tm(tm_code)
        states = sorted({st for (st, _) in table.keys()})
        parity: Dict[str, int] = {"A": 0}
        bipartite = True

        changed = True
        while changed and bipartite:
            changed = False
            for st in list(parity.keys()):
                p_st = parity[st]
                allowed_bits = (0, 1) if p_st == 0 else (0,)
                for bit in allowed_bits:
                    act = table[(st, bit)]
                    if act is None:
                        return {"certified_nonhalting": False, "reason": f"Halt ({st},{bit}) active"}
                    w, _, nst = act
                    if p_st == 1 and w != 0:
                        return {
                            "certified_nonhalting": False,
                            "reason": f"Odd-cell state {st} writes 1",
                        }
                    req_p = 1 - p_st
                    if nst in parity:
                        if parity[nst] != req_p:
                            bipartite = False
                            break
                    else:
                        parity[nst] = req_p
                        changed = True

        if not bipartite:
            return {"certified_nonhalting": False, "reason": "State graph not bipartite"}

        even_states = sorted(s for s, p in parity.items() if p == 0)
        odd_states = sorted(s for s, p in parity.items() if p == 1)
        return {
            "certified_nonhalting": True,
            "even_states": even_states,
            "odd_states": odd_states,
            "active_states_in_cocycle": len(parity),
            "total_states": len(states),
        }


# ---------------------------------------------------------------------------
# Engine 6: Exact Molien / Reynolds Degree Predictor & Rational Walk Series
# ---------------------------------------------------------------------------


def exact_matrix_rank(mat: Sequence[Sequence[Fraction]]) -> int:
    """Exact rank over `Q` (`Fraction`) via Gauss-Jordan elimination."""
    if not mat or not mat[0]:
        return 0
    rows = len(mat)
    cols = len(mat[0])
    A = [[Fraction(mat[r][c]) for c in range(cols)] for r in range(rows)]
    rank = 0
    for col in range(cols):
        piv = None
        for r in range(rank, rows):
            if A[r][col] != 0:
                piv = r
                break
        if piv is None:
            continue
        A[rank], A[piv] = A[piv], A[rank]
        sc = A[rank][col]
        A[rank] = [fdiv(v, sc) for v in A[rank]]
        for r in range(rows):
            if r != rank and A[r][col] != 0:
                fac = A[r][col]
                A[r] = [A[r][c] - fac * A[rank][c] for c in range(cols)]
        rank += 1
    return rank


class MolienAndWalkZetaClassifier:
    """Exact Reynolds invariant-dimension calculator & `Fraction` Berlekamp-Massey."""

    @staticmethod
    def invariant_dims_2d(
        group_mats_2x2: Sequence[Tuple[Tuple[int, int], Tuple[int, int]]], max_deg: int = 4
    ) -> Dict[int, int]:
        """
        Compute exact dimension `dim Q[x, y]_d^G` for each homogeneous degree `d = 1..max_deg`
        via the Reynolds projector `R_G = (1/|G|) sum_{g in G} rho_d(g)`.
        """
        g_order = len(group_mats_2x2)
        dims: Dict[int, int] = {0: 1}
        for deg in range(1, max_deg + 1):
            monoms = [(deg - j, j) for j in range(deg + 1)]
            idx_of = {m: idx for idx, m in enumerate(monoms)}
            m_cnt = len(monoms)
            reynolds = [[Fraction(0) for _ in range(m_cnt)] for _ in range(m_cnt)]

            for ((g00, g01), (g10, g11)) in group_mats_2x2:
                tx: Poly2D = {(1, 0): Fraction(g00), (0, 1): Fraction(g01)}
                ty: Poly2D = {(1, 0): Fraction(g10), (0, 1): Fraction(g11)}
                for col_idx, (i_exp, j_exp) in enumerate(monoms):
                    img = poly_compose({(i_exp, j_exp): Fraction(1)}, tx, ty)
                    for m_out, coeff in img.items():
                        row_idx = idx_of[m_out]
                        reynolds[row_idx][col_idx] = reynolds[row_idx][col_idx] + fdiv(
                            coeff, Fraction(g_order)
                        )
            dims[deg] = exact_matrix_rank(reynolds)
        return dims

    @staticmethod
    def berlekamp_massey_exact(seq: Sequence[int]) -> Tuple[List[Fraction], List[Fraction]]:
        """
        Exact zero-float Berlekamp-Massey over `Fraction`.
        Returns `(P_coeffs, Q_coeffs)` with `Q_coeffs[0] == 1` such that
        `sum_{i=0..L} Q[i] * seq[n - i] == 0` for all `n >= L` and `P(t) = (Q(t) * S(t)) mod t^(L+1)`.
        """
        s = [Fraction(v) for v in seq]
        C: List[Fraction] = [Fraction(1)]
        B: List[Fraction] = [Fraction(1)]
        L = 0
        m = 1
        b = Fraction(1)

        for n in range(len(s)):
            d = s[n]
            for i in range(1, L + 1):
                d = d + C[i] * s[n - i]
            if d == 0:
                m += 1
            elif 2 * L <= n:
                T = list(C)
                factor = fdiv(d, b)
                need = len(B) + m
                if len(C) < need:
                    C.extend([Fraction(0)] * (need - len(C)))
                for i in range(len(B)):
                    C[i + m] = C[i + m] - factor * B[i]
                L = n + 1 - L
                B = T
                b = d
                m = 1
            else:
                factor = fdiv(d, b)
                need = len(B) + m
                if len(C) < need:
                    C.extend([Fraction(0)] * (need - len(C)))
                for i in range(len(B)):
                    C[i + m] = C[i + m] - factor * B[i]
                m += 1

        while len(C) > 1 and C[-1] == 0:
            C.pop()

        deg_q = len(C) - 1
        P: List[Fraction] = []
        for k in range(deg_q):
            acc = Fraction(0)
            for j in range(min(k + 1, len(C))):
                acc = acc + C[j] * s[k - j]
            P.append(acc)
        while len(P) > 1 and P[-1] == 0:
            P.pop()
        return (P, C)

    @staticmethod
    def classify_denominator(q_coeffs: Sequence[Fraction]) -> str:
        """Classify a normalized walk denominator `Q(t)` (`Q[0] == 1`) into BB(6) regimes."""
        q = list(q_coeffs)
        if q == [Fraction(1), Fraction(-3), Fraction(3), Fraction(-1)]:
            return "PARABOLIC_POLYNOMIAL_BOUNCER"
        if q == [Fraction(1), Fraction(-1), Fraction(-1)]:
            return "PISOT_IRRATIONAL_SUBSTITUTIVE"
        if q == [Fraction(1), Fraction(-4), Fraction(5), Fraction(-2)]:
            return "MIXED_COLLATZ_PORTAL"
        if len(q) >= 4:
            p = len(q) - 2
            expected_cd = [Fraction(0)] * (p + 2)
            expected_cd[0] = Fraction(1)
            expected_cd[1] = Fraction(-1)
            expected_cd[p] = expected_cd[p] + Fraction(-1)
            expected_cd[p + 1] = Fraction(1)
            if q == expected_cd:
                return f"CYCLOTOMIC_TRANSLATED_CYCLER(period={p})"
        if len(q) >= 3 and len(q) % 2 == 1:
            p = (len(q) - 1) // 2
            expected = [Fraction(0)] * (2 * p + 1)
            expected[0] = Fraction(1)
            expected[p] = Fraction(-2)
            expected[2 * p] = Fraction(1)
            if q == expected:
                return f"CYCLOTOMIC_TRANSLATED_CYCLER(period={p})"
        return "GENERAL_RATIONAL_WALK"


# ---------------------------------------------------------------------------
# Engine 7: Multi-Prime CRT Sieve & Exact Rational Kirchhoff Escape Resistance
# ---------------------------------------------------------------------------


def exact_gauss_jordan_solve(
    A_in: Sequence[Sequence[Fraction]], B_in: Sequence[Sequence[Fraction]]
) -> List[List[Fraction]]:
    """Exact zero-float Gauss-Jordan solver for `A * X = B` over `Fraction`."""
    n = len(A_in)
    m = len(B_in[0])
    aug = [
        [Fraction(A_in[i][j]) for j in range(n)] + [Fraction(B_in[i][k]) for k in range(m)]
        for i in range(n)
    ]
    for col in range(n):
        piv = None
        for r in range(col, n):
            if aug[r][col] != 0:
                piv = r
                break
        if piv is None:
            raise ValueError("Singular matrix in exact_gauss_jordan_solve")
        aug[col], aug[piv] = aug[piv], aug[col]
        sc = aug[col][col]
        aug[col] = [fdiv(v, sc) for v in aug[col]]
        for r in range(n):
            if r != col and aug[r][col] != 0:
                fac = aug[r][col]
                aug[r] = [aug[r][c] - fac * aug[col][c] for c in range(n + m)]
    return [row[n:] for row in aug]


class MultiPrimeAndKirchhoffAnalyzer:
    """Multi-prime CRT portal obstruction & exact `L_G^+` Moore-Penrose pseudoinverse."""

    @staticmethod
    def verify_multiprime_portal(
        portal_fn_mod: Callable[[int, int], int],
        target_residue: int,
        composite_mod: int,
        period_len: int,
        prime_powers: Sequence[int],
        j_min: int = 1,
        search_limit: int = 200,
    ) -> Dict[str, object]:
        single_prime_witnesses: Dict[int, Optional[int]] = {}
        for q in prime_powers:
            wit: Optional[int] = None
            for j in range(j_min, j_min + search_limit):
                if portal_fn_mod(j, q) == (target_residue % q):
                    wit = j
                    break
            single_prime_witnesses[q] = wit

        composite_hits = [
            j
            for j in range(j_min, j_min + period_len)
            if portal_fn_mod(j, composite_mod) == (target_residue % composite_mod)
        ]
        return {
            "all_single_primes_fail": all(v is not None for v in single_prime_witnesses.values()),
            "single_prime_witnesses": single_prime_witnesses,
            "composite_eliminated": len(composite_hits) == 0,
        }

    @staticmethod
    def laplacian_pseudoinverse_exact(L_in: Sequence[Sequence[int]]) -> Dict[str, object]:
        n = len(L_in)
        inv_n = Fraction(1, n)
        M = [[Fraction(L_in[i][j]) + inv_n for j in range(n)] for i in range(n)]
        I_n = [[Fraction(1 if i == j else 0) for j in range(n)] for i in range(n)]
        M_inv = exact_gauss_jordan_solve(M, I_n)
        L_plus = [[M_inv[i][j] - inv_n for j in range(n)] for i in range(n)]

        projector_ok = True
        for i in range(n):
            for j in range(n):
                prod_ij = sum(Fraction(L_in[i][k]) * L_plus[k][j] for k in range(n))
                expected = (Fraction(1) if i == j else Fraction(0)) - inv_n
                if prod_ij != expected or L_plus[i][j] != L_plus[j][i]:
                    projector_ok = False
                    break

        lcm_den = 1
        for row in L_plus:
            for val in row:
                lcm_den = math.lcm(lcm_den, val.denominator)

        cleared = [[int(val * lcm_den) for val in row] for row in L_plus]
        return {
            "L_plus": L_plus,
            "projector_ok": projector_ok,
            "lcm_den": lcm_den,
            "cleared_matrix": cleared,
        }

    @staticmethod
    def effective_resistance(L_plus: Sequence[Sequence[Fraction]], s: int, t: int) -> Fraction:
        return L_plus[s][s] + L_plus[t][t] - Fraction(2) * L_plus[s][t]

    @classmethod
    def antihydra_mod_2k_kirchhoff(cls, k: int) -> Dict[str, object]:
        """
        Build the symmetrized finite Mod-`2^k` quotient Laplacian of Antihydra's base map
        (`a -> (3a + 2)//2` even, `(3a + 1)//2` odd) and compute exact `R_eff(3 <-> 7)`.
        (`[-1]` Fenced strictly to the finite Mod-`2^k` quotient graph.)
        """
        mod = 1 << k
        L = [[0 for _ in range(mod)] for _ in range(mod)]
        for r in range(mod):
            for lift in (r, r + mod):
                nxt = ((3 * lift + 2) // 2 if lift % 2 == 0 else (3 * lift + 1) // 2) % mod
                if nxt != r:
                    L[r][r] += 1
                    L[nxt][nxt] += 1
                    L[r][nxt] -= 1
                    L[nxt][r] -= 1
        pinv = cls.laplacian_pseudoinverse_exact(L)
        r37 = cls.effective_resistance(pinv["L_plus"], 3 % mod, 7 % mod)
        return {
            "modulus": mod,
            "L": L,
            "projector_ok": pinv["projector_ok"],
            "lcm_den": pinv["lcm_den"],
            "cleared_matrix": pinv["cleared_matrix"],
            "r_eff_3_7": r37,
        }
