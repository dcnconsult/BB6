/-
  CryptidSolvePhase4.Transfer6MolienAndWalkSeries
  ===============================================
  Transfer 6:
  Molien / Reynolds Symmetry Degree Predictors for Barrier Synthesis and Rational
  Generating-Series Annihilators for Example Sequences. These do not classify all BB(6) dynamics.

  Formalizes in pure Lean 4 Core (`Init` + `omega` + `decide`):
    1. Reynolds / Molien degree routing:
       - Order-two coordinate swap `(x, y) ↦ (y, x)` admits degree-1 invariants (`d_min = 1` -> Stage 3a/3b),
       - Signed central inversion `(x, y) ↦ (-x, -y)` kills ALL degree-1 forms (`dim Inv_1 = 0`)
         while preserving the full 3D space `{x^2, xy, y^2}` (`d_min = 2` -> Stage 3c SOS),
       - Dihedral `D_4` sign-and-swap action kills all linear forms and leaves `x^2 + y^2` invariant.
    2. Exact shift-polynomial `Q(S)` annihilation laws (`RO-1` rational walk `P(t)/Q(t)`):
       - Cyclotomic translated cycler (annihilator `(1 - t^3)^2`, not necessarily minimal),
       - Parabolic bouncers `AppC_7` (`16b^2 + 28b + 15`) & `AppC_8` (`108q^2 + 332q + 238`)
         (`Q(t) = (1 - t)^3`, minimal since `Δ^2 = 32 ≠ 0` and `Δ^2 = 216 ≠ 0`),
       - Pisot substitutive Fibonacci counter (`Q(t) = 1 - t - t^2`),
       - Mixed exponential-linear Collatz portal `A.5 / BMO 5` (`5 * 2^j - j - 6`)
         (`Q(t) = (1 - 2t)(1 - t)^2 = 1 - 4t + 5t^2 - 2t^3`, minimal since `(1 - 2S)(1 - S) = +1`).
-/

import CryptidSolvePhase4.Basic

namespace CryptidSolvePhase4

/-! ## 1. Reynolds / Molien Symmetry Degree Predictors -/

/-- `2 * R_{swap}(a*x + b*y) = (a + b) * (x + y)`: degree-1 invariant survives iff `a + b ≠ 0`. -/
theorem reynolds_pin2_swap_linear (a b x y : Int) :
    (a * x + b * y) + (a * y + b * x) = (a + b) * (x + y) := by
  have hL : (a + b) * (x + y) = (a + b) * x + (a + b) * y := Int.mul_add (a + b) x y
  have h1 : (a + b) * x = a * x + b * x := Int.add_mul a b x
  have h2 : (a + b) * y = a * y + b * y := Int.add_mul a b y
  omega

/-- **Molien `t^1 = 0` Obstruction under Central Inversion `(x, y) ↦ (-x, -y)`**:
    In Molien series `M(t) = (1 + t^2) / (1 - t^2)^2 = 1 + 0*t + 3*t^2 + ...`, EVERY linear form
    averages to identically zero, proving Stage 3a/3b degree-1 invariants vanish under sign flip. -/
theorem reynolds_inversion_kills_all_linear (a b x y : Int) :
    (a * x + b * y) + (a * (-x) + b * (-y)) = 0 := by
  rw [Int.mul_neg, Int.mul_neg]
  omega

/-- **Molien `3 * t^2` Basis Preservation under Central Inversion**:
    Every homogeneous quadratic form `c20*x^2 + c11*x*y + c02*y^2` is strictly invariant under
    `(x, y) ↦ (-x, -y)`, within the symmetry-restricted invariant search; no general affine-barrier obstruction follows. -/
theorem reynolds_inversion_preserves_quadratic (c20 c11 c02 x y : Int) :
    c20 * (-x) * (-x) + c11 * (-x) * (-y) + c02 * (-y) * (-y) =
      c20 * x * x + c11 * x * y + c02 * y * y := by
  have hxx : (-x) * (-x) = x * x := by simp [Int.neg_mul_neg]
  have hxy : (-x) * (-y) = x * y := by simp [Int.neg_mul_neg]
  have hyy : (-y) * (-y) = y * y := by simp [Int.neg_mul_neg]
  rw [Int.mul_assoc c20 (-x) (-x), Int.mul_assoc c11 (-x) (-y), Int.mul_assoc c02 (-y) (-y)]
  rw [hxx, hxy, hyy]
  rw [← Int.mul_assoc c20 x x, ← Int.mul_assoc c11 x y, ← Int.mul_assoc c02 y y]

/-- **Dihedral `D_4` (`M(t) = 1 / ((1 - t^2)(1 - t^4))`) Degree Routing**:
    Summing a linear form across `(±x, ±y)` and `(±y, ±x)` gives `0`, whereas `x^2 + y^2` is
    fixed by both coordinate sign flips and swap (`dim Inv_1 = 0, dim Inv_2 = 1`). -/
theorem reynolds_d4_degree2_routing (a b x y : Int) :
    (a * x + b * y) + (a * (-x) + b * y) + (a * x + b * (-y)) + (a * (-x) + b * (-y)) = 0 ∧
      ((-y) * (-y) + x * x = x * x + y * y) := by
  have hyy : (-y) * (-y) = y * y := by simp [Int.neg_mul_neg]
  exact ⟨by rw [Int.mul_neg, Int.mul_neg]; omega, by rw [hyy]; omega⟩

/-! ## 2. Rational Walk Generating-Series Denominators `Q(t)` (`RO-1`) -/

/-- **Regime I (`Q(t) = (1 - t^3)^2`): Cyclotomic Translated Cycler**:
    Any sequence satisfying `u(n + 3) = u(n) + d` (`d ≠ 0`) is annihilated by `(S^3 - 1)^2`
    (`u(n + 6) - 2*u(n + 3) + u(n) = 0`), while `(S^3 - 1) u(n) = d ≠ 0`. -/
theorem walk_denom_translated_cycler_period3
    (u : Nat → Int) (d : Int) (hd : d ≠ 0)
    (hShift : ∀ n : Nat, u (n + 3) = u n + d) (n : Nat) :
    u (n + 6) - 2 * u (n + 3) + u n = 0 ∧ u (n + 3) - u n ≠ 0 := by
  have h1 := hShift n
  have h2 := hShift (n + 3)
  have hEq : n + 3 + 3 = n + 6 := by omega
  rw [hEq] at h2
  exact ⟨by omega, by omega⟩

/-- `AppC_7` quadratic sweep duration `T(b) = 16b^2 + 28b + 15` over `Int`. -/
def walkAppC7Gate (b : Int) : Int := 16 * b * b + 28 * b + 15

/-- `AppC_8` width-3 clean macro duration `S(q) = 108q^2 + 332q + 238` over `Int`. -/
def walkAppC8Macro (q : Int) : Int := 108 * q * q + 332 * q + 238

/-- General quadratic polynomial finite-difference lemma:
    For `P(z) = A*z^2 + B*z + C`, `Δ^2 P(z) = 2*A` and `Δ^3 P(z) = 0`! -/
theorem quadratic_walk_denom_cube (A B C z : Int) :
    let P := fun w : Int => A * w * w + B * w + C
    P (z + 2) - 2 * P (z + 1) + P z = 2 * A ∧
      P (z + 3) - 3 * P (z + 2) + 3 * P (z + 1) - P z = 0 := by
  dsimp only
  have expandSq : ∀ k : Int, (z + k) * (z + k) = z * z + 2 * (k * z) + k * k := by
    intro k
    calc
      (z + k) * (z + k) = (z + k) * z + (z + k) * k := Int.mul_add (z + k) z k
      _ = (z * z + k * z) + (z * k + k * k) := by rw [Int.add_mul, Int.add_mul]
      _ = z * z + 2 * (k * z) + k * k := by
            have hkz : z * k = k * z := Int.mul_comm z k
            omega
  have h1 : A * (z + 1) * (z + 1) = A * (z * z) + 2 * (A * z) + A := by
    rw [Int.mul_assoc A (z + 1) (z + 1), expandSq 1]
    simp [Int.mul_add]
    have hAz : A * (2 * z) = 2 * (A * z) := by
      rw [← Int.mul_assoc A 2 z, Int.mul_comm A 2, Int.mul_assoc 2 A z]
    omega
  have h2 : A * (z + 2) * (z + 2) = A * (z * z) + 4 * (A * z) + 4 * A := by
    rw [Int.mul_assoc A (z + 2) (z + 2), expandSq 2]
    have h22 : (2 : Int) * (2 * z) = 4 * z := by
      rw [← Int.mul_assoc 2 2 z]; rfl
    have h2sq : (2 : Int) * 2 = 4 := rfl
    rw [h22, h2sq]
    simp [Int.mul_add]
    have hAz : A * (4 * z) = 4 * (A * z) := by
      rw [← Int.mul_assoc A 4 z, Int.mul_comm A 4, Int.mul_assoc 4 A z]
    have hA4 : A * 4 = 4 * A := Int.mul_comm A 4
    omega
  have h3 : A * (z + 3) * (z + 3) = A * (z * z) + 6 * (A * z) + 9 * A := by
    rw [Int.mul_assoc A (z + 3) (z + 3), expandSq 3]
    have h23 : (2 : Int) * (3 * z) = 6 * z := by
      rw [← Int.mul_assoc 2 3 z]; rfl
    have h3sq : (3 : Int) * 3 = 9 := rfl
    rw [h23, h3sq]
    simp [Int.mul_add]
    have hAz : A * (6 * z) = 6 * (A * z) := by
      rw [← Int.mul_assoc A 6 z, Int.mul_comm A 6, Int.mul_assoc 6 A z]
    have hA9 : A * 9 = 9 * A := Int.mul_comm A 9
    omega
  have h0 : A * z * z = A * (z * z) := Int.mul_assoc A z z
  rw [h0, h1, h2, h3]
  simp [Int.mul_add]
  exact ⟨by omega, by omega⟩

/-- **Regime II (`Q(t) = (1 - t)^3`): Parabolic Bouncer / Quadratic Sweep Denominator**:
    Both `AppC_7`'s halting-gate duration `16b^2 + 28b + 15` (`Δ^2 = 32`) and `AppC_8`'s
    clean width-3 macro duration `108q^2 + 332q + 238` (`Δ^2 = 216`) have minimal rational
    walk denominator `Q(t) = (1 - t)^3 = 1 - 3t + 3t^2 - t^3`. -/
theorem walk_denom_parabolic_appC7_and_appC8 (n : Int) :
    (walkAppC7Gate (n + 2) - 2 * walkAppC7Gate (n + 1) + walkAppC7Gate n = 32 ∧
      walkAppC7Gate (n + 3) - 3 * walkAppC7Gate (n + 2) + 3 * walkAppC7Gate (n + 1) -
        walkAppC7Gate n = 0) ∧
    (walkAppC8Macro (n + 2) - 2 * walkAppC8Macro (n + 1) + walkAppC8Macro n = 216 ∧
      walkAppC8Macro (n + 3) - 3 * walkAppC8Macro (n + 2) + 3 * walkAppC8Macro (n + 1) -
        walkAppC8Macro n = 0) := by
  unfold walkAppC7Gate walkAppC8Macro
  exact ⟨quadratic_walk_denom_cube 16 28 15 n, quadratic_walk_denom_cube 108 332 238 n⟩

/-- **Regime III (`Q(t) = 1 - t - t^2`): Pisot Substitutive Walk Denominator**:
    The Fibonacci counter sequence `2, 3, 5, 8, 13, ...` satisfies `F(n+2) - F(n+1) - F(n) = 0`,
    and NO integer geometric operator `S - r` (`r ∈ Z`) annihilates even the first two steps! -/
def fibCounterSeq : Nat → Int
  | 0 => 2
  | 1 => 3
  | n + 2 => fibCounterSeq (n + 1) + fibCounterSeq n

theorem walk_denom_pisot_fibonacci (n : Nat) :
    fibCounterSeq (n + 2) - fibCounterSeq (n + 1) - fibCounterSeq n = 0 ∧
      (∀ r : Int, ¬ (fibCounterSeq 1 = r * fibCounterSeq 0 ∧ fibCounterSeq 2 = r * fibCounterSeq 1)) := by
  constructor
  · simp [fibCounterSeq]; omega
  · intro r hr
    simp [fibCounterSeq] at hr
    omega

/-- **Regime IV (`Q(t) = (1 - 2t)(1 - t)^2 = 1 - 4t + 5t^2 - 2t^3`): Mixed Portal Sequence**:
    `A.5 / BMO 5`'s exact halting-portal sequence `N(j) = 5 * 2^j - j - 6` is annihilated by
    `S^3 - 4*S^2 + 5*S - 2`, while `(S - 2)(S - 1) N(j) = +1 ≠ 0` proves minimality. -/
def walkPortalA5 (j : Nat) : Int :=
  5 * (Int.ofNat (2 ^ j)) - (j : Int) - 6

theorem walk_denom_mixed_portal_a5_bmo5 (j : Nat) :
    walkPortalA5 (j + 2) - 3 * walkPortalA5 (j + 1) + 2 * walkPortalA5 j = 1 ∧
      walkPortalA5 (j + 3) - 4 * walkPortalA5 (j + 2) + 5 * walkPortalA5 (j + 1) -
        2 * walkPortalA5 j = 0 := by
  unfold walkPortalA5
  have hp1 : (2 ^ (j + 1) : Nat) = 2 * (2 ^ j) := by rw [Nat.pow_succ]; omega
  have hp2 : (2 ^ (j + 2) : Nat) = 4 * (2 ^ j) := by
    rw [show j + 2 = (j + 1) + 1 by omega, Nat.pow_succ, hp1]; omega
  have hp3 : (2 ^ (j + 3) : Nat) = 8 * (2 ^ j) := by
    rw [show j + 3 = (j + 2) + 1 by omega, Nat.pow_succ, hp2]; omega
  rw [hp1, hp2, hp3]
  simp [Int.ofNat_mul]
  omega

end CryptidSolvePhase4
