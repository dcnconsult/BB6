/-
  CryptidSolvePhase4.Transfer7MultiPrimeKirchhoff
  ===============================================
  Transfer 7:
  Multi-Prime CRT Local-Global Portal Eliminations (Where Every Constituent Prime-Power Fails)
  and Exact Zero-Float Integer-Cleared Kirchhoff Escape Resistance on Antihydra Mod-8.

  Formalizes in pure Lean 4 Core (`Init` + `omega` + `decide`):
    1. Multiplicative order periodicity lemmas `pow2_mod3_cycle`, `pow2_mod7_cycle`, `pow3_mod7_cycle`.
    2. Three Multi-Prime Local-Global Portal Elimination Theorems + explicit single-prime-power
       failure witnesses:
       - `{2, 3}` CRT (`ord_3(2) = 2`): `(2^j + 3*j) % 6 ≠ 1` (`j ≥ 1`), whereas `2^3 = 8` fails
         at `j = 3` and `3^2 = 9` fails at `j = 4`.
       - `{3, 7}` CRT (`ord_7(2) = 3`): `(2^j + 7*j) % 21 ≠ 15` (`∀ j`), whereas `3^2 = 9` fails
         at `j = 7` and `7^2 = 49` fails at `j = 12`.
       - `{3, 7}` Dual-Exponential (`2^j + 3^j`): `(2^j + 3^j) % 21 ≠ 7` (`j ≥ 1`), whereas
         `3^2 = 9` fails at `j = 4` and `7^2 = 49` fails at `j = 9`.
    3. Pure-kernel `decide` verification of Antihydra's Mod-8 symmetrized quotient Laplacian `L`
       and exact integer-cleared Moore-Penrose pseudoinverse `48 * L^+` (`L * (48 * L^+) = 48 * I_8 - 6 * J_8`),
       certifying exact Kirchhoff effective resistance `R_eff(3 <-> 7) = 29 / 48` (fenced strictly
       as a finite Mod-8 quotient graph metric per `[-1]` computability guardrails).
-/

import CryptidSolvePhase4.Basic

namespace CryptidSolvePhase4

/-! ## 1. Multiplicative Order Cycles Modulo `3` and `7` -/

theorem pow2_mod3_cycle (j : Nat) :
    (j % 2 = 0 → (2 ^ j) % 3 = 1) ∧ (j % 2 = 1 → (2 ^ j) % 3 = 2) := by
  induction j with
  | zero => omega
  | succ n ih =>
      have hp : 2 ^ (n + 1) = 2 * (2 ^ n) := by rw [Nat.pow_succ]; omega
      rw [hp]
      omega

theorem pow2_mod7_cycle (j : Nat) :
    (j % 3 = 0 → (2 ^ j) % 7 = 1) ∧
      (j % 3 = 1 → (2 ^ j) % 7 = 2) ∧
      (j % 3 = 2 → (2 ^ j) % 7 = 4) := by
  induction j with
  | zero => omega
  | succ n ih =>
      have hp : 2 ^ (n + 1) = 2 * (2 ^ n) := by rw [Nat.pow_succ]; omega
      rw [hp]
      omega

theorem pow3_mod7_cycle (j : Nat) :
    (j % 6 = 0 → (3 ^ j) % 7 = 1) ∧
      (j % 6 = 1 → (3 ^ j) % 7 = 3) ∧
      (j % 6 = 2 → (3 ^ j) % 7 = 2) ∧
      (j % 6 = 3 → (3 ^ j) % 7 = 6) ∧
      (j % 6 = 4 → (3 ^ j) % 7 = 4) ∧
      (j % 6 = 5 → (3 ^ j) % 7 = 5) := by
  induction j with
  | zero => omega
  | succ n ih =>
      have hp : 3 ^ (n + 1) = 3 * (3 ^ n) := by rw [Nat.pow_succ]; omega
      rw [hp]
      omega

/-! ## 2. Multi-Prime CRT Local-Global Portal Eliminations -/

/-- **Multi-Prime Elimination #1 (`{2, 3}`, `ord_3(2) = 2`)**:
    - Mod `8 = 2^3` ALONE fails at `j = 3` (`2^3 + 3*3 = 17 ≡ 1 mod 8`),
    - Mod `9 = 3^2` ALONE fails at `j = 4` (`2^4 + 3*4 = 28 ≡ 1 mod 9`),
    - Yet jointly modulo `6 = 2 * 3`, `(2^j + 3*j) % 6 ≠ 1` for ALL `j ≥ 1`! -/
theorem multiprime_2_3_eliminates_portal_2j_3j_1 :
    ((2 ^ 3 + 3 * 3) % 8 = 1) ∧
      ((2 ^ 4 + 3 * 4) % 9 = 1) ∧
      (∀ j : Nat, j ≥ 1 → (2 ^ j + 3 * j) % 6 ≠ 1) := by
  refine ⟨by decide, by decide, ?_⟩
  intro j hj hHit
  cases j with
  | zero => omega
  | succ m =>
      have hp2 : 2 ^ (m + 1) = 2 * (2 ^ m) := by rw [Nat.pow_succ]; omega
      have hMod2 : (2 ^ (m + 1) + 3 * (m + 1)) % 2 = 1 := by omega
      have hmEven : (m + 1) % 2 = 1 := by
        rw [hp2] at hMod2
        omega
      have hPow3 : (2 ^ (m + 1)) % 3 = 2 := (pow2_mod3_cycle (m + 1)).2 hmEven
      have hMod3 : (2 ^ (m + 1) + 3 * (m + 1)) % 3 = 1 := by omega
      omega

/-- **Multi-Prime Elimination #2 (`{3, 7}`, `ord_7(2) = 3`)**:
    - Mod `9 = 3^2` ALONE fails at `j = 7` (`2^7 + 7*7 = 177 ≡ 15 mod 9`),
    - Mod `49 = 7^2` ALONE fails at `j = 12` (`2^12 + 7*12 = 4180 ≡ 15 mod 49`),
    - Yet jointly modulo `21 = 3 * 7`, `(2^j + 7*j) % 21 ≠ 15` for ALL `j : Nat`! -/
theorem multiprime_3_7_eliminates_portal_2j_7j_15 :
    ((2 ^ 7 + 7 * 7) % 9 = 15 % 9) ∧
      ((2 ^ 12 + 7 * 12) % 49 = 15) ∧
      (∀ j : Nat, (2 ^ j + 7 * j) % 21 ≠ 15) := by
  refine ⟨by decide, by decide, ?_⟩
  intro j hHit
  have hMod7 : (2 ^ j + 7 * j) % 7 = 1 := by omega
  have hMod3 : (2 ^ j + 7 * j) % 3 = 0 := by omega
  have hCyc7 := pow2_mod7_cycle j
  have hj3 : j % 3 = 0 := by omega
  have hCyc3 := pow2_mod3_cycle j
  omega

/-- **Multi-Prime Elimination #3 (`{3, 7}` Dual-Base Exponential `2^j + 3^j`)**:
    - Mod `9 = 3^2` ALONE fails at `j = 4` (`2^4 + 3^4 = 97 ≡ 7 mod 9`),
    - Mod `49 = 7^2` ALONE fails at `j = 9` (`2^9 + 3^9 = 20195 ≡ 7 mod 49`),
    - Yet jointly modulo `21 = 3 * 7`, `(2^j + 3^j) % 21 ≠ 7` for ALL `j ≥ 1`! -/
theorem multiprime_3_7_eliminates_dual_exp_2j_3j :
    ((2 ^ 4 + 3 ^ 4) % 9 = 7) ∧
      ((2 ^ 9 + 3 ^ 9) % 49 = 7) ∧
      (∀ j : Nat, j ≥ 1 → (2 ^ j + 3 ^ j) % 21 ≠ 7) := by
  refine ⟨by decide, by decide, ?_⟩
  intro j hj hHit
  cases j with
  | zero => omega
  | succ m =>
      have hp3 : 3 ^ (m + 1) = 3 * (3 ^ m) := by rw [Nat.pow_succ]; omega
      have hMod3 : (2 ^ (m + 1) + 3 ^ (m + 1)) % 3 = 1 := by omega
      rw [hp3] at hMod3
      have hPow2Mod3 : (2 ^ (m + 1)) % 3 = 1 := by omega
      have hCyc2_3 := pow2_mod3_cycle (m + 1)
      have hEven : (m + 1) % 2 = 0 := by omega
      have hMod7 : (2 ^ (m + 1) + 3 ^ (m + 1)) % 7 = 0 := by omega
      have hCyc2_7 := pow2_mod7_cycle (m + 1)
      have hCyc3_7 := pow3_mod7_cycle (m + 1)
      omega

/-! ## 3. Exact Integer-Cleared Laplacian Pseudoinverse `48 * L^+` on Antihydra Mod-8 -/

/-- Exact `8 × 8` undirected graph Laplacian `L` of Antihydra's Mod-8 quotient multigraph
    (`a ↦ floor((3a + 2)/2)` for even `a`, `floor((3a + 1)/2)` for odd `a`, lifted to `Z / 16Z`). -/
def antihydraMod8Laplacian : List (List Int) :=
  [ [ 4, -1, -1,  0,  0, -2,  0,  0],
    [-1,  4, -1, -1,  0,  0, -1,  0],
    [-1, -1,  4,  0, -1,  0, -1,  0],
    [ 0, -1,  0,  4, -1, -1,  0, -1],
    [ 0,  0, -1, -1,  4, -1,  0, -1],
    [-2,  0,  0, -1, -1,  4,  0,  0],
    [ 0, -1, -1,  0,  0,  0,  2,  0],
    [ 0,  0,  0, -1, -1,  0,  0,  2] ]

/-- Exact integer-cleared Moore-Penrose pseudoinverse `G = 48 * L^+` (`G ∈ Mat_8(Z)`). -/
def antihydraMod8ScaledPinverse48 : List (List Int) :=
  [ [12,  0,  0, -3, -3,  3, -3, -6],
    [ 0, 11,  1, -2, -4, -3,  3, -6],
    [ 0,  1, 11, -4, -2, -3,  3, -6],
    [-3, -2, -4, 11,  1,  0, -6,  3],
    [-3, -4, -2,  1, 11,  0, -6,  3],
    [ 3, -3, -3,  0,  0, 12, -6, -3],
    [-3,  3,  3, -6, -6, -6, 24, -9],
    [-6, -6, -6,  3,  3, -3, -9, 24] ]

def matGet8 (M : List (List Int)) (i j : Nat) : Int :=
  match M[i]? with
  | none => 0
  | some row =>
      match row[j]? with
      | none => 0
      | some v => v

def matMulEntry8 (A B : List (List Int)) (i j : Nat) : Int :=
  (List.range 8).foldl (fun acc k => acc + matGet8 A i k * matGet8 B k j) 0

/-- Check all Moore-Penrose Laplacian pseudoinverse equations over `Z`:
    1. `L * (48 * L^+) = 48 * I_8 - 6 * J_8` (exact centering projector `I - (1/8)J` cleared by `48`),
    2. Symmetry `(48 * L^+)[i, j] = (48 * L^+)[j, i]`,
    3. Zero row-sums `∑_j (48 * L^+)[i, j] = 0` (`(48 * L^+) * 1 = 0`),
    4. Exact scaled Kirchhoff effective resistance `48 * R_eff(3 <-> 7) = G[3,3] + G[7,7] - 2*G[3,7] = 29`. -/
def verifyAntihydraMod8Kirchhoff : Bool :=
  let L := antihydraMod8Laplacian
  let G := antihydraMod8ScaledPinverse48
  let prodOk := (List.range 8).all fun i =>
    (List.range 8).all fun j =>
      let target : Int := if i == j then 42 else -6
      matMulEntry8 L G i j == target
  let symOk := (List.range 8).all fun i =>
    (List.range 8).all fun j =>
      matGet8 G i j == matGet8 G j i
  let zeroSumOk := (List.range 8).all fun i =>
    ((List.range 8).foldl (fun acc j => acc + matGet8 G i j) (0 : Int)) == 0
  let reff37 := matGet8 G 3 3 + matGet8 G 7 7 - 2 * matGet8 G 3 7
  prodOk && symOk && zeroSumOk && (reff37 == 29)

/-- **Pure-Kernel `decide` Certificate for Antihydra Mod-8 Kirchhoff Escape Resistance**:
    Certifies `L * (48 * L^+) = 48 * I_8 - 6 * J_8`, `G^T = G`, `G * 1 = 0`, and
    `R_eff(3 <-> 7) = 29 / 48` on the finite Mod-8 quotient graph (`[-1]` fenced strictly
    to the finite quotient graph, never conflated with infinite-state halting). -/
theorem antihydra_mod8_kirchhoff_pseudoinverse_verified :
    verifyAntihydraMod8Kirchhoff = true := by
  decide

end CryptidSolvePhase4
