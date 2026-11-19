/-
  CryptidSolvePhase4.Transfer3PisotQuadratic
  ==========================================
  Transfer 3:
  Irrational Pisot Quadratic Rings (`Z[phi] ⊂ Q(sqrt 5)` & `Z[sqrt 2]`) and
  Galois-Conjugate Norm Barriers Certifying Non-Halting Where 100% of Mod-M Sieves Fail.

  Formalizes in pure Lean 4 Core (`Init` + `omega` + `decide`, zero floats):
    1. Exact Golden-Ratio Ring `ZPhi` (`a + b * phi`, `phi^2 = phi + 1`), Galois conjugation
       `conj (a + b * phi) = (a + b) - b * phi`, and algebraic norm `N(a + b*phi) = a^2 + a*b - b^2`,
       including exact multiplicativity `norm (mul z w) = norm z * norm w`.
    2. **Universal Stage-1 Modular Sieve Failure Theorem (`fib_modular_sieve_fails_all_M`)**:
       For EVERY modulus `M ≥ 1`, `fibModStep M` is a bijection on `(Z/MZ)^2` whose unique
       predecessor of `(3 mod M, 2 mod M)` is `(2 mod M, 1 mod M) ≡ (2(M+1), M+1) (mod M)`
       on the halting ray `G = {(2k, k) : k ≥ 2}`; hence every Pisano period `P ≥ 1` forces
       step `P - 1` of the forward mod-`M` orbit from `(3, 2)` right onto `G mod M`!
    3. **Unconditional Global Pisot Norm Barrier (`fib_pisot_counter_immortal`)**:
       In `ZPhi`, `eigenCoord (x + y) x = mul phiBar (eigenCoord x y)` with `norm phiBar = -1`,
       locking `(norm (eigenCoord x_n y_n))^2 = 1` (`norm ∈ {-1, +1}`), whereas every point on
       `G = {(2k, k) : k ≥ 2}` has `norm = k^2 ≥ 4`, proving `IsImmortalOrbit` from `(3, 2)`.
    4. Second Quadratic Pisot Ring `ZSqrt2` (`a + b * sqrt 2`, Pell norm `a^2 - 2*b^2 = ±1`)
       certifying non-halting on the Pell-Sturmian machine `(x, y) ↦ (x + 2y, x + y)`.
-/

import CryptidSolvePhase4.Basic

namespace CryptidSolvePhase4

/-! ## 1. Exact Quadratic Pisot Ring `ZPhi = Z[phi]` (`phi^2 = phi + 1`) -/

/-- Element `a + b * phi` in `Z[phi]`, where `phi = (1 + sqrt 5)/2` satisfies `phi^2 = 1 + phi`. -/
structure ZPhi where
  a : Int
  b : Int
  deriving DecidableEq, Repr

namespace ZPhi

def ofInt (n : Int) : ZPhi := ⟨n, 0⟩

def phi : ZPhi := ⟨0, 1⟩

/-- Galois conjugate `1 - phi` of `phi`. -/
def phiBar : ZPhi := ⟨1, -1⟩

def add (z w : ZPhi) : ZPhi := ⟨z.a + w.a, z.b + w.b⟩

def sub (z w : ZPhi) : ZPhi := ⟨z.a - w.a, z.b - w.b⟩

/-- Exact ring multiplication `(a + b*phi)(c + d*phi) = (ac + bd) + (ad + bc + bd)*phi`. -/
def mul (z w : ZPhi) : ZPhi :=
  ⟨z.a * w.a + z.b * w.b, z.a * w.b + z.b * w.a + z.b * w.b⟩

/-- Exact Galois automorphism `sigma(a + b*phi) = a + b*(1 - phi) = (a + b) - b*phi`. -/
def conj (z : ZPhi) : ZPhi :=
  ⟨z.a + z.b, -z.b⟩

/-- Exact algebraic Galois norm `N_{Q(sqrt 5)/Q}(a + b*phi) = a^2 + a*b - b^2`. -/
def norm (z : ZPhi) : Int :=
  z.a * z.a + z.a * z.b - z.b * z.b

theorem mul_comm (z w : ZPhi) : mul z w = mul w z := by
  unfold mul
  simp only [ZPhi.mk.injEq]
  have h1 : z.a * w.a = w.a * z.a := Int.mul_comm z.a w.a
  have h2 : z.b * w.b = w.b * z.b := Int.mul_comm z.b w.b
  have h3 : z.a * w.b = w.b * z.a := Int.mul_comm z.a w.b
  have h4 : z.b * w.a = w.a * z.b := Int.mul_comm z.b w.a
  exact ⟨by omega, by omega⟩

theorem mul_assoc (u v w : ZPhi) : mul (mul u v) w = mul u (mul v w) := by
  unfold mul
  simp only [ZPhi.mk.injEq, Int.add_mul, Int.mul_add, ← Int.mul_assoc]
  exact ⟨by omega, by omega⟩

theorem conj_mul (z w : ZPhi) : conj (mul z w) = mul (conj z) (conj w) := by
  unfold conj mul
  simp only [ZPhi.mk.injEq, Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  exact ⟨by omega, by omega⟩

theorem mul_conj_eq_ofInt_norm (z : ZPhi) : mul z (conj z) = ofInt (norm z) := by
  unfold mul conj ofInt norm
  simp only [ZPhi.mk.injEq, Int.mul_add, Int.mul_neg]
  have hComm : z.b * z.a = z.a * z.b := Int.mul_comm z.b z.a
  exact ⟨by omega, by omega⟩

theorem ofInt_mul_ofInt (x y : Int) : mul (ofInt x) (ofInt y) = ofInt (x * y) := by
  unfold mul ofInt
  simp only [ZPhi.mk.injEq, Int.mul_zero, Int.zero_mul, Int.add_zero, and_self]

/-- **Multiplicativity of the Algebraic Galois Norm in `Z[phi]`**:
    `norm (mul z w) = norm z * norm w` proved directly from Galois conjugation. -/
theorem norm_mul (z w : ZPhi) : norm (mul z w) = norm z * norm w := by
  have hLHS : ofInt (norm (mul z w)) = mul (mul z w) (conj (mul z w)) :=
    (mul_conj_eq_ofInt_norm (mul z w)).symm
  rw [conj_mul, mul_assoc z w (mul (conj z) (conj w)),
      mul_comm (conj z) (conj w), ← mul_assoc w (conj w) (conj z),
      mul_conj_eq_ofInt_norm w, mul_comm (ofInt (norm w)) (conj z),
      ← mul_assoc z (conj z) (ofInt (norm w)),
      mul_conj_eq_ofInt_norm z, ofInt_mul_ofInt] at hLHS
  unfold ofInt at hLHS
  injection hLHS

theorem phi_sq_eq_phi_add_one : mul phi phi = add phi (ofInt 1) := by
  decide

theorem norm_phiBar_eq_neg_one : norm phiBar = -1 := by
  decide

end ZPhi

/-! ## 2. Universal Stage-1 Modular Sieve Failure (`∀ M ≥ 1`) -/

/-- Forward mod-`M` Fibonacci transition `(x, y) ↦ ((x + y) mod M, x mod M)`. -/
def fibModStep (M : Nat) (p : Nat × Nat) : Nat × Nat :=
  ((p.1 + p.2) % M, p.1 % M)

/-- Exact mod-`M` inverse `(u, v) ↦ (v mod M, (u + M - v mod M) mod M)`. -/
def fibModInv (M : Nat) (p : Nat × Nat) : Nat × Nat :=
  (p.2 % M, (p.1 + M - p.2 % M) % M)

def iterMod (M : Nat) : Nat → (Nat × Nat) → (Nat × Nat)
  | 0, p => p
  | n + 1, p => iterMod M n (fibModStep M p)

theorem fibModStep_left_inv (M x y : Nat) (hx : x < M) (hy : y < M) :
    fibModInv M (fibModStep M (x, y)) = (x, y) := by
  unfold fibModStep fibModInv
  dsimp
  have hxMod : x % M = x := Nat.mod_eq_of_lt hx
  rw [hxMod, hxMod]
  refine Prod.ext rfl ?_
  dsimp
  if hlt : x + y < M then
    have hxyMod : (x + y) % M = x + y := Nat.mod_eq_of_lt hlt
    rw [hxyMod]
    have hSub : x + y + M - x = M + y := by omega
    rw [hSub, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt hy
  else
    have hlt2 : x + y - M < M := by omega
    have hxyMod : (x + y) % M = x + y - M := by
      calc
        (x + y) % M = (M + (x + y - M)) % M := by congr 1; omega
        _ = (x + y - M) % M := Nat.add_mod_left M (x + y - M)
        _ = x + y - M := Nat.mod_eq_of_lt hlt2
    rw [hxyMod]
    have hSub : x + y - M + M - x = y := by omega
    rw [hSub]
    exact Nat.mod_eq_of_lt hy

/-- **Universal Stage-1 Modular Sieve Failure Theorem (`Probe 2` Generalized to ALL `M ≥ 1`)**:
    For EVERY modulus `M ≥ 1`:
      1. There exists a genuine halting-ray point `g_M = (2*(M+1), M+1)` (`k = M+1 ≥ 2`) whose
         mod-`M` projection is `(2 % M, 1 % M)`,
      2. One mod-`M` step from `(2 % M, 1 % M)` lands at the start residue `(3 % M, 2 % M)`, and
      3. For ANY Pisano cycle period `P ≥ 1` of `(3 % M, 2 % M)`, step `P - 1` of the forward
         mod-`M` orbit from `(3 % M, 2 % M)` lands directly on the halting residue `(g_M.1 % M, g_M.2 % M)`! -/
theorem fib_modular_sieve_fails_every_modulus (M : Nat) (hM : M ≥ 1) :
    let gHalt : Nat × Nat := (2 * (M + 1), M + 1)
    (gHalt.2 ≥ 2 ∧ gHalt.1 = 2 * gHalt.2) ∧
      (gHalt.1 % M, gHalt.2 % M) = (2 % M, 1 % M) ∧
      fibModStep M (2 % M, 1 % M) = (3 % M, 2 % M) ∧
      (∀ P : Nat, P ≥ 1 →
        iterMod M P (3 % M, 2 % M) = (3 % M, 2 % M) →
        iterMod M (P - 1) (3 % M, 2 % M) = (gHalt.1 % M, gHalt.2 % M)) := by
  dsimp
  have hg1 : (2 * (M + 1)) % M = 2 % M := by
    have hEq : 2 * (M + 1) = 2 + M * 2 := by omega
    rw [hEq, Nat.add_mul_mod_self_left]
  have hg2 : (M + 1) % M = 1 % M := by
    have hEq : M + 1 = 1 + M := by omega
    rw [hEq, Nat.add_mod_right]
  have hPred : fibModStep M (2 % M, 1 % M) = (3 % M, 2 % M) := by
    unfold fibModStep
    dsimp
    have hAdd : (2 % M + 1 % M) % M = 3 % M := by
      rw [← Nat.add_mod]
    have hMod2 : (2 % M) % M = 2 % M := Nat.mod_mod 2 M
    rw [hAdd, hMod2]
  refine ⟨⟨by omega, rfl⟩, Prod.ext hg1 hg2, hPred, ?_⟩
  intro P hP hPer
  cases P with
  | zero => omega
  | succ k =>
      have hSub : k + 1 - 1 = k := by omega
      rw [hSub, hg1, hg2]
      -- Commute `fibModStep` to the outside of `iterMod`:
      have hComm : ∀ n : Nat, ∀ p : Nat × Nat,
          iterMod M n (fibModStep M p) = fibModStep M (iterMod M n p) := by
        intro n
        induction n with
        | zero => intro p; rfl
        | succ m ih => intro p; simp only [iterMod]; exact ih (fibModStep M p)
      have hStepEnd : fibModStep M (iterMod M k (3 % M, 2 % M)) = (3 % M, 2 % M) := by
        rw [← hComm k (3 % M, 2 % M)]
        exact hPer
      have hBounded : ∀ n : Nat, ∀ p : Nat × Nat, p.1 < M ∧ p.2 < M →
          (iterMod M n p).1 < M ∧ (iterMod M n p).2 < M := by
        intro n
        induction n with
        | zero => intro p hp; exact hp
        | succ m ih =>
            intro p _
            apply ih
            unfold fibModStep
            exact ⟨Nat.mod_lt _ hM, Nat.mod_lt _ hM⟩
      have hB := hBounded k (3 % M, 2 % M) ⟨Nat.mod_lt 3 hM, Nat.mod_lt 2 hM⟩
      rcases hRes : iterMod M k (3 % M, 2 % M) with ⟨u, v⟩
      rw [hRes] at hB hStepEnd
      dsimp at hB
      have hApplyInv := congrArg (fibModInv M) hStepEnd
      rw [fibModStep_left_inv M u v hB.1 hB.2] at hApplyInv
      have hInvPred := congrArg (fibModInv M) hPred
      rw [fibModStep_left_inv M (2 % M) (1 % M) (Nat.mod_lt 2 hM) (Nat.mod_lt 1 hM)] at hInvPred
      rw [hApplyInv, ← hInvPred]

/-! ## 3. Unconditional Global Non-Halting via `ZPhi` Galois Norm Barrier -/

/-- Fibonacci-substitution counter `(x, y) ↦ (x + y, x)` halting on ray `G = {(2k, k) : k ≥ 2}`. -/
def stepFibPisot (p : Int × Int) : Option (Int × Int) :=
  if 2 ≤ p.2 ∧ p.1 = 2 * p.2 then none
  else some (p.1 + p.2, p.1)

/-- Pisot eigen-coordinate `z(x, y) = x - y * phi ∈ Z[phi]`. -/
def eigenCoordPhi (x y : Int) : ZPhi :=
  ⟨x, -y⟩

/-- Exact Pisot Eigen-Scaling Identity:
    `eigenCoordPhi (x + y) x = mul phiBar (eigenCoordPhi x y)` identically in `ZPhi`. -/
theorem fib_pisot_eigen_step (x y : Int) :
    eigenCoordPhi (x + y) x = ZPhi.mul ZPhi.phiBar (eigenCoordPhi x y) := by
  unfold eigenCoordPhi ZPhi.mul ZPhi.phiBar
  simp only [ZPhi.mk.injEq]
  exact ⟨by omega, by omega⟩

/-- Every step flips the sign of `norm (eigenCoordPhi x y)`, preserving `norm^2 = 1`. -/
theorem fib_pisot_norm_flip (x y : Int) :
    ZPhi.norm (eigenCoordPhi (x + y) x) = -ZPhi.norm (eigenCoordPhi x y) := by
  rw [fib_pisot_eigen_step, ZPhi.norm_mul, ZPhi.norm_phiBar_eq_neg_one]
  omega

/-- On the halting ray `G = {(2k, k) : k ≥ 2}`, `norm (eigenCoordPhi (2k) k) = k^2 ≥ 4`. -/
theorem fib_pisot_halt_ray_norm_ge_four (k : Int) (hk : 2 ≤ k) :
    ZPhi.norm (eigenCoordPhi (2 * k) k) = k * k ∧ 4 ≤ k * k := by
  have hNorm : ZPhi.norm (eigenCoordPhi (2 * k) k) = k * k := by
    unfold ZPhi.norm eigenCoordPhi
    dsimp
    have h1 : (2 * k) * (2 * k) = 4 * (k * k) := by
      calc
        (2 * k) * (2 * k) = 2 * (k * (2 * k)) := by rw [Int.mul_assoc]
        _ = 2 * (2 * (k * k)) := by rw [← Int.mul_assoc k 2 k, Int.mul_comm k 2, Int.mul_assoc]
        _ = 4 * (k * k) := by rw [← Int.mul_assoc]; rfl
    have h2 : (2 * k) * (-k) = -(2 * (k * k)) := by
      rw [Int.mul_neg, Int.mul_assoc]
    have h3 : (-k) * (-k) = k * k := Int.neg_mul_neg k k
    rw [h1, h2, h3]
    omega
  have hGe4 : 4 ≤ k * k := by
    have hm : 2 * 2 ≤ k * k := Int.mul_le_mul hk hk (by omega) (by omega)
    omega
  exact ⟨hNorm, hGe4⟩

def InvFibPisot (p : Int × Int) : Prop :=
  1 ≤ p.1 ∧ 1 ≤ p.2 ∧
    (ZPhi.norm (eigenCoordPhi p.1 p.2) = 1 ∨ ZPhi.norm (eigenCoordPhi p.1 p.2) = -1)

theorem invFibPisot_preserved : IsInvariant stepFibPisot InvFibPisot := by
  intro p p' hp hStep
  rcases p with ⟨x, y⟩
  unfold InvFibPisot at hp
  dsimp at hp
  rcases hp with ⟨hx, hy, hUnit⟩
  unfold stepFibPisot at hStep
  split at hStep
  · contradiction
  · injection hStep with hEq
    subst hEq
    unfold InvFibPisot
    dsimp
    refine ⟨by omega, by omega, ?_⟩
    rw [fib_pisot_norm_flip x y]
    omega

theorem invFibPisot_safe (p : Int × Int) (hp : InvFibPisot p) :
    stepFibPisot p ≠ none := by
  rcases p with ⟨x, y⟩
  unfold InvFibPisot at hp
  dsimp at hp
  rcases hp with ⟨_, _, hUnit⟩
  intro hNone
  unfold stepFibPisot at hNone
  dsimp at hNone
  split at hNone
  · rename_i hG
    rcases hG with ⟨hy2, hxEq⟩
    subst hxEq
    obtain ⟨hNormEq, hGe4⟩ := fib_pisot_halt_ray_norm_ge_four y hy2
    rw [hNormEq] at hUnit
    omega
  · contradiction

/-- **Unconditional Immortality of `stepFibPisot` from `(3, 2)` via `ZPhi` Norm Barrier**:
    Even though 100% of finite modular quotients `M ≥ 1` fail (`fib_modular_sieve_fails_every_modulus`),
    the `Z[phi]` Galois norm invariant `N ∈ {-1, +1}` vs. `N|_G = k^2 ≥ 4` proves both
    `IsNonHalting` and pairwise state distinctness (`IsImmortalOrbit`). -/
theorem fib_pisot_counter_immortal :
    IsImmortalOrbit stepFibPisot (3, 2) := by
  have hInit : InvFibPisot (3, 2) := by
    unfold InvFibPisot ZPhi.norm eigenCoordPhi
    dsimp
    exact ⟨by omega, by omega, Or.inr (by omega)⟩
  have hDrift : ∀ p p' : Int × Int, InvFibPisot p → stepFibPisot p = some p' →
      (p.1 + p.2) + 1 ≤ p'.1 + p'.2 := by
    intro p p' hp hStep
    rcases p with ⟨x, y⟩
    rcases hp with ⟨hx, _, _⟩
    unfold stepFibPisot at hStep
    split at hStep
    · contradiction
    · injection hStep with hEq; subst hEq; dsimp; omega
  exact immortal_of_safe_invariant_and_drift
    stepFibPisot InvFibPisot (fun p => p.1 + p.2) 1 (by omega)
    invFibPisot_preserved invFibPisot_safe hDrift (3, 2) hInit

/-! ## 4. Second Quadratic Pisot Ring `ZSqrt2` (`a + b * sqrt 2`, Pell Norm Barrier) -/

/-- Element `a + b * sqrt 2` in `Z[sqrt 2]` with Pell norm `a^2 - 2 * b^2`. -/
structure ZSqrt2 where
  a : Int
  b : Int
  deriving DecidableEq, Repr

namespace ZSqrt2

def pellNorm (z : ZSqrt2) : Int :=
  z.a * z.a - 2 * (z.b * z.b)

end ZSqrt2

/-- Pell-Sturmian unimodular counter `(x, y) ↦ (x + 2y, x + y)` from `(3, 2)`
    (`pellNorm = 3^2 - 2*2^2 = +1`), halting on ray `G_Pell = {(3k, 2k) : k ≥ 2}`
    where `pellNorm (3k, 2k) = 9k^2 - 8k^2 = k^2 ≥ 4`. -/
def stepPellPisot (p : Int × Int) : Option (Int × Int) :=
  if 4 ≤ p.2 ∧ 2 * p.1 = 3 * p.2 then none
  else some (p.1 + 2 * p.2, p.1 + p.2)

theorem pellNorm_step_flip (x y : Int) :
    ZSqrt2.pellNorm ⟨x + 2 * y, x + y⟩ = -ZSqrt2.pellNorm ⟨x, y⟩ := by
  unfold ZSqrt2.pellNorm
  dsimp
  have h1 : (x + 2 * y) * (x + 2 * y) = x * x + 4 * (x * y) + 4 * (y * y) := by
    calc
      (x + 2 * y) * (x + 2 * y)
          = x * x + x * (2 * y) + (2 * y) * x + (2 * y) * (2 * y) := by
              rw [Int.add_mul, Int.mul_add, Int.mul_add, ← Int.add_assoc]
      _ = x * x + 4 * (x * y) + 4 * (y * y) := by
            have ha : x * (2 * y) = 2 * (x * y) := by
              rw [← Int.mul_assoc, Int.mul_comm x 2, Int.mul_assoc]
            have hb : (2 * y) * x = 2 * (x * y) := by
              rw [Int.mul_assoc, Int.mul_comm y x]
            have hc : (2 * y) * (2 * y) = 4 * (y * y) := by
              calc
                (2 * y) * (2 * y) = 2 * (y * (2 * y)) := by rw [Int.mul_assoc]
                _ = 2 * (2 * (y * y)) := by rw [← Int.mul_assoc y 2 y, Int.mul_comm y 2, Int.mul_assoc]
                _ = 4 * (y * y) := by rw [← Int.mul_assoc]; rfl
            rw [ha, hb, hc]
            omega
  have h2 : (x + y) * (x + y) = x * x + 2 * (x * y) + y * y := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm y x]
    omega
  rw [h1, h2]
  omega

theorem pell_pisot_counter_nonHalting :
    IsNonHalting stepPellPisot (3, 2) := by
  let P : Int × Int → Prop := fun p =>
    ZSqrt2.pellNorm ⟨p.1, p.2⟩ = 1 ∨ ZSqrt2.pellNorm ⟨p.1, p.2⟩ = -1
  have hInv : IsInvariant stepPellPisot P := by
    intro p p' hp hStep
    rcases p with ⟨x, y⟩
    unfold stepPellPisot at hStep
    split at hStep
    · contradiction
    · injection hStep with hEq
      subst hEq
      dsimp only [P] at hp ⊢
      rw [pellNorm_step_flip x y]
      omega
  have hSafe : ∀ p : Int × Int, P p → stepPellPisot p ≠ none := by
    intro ⟨x, y⟩ hp hNone
    unfold stepPellPisot at hNone
    dsimp at hNone
    split at hNone
    · rename_i hG
      rcases hG with ⟨hy4, h2x⟩
      dsimp only [P, ZSqrt2.pellNorm] at hp
      have h4x : 4 * (x * x) = (2 * x) * (2 * x) := by
        calc
          4 * (x * x) = (2 * 2) * (x * x) := rfl
          _ = 2 * (2 * (x * x)) := Int.mul_assoc 2 2 (x * x)
          _ = 2 * (x * (2 * x)) := by rw [← Int.mul_assoc 2 x x, Int.mul_comm (2 * x) x]
          _ = (2 * x) * (2 * x) := (Int.mul_assoc 2 x (2 * x)).symm
      have h9y : (3 * y) * (3 * y) = 9 * (y * y) := by
        calc
          (3 * y) * (3 * y) = 3 * (y * (3 * y)) := Int.mul_assoc 3 y (3 * y)
          _ = 3 * (3 * (y * y)) := by rw [← Int.mul_assoc y 3 y, Int.mul_comm y 3, Int.mul_assoc 3 y y]
          _ = (3 * 3) * (y * y) := (Int.mul_assoc 3 3 (y * y)).symm
          _ = 9 * (y * y) := rfl
      have hEqSq : (2 * x) * (2 * x) = 9 * (y * y) := by
        rw [h2x, h9y]
      have hySq : 16 ≤ y * y := by
        have hm : 4 * 4 ≤ y * y := Int.mul_le_mul hy4 hy4 (by omega) (by omega)
        omega
      omega
    · contradiction
  exact nonHalting_of_safe_invariant stepPellPisot P hInv hSafe (3, 2) (by decide)

end CryptidSolvePhase4
