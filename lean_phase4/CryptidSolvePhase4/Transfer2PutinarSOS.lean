/- Scope: AppC step-count theorems below are arithmetic identities for specified
   counter recurrences. Raw-TM correspondence is finite-tested in Python, not
   universally formalized by these declarations. AppC7RawGate.lean now separately
   proves the AppC7 gate recurrence from the raw transition table for every a,r.
   See paper/main.tex. -/

/-
  CryptidSolvePhase4.Transfer2PutinarSOS
  ======================================
  Transfer 2:
  Exact Rational `LDL^T` Putinar Positivstellensatz Barrier Certificates &
  Parabolic Counter / `AppC_7` Quadratic Step Laws.

  Formalizes in pure Lean 4 Core (`Int` & `Nat`, zero floats, zero Mathlib):
    1. Non-negativity of integer squares (`sq_nonneg_int`) and denominator-cleared
       rational `LDL^T` Putinar SOS positivity (`putinar2_nonneg_on_guard`):
       whenever `N * B(x, y) = d0 * q0(x,y)^2 + d1 * q1(x,y)^2 + g(x,y) * (e0 * r0(x,y)^2)`
       with `N > 0` and `d0, d1, e0 ≥ 0`, `g(x, y) ≥ 0` implies `0 ≤ B(x, y)`.
    2. Universal `Stage 3c` Putinar SOS Non-Halting Meta-Theorem (`putinar_sos_barrier_nonHalting`).
    3. Parabolic Counter `(x, y) ↦ (x + 2y + 1, y + 1)` from `(2, 0)` with halting guard
       `4y - x - 3 ≥ 0`:
       - **Hyperplane Impossibility Theorem (`parabolic_no_affine_barrier`)**: proves NO affine
         barrier `L(x, y) = a*x + b*y + c` over `Int` can certify this machine!
       - **Single-Pivot Putinar SOS Immortality (`parabolic_counter_immortal`)**: certifies
         `B(x, y) = y^2 - x + 1 = (y - 2)^2 + (4y - x - 3)` (`IsImmortalOrbit`).
    4. Coupled Nonlinear Bouncer `(x, y) ↦ (x + 2y + 2, y + 1)` from `(3, 0)` with guard
       `4y - x - 1 ≥ 0`, certified via a **2-pivot non-integer rational `LDL^T` SOS**
       (`d0 = 3`, `l10 = -1/2`, `d1 = 1/4` -> cleared by `N = 4`:
       `4 * B(x, y) = 3 * (2 - y)^2 + 1 * y^2 + 4 * (4y - x - 1)`).
    5. Mechanistic `AppC_7` Parabolic Halting Gate Theorem (`appC7_parabolic_gate_step_law`):
       formalizes the exact raw-TM sweep `D(a, r) -> D(a + 4, r - 1)` (`8a + 20` steps,
       exit `2a + 5` steps) and proves `6 + appC7GateSweep 2 b = 16*b^2 + 28*b + 15`.
-/

import CryptidSolvePhase4.Basic

namespace CryptidSolvePhase4

/-! ## 1. Pure-Core Integer Squares & Denominator-Cleared Rational `LDL^T` Putinar SOS -/

/-- For every integer `z : Int`, `0 ≤ z * z` (pure Lean 4 Core proof). -/
theorem sq_nonneg_int (z : Int) : 0 ≤ z * z := by
  if h : 0 ≤ z then
    exact Int.mul_nonneg h h
  else
    have hNeg : 0 ≤ -z := by omega
    have hProd : 0 ≤ (-z) * (-z) := Int.mul_nonneg hNeg hNeg
    rw [Int.neg_mul_neg] at hProd
    exact hProd

/-- Weighted 2-pivot SOS expression `d0 * q0^2 + d1 * q1^2` is always non-negative for `d0, d1 ≥ 0`. -/
theorem weighted_sos2_nonneg {d0 d1 : Int} (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (q0 q1 : Int) :
    0 ≤ d0 * (q0 * q0) + d1 * (q1 * q1) := by
  have h0 : 0 ≤ d0 * (q0 * q0) := Int.mul_nonneg hd0 (sq_nonneg_int q0)
  have h1 : 0 ≤ d1 * (q1 * q1) := Int.mul_nonneg hd1 (sq_nonneg_int q1)
  omega

/-- Denominator-Cleared Putinar Positivstellensatz Certificate Lemma:
    If `N > 0`, pivots `d0, d1, e0 ≥ 0`, and `N * B = d0 * q0^2 + d1 * q1^2 + g * (e0 * r0^2)`,
    then on the semi-algebraic guard `0 ≤ g`, we must have `0 ≤ B`. -/
theorem putinar_cleared_nonneg_of_guard
    {N B d0 d1 e0 q0 q1 g r0 : Int}
    (hN : 0 < N) (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (he0 : 0 ≤ e0)
    (hId : N * B = d0 * (q0 * q0) + d1 * (q1 * q1) + g * (e0 * (r0 * r0)))
    (hGuard : 0 ≤ g) : 0 ≤ B := by
  have hS0 : 0 ≤ d0 * (q0 * q0) + d1 * (q1 * q1) := weighted_sos2_nonneg hd0 hd1 q0 q1
  have hR0 : 0 ≤ e0 * (r0 * r0) := Int.mul_nonneg he0 (sq_nonneg_int r0)
  have hS1 : 0 ≤ g * (e0 * (r0 * r0)) := Int.mul_nonneg hGuard hR0
  have hNB : 0 ≤ N * B := by omega
  if hB : 0 ≤ B then
    exact hB
  else
    have hNegB : 0 < -B := by omega
    have hPos : 0 < N * (-B) := Int.mul_pos hN hNegB
    rw [Int.mul_neg] at hPos
    omega

/-- Universal `Stage 3c` Rational `LDL^T` Putinar SOS Barrier Non-Halting Meta-Theorem. -/
theorem putinar_sos_barrier_nonHalting {S : Type}
    (step : StepFn S) (Dom : S → Prop)
    (B g q0 q1 r0 : S → Int) (N d0 d1 e0 : Int)
    (hN : 0 < N) (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (he0 : 0 ≤ e0)
    (hDomInv : IsInvariant step Dom)
    (hMono : ∀ s s' : S, Dom s → B s < 0 → step s = some s' → B s' ≤ B s)
    (hHaltGuard : ∀ s : S, Dom s → step s = none → 0 ≤ g s)
    (hPutinar : ∀ s : S, Dom s →
      N * B s = d0 * (q0 s * q0 s) + d1 * (q1 s * q1 s) + g s * (e0 * (r0 s * r0 s)))
    (s0 : S) (hDom0 : Dom s0) (hInitNeg : B s0 < 0) :
    IsNonHalting step s0 := by
  refine nonHalting_of_barrier_cert step Dom B hDomInv hMono ?_ s0 hDom0 hInitNeg
  intro s hDom hNone
  exact putinar_cleared_nonneg_of_guard hN hd0 hd1 he0 (hPutinar s hDom) (hHaltGuard s hDom hNone)

/-! ## 2. Parabolic Counter: Hyperplane Impossibility + Degree-2 Putinar SOS Immortality -/

/-- Parabolic counter `(x, y) ↦ (x + 2y + 1, y + 1)` halting iff `4y - x - 3 ≥ 0`. -/
def guardParabolic (p : Int × Int) : Int :=
  4 * p.2 - p.1 - 3

def stepParabolic (p : Int × Int) : Option (Int × Int) :=
  if 0 ≤ guardParabolic p then none
  else some (p.1 + 2 * p.2 + 1, p.2 + 1)

def DomParabolic (p : Int × Int) : Prop :=
  0 ≤ p.1 ∧ 0 ≤ p.2

/-- **Universal Affine Barrier No-Go Theorem (`Probe 3` Hyperplane Impossibility)**:
    NO affine polynomial `L(x, y) = a*x + b*y + c` (`a, b, c : Int`) can simultaneously satisfy:
      1. `L(2, 0) < 0` (initial negativity),
      2. `L(x + 2y + 1, y + 1) ≤ L(x, y)` for all `x, y ≥ 0` (non-increasing along transitions), and
      3. `0 ≤ L(x, y)` for all `x, y ≥ 0` in the halting region `4y - x - 3 ≥ 0`. -/
theorem parabolic_no_affine_barrier (a b c : Int)
    (hInit : a * 2 + b * 0 + c < 0)
    (hMono : ∀ x y : Int, 0 ≤ x → 0 ≤ y →
      a * (x + 2 * y + 1) + b * (y + 1) + c ≤ a * x + b * y + c)
    (hHalt : ∀ x y : Int, 0 ≤ x → 0 ≤ y → 0 ≤ 4 * y - x - 3 →
      0 ≤ a * x + b * y + c) : False := by
  -- 1. Evaluate `hMono` at `(0, 0)` and `(0, 1)` to constrain `a` and `b`:
  have hm0 := hMono 0 0 (by omega) (by omega)
  have hm1 := hMono 0 1 (by omega) (by omega)
  -- From `hm0`: `a + b ≤ 0`; from `hm1`: `3*a + b ≤ 0`.
  -- 2. Evaluate `hHalt` at `(1, 1)` (`4*1 - 1 - 3 = 0 ≥ 0`) and `(0, 1)` (`4*1 - 0 - 3 = 1 ≥ 0`):
  have hh11 := hHalt 1 1 (by omega) (by omega) (by omega)
  have hh01 := hHalt 0 1 (by omega) (by omega) (by omega)
  -- `hh01`: `0 ≤ b + c`, while `hInit`: `2*a + c < 0`, and `hh11`: `0 ≤ a + b + c`.
  -- Combine: `0 ≤ (a + b) + c ≤ 0 + c = c`, wait: if `0 ≤ c` and `2*a + c < 0`, then `a < 0` (`a ≤ -1`),
  -- wait: check `hHalt` at `(5, 2)` (`4*2 - 5 - 3 = 0 ≥ 0`): `0 ≤ 5*a + 2*b + c`!
  have hh52 := hHalt 5 2 (by omega) (by omega) (by omega)
  omega

/-- Degree-2 Prajna-Jadbabaie barrier `B(x, y) = y^2 - x + 1`. -/
def barrierParabolic (p : Int × Int) : Int :=
  p.2 * p.2 - p.1 + 1

/-- Exact Putinar SOS algebraic identity:
    `1 * (y^2 - x + 1) = 1 * (y - 2)^2 + 0 * 0^2 + (4y - x - 3) * (1 * 1^2)`. -/
theorem parabolic_putinar_sos_identity (x y : Int) :
    1 * barrierParabolic (x, y) =
      1 * ((y - 2) * (y - 2)) + 0 * (0 * 0) + guardParabolic (x, y) * (1 * (1 * 1)) := by
  unfold barrierParabolic guardParabolic
  dsimp
  have hSq : (y - 2) * (y - 2) = y * y - 4 * y + 4 := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
    omega
  rw [hSq]
  omega

/-- Exact conservation `ΔB = 0` along every surviving parabolic step. -/
theorem parabolic_barrier_conserved (p p' : Int × Int)
    (_hDom : DomParabolic p) (_hNeg : barrierParabolic p < 0)
    (hStep : stepParabolic p = some p') :
    barrierParabolic p' ≤ barrierParabolic p := by
  rcases p with ⟨x, y⟩
  unfold stepParabolic at hStep
  split at hStep
  · contradiction
  · injection hStep with hEq
    subst hEq
    unfold barrierParabolic
    dsimp
    have hSq : (y + 1) * (y + 1) = y * y + 2 * y + 1 := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]
      omega
    rw [hSq]
    omega

theorem domParabolic_preserved : IsInvariant stepParabolic DomParabolic := by
  intro p p' hDom hStep
  rcases p with ⟨x, y⟩
  unfold DomParabolic at hDom ⊢
  unfold stepParabolic at hStep
  split at hStep
  · contradiction
  · injection hStep with hEq
    subst hEq
    dsimp
    omega

/-- **Unconditional Non-Halting & Immortality of `stepParabolic` from `(2, 0)`**:
    Proves BOTH `IsNonHalting stepParabolic (2, 0)` (via `Stage 3c` Putinar SOS)
    AND pairwise state distinctness (`Δy = +1`), upgrading aperiodicity to immortality. -/
theorem parabolic_counter_nonHalting :
    IsNonHalting stepParabolic (2, 0) := by
  exact putinar_sos_barrier_nonHalting
    stepParabolic DomParabolic barrierParabolic guardParabolic
    (fun p => p.2 - 2) (fun _ => 0) (fun _ => 1)
    1 1 0 1
    (by omega) (by omega) (by omega) (by omega)
    domParabolic_preserved
    parabolic_barrier_conserved
    (fun p _ hNone => by
      unfold stepParabolic at hNone
      split at hNone
      · rename_i hG; exact hG
      · contradiction)
    (fun p _ => parabolic_putinar_sos_identity p.1 p.2)
    (2, 0) ⟨by omega, by omega⟩ (by decide)

theorem parabolic_counter_immortal :
    IsImmortalOrbit stepParabolic (2, 0) := by
  let SafeP : Int × Int → Prop := fun p => DomParabolic p ∧ barrierParabolic p < 0
  have hSafeInv : IsInvariant stepParabolic SafeP := by
    intro p p' hp hStep
    refine ⟨domParabolic_preserved p p' hp.1 hStep, ?_⟩
    have hLe := parabolic_barrier_conserved p p' hp.1 hp.2 hStep
    omega
  have hSafeStep : ∀ p : Int × Int, SafeP p → stepParabolic p ≠ none := by
    intro ⟨px, py⟩ hp hNone
    unfold stepParabolic at hNone
    split at hNone
    · rename_i hG
      have hGe := putinar_cleared_nonneg_of_guard
        (N := 1) (d0 := 1) (d1 := 0) (e0 := 1)
        (by omega) (by omega) (by omega) (by omega)
        (parabolic_putinar_sos_identity px py) hG
      have hLt := hp.2
      omega
    · contradiction
  have hDrift : ∀ p p' : Int × Int, SafeP p → stepParabolic p = some p' → p.2 + 1 ≤ p'.2 := by
    intro p p' _ hStep
    unfold stepParabolic at hStep
    split at hStep
    · contradiction
    · injection hStep with hEq; subst hEq; omega
  exact immortal_of_safe_invariant_and_drift
    stepParabolic SafeP (fun p => p.2) 1 (by omega)
    hSafeInv hSafeStep hDrift (2, 0) ⟨⟨by omega, by omega⟩, by decide⟩

/-! ## 3. Multi-Pivot Non-Integer Rational `LDL^T` Certificate on Coupled Bouncer -/

/-- Coupled 2D bouncer `(x, y) ↦ (x + 2y + 2, y + 1)` from `(3, 0)` with guard `4y - x - 1 ≥ 0`.
    Over `ℚ`, `B(x, y) - g(x, y) = y^2 - 3y + 3 = 3*(1 - y/2)^2 + (1/4)*y^2` (`d0 = 3, d1 = 1/4`).
    Clearing by `N = 4` gives the exact 2-pivot integer identity:
    `4 * B(x, y) = 3 * (2 - y)^2 + 1 * y^2 + (4y - x - 1) * (4 * 1^2)`. -/
def guardCoupledBouncer (p : Int × Int) : Int :=
  4 * p.2 - p.1 - 1

def stepCoupledBouncer (p : Int × Int) : Option (Int × Int) :=
  if 0 ≤ guardCoupledBouncer p then none
  else some (p.1 + 2 * p.2 + 2, p.2 + 1)

def barrierCoupledBouncer (p : Int × Int) : Int :=
  p.2 * p.2 + p.2 - p.1 + 2

theorem coupled_bouncer_2pivot_ldlt_identity (x y : Int) :
    4 * barrierCoupledBouncer (x, y) =
      3 * ((2 - y) * (2 - y)) + 1 * (y * y) + guardCoupledBouncer (x, y) * (4 * (1 * 1)) := by
  unfold barrierCoupledBouncer guardCoupledBouncer
  dsimp
  have hSq : (2 - y) * (2 - y) = 4 - 4 * y + y * y := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
    omega
  rw [hSq]
  omega

theorem coupled_bouncer_nonHalting :
    IsNonHalting stepCoupledBouncer (3, 0) := by
  exact putinar_sos_barrier_nonHalting
    stepCoupledBouncer (fun _ => True) barrierCoupledBouncer guardCoupledBouncer
    (fun p => 2 - p.2) (fun p => p.2) (fun _ => 1)
    4 3 1 4
    (by omega) (by omega) (by omega) (by omega)
    (fun _ _ _ _ => trivial)
    (fun p p' _ _ hStep => by
      rcases p with ⟨x, y⟩
      unfold stepCoupledBouncer at hStep
      split at hStep
      · contradiction
      · injection hStep with hEq
        subst hEq
        unfold barrierCoupledBouncer
        dsimp
        have hSq : (y + 1) * (y + 1) = y * y + 2 * y + 1 := by
          rw [Int.add_mul, Int.mul_add, Int.mul_add]
          omega
        rw [hSq]
        omega)
    (fun p _ hNone => by
      unfold stepCoupledBouncer at hNone
      split at hNone
      · rename_i hG; exact hG
      · contradiction)
    (fun p _ => coupled_bouncer_2pivot_ldlt_identity p.1 p.2)
    (3, 0) trivial (by decide)

/-! ## 4. Mechanistic `AppC_7` Quadratic Halting Gate Step-Count Law (`16b^2 + 28b + 15`) -/

/-- Exact raw-TM phase recurrence for `AppC_7` (`1RB1RC_1LC0LE_0RA1RD_1RF1LB_1LD0LA_---0RC`)
    on `<D:0> (10)^a (1110)^r 11 0^∞`:
      - `r = 0`: sweeps right across `(10)^a 11 00` and halts in `2a + 5` steps;
      - `r + 1`: converts one `(1110)` block into `(10)^4` (`a ↦ a + 4`) in `8a + 20` steps. -/
def appC7GateSweep (a : Nat) : Nat → Nat
  | 0 => 2 * a + 5
  | r + 1 => (8 * a + 20) + appC7GateSweep (a + 4) r

/-- Generalized parametric closed form for `appC7GateSweep a r`:
    `appC7GateSweep a r = 16 * r^2 + (8 * a + 12) * r + (2 * a + 5)`. -/
theorem appC7GateSweep_closed_form :
    ∀ (r a : Nat),
      appC7GateSweep a r = 16 * r * r + (8 * a + 12) * r + (2 * a + 5)
  | 0, a => by
      simp [appC7GateSweep]
  | r + 1, a => by
      simp only [appC7GateSweep]
      rw [appC7GateSweep_closed_form r (a + 4)]
      have hSq : 16 * (r + 1) * (r + 1) = 16 * r * r + 32 * r + 16 := by
        have h1 : (r + 1) * (r + 1) = r * r + 2 * r + 1 := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
          omega
        rw [Nat.mul_assoc 16 (r + 1) (r + 1), h1, Nat.mul_add, Nat.mul_add,
            ← Nat.mul_assoc 16 r r]
        omega
      have hLinR : (8 * (a + 4) + 12) * r = (8 * a + 12) * r + 32 * r := by
        have h2 : 8 * (a + 4) + 12 = (8 * a + 12) + 32 := by omega
        rw [h2, Nat.add_mul]
      have hLinR1 : (8 * a + 12) * (r + 1) = (8 * a + 12) * r + (8 * a + 12) := by
        rw [Nat.mul_add, Nat.mul_one]
      omega

/-- **Exact `AppC_7` Quadratic Halting Gate Theorem (`16b^2 + 28b + 15`)**:
    Entering `<D:0> (10)^2 (1110)^b 11` after the 6-step blank-left prefix on
    `<A:0> 00 (1110)^b 11` halts in exact step count `16 * b^2 + 28 * b + 15`. -/
theorem appC7_parabolic_gate_step_law (b : Nat) :
    6 + appC7GateSweep 2 b = 16 * b * b + 28 * b + 15 := by
  rw [appC7GateSweep_closed_form b 2]
  omega

end CryptidSolvePhase4
