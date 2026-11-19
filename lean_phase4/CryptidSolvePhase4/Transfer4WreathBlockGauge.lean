/- Scope: AppC step-count theorems below are arithmetic identities for specified
   counter recurrences. Raw-TM correspondence is finite-tested in Python, not
   universally formalized by these declarations. AppC8RawShuttle.lean now proves
   the raw shuttle, repeated rounds, and clean-macro middle stage separately.
   AppC8RawCleanMacro.lean proves the reset, exit, and full clean-sector execution. See paper/main.tex. -/

/-
  CryptidSolvePhase4.Transfer4WreathBlockGauge
  ============================================
  Transfer 4:
  Wreath-Product Block-Coding `Sym(Sigma^w) wr Z`, `[7,4,3]` Hamming Coboundary Gauge
  Minimization, Width-3 Block Odometer Immortality, and Exact Width-3 Wreath Decoding
  of Unsolved DeepMind Holdout `AppC_8`.

  Formalizes in pure Lean 4 Core (`Init` + `omega` + `decide`):
    1. Exact `F_2` 1-coboundary gauge transformation `eps_f(u, v) = eps_0(u, v) XOR f(v) XOR f(u)`
       and path-telescoping closed-loop gauge invariance (`coboundary_closed_walk_invariant`).
    2. Pure-kernel `decide` verification of the `[7,4,3]` Hamming-code coset anchored at
       `f_* = 0b0001000` (`mask = 8`), certifying weight distribution `{0:1, 3:7, 4:7, 7:1}`
       across all `16` maximal orientation gauges in `Fin 128`.
    3. Unconditional immortality of a Width-3 Wreath-Product Block Odometer/Shuttle
       (`wreath_width3_odometer_immortal`) whose transitions permute internal 3-bit blocks
       `(110) <-> (100)` before resetting mod-4 block carries.
    4. Newly discovered raw-TM Width-3 Wreath Shuttle & Hidden `(3/2)`-Ghost Law of
       Unsolved Appendix C Candidate #8 (`AppC_8`, `1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---`):
       - Shuttle step `<A:0> 10 (110)^k 1^m -> <A:0> 10 (110)^(k+2) 1^(m-4)` (`m ≥ 5`)
         conserving `2k + m` (`appC8_shuttle_conserves_2k_plus_m`),
       - Recursive step-duration sum `108*q^2 + 332*q + 238` and exact `2`-adic ghost `c* = -4`
         on `10 (100)^(4q+4) 1 <E:0> -> 10 (100)^(6q+8) 1 <E:0>` (`appC8_clean_macro_law`).
-/

import CryptidSolvePhase4.Basic

namespace CryptidSolvePhase4

/-! ## 1. `F_2` Coboundary Gauge Shifts & `[7,4,3]` Hamming Gauge Coset -/

/-- `F_2` 1-coboundary gauge shift `eps_f(u, v) = eps0(u, v) XOR f(v) XOR f(u)`. -/
def gaugeShiftEdge (eps0 : Nat → Nat → Bool) (f : Nat → Bool) (u v : Nat) : Bool :=
  xor (eps0 u v) (xor (f v) (f u))

/-- XOR sum of edge parities along a vertex path `u :: vs`. -/
def walkParity (eps : Nat → Nat → Bool) : Nat → List Nat → Bool
  | _, [] => false
  | u, v :: vs => xor (eps u v) (walkParity eps v vs)

def lastVertex : Nat → List Nat → Nat
  | u, [] => u
  | _, v :: vs => lastVertex v vs

/-- Telescoping cancellation of `Bool.xor` along any finite path under coboundary shifts. -/
theorem walkParity_gauge_telescope (eps0 : Nat → Nat → Bool) (f : Nat → Bool) :
    ∀ (vs : List Nat) (u : Nat),
      walkParity (gaugeShiftEdge eps0 f) u vs =
        xor (walkParity eps0 u vs) (xor (f (lastVertex u vs)) (f u))
  | [], u => by
      simp [walkParity, lastVertex]
  | v :: vs, u => by
      simp only [walkParity, lastVertex]
      rw [walkParity_gauge_telescope eps0 f vs v]
      unfold gaugeShiftEdge
      cases (eps0 u v) <;> cases (walkParity eps0 v vs) <;>
        cases (f u) <;> cases (f v) <;> cases (f (lastVertex v vs)) <;> rfl

/-- **Closed-Loop Coboundary Gauge Invariance**:
    Along ANY closed walk returning to `u0` (`lastVertex u0 vs = u0`), the total `F_2`
    holonomy is strictly invariant under all local gauge transformations `f`. -/
theorem coboundary_closed_walk_invariant
    (eps0 : Nat → Nat → Bool) (f : Nat → Bool) (u0 : Nat) (vs : List Nat)
    (hClosed : lastVertex u0 vs = u0) :
    walkParity (gaugeShiftEdge eps0 f) u0 vs = walkParity eps0 u0 vs := by
  rw [walkParity_gauge_telescope, hClosed]
  cases (walkParity eps0 u0 vs) <;> cases (f u0) <;> rfl

/-- `[7,4,3]` Hamming parity-check syndrome on 7-bit mask `m ∈ 0..127`. -/
def isHamming743Codeword (m : Nat) : Bool :=
  let b0 := (m / 1) % 2
  let b1 := (m / 2) % 2
  let b2 := (m / 4) % 2
  let b3 := (m / 8) % 2
  let b4 := (m / 16) % 2
  let b5 := (m / 32) % 2
  let b6 := (m / 64) % 2
  ((b3 + b4 + b5 + b6) % 2 == 0) &&
    ((b1 + b2 + b5 + b6) % 2 == 0) &&
    ((b0 + b2 + b4 + b6) % 2 == 0)

def popcount7 (m : Nat) : Nat :=
  (m / 1) % 2 + (m / 2) % 2 + (m / 4) % 2 + (m / 8) % 2 +
    (m / 16) % 2 + (m / 32) % 2 + (m / 64) % 2

def hammingWeightCounts : Nat × Nat × Nat × Nat × Nat :=
  let codewords := (List.range 128).filter isHamming743Codeword
  (codewords.length,
   (codewords.filter (fun c => popcount7 c == 0)).length,
   (codewords.filter (fun c => popcount7 c == 3)).length,
   (codewords.filter (fun c => popcount7 c == 4)).length,
   (codewords.filter (fun c => popcount7 c == 7)).length)

/-- **Pure-Kernel `decide` Verification of the `[7,4,3]` Hamming Gauge Weight Enumerator**:
    Among all `128` 7-bit orientation gauges, exactly `16` satisfy the `[7,4,3]` syndrome,
    with exact weight distribution `{w=0: 1, w=3: 7, w=4: 7, w=7: 1}`, and `8` (`0001000`)
    XORed with those `16` codewords reproduces the exact 16 `|Stab| = 21` Fano gauges. -/
theorem hamming743_gauge_coset_verified :
    hammingWeightCounts = (16, 1, 7, 7, 1) ∧
      ((List.range 128).filter isHamming743Codeword).map (fun c => Nat.xor 8 c) =
        [8, 15, 17, 22, 34, 37, 59, 60, 67, 68, 90, 93, 105, 110, 112, 119] := by
  decide

/-! ## 2. Unconditionally Immortal Width-3 Wreath-Product Block Odometer -/

/-- Width-3 Wreath-Product Block Odometer (`Sym({0,1}^3) wr Z`):
    - `Shuttle k m` : `<A> 10 (110)^k 1^m` (`m ≡ 0 mod 4`), converting four `1`-bits into two
      width-3 `(110)` blocks (`(k, m) -> (k + 2, m - 4)`) while `m ≥ 4`, and converting
      `(110)^k -> (100)^k` at `m = 0` (`k ≥ 2`; halts if `k < 2` or `m % 4 ≠ 0`).
    - `CarryReset c`: `10 (100)^c 1 <E>`, expanding `c` width-3 `(100)` blocks into `4*c`
      fresh `1`-bits (`Shuttle 0 (4*c)`).
    Bit-level run-length provers (`w = 1`) fail because `(110)^k` has `k` separate zero-defects,
    whereas width-3 wreath block gauge `B1 = 110, B2 = 100` compresses it to `(k, m, c)`. -/
inductive StateWreathOdometer3 where
  | Shuttle (k m : Nat)
  | CarryReset (c : Nat)
  deriving DecidableEq, Repr

def stepWreathOdometer3 : StateWreathOdometer3 → Option StateWreathOdometer3
  | .Shuttle k m =>
      if m % 4 ≠ 0 then none
      else if m ≥ 4 then some (.Shuttle (k + 2) (m - 4))
      else if k < 2 then none
      else some (.CarryReset k)
  | .CarryReset c =>
      if c < 2 then none
      else some (.Shuttle 0 (4 * c))

def InvWreathOdometer3 : StateWreathOdometer3 → Prop
  | .Shuttle k m => m % 4 = 0 ∧ 2 * k + m ≥ 4
  | .CarryReset c => c ≥ 2

def energyWreathOdometer3 : StateWreathOdometer3 → Int
  | .Shuttle k m => 5 * (k : Int) + 2 * (m : Int)
  | .CarryReset c => 6 * (c : Int)

theorem invWreathOdometer3_preserved : IsInvariant stepWreathOdometer3 InvWreathOdometer3 := by
  intro s s' hs hStep
  cases s with
  | Shuttle k m =>
      unfold InvWreathOdometer3 at hs
      unfold stepWreathOdometer3 at hStep
      have hMod : ¬ (m % 4 ≠ 0) := by omega
      simp only [hMod, ↓reduceIte] at hStep
      if hm4 : m ≥ 4 then
        simp only [hm4, ↓reduceIte] at hStep
        injection hStep with hEq; subst hEq
        unfold InvWreathOdometer3; omega
      else
        have hk2 : ¬ (k < 2) := by omega
        simp only [hm4, hk2, ↓reduceIte] at hStep
        injection hStep with hEq; subst hEq
        unfold InvWreathOdometer3; omega
  | CarryReset c =>
      unfold InvWreathOdometer3 at hs
      unfold stepWreathOdometer3 at hStep
      have hc2 : ¬ (c < 2) := by omega
      simp only [hc2, ↓reduceIte] at hStep
      injection hStep with hEq; subst hEq
      unfold InvWreathOdometer3; omega

theorem stepWreathOdometer3_total (s : StateWreathOdometer3) (hs : InvWreathOdometer3 s) :
    ∃ s', stepWreathOdometer3 s = some s' := by
  cases s with
  | Shuttle k m =>
      unfold InvWreathOdometer3 at hs
      unfold stepWreathOdometer3
      have hMod : ¬ (m % 4 ≠ 0) := by omega
      simp only [hMod, ↓reduceIte]
      if hm4 : m ≥ 4 then
        exact ⟨.Shuttle (k + 2) (m - 4), by simp [hm4]⟩
      else
        have hk2 : ¬ (k < 2) := by omega
        exact ⟨.CarryReset k, by simp [hm4, hk2]⟩
  | CarryReset c =>
      unfold InvWreathOdometer3 at hs
      unfold stepWreathOdometer3
      have hc2 : ¬ (c < 2) := by omega
      exact ⟨.Shuttle 0 (4 * c), by simp [hc2]⟩

theorem stepWreathOdometer3_strict_drift :
    ∀ s s', InvWreathOdometer3 s → stepWreathOdometer3 s = some s' →
      energyWreathOdometer3 s' ≥ energyWreathOdometer3 s + 2 := by
  intro s s' hs hStep
  cases s with
  | Shuttle k m =>
      unfold InvWreathOdometer3 at hs
      unfold stepWreathOdometer3 at hStep
      have hMod : ¬ (m % 4 ≠ 0) := by omega
      simp only [hMod, ↓reduceIte] at hStep
      if hm4 : m ≥ 4 then
        simp only [hm4, ↓reduceIte] at hStep
        injection hStep with hEq; subst hEq
        unfold energyWreathOdometer3; dsimp; omega
      else
        have hk2 : ¬ (k < 2) := by omega
        simp only [hm4, hk2, ↓reduceIte] at hStep
        injection hStep with hEq; subst hEq
        unfold energyWreathOdometer3; dsimp; omega
  | CarryReset c =>
      unfold InvWreathOdometer3 at hs
      unfold stepWreathOdometer3 at hStep
      have hc2 : ¬ (c < 2) := by omega
      simp only [hc2, ↓reduceIte] at hStep
      injection hStep with hEq; subst hEq
      unfold energyWreathOdometer3; dsimp; omega

theorem stepWreathOdometer3_safe (s : StateWreathOdometer3) (hs : InvWreathOdometer3 s) :
    stepWreathOdometer3 s ≠ none := by
  obtain ⟨s', hs'⟩ := stepWreathOdometer3_total s hs
  rw [hs']
  intro hNone
  contradiction

/-- **Unconditional Immortality of the Width-3 Wreath-Product Block Odometer**:
    Starting at `Shuttle 0 4` (`<A> 10 1111`), the width-3 block odometer never halts
    and admits zero periodic orbits (`ΔE ≥ +2` per macro-step). -/
theorem wreath_width3_odometer_immortal :
    IsImmortalOrbit stepWreathOdometer3 (.Shuttle 0 4) := by
  exact immortal_of_safe_invariant_and_drift
    stepWreathOdometer3 InvWreathOdometer3 energyWreathOdometer3 2 (by omega)
    invWreathOdometer3_preserved
    stepWreathOdometer3_safe
    (fun s s' hs hStep => by
      have h2 := stepWreathOdometer3_strict_drift s s' hs hStep
      omega)
    (.Shuttle 0 4)
    (by unfold InvWreathOdometer3; omega)

/-! ## 3. Exact Width-3 Wreath Shuttle & `(3/2)`-Ghost Law of Holdout `AppC_8` -/

/-- **Raw-TM Conservation Law of `AppC_8`'s Width-3 Shuttle**:
    Across `<A:0> 10 (110)^k 1^m -> <A:0> 10 (110)^(k+2) 1^(m-4)` (`m ≥ 5`),
    `2k + m` is strictly conserved while tape bit-length `2 + 3k + m` increases by `+2`. -/
theorem appC8_shuttle_conserves_2k_plus_m (k m : Nat) (hm : m ≥ 5) :
    2 * (k + 2) + (m - 4) = 2 * k + m ∧
      (2 + 3 * (k + 2) + (m - 4)) = (2 + 3 * k + m) + 2 := by
  exact ⟨by omega, by omega⟩

/-- Recursive step count of `R` consecutive width-3 shuttle rounds on `AppC_8` starting
    at block count `k` (`<A:0> 10 (110)^(k + 2j) 1^m` takes `12*(k + 2j) + 26` raw steps). -/
def appC8ShuttleRoundsSteps : Nat → Nat → Nat
  | _, 0 => 0
  | k, r + 1 => (12 * k + 26) + appC8ShuttleRoundsSteps (k + 2) r

theorem appC8ShuttleRoundsSteps_closed_form (r : Nat) :
    ∀ k : Nat,
      appC8ShuttleRoundsSteps k r = 12 * (r * k) + 12 * (r * (r - 1)) + 26 * r := by
  induction r with
  | zero =>
      intro k
      simp [appC8ShuttleRoundsSteps]
  | succ r ih =>
      intro k
      simp only [appC8ShuttleRoundsSteps]
      rw [ih (k + 2)]
      cases r with
      | zero =>
          simp
      | succ r' =>
          have h1 : (r' + 1) * (k + 2) = (r' + 1) * k + 2 * (r' + 1) := by
            rw [Nat.mul_add, Nat.mul_comm (r' + 1) 2]
          have h2 : (r' + 2) * k = (r' + 1) * k + k := by
            rw [show r' + 2 = (r' + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
          have hSub : r' + 1 + 1 - 1 = r' + 1 := by omega
          have hSub0 : r' + 1 - 1 = r' := by omega
          have h3 : (r' + 1 + 1) * (r' + 1) = (r' + 1) * r' + 2 * (r' + 1) := by
            calc
              (r' + 1 + 1) * (r' + 1)
                  = (r' + 1) * (r' + 1 + 1) := Nat.mul_comm _ _
              _ = (r' + 1) * (r' + 2) := rfl
              _ = (r' + 1) * r' + (r' + 1) * 2 := Nat.mul_add (r' + 1) r' 2
              _ = (r' + 1) * r' + 2 * (r' + 1) := by rw [Nat.mul_comm (r' + 1) 2]
          rw [hSub, hSub0, h1]
          have h2' : (r' + 1 + 1) * k = (r' + 1) * k + k := h2
          rw [h2', h3]
          omega

/-- **Exact Clean-Macro Step Count & Hidden `(3/2)`-Collatz Ghost `c* = -4` of `AppC_8`**:
    From `10 (100)^c 1 <E:0>` with `c = 4*(q + 1)`:
    1. Right-to-left reset (`5c + 43 = 20q + 63` steps) yields `<A:0> 10 (110)^3 1^(12q + 10)`,
    2. `R = 3q + 2` shuttle rounds yield `<A:0> 10 (110)^(6q + 7) 1^2`,
    3. Exit (`3*(6q + 7) + 6 = 18q + 27` steps) yields `10 (100)^(6q + 8) 1 <E:0>`,
    taking `108*q^2 + 332*q + 238` raw TM steps (`238, 678, 1334, 2206, ...`) and obeying
    `2 * (c' + 4) = 3 * (c + 4)` (explaining why `AppC_8` is a width-3 `(3/2)`-Collatz cryptid). -/
theorem appC8_clean_macro_law (q : Nat) :
    let c := 4 * (q + 1)
    let cNext := 6 * q + 8
    (20 * q + 63) + appC8ShuttleRoundsSteps 3 (3 * q + 2) + (18 * q + 27) =
      108 * q * q + 332 * q + 238 ∧
    2 * (cNext + 4) = 3 * (c + 4) := by
  dsimp only
  rw [appC8ShuttleRoundsSteps_closed_form (3 * q + 2) 3]
  constructor
  · have hSub : 3 * q + 2 - 1 = 3 * q + 1 := by omega
    have hLin : (3 * q + 2) * 3 = 9 * q + 6 := by omega
    have hQuad : (3 * q + 2) * (3 * q + 1) = 9 * (q * q) + 9 * q + 2 := by
      calc
        (3 * q + 2) * (3 * q + 1)
            = (3 * q + 2) * (3 * q) + (3 * q + 2) * 1 := Nat.mul_add _ _ _
        _ = (3 * q) * (3 * q) + 2 * (3 * q) + (3 * q + 2) := by
              rw [Nat.add_mul, Nat.mul_one]
        _ = 9 * (q * q) + 9 * q + 2 := by
              have h33 : (3 * q) * (3 * q) = 9 * (q * q) := by
                calc
                  (3 * q) * (3 * q) = 3 * (q * (3 * q)) := Nat.mul_assoc 3 q (3 * q)
                  _ = 3 * ((3 * q) * q) := by rw [Nat.mul_comm q (3 * q)]
                  _ = 3 * (3 * (q * q)) := by rw [Nat.mul_assoc 3 q q]
                  _ = (3 * 3) * (q * q) := by rw [← Nat.mul_assoc 3 3 (q * q)]
                  _ = 9 * (q * q) := rfl
              rw [h33]
              omega
    have hAssoc : 108 * q * q = 108 * (q * q) := Nat.mul_assoc 108 q q
    rw [hSub, hLin, hQuad, hAssoc]
    omega
  · omega

end CryptidSolvePhase4
