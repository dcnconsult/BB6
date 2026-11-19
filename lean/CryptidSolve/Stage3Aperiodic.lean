/-
  CryptidSolve.Stage3Aperiodic
  ============================
  Unconditional Global Aperiodicity Certificates (`¬ IsPeriodic`) across all
  10 non-tower Appendix A Cryptids (`A.1`–`A.10`), `Cryptid B.9`, and `BMO #8`
  (with `Cryptid A.11` formalized separately in `CryptidSolve.CryptidA11`):

    - Stage-3a Left-Nullspace Certificates (`⋂ ker(M_k^T - I) ≠ {0}`):
        `A.1`, `A.2`, `A.4`, `A.5`, `A.6`, `A.10`, `B.9`, `BMO #8`
    - Stage-3b Positive-Orthant Dual Certificates (`⋂ ker(M_k^T - I) = {0}`, `D_ret = 2`):
        `A.3`, `A.7`, `A.8`, `A.9` (on `R-F` boundary coordinates)
-/

import CryptidSolve.Stage1Invariants

namespace CryptidSolve

/-! ## 1. Cryptid A.1 — 4D Lexicographic Lyapunov `(E_A1, d)` -/

def energyA1 (s : StateA1) : Nat :=
  s.a + 2 * s.b + 2 * s.c + s.d +
    if s.c = 0 ∧ s.a = 0 then
      if s.d = 0 then 3 else if s.d = 1 then 1 else 2
    else 0

def rankA1 (s : StateA1) : Nat := s.d

theorem a1_lex_drift (s s' : StateA1) (hs : InvA1 s) (hStep : stepA1 s = some s') :
    LexProgress energyA1 rankA1 s s' := by
  cases s with
  | mk a b c d =>
    unfold InvA1 at hs
    unfold LexProgress energyA1 rankA1
    dsimp only [stepA1] at hStep
    cryptid_step_omega hStep

theorem a1_no_periodic_orbits (s : StateA1) (hs : InvA1 s) :
    ¬ IsPeriodic stepA1 s :=
  no_periodic_of_lex_lyapunov stepA1 InvA1 energyA1 rankA1 invA1_preserved a1_lex_drift s hs

/-! ## 2. Cryptids A.2 & A.10 — Unified Epoch Energy `4L + 2R + 1_{R>0}` -/

def stepA2Epoch (s : Nat × Nat) : Option (Nat × Nat) :=
  let L := s.1
  let R := s.2
  if R ≥ 2 * L + 4 then some (2 * L + 3, R - 2 * L - 4)
  else if R = 2 * L + 3 then none
  else
    let k := if R ≥ 3 then (R - 1) / 2 else 0
    if L - k = 0 then some (0, 2 * (2 * k) + 2 * (R - 2 * k) + 1)
    else if L - k = 1 then some (0, 2 * (2 * k) + 2 * (R - 2 * k) + 2)
    else some (L - k - 1, 2 * (2 * k) + 2 * (R - 2 * k) + 2)

def stepA10Epoch (s : Nat × Nat) : Option (Nat × Nat) :=
  let L := s.1
  let R := s.2
  if R ≥ 2 * L + 4 then some (2 * L + 3, R - 2 * L - 4)
  else if R = 2 * L + 3 then none
  else
    let k := if R ≥ 3 then (R - 1) / 2 else 0
    if L - k = 0 then some (1, 2 * (2 * k) + 2 * (R - 2 * k) + 1)
    else if L - k = 1 then some (1, 2 * (2 * k) + 2 * (R - 2 * k) + 2)
    else some (L - k - 2, 2 * (2 * k) + 2 * (R - 2 * k) + 4)

def energyCousinEpoch (s : Nat × Nat) : Nat :=
  4 * s.1 + 2 * s.2 + (if s.2 = 0 then 0 else 1)

theorem a2_strict_drift (s s' : Nat × Nat) (_ : True) (hStep : stepA2Epoch s = some s') :
    energyCousinEpoch s + 1 ≤ energyCousinEpoch s' := by
  cases s with
  | mk L R =>
    unfold energyCousinEpoch
    dsimp only [stepA2Epoch] at hStep
    cryptid_step_omega hStep

theorem a2_no_periodic_orbits (s : Nat × Nat) :
    ¬ IsPeriodic stepA2Epoch s :=
  no_periodic_of_strict_lyapunov stepA2Epoch (fun _ => True) energyCousinEpoch 1 (by omega)
    (fun _ _ _ _ => trivial) a2_strict_drift s trivial

theorem a10_strict_drift (s s' : Nat × Nat) (_ : True) (hStep : stepA10Epoch s = some s') :
    energyCousinEpoch s + 1 ≤ energyCousinEpoch s' := by
  cases s with
  | mk L R =>
    unfold energyCousinEpoch
    dsimp only [stepA10Epoch] at hStep
    cryptid_step_omega hStep

theorem a10_no_periodic_orbits (s : Nat × Nat) :
    ¬ IsPeriodic stepA10Epoch s :=
  no_periodic_of_strict_lyapunov stepA10Epoch (fun _ => True) energyCousinEpoch 1 (by omega)
    (fun _ _ _ _ => trivial) a10_strict_drift s trivial

/-! ## 3. Cryptid A.3 — Complete 16-Branch Division-Free 2D Return Map (`Δ(k+m) ≥ 2`) -/

def stepA3 (s : Nat × Nat × Nat) : Option (Nat × Nat × Nat) :=
  let k := s.1
  let m := s.2.1
  let r := s.2.2
  if (k = 1 ∧ (m = 1 ∨ m = 2)) ∨ (k ≥ 2 ∧ (m = k ∨ m = k + 1)) then none
  else if m = 1 then
    if k = 2 then
      if r = 0 then some (3, 3, 1) else some (6, 1, 0)
    else
      if r = 0 then some (k - 2, 5, 0) else some (k - 2, 6, 1)
  else if k = 1 then
    if m = 3 then
      if r = 0 then some (6, 1, 0) else some (6, 3, 1)
    else
      if r = 0 then some (m - 3, 6, 1) else some (m - 3, 8, 0)
  else if k > m then
    if k = m + 1 then
      if r = 0 then some (3 * m, 3, 1) else some (3 * m + 3, 1, 0)
    else
      if r = 0 then some (k - m - 1, 3 * m + 2, 0) else some (k - m - 1, 3 * m + 3, 1)
  else
    if m = k + 2 then
      if r = 0 then some (3 * k + 3, 1, 0) else some (3 * k + 3, 3, 1)
    else
      if r = 0 then some (m - k - 2, 3 * k + 3, 1) else some (m - k - 2, 3 * k + 5, 0)

def InvA3 (s : Nat × Nat × Nat) : Prop :=
  s.1 ≥ 1 ∧ s.2.1 ≥ 1 ∧ s.2.2 ≤ 1

def energyA3 (s : Nat × Nat × Nat) : Nat := s.1 + s.2.1

theorem invA3_preserved : IsInvariant stepA3 InvA3 := by
  intro ⟨k, m, r⟩ s' hs hStep
  unfold InvA3 at hs ⊢
  dsimp only [stepA3] at hStep
  cryptid_step_omega hStep

theorem a3_strict_drift (s s' : Nat × Nat × Nat) (hs : InvA3 s) (hStep : stepA3 s = some s') :
    energyA3 s + 2 ≤ energyA3 s' := by
  cases s with
  | mk k mr =>
    cases mr with
    | mk m r =>
      unfold InvA3 at hs
      unfold energyA3
      dsimp only [stepA3] at hStep
      cryptid_step_omega hStep

theorem a3_no_periodic_orbits (s : Nat × Nat × Nat) (hs : InvA3 s) :
    ¬ IsPeriodic stepA3 s :=
  no_periodic_of_strict_lyapunov stepA3 InvA3 energyA3 2 (by omega)
    invA3_preserved a3_strict_drift s hs

/-! ## 4. Cryptid A.4 — Single-Step Global Lyapunov `E = 2a + b` (`ΔE ≥ 1`) -/

def energyA4 (s : Nat × Nat) : Nat := 2 * s.1 + s.2

theorem a4_strict_drift (s s' : Nat × Nat) (_ : True) (hStep : stepA4 s = some s') :
    energyA4 s + 1 ≤ energyA4 s' := by
  cases s with
  | mk a b =>
    unfold energyA4
    dsimp only [stepA4] at hStep
    cryptid_step_omega hStep

theorem a4_no_periodic_orbits (s : Nat × Nat) :
    ¬ IsPeriodic stepA4 s :=
  no_periodic_of_strict_lyapunov stepA4 (fun _ => True) energyA4 1 (by omega)
    (fun _ _ _ _ => trivial) a4_strict_drift s trivial

/-! ## 5. Cryptid A.5 — Shuttle-Complete Lexicographic Lyapunov `(E_A5, da)` -/

def energyA5 : StateA5 → Nat
  | .C L R => 2 * L + R
  | .D da du dw => 2 * da + du + dw

def rankA5 : StateA5 → Nat
  | .C _ _ => 0
  | .D da _ _ => da

theorem a5_lex_drift (s s' : StateA5) (hs : InvA5 s) (hStep : stepA5 s = some s') :
    LexProgress energyA5 rankA5 s s' := by
  cases s <;> unfold InvA5 at hs <;>
    unfold LexProgress energyA5 rankA5 <;> dsimp only [stepA5] at hStep
  all_goals cryptid_step_omega hStep

theorem a5_no_periodic_orbits (s : StateA5) (hs : InvA5 s) :
    ¬ IsPeriodic stepA5 s :=
  no_periodic_of_lex_lyapunov stepA5 InvA5 energyA5 rankA5 invA5_preserved a5_lex_drift s hs

/-! ## 6. Cryptid A.6 — Tape-Width & Sawtooth Lyapunov (`ΔE_A6 ≥ 3`) -/

def energyA6 : StateA6 → Nat
  | .DR b c eps => (if b > 0 then 6 + 2 * b + c else c) + 2 * eps
  | .LE k m => 2 * k + m + 5

theorem a6_strict_drift (s s' : StateA6) (hs : InvA6 s) (hStep : stepA6 s = some s') :
    energyA6 s + 3 ≤ energyA6 s' := by
  cases s <;> unfold InvA6 at hs <;>
    unfold energyA6 <;> dsimp only [stepA6] at hStep
  all_goals cryptid_step_omega hStep

theorem a6_no_periodic_orbits (s : StateA6) (hs : InvA6 s) :
    ¬ IsPeriodic stepA6 s :=
  no_periodic_of_strict_lyapunov stepA6 InvA6 energyA6 3 (by omega)
    invA6_preserved a6_strict_drift s hs

/-! ## 7. Cryptid A.7 — Stage-3b Positive-Orthant Certificate (`Δ(b+c) ≥ 3`) -/

def energyA7 (s : Nat × Nat) : Nat := s.1 + s.2

theorem a7_strict_drift (s s' : Nat × Nat) (hs : InvA7 s) (hStep : stepA7 s = some s') :
    energyA7 s + 3 ≤ energyA7 s' := by
  cases s with
  | mk b c =>
    unfold InvA7 at hs
    unfold energyA7
    dsimp only [stepA7] at hStep
    if hb0 : b = 0 then
      rw [if_pos hb0] at hStep; cryptid_step_omega hStep
    else
      rw [if_neg hb0] at hStep
      if hb40 : b % 4 = 0 then
        rw [if_pos hb40] at hStep; cryptid_step_omega hStep
      else
        rw [if_neg hb40] at hStep
        if hb41 : b % 4 = 1 then
          rw [if_pos hb41] at hStep; cryptid_step_omega hStep
        else
          rw [if_neg hb41] at hStep
          if hb42 : b % 4 = 2 then
            rw [if_pos hb42] at hStep; cryptid_step_omega hStep
          else
            rw [if_neg hb42] at hStep; cryptid_step_omega hStep

theorem a7_no_periodic_orbits (s : Nat × Nat) (hs : InvA7 s) :
    ¬ IsPeriodic stepA7 s :=
  no_periodic_of_strict_lyapunov stepA7 InvA7 energyA7 3 (by omega)
    invA7_preserved a7_strict_drift s hs

/-! ## 8. Cryptid A.8 — Stage-3b Positive-Orthant Certificate (`Δ(a+b) ≥ 7`) -/

def energyA8 (s : Nat × Nat) : Nat := s.1 + s.2

theorem a8_strict_drift (s s' : Nat × Nat) (hs : InvA8 s) (hStep : stepA8 s = some s') :
    energyA8 s + 7 ≤ energyA8 s' := by
  cases s with
  | mk a b =>
    unfold InvA8 at hs
    unfold energyA8
    dsimp only [stepA8] at hStep
    cryptid_step_omega hStep

theorem a8_no_periodic_orbits (s : Nat × Nat) (hs : InvA8 s) :
    ¬ IsPeriodic stepA8 s :=
  no_periodic_of_strict_lyapunov stepA8 InvA8 energyA8 7 (by omega)
    invA8_preserved a8_strict_drift s hs

/-! ## 9. Cryptid A.9 — Stage-3b Mirror-Cousin Certificate (`Δ(u+v) ≥ 3`) -/

def energyA9 (s : Nat × Nat) : Nat := s.1 + s.2

theorem a9_strict_drift (s s' : Nat × Nat) (hs : InvA9 s) (hStep : stepA9 s = some s') :
    energyA9 s + 3 ≤ energyA9 s' := by
  cases s with
  | mk u v =>
    unfold InvA9 at hs
    unfold energyA9
    dsimp only [stepA9] at hStep
    cryptid_step_omega hStep

theorem a9_no_periodic_orbits (s : Nat × Nat) (hs : InvA9 s) :
    ¬ IsPeriodic stepA9 s :=
  no_periodic_of_strict_lyapunov stepA9 InvA9 energyA9 3 (by omega)
    invA9_preserved a9_strict_drift s hs

/-! ## 10. Cryptid B.9 — Base-2 Sawtooth Lyapunov `2(2x+y) + 1_{y ≠ 2x+3}` (`ΔE ≥ 1`) -/

def stepB9 (s : Nat × Nat) : Option (Nat × Nat) :=
  let x := s.1
  let y := s.2
  if y ≥ 2 * x + 4 then some (2 * x + 2, y - 2 * x - 3)
  else if y = 2 * x + 3 then some (2 * x + 1, 1)
  else if y = 2 * x + 2 then some (0, 4 * x + 6)
  else if y = 2 * x + 1 then some (0, 4 * x + 4)
  else if y = 2 * x then none
  else if y + 1 = 2 * x then some (0, 4 * x + 6)
  else if y + 2 = 2 * x then some (0, 4 * x)
  else if y + 3 = 2 * x then some (2 * x, 1)
  else if y + 4 = 2 * x then some (0, 4 * x + 2)
  else some (2 * (y / 2) + 4, 2 * x - 2 * (y / 2) - 5 + 2 * (y % 2))

def energyB9 (s : Nat × Nat) : Nat :=
  2 * (2 * s.1 + s.2) + (if s.2 = 2 * s.1 + 3 then 0 else 1)

theorem b9_strict_drift (s s' : Nat × Nat) (_ : True) (hStep : stepB9 s = some s') :
    energyB9 s + 1 ≤ energyB9 s' := by
  cases s with
  | mk x y =>
    unfold energyB9
    dsimp only [stepB9] at hStep
    if h1 : y ≥ 2 * x + 4 then
      rw [if_pos h1] at hStep; cryptid_step_omega hStep
    else
      rw [if_neg h1] at hStep
      if h2 : y = 2 * x + 3 then
        rw [if_pos h2] at hStep; cryptid_step_omega hStep
      else
        rw [if_neg h2] at hStep
        if h3 : y = 2 * x + 2 then
          rw [if_pos h3] at hStep; cryptid_step_omega hStep
        else
          rw [if_neg h3] at hStep
          if h4 : y = 2 * x + 1 then
            rw [if_pos h4] at hStep; cryptid_step_omega hStep
          else
            rw [if_neg h4] at hStep; cryptid_step_omega hStep

theorem b9_no_periodic_orbits (s : Nat × Nat) :
    ¬ IsPeriodic stepB9 s :=
  no_periodic_of_strict_lyapunov stepB9 (fun _ => True) energyB9 1 (by omega)
    (fun _ _ _ _ => trivial) b9_strict_drift s trivial

/-! ## 11. BMO #8 — Rank-1 Left-Nullspace Drift `Δ(a+c) ∈ {3, 5}` -/

def energyBMO8 (s : Nat × Nat) : Nat := s.1 + s.2

theorem bmo8_drift_3_or_5 (s s' : Nat × Nat) (hs : InvBMO8 s)
    (hStep : stepBMO8 s = some s') :
    energyBMO8 s' = energyBMO8 s + 3 ∨ energyBMO8 s' = energyBMO8 s + 5 := by
  cases s with
  | mk a c =>
    unfold InvBMO8 at hs
    unfold energyBMO8
    dsimp only [stepBMO8] at hStep
    cryptid_step_omega hStep

theorem bmo8_strict_drift (s s' : Nat × Nat) (hs : InvBMO8 s)
    (hStep : stepBMO8 s = some s') :
    energyBMO8 s + 3 ≤ energyBMO8 s' := by
  have h35 := bmo8_drift_3_or_5 s s' hs hStep
  omega

theorem bmo8_no_periodic_orbits (s : Nat × Nat) (hs : InvBMO8 s) :
    ¬ IsPeriodic stepBMO8 s :=
  no_periodic_of_strict_lyapunov stepBMO8 InvBMO8 energyBMO8 3 (by omega)
    invBMO8_preserved bmo8_strict_drift s hs

end CryptidSolve
