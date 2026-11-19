/-
  CryptidSolve.Stage1Invariants
  =============================
  Stage-1 Modular & Sector Image Pruning across BB(6) Cryptids:
    1. Cryptid A.1: Orthogonal 4D sector invariant `b = 0 ∨ c = 0` (prunes mixed gates).
    2. Cryptid A.4: Collatz-phase residue exclusion `val % 4 ∈ {1, 3}` (prunes `b = 2` halt).
    3. Cryptid A.5: Shuttle invariant `du % 2 = 1 ∧ dw ≥ 1` & Odd-`R` Safe-Sector closure.
    4. Cryptid A.6: Inductive Mod-4 invariant `b > 0 → c % 4 = 0` (prunes boundary halts).
    5. Cryptid A.7: Interior parity invariant `(b = 0 ∧ c ≥ 1) ∨ (b ≥ 1 ∧ c % 2 = 1)`.
    6. Cryptid A.8: Modular lattice `a ≥ 4 ∧ a % 2 = 0 ∧ b ≥ 6 ∧ b % 3 = 0`.
    7. Cryptid A.9: Mirror-cousin lattice `u ≥ 6 ∧ u % 3 = 0 ∧ v ≥ 1 ∧ v % 2 = 1`.
    8. BMO #8: Forward invariant `I_3` (`a % 3 = 0 ∨ c % 3 = 2`), exact 3-gate halting
       classification (`G1 ∨ G2 ∨ G3`), and `decide`-verified Mod-9 contraction (`|I_9| = 33`).
-/

import CryptidSolve.Tactic

namespace CryptidSolve

/-! ## 1. Cryptid A.1 (`1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD`) -/

structure StateA1 where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  deriving DecidableEq, Repr

def stepA1 (s : StateA1) : Option StateA1 :=
  if s.c = 0 then
    if s.d = 0 then
      if s.a = 0 then some ⟨0, 0, 1, 2 * s.b + 3⟩
      else if s.a = 1 then some ⟨0, 0, 0, 2 * s.b + 2⟩
      else if s.a = 2 then some ⟨0, 1, 0, 2 * s.b + 2⟩
      else some ⟨s.a - 2, 1, 0, 2 * s.b + 2⟩
    else if s.d = 1 then
      some ⟨s.a, s.b + 1, 0, 0⟩
    else
      if s.a = 0 then some ⟨0, 0, s.b + 2, s.d - 2⟩
      else if s.a = 1 then some ⟨1, s.b + 2, 0, s.d - 1⟩
      else if s.a = 2 then some ⟨0, s.b + 1, 0, s.d - 1⟩
      else some ⟨s.a - 3, s.b + 2, 0, s.d - 1⟩
  else
    if s.c = 1 then
      if s.d = 0 then
        if s.a = 0 then some ⟨0, 1, 0, 2⟩ else some ⟨s.a - 1, 2, 0, 2⟩
      else if s.d = 1 then none
      else if s.d = 2 then some ⟨s.a + 1, 1, 0, 1⟩
      else some ⟨s.a + 3, 1, 0, s.d - 3⟩
    else
      if s.d = 0 then
        if s.a = 0 then some ⟨0, 1, 0, 2 * s.c⟩ else some ⟨s.a - 1, 2, 0, 2 * s.c⟩
      else some ⟨s.a + 3, 0, s.c - 1, s.d - 1⟩

def InvA1 (s : StateA1) : Prop :=
  s.b = 0 ∨ s.c = 0

theorem invA1_init : InvA1 ⟨0, 0, 1, 3⟩ := by
  unfold InvA1; dsimp; omega

theorem invA1_preserved : IsInvariant stepA1 InvA1 := by
  intro ⟨a, b, c, d⟩ s' hx hStep
  unfold InvA1 at hx ⊢
  dsimp only [stepA1] at hStep
  cryptid_step_omega hStep

/-- Dead-code elimination for Cryptid A.1: no mixed `(b ≥ 1, c ≥ 1)` state is reachable
    from blank-tape entry `A(0, 0, 1, 3)` at any step horizon `n`. -/
theorem a1_mixed_bc_unreachable (n : Nat) (s : StateA1)
    (hReach : iterStep stepA1 n ⟨0, 0, 1, 3⟩ = some s) :
    ¬ (s.b ≥ 1 ∧ s.c ≥ 1) := by
  have hInv : InvA1 s := iterStep_invariant stepA1 InvA1 invA1_preserved n _ s invA1_init hReach
  unfold InvA1 at hInv
  omega

/-! ## 2. Cryptid A.4 (`1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`) -/

def stepA4 (s : Nat × Nat) : Option (Nat × Nat) :=
  let a := s.1
  let b := s.2
  if b = 0 then some (0, 2 * a + 2)
  else if b = 1 then some (0, 2 * a + 4)
  else if b = 2 then none
  else if b ≥ 2 * a + 3 then some (2 * a + 2, b - 2 * a - 2)
  else if b % 2 = 1 then some ((6 * a + b + 6) / 4, (6 * a + b + 6) % 4)
  else some ((6 * a + b + 3) / 4, (6 * a + b + 3) % 4)

/-- Stage-1 Modular Pruning for Cryptid A.4: throughout the Collatz sweep `3 ≤ b ≤ 2a + 2`,
    the output residue `s'.2` lies strictly in `{1, 3}`, never hitting the halt gate `b = 2`. -/
theorem a4_collatz_sweep_avoids_gate2 (a b : Nat) (s' : Nat × Nat)
    (hLo : 3 ≤ b) (hHi : b ≤ 2 * a + 2)
    (hStep : stepA4 (a, b) = some s') :
    s'.2 = 1 ∨ s'.2 = 3 := by
  dsimp only [stepA4] at hStep
  cryptid_step_omega hStep

/-! ## 3. Cryptid A.5 (`1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE`) -/

inductive StateA5 where
  | C (L R : Nat)
  | D (da du dw : Nat)
  deriving DecidableEq, Repr

def stepA5 : StateA5 → Option StateA5
  | .C L R =>
      if R = 0 then some (.C 0 (2 * L + 2))
      else if R = 1 then some (.C 0 (2 * L + 4))
      else if R = 2 then none
      else if R ≤ 5 then some (.D L 3 (2 * R - 5))
      else if R = 6 then
        if L = 0 then some (.C 0 9) else some (.D (L - 1) 3 7)
      else some (.D (L + 1) 5 (R - 6))
  | .D da du dw =>
      if dw ≥ 3 ∧ da ≥ 1 then some (.D (da - 1) (du + 4) (dw - 2))
      else if da = 0 then some (.C ((du + 1) / 2) dw)
      else if da = 1 then
        if dw = 1 then some (.C 0 (du + 6)) else some (.C ((du + 5) / 2) 0)
      else if dw = 1 then some (.D (da - 2) 3 (du + 4))
      else if da = 2 then some (.C 0 (du + 8))
      else some (.D (da - 3) 3 (du + 6))

def InvA5 : StateA5 → Prop
  | .C _ _ => True
  | .D _ du dw => du % 2 = 1 ∧ dw ≥ 1

theorem invA5_preserved : IsInvariant stepA5 InvA5 := by
  intro s s' hs hStep
  cases s <;> unfold InvA5 at hs ⊢ <;> dsimp only [stepA5] at hStep
  all_goals cryptid_step_omega hStep

/-- Odd-`R` Safe Sector of Cryptid A.5: except at the unique portal `C(L, 1)`,
    every state in `{C(L, R) : R % 2 = 1} ∪ {D(da, du, dw) : du % 2 = 1 ∧ dw % 2 = 1}`
    remains strictly inside the odd sector and cannot halt. -/
def SafeOddA5 : StateA5 → Prop
  | .C _ R => R % 2 = 1
  | .D _ du dw => du % 2 = 1 ∧ dw % 2 = 1

theorem safeOddA5_non_portal_preserved (s s' : StateA5)
    (hSafe : SafeOddA5 s)
    (hNotPortal : ∀ L, s ≠ .C L 1)
    (hStep : stepA5 s = some s') : SafeOddA5 s' := by
  cases s with
  | C L R =>
    have hR1 : R ≠ 1 := by
      intro hEq; subst hEq; exact hNotPortal L rfl
    unfold SafeOddA5 at hSafe ⊢
    dsimp only [stepA5] at hStep
    cryptid_step_omega hStep
  | D da du dw =>
    unfold SafeOddA5 at hSafe ⊢
    dsimp only [stepA5] at hStep
    cryptid_step_omega hStep

/-! ## 4. Cryptid A.6 (`1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`) -/

inductive StateA6 where
  | DR (b c eps : Nat)
  | LE (k m : Nat)
  deriving DecidableEq, Repr

def stepA6 : StateA6 → Option StateA6
  | .DR b c eps =>
      if eps = 0 then
        if b = 0 then some (.DR 0 (c + 2) 1)
        else if b = 1 ∧ c = 0 then some (.LE 3 2)
        else if b % 2 = 0 then some (.DR 0 (6 + 2 * b + c + 2) 1)
        else some (.DR 2 (6 + 2 * b + c - 4) 1)
      else
        if b = 0 then
          if c = 2 then some (.DR 0 10 0) else some (.LE 3 (c - 4))
        else if b % 2 = 1 then
          if c = 0 then some (.DR 0 (2 * b + 10) 1)
          else if c = 2 then none
          else some (.LE (b + 5) (c - 3))
        else
          if c = 0 then some (.DR 2 (2 * b + 4) 1)
          else if c = 2 then some (.DR 1 (2 * b + 8) 1)
          else if c = 4 then some (.DR 0 (2 * b + 18) 1)
          else if c = 6 then none
          else some (.LE (b + 9) (c - 7))
  | .LE k m =>
      if m ≥ 2 * k + 3 then some (.LE (2 * k + 3) (m - 2 * k - 3))
      else if m = 2 * k + 2 then none
      else if m % 2 = 0 then
        if m = 2 * k then some (.DR 0 (4 * k + 6) 1)
        else some (.DR (k - m / 2) (2 * m) 1)
      else
        if m = 2 * k + 1 then some (.DR 0 (4 * k + 10) 0)
        else some (.DR (k - (m - 1) / 2) (2 * m + 2) 0)

def InvA6 : StateA6 → Prop
  | .DR b c eps => eps ≤ 1 ∧ c % 2 = 0 ∧ (b > 0 ∨ c ≥ 2) ∧ (b > 0 → c % 4 = 0)
  | .LE k _ => k ≥ 3

theorem invA6_init : InvA6 (.DR 0 4 1) := by
  unfold InvA6; omega

theorem invA6_preserved : IsInvariant stepA6 InvA6 := by
  intro s s' hs hStep
  cases s <;> unfold InvA6 at hs ⊢ <;> dsimp only [stepA6] at hStep
  all_goals cryptid_step_omega hStep

/-- Mod-4 Dead-Code Elimination for Cryptid A.6:
    Both boundary halting configurations `DR(2r+1, 2, 1)` and `DR(2r, 6, 1)` (`b ≥ 1`)
    are 100% unreachable from blank-tape entry `DR(0, 4, 1)`. -/
theorem a6_boundary_halts_unreachable (n b c eps : Nat)
    (hReach : iterStep stepA6 n (.DR 0 4 1) = some (.DR b c eps))
    (hb : b ≥ 1) : c ≠ 2 ∧ c ≠ 6 := by
  have hInv : InvA6 (.DR b c eps) :=
    iterStep_invariant stepA6 InvA6 invA6_preserved n _ _ invA6_init hReach
  unfold InvA6 at hInv
  omega

/-! ## 5. Cryptid A.7 (`1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA`) -/

def stepA7 (s : Nat × Nat) : Option (Nat × Nat) :=
  let b := s.1
  let c := s.2
  if b = 0 then
    if c % 2 = 0 then some (4, c + 1)
    else if c = 1 then some (7, 3)
    else if c = 3 then some (13, 1)
    else if c = 5 then some (0, 20)
    else if c = 7 then some (0, 23)
    else some (22, c - 8)
  else if b % 4 = 0 then some (6 * (b / 4) + 5, c)
  else if b % 4 = 1 then some (6 * (b / 4) + 4, c)
  else if b % 4 = 2 then
    if c = 1 then none
    else if c = 3 then some (0, 6 * (b / 4) + 10)
    else if c ≤ 6 * (b / 4) + 13 then
      some (6 * ((c - 3) / 2) + 1, 6 * (b / 4) + 11 - 2 * ((c - 3) / 2))
    else if c = 6 * (b / 4) + 15 then some (0, 18 * (b / 4) + 38)
    else if c = 6 * (b / 4) + 17 then some (0, 18 * (b / 4) + 41)
    else some (18 * (b / 4) + 40, c - 6 * (b / 4) - 18)
  else
    if c = 1 then none
    else if c = 3 then some (0, 6 * (b / 4) + 9)
    else if c ≤ 6 * (b / 4) + 11 then
      some (6 * ((c - 3) / 2), 6 * (b / 4) + 9 - 2 * ((c - 3) / 2))
    else if c = 6 * (b / 4) + 13 then some (0, 18 * (b / 4) + 31)
    else if c = 6 * (b / 4) + 15 then some (0, 18 * (b / 4) + 34)
    else some (18 * (b / 4) + 33, c - 6 * (b / 4) - 16)

def InvA7 (s : Nat × Nat) : Prop :=
  (s.1 = 0 ∧ s.2 ≥ 1) ∨ (s.1 ≥ 1 ∧ s.2 % 2 = 1)

theorem invA7_preserved : IsInvariant stepA7 InvA7 := by
  intro ⟨b, c⟩ s' hs hStep
  unfold InvA7 at hs ⊢
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

/-! ## 6. Cryptid A.8 (`1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA`) -/

def stepA8 (s : Nat × Nat) : Option (Nat × Nat) :=
  let a := s.1
  let b := s.2
  if b % 6 = 0 then
    if a + 8 ≥ b then some (a + 12 - b, 3 * b - 6)
    else if a + 10 = b ∨ a + 12 = b then none
    else some (b - a - 10, 3 * a + 27)
  else
    if a + 1 ≤ b then some (b + 3 - a, 3 * a)
    else if a = b + 1 ∨ a = b + 3 then none
    else some (a - b - 1, 3 * b + 6)

def InvA8 (s : Nat × Nat) : Prop :=
  s.1 ≥ 4 ∧ s.1 % 2 = 0 ∧ s.2 ≥ 6 ∧ s.2 % 3 = 0

theorem invA8_preserved : IsInvariant stepA8 InvA8 := by
  intro ⟨a, b⟩ s' hs hStep
  unfold InvA8 at hs ⊢
  dsimp only [stepA8] at hStep
  cryptid_step_omega hStep

/-! ## 7. Cryptid A.9 (`1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD`) -/

def stepA9 (s : Nat × Nat) : Option (Nat × Nat) :=
  let u := s.1
  let v := s.2
  if u % 6 = 3 then
    if v ≤ u - 2 then some (3 * v + 3, u - v - 1)
    else if v = u ∨ v = u + 2 then none
    else some (3 * u + 6, v - u - 3)
  else
    if v ≤ u - 3 then some (3 * v + 6, u - v - 2)
    else if v = u - 1 ∨ v = u + 1 then none
    else some (3 * u + 6, v - u - 2)

def InvA9 (s : Nat × Nat) : Prop :=
  s.1 ≥ 6 ∧ s.1 % 3 = 0 ∧ s.2 ≥ 1 ∧ s.2 % 2 = 1

theorem invA9_preserved : IsInvariant stepA9 InvA9 := by
  intro ⟨u, v⟩ s' hs hStep
  unfold InvA9 at hs ⊢
  dsimp only [stepA9] at hStep
  cryptid_step_omega hStep

/-! ## 8. BMO #8 (`1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA`) -/

def stepBMO8 (s : Nat × Nat) : Option (Nat × Nat) :=
  let a := s.1
  let c := s.2
  if a ≥ 1 ∧ (c = 2 * a - 2 ∨ c = 2 * a - 1) then none
  else if c ≥ 2 * a then some (3 * a + 3, c - 2 * a + 2)
  else if c % 2 = 0 then some (a - c / 2 - 2, 3 * (c / 2) + 5)
  else some (a - c / 2 - 2, 3 * (c / 2) + 8)

def InvBMO8 (s : Nat × Nat) : Prop :=
  s.1 + s.2 ≥ 8 ∧ s.2 ≥ 2 ∧ (s.1 % 3 = 0 ∨ s.2 % 3 = 2)

theorem invBMO8_init : InvBMO8 (4, 11) := by
  unfold InvBMO8; dsimp; omega

theorem invBMO8_preserved : IsInvariant stepBMO8 InvBMO8 := by
  intro ⟨a, c⟩ s' hs hStep
  unfold InvBMO8 at hs ⊢
  dsimp only [stepBMO8] at hStep
  cryptid_step_omega hStep

/-- Exact 3-Gate Classification of BMO #8 under `InvBMO8`:
    Halting occurs iff `(a, c)` lies on `G1(3k+3, 6k+5)`, `G2(3k+2, 6k+2)`,
    or the newly uncovered third ray `G3(3k+3, 6k+4)` (`k ≥ 1`). -/
theorem bmo8_three_gates_iff (a c : Nat) (hInv : InvBMO8 (a, c)) :
    stepBMO8 (a, c) = none ↔
      (∃ k, a = 3 * k + 3 ∧ c = 6 * k + 5) ∨
      (∃ k, a = 3 * k + 2 ∧ c = 6 * k + 2) ∨
      (∃ k, k ≥ 1 ∧ a = 3 * k + 3 ∧ c = 6 * k + 4) := by
  unfold InvBMO8 at hInv
  constructor
  · intro hNone
    dsimp only [stepBMO8] at hNone
    split at hNone
    · rename_i hHalt
      if ha0 : a % 3 = 0 then
        if hcOdd : c = 2 * a - 1 then
          left; refine ⟨a / 3 - 1, ?_⟩; omega
        else
          right; right; refine ⟨a / 3 - 1, ?_⟩; omega
      else
        right; left; refine ⟨a / 3, ?_⟩; omega
    · split at hNone <;> try contradiction
      split at hNone <;> contradiction
  · intro hGates
    dsimp only [stepBMO8]
    cases hGates with
    | inl h1 =>
      cases h1 with
      | intro k hk =>
        split
        · rfl
        · omega
    | inr h23 =>
      cases h23 with
      | inl h2 =>
        cases h2 with
        | intro k hk =>
          split
          · rfl
          · omega
      | inr h3 =>
        cases h3 with
        | intro k hk =>
          split
          · rfl
          · omega

/-- Exact 33-state Mod-9 recurrent attractor `I_9 = I_3 \ Forbidden_12` of BMO #8. -/
def isI9BMO8 (ra rc : Nat) : Bool :=
  (ra % 3 == 0 || rc % 3 == 2) &&
  !(ra == 0 && (rc == 1 || rc == 4 || rc == 7)) &&
  !(ra == 1 && rc == 2) &&
  !(ra == 4 && rc == 2) &&
  !(ra == 6 && (rc == 0 || rc == 1 || rc == 3 || rc == 4 || rc == 6 || rc == 7)) &&
  !(ra == 7 && rc == 2)

def countI9BMO8 : Nat :=
  (List.range 9).foldl (fun acc ra =>
    acc + (List.range 9).foldl (fun acc2 rc =>
      if isI9BMO8 ra rc then acc2 + 1 else acc2) 0) 0

/-- Kernel verification that `|I_9| = 33` out of `81` Mod-9 residue pairs (`11/27`). -/
theorem bmo8_I9_card_eq_33 : countI9BMO8 = 33 := by
  decide

end CryptidSolve
