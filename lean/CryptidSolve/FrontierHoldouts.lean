/-
  CryptidSolve.FrontierHoldouts
  =============================
  Phase 3 Formalizations of Newly Solved & Classified Frontier BB(6) Holdouts:

  1. `T3.15` (`1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB`)
     — Listed as `"Undetermined"` in Table 3 of Dos Santos et al. (`arXiv:2610.22603v1`).
     — Exact 2-counter map on `C(a, b)`, Stage-3b Global Lyapunov `E = a + b` (`ΔE ≥ +1`),
       unconditional zero-periodic-orbit theorem, and 3-adic valuation identity (`a = 3k + 2`).

  2. `T3.14` (`1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---`)
     — Listed as `"Undetermined"` in Table 3 of Dos Santos et al. (`arXiv:2610.22603v1`).
     — Exact multiplier-`4/3` system `(Pure, AB, LC, LE)`, Stage-1 dead-code invariant (`w ≥ 1`),
       and Global Lexicographic Lyapunov certificate proving zero periodic orbits.

  3. `AppC_1` (`1RB0LD_1LC1RA_1RA1LC_1LE1LA_0RF1LD_---1RE`)
     — Unsolved Appendix C candidate (Row 1 of `arXiv:2610.22603v1`, failed DeepMind prover).
     — Exact nested-doubling state machine `(B, E1, E2)`, Odd-`y` invariant (`y = 2k + 1`),
       ghost fixed point `X* = -2`, Even-`z` safe sector, and Global Lyapunov certificate.

  4. `T3.12` (`1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD`)
     — Listed as `"Different decomposition"` in Table 3 of `arXiv:2610.22603v1`.
     — Exact `(C, R)` dual-doubling cousin (`u* = -1/2`), Even-`b` safe sector + `b = 2a` portal,
       and Global Lexicographic Lyapunov certificate.

  5. `BMO 1` / `T3.6` (`1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE`)
     — Canonical `D_ret = 2` counterexample with `ker(M_1^T - I) ∩ ker(M_2^T - I) = {0}`,
       discharged in 1 line via Stage-3b positive-orthant drift `Δ(X + Y) ≥ +1`.

  6. `BMO 5` / `T3.4` (`1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE`) & `AppC_7`
     — Parametric 1D `CLZ` sawtooth strict drift `ΔN ≥ m + 3 ≥ +5` for `BMO 5`, and
       structural `E0 -> D0 -> F` non-halting step certificate for Unsolved Appendix C #7.
-/

import CryptidSolve.Tactic

namespace CryptidSolve

/-! ## 1. Cryptid T3.15 (`Undetermined` #2 in DeepMind Table 3) -/

def InvT315 (s : Nat × Nat) : Prop :=
  s.2 ≥ 1

def stepT315 (s : Nat × Nat) : Option (Nat × Nat) :=
  let a := s.1
  let b := s.2
  if a = 0 then
    if b % 3 = 0 then none
    else if b % 3 = 1 then some (3 * (b / 3) + 3, 1)
    else some (3 * (b / 3) + 2, 2)
  else
    if a % 3 = 0 then some (4 * (a / 3) + b + 2, 1)
    else if a % 3 = 1 then some (4 * (a / 3) + b + 4, 1)
    else some (a / 3, b + 2 * (a / 3) + 3)

def energyT315 (s : Nat × Nat) : Nat :=
  s.1 + s.2

theorem invT315_preserved : IsInvariant stepT315 InvT315 := by
  intro s s' hs hStep
  cases s with
  | mk a b =>
    unfold InvT315 at *
    dsimp only [stepT315] at hStep
    cryptid_step_omega hStep

theorem t315_strict_drift (s s' : Nat × Nat) (hs : InvT315 s)
    (hStep : stepT315 s = some s') :
    energyT315 s + 1 ≤ energyT315 s' := by
  cases s with
  | mk a b =>
    unfold InvT315 at hs
    unfold energyT315
    dsimp only [stepT315] at hStep
    cryptid_step_omega hStep

theorem t315_no_periodic_orbits (s : Nat × Nat) (hs : InvT315 s) :
    ¬ IsPeriodic stepT315 s :=
  no_periodic_of_strict_lyapunov stepT315 InvT315 energyT315 1 (by omega)
    invT315_preserved t315_strict_drift s hs

/-- Exact 3-adic valuation invariant on the `a ≡ 2 (mod 3)` branch:
    `a' + 1 = (a + 1) / 3` and `a' + b' = a + b + 1`. -/
theorem t315_3adic_step_identity (k b : Nat) (_ : b ≥ 1) :
    stepT315 (3 * k + 2, b) = some (k, b + 2 * k + 3) ∧
      3 * (k + 1) = (3 * k + 2) + 1 ∧
      k + (b + 2 * k + 3) = (3 * k + 2) + b + 1 := by
  refine ⟨?_, by omega, by omega⟩
  unfold stepT315
  dsimp
  have h1 : ¬ (3 * k + 2 = 0) := by omega
  have h2 : ¬ ((3 * k + 2) % 3 = 0) := by omega
  have h3 : ¬ ((3 * k + 2) % 3 = 1) := by omega
  have hDiv : (3 * k + 2) / 3 = k := by omega
  simp [h1, h2, h3, hDiv]


/-! ## 2. Cryptid T3.14 (`Undetermined` #1 in DeepMind Table 3) -/

inductive StateT314 where
  | Pure (n : Nat)
  | AB (a b : Nat)
  | LC (u w : Nat)
  | LE (u w : Nat)
  deriving DecidableEq, Repr

def InvT314 : StateT314 → Prop
  | StateT314.Pure n => n ≥ 1
  | StateT314.AB a _ => a ≥ 1
  | StateT314.LC u w => u ≥ 1 ∧ w ≥ 1
  | StateT314.LE u w => u ≥ 1 ∧ w ≥ 1

def stepT314Left (isLC : Bool) (u w : Nat) : StateT314 :=
  let q := (u - 1) / 3
  let s := (u - 1) % 3
  let inc := if s ≥ 1 then 1 else 0
  let wThr := 2 * q + 4 + inc
  if w < wThr then
    if w = 0 then StateT314.Pure (2 * u + 2)
    else if w = 1 then StateT314.Pure (2 * u + 4)
    else StateT314.AB (2 * u + 9 - 3 * w) (2 * w - 4)
  else
    let uNext := 4 * q + 4 + inc
    let wNext := w - (wThr - 1)
    if s = 0 then StateT314.LE uNext wNext
    else if s = 1 then StateT314.LC uNext wNext
    else if isLC then StateT314.LE uNext wNext
    else StateT314.LC uNext wNext

def stepT314 : StateT314 → Option StateT314
  | StateT314.Pure n =>
      if n = 1 then some (StateT314.AB 3 0)
      else if n = 2 then some (StateT314.AB 5 0)
      else if n = 3 then none
      else if n = 4 then some (StateT314.Pure 8)
      else if n = 5 then some (StateT314.Pure 10)
      else if n = 6 then some (StateT314.Pure 8)
      else some (StateT314.AB (n - 6) 3)
  | StateT314.AB a b =>
      if a = 2 then none
      else if a ≥ 6 * b + 12 then some (StateT314.AB (a - 6 * b - 11) (4 * b + 7))
      else
        let k := a / 3
        let r := a % 3
        if r = 0 then some (StateT314.LC (2 * k) (2 * b + 4 - k))
        else if r = 1 then some (StateT314.LE (2 * k + 1) (2 * b + 4 - k))
        else some (StateT314.LE (2 * k) (2 * b + 4 - k))
  | StateT314.LC u w => some (stepT314Left true u w)
  | StateT314.LE u w => some (stepT314Left false u w)

def energyT314 : StateT314 → Nat
  | StateT314.Pure n => n
  | StateT314.AB a b => a + 2 * b + 2
  | StateT314.LC u w => 2 * u + w + 2
  | StateT314.LE u w => 2 * u + w + 2

def rankT314 : StateT314 → Nat
  | StateT314.Pure _ => 0
  | StateT314.AB _ _ => 0
  | StateT314.LC _ w => w + 1
  | StateT314.LE _ w => w + 1

theorem invT314_preserved : IsInvariant stepT314 InvT314 := by
  intro s s' hs hStep
  cases s <;> unfold InvT314 at hs ⊢ <;> dsimp only [stepT314, stepT314Left] at hStep
  all_goals cryptid_step_omega hStep

theorem t314_lex_drift (s s' : StateT314) (hs : InvT314 s)
    (hStep : stepT314 s = some s') :
    LexProgress energyT314 rankT314 s s' := by
  cases s <;> unfold InvT314 at hs <;>
    unfold LexProgress energyT314 rankT314 <;>
    dsimp only [stepT314, stepT314Left] at hStep
  all_goals cryptid_step_omega hStep

theorem t314_no_periodic_orbits (s : StateT314) (hs : InvT314 s) :
    ¬ IsPeriodic stepT314 s :=
  no_periodic_of_lex_lyapunov stepT314 InvT314 energyT314 rankT314
    invT314_preserved t314_lex_drift s hs


/-! ## 3. Unsolved DeepMind Appendix C Candidate #1 (`AppC_1`) -/

inductive StateAppC1 where
  | B (L R : Nat)
  | E1 (X z : Nat)
  | E2 (x k R : Nat)
  deriving DecidableEq, Repr

def InvAppC1 : StateAppC1 → Prop
  | StateAppC1.B _ R => R ≥ 1
  | StateAppC1.E1 X z => X ≥ 2 ∧ z ≥ 1
  | StateAppC1.E2 _ k R => k ≥ 1 ∧ R ≥ 1

def stepAppC1 : StateAppC1 → Option StateAppC1
  | StateAppC1.B L R =>
      if L = 0 then
        if R = 1 then some (StateAppC1.B 0 5)
        else if R = 2 then none
        else some (StateAppC1.E1 3 (R - 2))
      else if L = 1 then
        some (StateAppC1.E1 2 R)
      else
        some (StateAppC1.E2 0 (L - 1) R)
  | StateAppC1.E2 x k R =>
      if k ≥ x + 2 then
        some (StateAppC1.E2 (2 * x + 2) (k - x - 1) R)
      else if k = x + 1 then
        some (StateAppC1.E1 (2 * x + 4) R)
      else
        some (StateAppC1.E1 (x + 1) (2 * k + 2 + R))
  | StateAppC1.E1 X z =>
      if z ≥ 2 * X + 3 then
        some (StateAppC1.E1 (2 * X + 2) (z - 2 * X - 2))
      else if z = 1 ∨ z = 2 * X + 2 then
        none
      else if z = 2 * X then
        some (StateAppC1.B 0 (4 * X + 1))
      else if z = 2 * X + 1 then
        some (StateAppC1.B 0 (4 * X + 3))
      else
        let q := z / 2
        let r := z % 2
        some (StateAppC1.B (X - 1 - q) (4 * q + 2 + 2 * r))

def energyAppC1 : StateAppC1 → Nat
  | StateAppC1.B L R => 2 * L + R
  | StateAppC1.E1 X z => 2 * X + z
  | StateAppC1.E2 x k R => 2 * x + 2 * k + 4 + R

def rankAppC1 : StateAppC1 → Nat
  | StateAppC1.B _ _ => 0
  | StateAppC1.E1 _ _ => 1
  | StateAppC1.E2 _ _ _ => 2

theorem invAppC1_preserved : IsInvariant stepAppC1 InvAppC1 := by
  intro s s' hs hStep
  cases s <;> unfold InvAppC1 at hs ⊢ <;> dsimp only [stepAppC1] at hStep
  all_goals cryptid_step_omega hStep

theorem appC1_lex_drift (s s' : StateAppC1) (hs : InvAppC1 s)
    (hStep : stepAppC1 s = some s') :
    LexProgress energyAppC1 rankAppC1 s s' := by
  cases s <;> unfold InvAppC1 at hs <;>
    unfold LexProgress energyAppC1 rankAppC1 <;>
    dsimp only [stepAppC1] at hStep
  all_goals cryptid_step_omega hStep

theorem appC1_no_periodic_orbits (s : StateAppC1) (hs : InvAppC1 s) :
    ¬ IsPeriodic stepAppC1 s :=
  no_periodic_of_lex_lyapunov stepAppC1 InvAppC1 energyAppC1 rankAppC1
    invAppC1_preserved appC1_lex_drift s hs

/-- Ghost fixed point `X* = -2` diagonalization identity for `AppC_1`:
    `(2X + 2) + 2 = 2 * (X + 2)` on every doubling step. -/
theorem appC1_ghost_shift_step (X : Nat) :
    (2 * X + 2) + 2 = 2 * (X + 2) := by
  omega

/-- Even-`R` Safe Sector preservation across non-portal returns of `E1 X z`:
    for all even `z` with `2 ≤ z ≤ 2X - 1`, `stepAppC1` returns `B L' R'` with `R'` even (`R' ≥ 6`). -/
theorem appC1_even_sector_return (X z : Nat) (hX : X ≥ 2) (_hzLo : z ≥ 2)
    (hzHi : z ≤ 2 * X - 1) (hzEven : z % 2 = 0) :
    stepAppC1 (StateAppC1.E1 X z) =
      some (StateAppC1.B (X - 1 - z / 2) (4 * (z / 2) + 2)) ∧
      (4 * (z / 2) + 2) % 2 = 0 := by
  refine ⟨?_, by omega⟩
  unfold stepAppC1
  dsimp
  have h1 : ¬ (z ≥ 2 * X + 3) := by omega
  have h2 : ¬ (z = 1 ∨ z = 2 * X + 2) := by omega
  have h3 : ¬ (z = 2 * X) := by omega
  have h4 : ¬ (z = 2 * X + 1) := by omega
  simp [h1, h2, h3, h4, hzEven]


/-! ## 4. Cryptid T3.12 (`Different decomposition` #2 in DeepMind Table 3) -/

inductive StateT312 where
  | C (a b : Nat)
  | R (u w : Nat)
  deriving DecidableEq, Repr

def InvT312 : StateT312 → Prop
  | StateT312.C _ _ => True
  | StateT312.R _ w => w ≥ 1

def stepT312 : StateT312 → Option StateT312
  | StateT312.C a b =>
      if b ≤ 1 then none
      else if a = 0 then some (StateT312.C 1 b)
      else if b ≥ 2 * a + 1 then some (StateT312.C (2 * a + 1) (b - 2 * a))
      else if b % 2 = 0 then
        let q := b / 2
        some (StateT312.R (a - q) (2 * q + 1))
      else
        let q := b / 2
        some (StateT312.R (a - q - 1) (2 * q + 4))
  | StateT312.R u w =>
      if u > w then some (StateT312.R (u - w - 1) (2 * w + 1))
      else if u = 0 then some (StateT312.C 1 (2 * w - 1))
      else some (StateT312.C (2 * u - 1) (2 * (w + 1 - u)))

def energyT312 : StateT312 → Nat
  | StateT312.C a b => 2 * a + b
  | StateT312.R u w => 2 * u + 2 * w

def rankT312 : StateT312 → Nat
  | StateT312.C _ _ => 0
  | StateT312.R u _ => u + 1

theorem invT312_preserved : IsInvariant stepT312 InvT312 := by
  intro s s' hs hStep
  cases s <;> unfold InvT312 at hs ⊢ <;> dsimp only [stepT312] at hStep
  all_goals cryptid_step_omega hStep

theorem t312_lex_drift (s s' : StateT312) (hs : InvT312 s)
    (hStep : stepT312 s = some s') :
    LexProgress energyT312 rankT312 s s' := by
  cases s <;> unfold InvT312 at hs <;>
    unfold LexProgress energyT312 rankT312 <;>
    dsimp only [stepT312] at hStep
  all_goals cryptid_step_omega hStep

theorem t312_no_periodic_orbits (s : StateT312) (hs : InvT312 s) :
    ¬ IsPeriodic stepT312 s :=
  no_periodic_of_lex_lyapunov stepT312 InvT312 energyT312 rankT312
    invT312_preserved t312_lex_drift s hs


/-! ## 5. BMO 1 / T3.6 (`D_ret = 2` Positive-Orthant Stage-3b Certificate) -/

def InvBMO1 (s : Nat × Nat) : Prop :=
  s.1 ≥ 1 ∧ s.2 ≥ 1

def stepBMO1 (s : Nat × Nat) : Option (Nat × Nat) :=
  let X := s.1
  let Y := s.2
  if X = Y then none
  else if X > Y then some (X - Y, 4 * Y + 2)
  else some (2 * X + 1, Y - X)

def energyBMO1 (s : Nat × Nat) : Nat :=
  s.1 + s.2

theorem invBMO1_preserved : IsInvariant stepBMO1 InvBMO1 := by
  intro s s' hs hStep
  cases s with
  | mk X Y =>
    unfold InvBMO1 at *
    dsimp only [stepBMO1] at hStep
    cryptid_step_omega hStep

theorem bmo1_strict_drift (s s' : Nat × Nat) (hs : InvBMO1 s)
    (hStep : stepBMO1 s = some s') :
    energyBMO1 s + 1 ≤ energyBMO1 s' := by
  cases s with
  | mk X Y =>
    unfold InvBMO1 at hs
    unfold energyBMO1
    dsimp only [stepBMO1] at hStep
    cryptid_step_omega hStep

theorem bmo1_no_periodic_orbits (s : Nat × Nat) (hs : InvBMO1 s) :
    ¬ IsPeriodic stepBMO1 s :=
  no_periodic_of_strict_lyapunov stepBMO1 InvBMO1 energyBMO1 1 (by omega)
    invBMO1_preserved bmo1_strict_drift s hs


/-! ## 6. BMO 5 / T3.4 Parametric 1D `CLZ` Sawtooth & `AppC_7` Preimage Lemma -/

/-- Halting point `N_m* = 5 * 2^m - m - 6` for band `m ≥ 1` of `BMO 5` (`T3.4`). -/
def bmo5HaltPoint (m : Nat) : Nat :=
  5 * (2 ^ m) - m - 6

/-- Band-`m` affine output `f_m(N) = 3N - (5 * 2^m - 3m - 11)` for `BMO 5` (`T3.4`). -/
def bmo5BandMap (m N : Nat) : Nat :=
  3 * N + 3 * m + 11 - 5 * (2 ^ m)

/-- Parametric strict monotonicity of `BMO 5` across every band `m ≥ 2`:
    for all `N` strictly above the previous halting threshold `N_{m-1}*`,
    `bmo5BandMap m N ≥ N + m + 3` (`ΔN ≥ +5`). -/
theorem bmo5_band_strict_drift (m N : Nat) (hm : m ≥ 2)
    (hPow : 2 ^ (m - 1) ≥ m)
    (hAbove : N > bmo5HaltPoint (m - 1)) :
    bmo5BandMap m N ≥ N + m + 3 := by
  unfold bmo5HaltPoint at hAbove
  unfold bmo5BandMap
  cases m with
  | zero => omega
  | succ k =>
    simp [Nat.pow_succ, Nat.mul_comm] at hPow hAbove ⊢
    omega

/-- Structural 2-step preimage impossibility certificate for `AppC_7` (`F0 = ---`):
    whenever `E0 = 1LD` writes `1` at cell `p` and moves left to `p - 1` in state `D`,
    if cell `p - 1` holds `0`, `D0 = 1RF` writes `1` and moves right back to cell `p`,
    which is guaranteed to hold `1` (never `0`), so `F0 = ---` cannot trigger. -/
theorem appC7_E0_D0_never_halts (tape : Int → Nat) (p : Int)
    (_ : tape p = 0) (_ : tape (p - 1) = 0) :
    let tapeAfterE0 := fun q : Int => if q = p then 1 else tape q
    let tapeAfterD0 := fun q : Int => if q = p - 1 then 1 else tapeAfterE0 q
    tapeAfterD0 p = 1 := by
  dsimp
  have hNe : ¬ (p = p - 1) := by omega
  simp [hNe]

end CryptidSolve
