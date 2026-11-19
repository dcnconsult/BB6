/-
  CryptidSolvePhase4.Transfer5SpaceTimeCohomology
  ===============================================
  Transfer 5:
  2D Space-Time Plaquette Cohomology, Discrete Stokes' Theorem on Space-Time Cylinders,
  and Raw 6-State Turing Machine Non-Halting Where Local 3-Cell Window NFAs Fail.

  Formalizes in pure Lean 4 Core (`Init` + `omega` + `decide`):
    1. Exactness of the 2D lattice cochain complex `plaquetteCurl (d0Horiz phi) (d0Vert phi) = 0`
       (`coboundary_d1_d0_zero`).
    2. 2D Discrete Stokes' / Gauss-Bonnet Theorem (`discrete_stokes_rectangle`) summing 2x2
       plaquette curls over `[0, W) × [0, T)` into boundary integrals, plus the cohomological
       halting obstruction (`stokes_cohomological_halting_obstruction`).
    3. Raw infinite-tape 6-state Parabolic Bouncer TM (`1RB0RF_0RE0RE_1RF1LD_0LC0LA_0LD1RF_0LA---`):
       - Kernel-checked proof (`bouncer_3cell_nfa_reaches_halt_in_3_steps` via `decide`) that
         the standard translation-invariant 3-cell local window NFA reaches `F1 = HALT` in 3 steps,
       - Kernel-checked proof (`bipartite_parabolic_bouncer_tm_never_halts`) that the global
         `Z/2Z` space-time sublattice 1-cocycle invariant makes `F1 = HALT` unreachable for
         all `n : Nat` raw steps from the blank tape.
-/

import CryptidSolvePhase4.Basic

namespace CryptidSolvePhase4

/-! ## 1. 2D Lattice Cochain Complex & Exactness (`d1 ∘ d0 = 0`) -/

/-- Horizontal coboundary `(d0 phi)^H(x, t) = phi(x + 1, t) - phi(x, t)`. -/
def d0Horiz (phi : Nat → Nat → Int) (x t : Nat) : Int :=
  phi (x + 1) t - phi x t

/-- Vertical coboundary `(d0 phi)^V(x, t) = phi(x, t + 1) - phi(x, t)`. -/
def d0Vert (phi : Nat → Nat → Int) (x t : Nat) : Int :=
  phi x (t + 1) - phi x t

/-- 2D Plaquette Curl `(d1 J)(x, t) = Jx(x, t) + Jt(x + 1, t) - Jx(x, t + 1) - Jt(x, t)`
    around the oriented elementary space-time plaquette `[x, x+1] × [t, t+1]`. -/
def plaquetteCurl (Jx Jt : Nat → Nat → Int) (x t : Nat) : Int :=
  Jx x t + Jt (x + 1) t - Jx x (t + 1) - Jt x t

/-- **Exactness of the 2D Space-Time Cochain Complex (`d1 ∘ d0 = 0`)**:
    Every potential-generated 1-cochain has identically zero plaquette curl everywhere. -/
theorem coboundary_d1_d0_zero (phi : Nat → Nat → Int) (x t : Nat) :
    plaquetteCurl (d0Horiz phi) (d0Vert phi) x t = 0 := by
  unfold plaquetteCurl d0Horiz d0Vert
  omega

/-! ## 2. 2D Discrete Stokes' Theorem & Space-Time Cohomological Obstruction -/

/-- Spatial integral `∑_{x=0}^{W-1} Jx(x, t)` along horizontal time-slice `t`. -/
def sumHoriz (Jx : Nat → Nat → Int) (t : Nat) : Nat → Int
  | 0 => 0
  | w + 1 => sumHoriz Jx t w + Jx w t

/-- Temporal flux `∑_{t=0}^{T-1} Jt(x, t)` along vertical world-boundary `x`. -/
def sumVert (Jt : Nat → Nat → Int) (x : Nat) : Nat → Int
  | 0 => 0
  | t + 1 => sumVert Jt x t + Jt x t

/-- 1-row plaquette sum `∑_{x=0}^{W-1} plaquetteCurl(x, t)`. -/
def sumPlaquetteRow (Jx Jt : Nat → Nat → Int) (t : Nat) : Nat → Int
  | 0 => 0
  | w + 1 => sumPlaquetteRow Jx Jt t w + plaquetteCurl Jx Jt w t

/-- Full 2D rectangular space-time plaquette sum `∑_{t=0}^{T-1} ∑_{x=0}^{W-1} plaquetteCurl(x, t)`. -/
def sumPlaquetteRect (Jx Jt : Nat → Nat → Int) (W : Nat) : Nat → Int
  | 0 => 0
  | t + 1 => sumPlaquetteRect Jx Jt W t + sumPlaquetteRow Jx Jt t W

/-- **1-Slice Telescoping Lemma**:
    Summing plaquette curls across `[0, W)` at fixed `t` cancels all interior vertical edges. -/
theorem discrete_stokes_row (Jx Jt : Nat → Nat → Int) (t W : Nat) :
    sumPlaquetteRow Jx Jt t W =
      sumHoriz Jx t W + Jt W t - sumHoriz Jx (t + 1) W - Jt 0 t := by
  induction W with
  | zero =>
      simp [sumPlaquetteRow, sumHoriz]
  | succ w ih =>
      simp only [sumPlaquetteRow, sumHoriz]
      rw [ih]
      unfold plaquetteCurl
      omega

/-- **2D Discrete Stokes' / Gauss-Bonnet Theorem on Space-Time `[0, W) × [0, T)`**:
    The bulk sum of 2x2 space-time plaquette curls equals the oriented boundary integral
    `(bottom t=0) + (right x=W) - (top t=T) - (left x=0)`. -/
theorem discrete_stokes_rectangle (Jx Jt : Nat → Nat → Int) (W T : Nat) :
    sumPlaquetteRect Jx Jt W T =
      sumHoriz Jx 0 W + sumVert Jt W T - sumHoriz Jx T W - sumVert Jt 0 T := by
  induction T with
  | zero =>
      simp [sumPlaquetteRect, sumVert]
  | succ t ih =>
      simp only [sumPlaquetteRect, sumVert]
      rw [ih, discrete_stokes_row]
      omega

theorem sumPlaquetteRow_nonneg_of_pointwise
    (Jx Jt : Nat → Nat → Int) (t W : Nat)
    (hRow : ∀ x, x < W → 0 ≤ plaquetteCurl Jx Jt x t) :
    0 ≤ sumPlaquetteRow Jx Jt t W := by
  induction W with
  | zero => simp [sumPlaquetteRow]
  | succ w ih =>
      simp only [sumPlaquetteRow]
      have h1 : 0 ≤ sumPlaquetteRow Jx Jt t w := ih (fun x hx => hRow x (by omega))
      have h2 : 0 ≤ plaquetteCurl Jx Jt w t := hRow w (by omega)
      omega

theorem sumPlaquetteRect_nonneg_of_pointwise
    (Jx Jt : Nat → Nat → Int) (W T : Nat)
    (hBulk : ∀ x t, x < W → t < T → 0 ≤ plaquetteCurl Jx Jt x t) :
    0 ≤ sumPlaquetteRect Jx Jt W T := by
  induction T with
  | zero => simp [sumPlaquetteRect]
  | succ t ih =>
      simp only [sumPlaquetteRect]
      have h1 : 0 ≤ sumPlaquetteRect Jx Jt W t :=
        ih (fun x t' hx ht' => hBulk x t' hx (by omega))
      have h2 : 0 ≤ sumPlaquetteRow Jx Jt t W :=
        sumPlaquetteRow_nonneg_of_pointwise Jx Jt t W (fun x hx => hBulk x t hx (by omega))
      omega

theorem sumVert_zero_of_pointwise
    (Jt : Nat → Nat → Int) (x T : Nat)
    (hBdry : ∀ t, t < T → Jt x t = 0) :
    sumVert Jt x T = 0 := by
  induction T with
  | zero => simp [sumVert]
  | succ t ih =>
      simp only [sumVert]
      rw [ih (fun t' ht' => hBdry t' (by omega)), hBdry t (by omega)]
      omega

/-- **Cohomological Space-Time Halting Obstruction**:
    If a TM space-time history on `[0, W) × [0, T]` has:
    1. Zero blank-boundary vertical flux (`Jt(0, t) = Jt(W, t) = 0`),
    2. Non-negative counterclockwise plaquette curl (`0 ≤ plaquetteCurl(x, t)`, i.e. non-positive
       time-step anomaly `Jx(x, t+1) - Jx(x, t) ≤ Jt(x+1, t) - Jt(x, t)`) on every cell,
    3. Zero initial charge (`sumHoriz Jx 0 W ≤ 0` on the blank tape),
    then NO slice at time `T` can ever carry positive halting anomaly (`sumHoriz Jx T W ≥ 1`). -/
theorem stokes_cohomological_halting_obstruction
    (Jx Jt : Nat → Nat → Int) (W T : Nat)
    (hBulk : ∀ x t, x < W → t < T → 0 ≤ plaquetteCurl Jx Jt x t)
    (hLeft : ∀ t, t < T → Jt 0 t = 0)
    (hRight : ∀ t, t < T → Jt W t = 0)
    (hInit : sumHoriz Jx 0 W ≤ 0) :
    ¬ (sumHoriz Jx T W ≥ 1) := by
  have hStokes := discrete_stokes_rectangle Jx Jt W T
  have hBulkSum := sumPlaquetteRect_nonneg_of_pointwise Jx Jt W T hBulk
  have hL := sumVert_zero_of_pointwise Jt 0 T hLeft
  have hR := sumVert_zero_of_pointwise Jt W T hRight
  rw [hL, hR] at hStokes
  omega

/-! ## 3. Raw 6-State Parabolic Bouncer TM (`1RB0RF_0RE0RE_1RF1LD_0LC0LA_0LD1RF_0LA---`) -/

/-- States `{A, B, C, D, E, F}` of the 6-state Bipartite Parabolic Bouncer TM. -/
inductive BouncerState where
  | A | B | C | D | E | F
  deriving DecidableEq, Repr

/-- Transition table of `1RB0RF_0RE0RE_1RF1LD_0LC0LA_0LD1RF_0LA---`:
    returns `some (writeBit, moveDir, nextState)` (`moveDir = true` for `R`, `false` for `L`),
    or `none` on the unique Halt transition `(F, true)`. -/
def bouncerDelta : BouncerState → Bool → Option (Bool × Bool × BouncerState)
  | .A, false => some (true,  true,  .B) -- 1RB
  | .A, true  => some (false, true,  .F) -- 0RF
  | .B, false => some (false, true,  .E) -- 0RE
  | .B, true  => some (false, true,  .E) -- 0RE
  | .C, false => some (true,  true,  .F) -- 1RF
  | .C, true  => some (true,  false, .D) -- 1LD
  | .D, false => some (false, false, .C) -- 0LC
  | .D, true  => some (false, false, .A) -- 0LA
  | .E, false => some (false, false, .D) -- 0LD
  | .E, true  => some (true,  true,  .F) -- 1RF
  | .F, false => some (false, false, .A) -- 0LA
  | .F, true  => none                    -- --- (HALT)

/-- 3-Cell Local Window Patch `(state, bLeft, bCenter, bRight)` used by standard local CTL NFAs. -/
structure Local3Patch where
  st : BouncerState
  bl : Bool
  bc : Bool
  br : Bool
  deriving DecidableEq, Repr

/-- Valid 1-step transition in the translation-invariant 3-cell window NFA with incoming bit `wild`. -/
def isValid3CellStep (p : Local3Patch) (wild : Bool) (p' : Local3Patch) : Bool :=
  match bouncerDelta p.st p.bc with
  | none => false
  | some (w, dirR, sNext) =>
      if dirR then
        p' == { st := sNext, bl := w, bc := p.br, br := wild }
      else
        p' == { st := sNext, bl := wild, bc := p.bl, br := w }

/-- **Local 3-Cell Window NFA Failure Theorem**:
    Because a translation-invariant 3-cell NFA forgets global `x mod 2` sublattice cohomology,
    it reaches the halting patch `(F, 1, 1, 0)` (`bouncerDelta F true = none`) in **3 steps**
    from the blank patch `(A, 0, 0, 0)`! -/
theorem bouncer_3cell_nfa_reaches_halt_in_3_steps :
    let p0 : Local3Patch := ⟨.A, false, false, false⟩
    let p1 : Local3Patch := ⟨.B, true,  false, true⟩
    let p2 : Local3Patch := ⟨.E, false, true,  true⟩
    let p3 : Local3Patch := ⟨.F, true,  true,  false⟩
    isValid3CellStep p0 true p1 = true ∧
      isValid3CellStep p1 true p2 = true ∧
      isValid3CellStep p2 false p3 = true ∧
      bouncerDelta p3.st p3.bc = none := by
  decide

/-- Raw infinite-tape configuration `(tape : Int → Bool, head : Int, state : BouncerState)`. -/
structure RawBouncerCfg where
  tape : Int → Bool
  head : Int
  st   : BouncerState

def tapeWrite (tape : Int → Bool) (pos : Int) (val : Bool) (z : Int) : Bool :=
  if z = pos then val else tape z

/-- Exact 1-step raw Turing Machine semantics on the bi-infinite integer tape `Z`. -/
def stepRawBouncer (cfg : RawBouncerCfg) : Option RawBouncerCfg :=
  match bouncerDelta cfg.st (cfg.tape cfg.head) with
  | none => none
  | some (w, dirR, sNext) =>
      let nextHead := if dirR then cfg.head + 1 else cfg.head - 1
      some { tape := tapeWrite cfg.tape cfg.head w, head := nextHead, st := sNext }

def blankTape (_ : Int) : Bool := false

def blankBouncerCfg : RawBouncerCfg :=
  { tape := blankTape, head := 0, st := .A }

def isEvenBouncerState : BouncerState → Bool
  | .A | .C | .E => true
  | .B | .D | .F => false

/-- **Global Space-Time Sublattice 1-Cocycle Invariant**:
    1. Bipartite head-phase lock: `head % 2 = 0` iff `st ∈ {A, C, E}` (and `head % 2 = 1` iff `st ∈ {B, D, F}`),
    2. Zero odd-sublattice occupation: every odd cell `z % 2 = 1` on `Z` holds `false` (`0`). -/
def OddSublatticeCocycleInv (cfg : RawBouncerCfg) : Prop :=
  (if isEvenBouncerState cfg.st then cfg.head % 2 = 0 else cfg.head % 2 = 1) ∧
    (∀ z : Int, z % 2 = 1 → cfg.tape z = false)

theorem oddSublatticeCocycle_init : OddSublatticeCocycleInv blankBouncerCfg := by
  unfold OddSublatticeCocycleInv blankBouncerCfg blankTape isEvenBouncerState
  exact ⟨rfl, fun _ _ => rfl⟩

theorem oddSublatticeCocycle_preserved :
    IsInvariant stepRawBouncer OddSublatticeCocycleInv := by
  intro cfg cfg' hInv hStep
  rcases cfg with ⟨tape, head, st⟩
  rcases hInv with ⟨hParity, hOddZero⟩
  dsimp at hOddZero
  cases st <;> simp [isEvenBouncerState] at hParity
  · -- State A (`head % 2 = 0`)
    cases hBit : tape head <;>
      simp [stepRawBouncer, hBit, bouncerDelta] at hStep <;>
      subst hStep <;>
      refine ⟨by simp [isEvenBouncerState]; omega, ?_⟩ <;>
      intro z hz <;> unfold tapeWrite <;>
      have hNe : z ≠ head := by omega
    · simp [hNe, hOddZero z hz]
    · simp [hNe, hOddZero z hz]
  · -- State B (`head % 2 = 1`)
    cases hBit : tape head <;>
      simp [stepRawBouncer, hBit, bouncerDelta] at hStep <;>
      subst hStep <;>
      refine ⟨by simp [isEvenBouncerState]; omega, ?_⟩ <;>
      intro z hz <;> unfold tapeWrite
    · by_cases hEq : z = head
      · simp [hEq]
      · simp [hEq, hOddZero z hz]
    · by_cases hEq : z = head
      · simp [hEq]
      · simp [hEq, hOddZero z hz]
  · -- State C (`head % 2 = 0`)
    cases hBit : tape head <;>
      simp [stepRawBouncer, hBit, bouncerDelta] at hStep <;>
      subst hStep <;>
      refine ⟨by simp [isEvenBouncerState]; omega, ?_⟩ <;>
      intro z hz <;> unfold tapeWrite <;>
      have hNe : z ≠ head := by omega
    · simp [hNe, hOddZero z hz]
    · simp [hNe, hOddZero z hz]
  · -- State D (`head % 2 = 1`)
    cases hBit : tape head <;>
      simp [stepRawBouncer, hBit, bouncerDelta] at hStep <;>
      subst hStep <;>
      refine ⟨by simp [isEvenBouncerState]; omega, ?_⟩ <;>
      intro z hz <;> unfold tapeWrite
    · by_cases hEq : z = head
      · simp [hEq]
      · simp [hEq, hOddZero z hz]
    · by_cases hEq : z = head
      · simp [hEq]
      · simp [hEq, hOddZero z hz]
  · -- State E (`head % 2 = 0`)
    cases hBit : tape head <;>
      simp [stepRawBouncer, hBit, bouncerDelta] at hStep <;>
      subst hStep <;>
      refine ⟨by simp [isEvenBouncerState]; omega, ?_⟩ <;>
      intro z hz <;> unfold tapeWrite <;>
      have hNe : z ≠ head := by omega
    · simp [hNe, hOddZero z hz]
    · simp [hNe, hOddZero z hz]
  · -- State F (`head % 2 = 1`): `tape head` MUST be `false`!
    have hHeadFalse : tape head = false := hOddZero head hParity
    simp [stepRawBouncer, hHeadFalse, bouncerDelta] at hStep
    subst hStep
    refine ⟨by simp [isEvenBouncerState]; omega, ?_⟩
    intro z hz
    unfold tapeWrite
    by_cases hEq : z = head
    · simp [hEq]
    · simp [hEq, hOddZero z hz]

theorem oddSublatticeCocycle_total (cfg : RawBouncerCfg) (hInv : OddSublatticeCocycleInv cfg) :
    ∃ cfg', stepRawBouncer cfg = some cfg' := by
  rcases cfg with ⟨tape, head, st⟩
  rcases hInv with ⟨hParity, hOddZero⟩
  cases st
  · cases hBit : tape head <;> simp [stepRawBouncer, hBit, bouncerDelta]
  · cases hBit : tape head <;> simp [stepRawBouncer, hBit, bouncerDelta]
  · cases hBit : tape head <;> simp [stepRawBouncer, hBit, bouncerDelta]
  · cases hBit : tape head <;> simp [stepRawBouncer, hBit, bouncerDelta]
  · cases hBit : tape head <;> simp [stepRawBouncer, hBit, bouncerDelta]
  · simp [isEvenBouncerState] at hParity
    have hHeadFalse : tape head = false := hOddZero head hParity
    simp [stepRawBouncer, hHeadFalse, bouncerDelta]

theorem oddSublatticeCocycle_safe (cfg : RawBouncerCfg) (hInv : OddSublatticeCocycleInv cfg) :
    stepRawBouncer cfg ≠ none := by
  obtain ⟨cfg', hStep⟩ := oddSublatticeCocycle_total cfg hInv
  rw [hStep]
  intro hNone
  contradiction

/-- **Unconditional Raw-Tape Non-Halting of `1RB0RF_0RE0RE_1RF1LD_0LC0LA_0LD1RF_0LA---`**:
    Even though the 3-cell local NFA reaches `F1 = HALT` in 3 steps, the global space-time
    sublattice 1-cocycle proves that from the blank tape, the raw 6-state parabolic bouncer
    TM NEVER halts for any step count `n : Nat`! -/
theorem bipartite_parabolic_bouncer_tm_never_halts :
    IsNonHalting stepRawBouncer blankBouncerCfg := by
  exact nonHalting_of_safe_invariant
    stepRawBouncer OddSublatticeCocycleInv
    oddSublatticeCocycle_preserved
    oddSublatticeCocycle_safe
    blankBouncerCfg
    oddSublatticeCocycle_init

end CryptidSolvePhase4
