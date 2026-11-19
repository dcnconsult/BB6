/-
  CryptidSolvePhase4.Basic
  ========================
  Foundational transition-system theory for the
  Phase 4 algebraic examples.

  Upgrades Phases 1-3 (`¬ IsPeriodic`, ruling out finite cycles) to:
    1. True Unconditional Non-Halting (`IsNonHalting`: `∀ n, iterStep step n x ≠ none`),
    2. Prajna-Jadbabaie Barrier Certificate Non-Halting (`nonHalting_of_barrier_cert`), and
    3. Immortal Distinct-State Orbits (`IsImmortalOrbit`: never halts AND never repeats).

  Zero external dependencies (pure Lean 4 Core `Init` + `omega` + `decide`).
-/

namespace CryptidSolvePhase4

/-- Deterministic partial transition function:
    `some s'` denotes survival to next state `s'`; `none` denotes `Halt`. -/
abbrev StepFn (S : Type) := S → Option S

/-- `n`-step iteration of a partial transition function. -/
def iterStep {S : Type} (step : StepFn S) : Nat → S → Option S
  | 0, x => some x
  | n + 1, x =>
      match step x with
      | none => none
      | some x' => iterStep step n x'

/-- Forward invariance of a state predicate `P` under surviving steps. -/
def IsInvariant {S : Type} (step : StepFn S) (P : S → Prop) : Prop :=
  ∀ x x', P x → step x = some x' → P x'

/-- State `x` lies on a non-trivial periodic orbit of period `n > 0`. -/
def IsPeriodic {S : Type} (step : StepFn S) (x : S) : Prop :=
  ∃ n : Nat, n > 0 ∧ iterStep step n x = some x

/-- True unconditional non-halting: `x` survives `n` steps for EVERY `n : Nat`. -/
def IsNonHalting {S : Type} (step : StepFn S) (x : S) : Prop :=
  ∀ n : Nat, iterStep step n x ≠ none

/-- Immortal orbit: `x` never halts (`IsNonHalting`) AND visits pairwise distinct
    configurations at all distinct times `m < n`. -/
def IsImmortalOrbit {S : Type} (step : StepFn S) (x : S) : Prop :=
  IsNonHalting step x ∧ ∀ m n : Nat, m < n → iterStep step m x ≠ iterStep step n x

/-- Addition law `iterStep step (m + k) x` along a surviving `m`-step prefix. -/
theorem iterStep_add_of_some {S : Type} (step : StepFn S) :
    ∀ m k : Nat, ∀ x y : S,
      iterStep step m x = some y → iterStep step (m + k) x = iterStep step k y
  | 0, k, _, y, h => by
      simp [iterStep] at h
      subst h
      simp
  | m + 1, k, x, y, h => by
      simp only [iterStep] at h
      split at h
      · contradiction
      · rename_i x' hStep
        have hIdx : m + 1 + k = (m + k) + 1 := by omega
        rw [hIdx]
        simp only [iterStep, hStep]
        exact iterStep_add_of_some step m k x' y h

/-- Inductive preservation of a forward-invariant predicate `P`. -/
theorem iterStep_invariant {S : Type} (step : StepFn S) (P : S → Prop)
    (hInv : IsInvariant step P) :
    ∀ n : Nat, ∀ x y : S, P x → iterStep step n x = some y → P y
  | 0, _, y, hx, hIter => by
      simp [iterStep] at hIter
      subst hIter
      exact hx
  | n + 1, x, y, hx, hIter => by
      simp only [iterStep] at hIter
      split at hIter
      · contradiction
      · rename_i x' hStep
        exact iterStep_invariant step P hInv n x' y (hInv x x' hx hStep) hIter

/-- Master Inductive Safety Meta-Theorem:
    If `P` is forward-invariant and every state satisfying `P` has a valid successor
    (`step x ≠ none`), then every initial state in `P` is unconditionally non-halting,
    producing a witness `y` in `P` at every step `n`. -/
theorem iterStep_exists_of_safe_invariant {S : Type} (step : StepFn S) (P : S → Prop)
    (hInv : IsInvariant step P)
    (hSafe : ∀ x : S, P x → step x ≠ none) :
    ∀ n : Nat, ∀ x : S, P x → ∃ y : S, iterStep step n x = some y ∧ P y
  | 0, x, hx => ⟨x, rfl, hx⟩
  | n + 1, x, hx => by
      cases hStep : step x with
      | none => exact False.elim (hSafe x hx hStep)
      | some x' =>
          have hx' : P x' := hInv x x' hx hStep
          simp only [iterStep, hStep]
          exact iterStep_exists_of_safe_invariant step P hInv hSafe n x' hx'

theorem nonHalting_of_safe_invariant {S : Type} (step : StepFn S) (P : S → Prop)
    (hInv : IsInvariant step P)
    (hSafe : ∀ x : S, P x → step x ≠ none)
    (x0 : S) (hx0 : P x0) : IsNonHalting step x0 := by
  intro n
  obtain ⟨y, hy, _⟩ := iterStep_exists_of_safe_invariant step P hInv hSafe n x0 hx0
  rw [hy]
  intro hNone
  contradiction

/-- Abstract Prajna-Jadbabaie Barrier Meta-Theorem over `Int`:
    Given a domain invariant `Dom`, a barrier functional `B : S → Int`, and initial state `x0`:
      1. `Dom x0` and `B x0 < 0`,
      2. `Dom` is preserved by surviving steps,
      3. `B x' ≤ B x` along surviving steps inside `Dom`, and
      4. Every halting state inside `Dom` (`step x = none`) forces `0 ≤ B x`,
    `x0` is unconditionally non-halting (`IsNonHalting step x0`). -/
theorem nonHalting_of_barrier_cert {S : Type} (step : StepFn S)
    (Dom : S → Prop) (B : S → Int)
    (hDomInv : IsInvariant step Dom)
    (hBarrierMono : ∀ x x' : S, Dom x → B x < 0 → step x = some x' → B x' ≤ B x)
    (hHaltNonneg : ∀ x : S, Dom x → step x = none → 0 ≤ B x)
    (x0 : S) (hDom0 : Dom x0) (hInitNeg : B x0 < 0) :
    IsNonHalting step x0 := by
  let P : S → Prop := fun x => Dom x ∧ B x < 0
  have hPInv : IsInvariant step P := by
    intro x x' hx hStep
    refine ⟨hDomInv x x' hx.1 hStep, ?_⟩
    have hLe := hBarrierMono x x' hx.1 hx.2 hStep
    omega
  have hPSafe : ∀ x : S, P x → step x ≠ none := by
    intro x hx hNone
    have hGe := hHaltNonneg x hx.1 hNone
    have hLt := hx.2
    omega
  exact nonHalting_of_safe_invariant step P hPInv hPSafe x0 ⟨hDom0, hInitNeg⟩

/-- Multi-step strict integer Lyapunov drift over `Int`. -/
theorem iterStep_strict_int_drift {S : Type} (step : StepFn S) (P : S → Prop)
    (E : S → Int) (d : Int)
    (hInv : IsInvariant step P)
    (hDrift : ∀ x x' : S, P x → step x = some x' → E x + d ≤ E x') :
    ∀ n : Nat, ∀ x y : S, P x → iterStep step n x = some y → E x + (n : Int) * d ≤ E y
  | 0, _, y, _, hIter => by
      simp [iterStep] at hIter
      subst hIter
      omega
  | n + 1, x, y, hx, hIter => by
      simp only [iterStep] at hIter
      split at hIter
      · contradiction
      · rename_i x' hStep
        have hx' : P x' := hInv x x' hx hStep
        have h1 : E x + d ≤ E x' := hDrift x x' hx hStep
        have h2 : E x' + (n : Int) * d ≤ E y :=
          iterStep_strict_int_drift step P E d hInv hDrift n x' y hx' hIter
        have hCast : ((n + 1 : Nat) : Int) * d = (n : Int) * d + d := by
          rw [Int.natCast_add, Int.add_mul]
          simp
        omega

/-- Strict integer drift (`d > 0`) rules out all periodic orbits. -/
theorem no_periodic_of_strict_int_drift {S : Type} (step : StepFn S) (P : S → Prop)
    (E : S → Int) (d : Int) (hd : 0 < d)
    (hInv : IsInvariant step P)
    (hDrift : ∀ x x' : S, P x → step x = some x' → E x + d ≤ E x')
    (x : S) (hx : P x) : ¬ IsPeriodic step x := by
  intro ⟨n, hnPos, hLoop⟩
  cases n with
  | zero => omega
  | succ k =>
      have hBound := iterStep_strict_int_drift step P E d hInv hDrift (k + 1) x x hx hLoop
      have hPos : 0 < ((k + 1 : Nat) : Int) * d :=
        Int.mul_pos (by omega) hd
      omega

/-- Unified Immortal-Orbit Meta-Theorem:
    Combining a safe forward-invariant `P` (`step x ≠ none`) with a positive-drift
    functional `E x + d ≤ E x'` (`d > 0`) certifies `IsImmortalOrbit step x0`:
    `x0` never halts AND visits pairwise distinct states for all `m < n`. -/
theorem immortal_of_safe_invariant_and_drift {S : Type} (step : StepFn S) (P : S → Prop)
    (E : S → Int) (d : Int) (hd : 0 < d)
    (hInv : IsInvariant step P)
    (hSafe : ∀ x : S, P x → step x ≠ none)
    (hDrift : ∀ x x' : S, P x → step x = some x' → E x + d ≤ E x')
    (x0 : S) (hx0 : P x0) : IsImmortalOrbit step x0 := by
  refine ⟨nonHalting_of_safe_invariant step P hInv hSafe x0 hx0, ?_⟩
  intro m n hmn hEq
  obtain ⟨ym, hym, hPm⟩ := iterStep_exists_of_safe_invariant step P hInv hSafe m x0 hx0
  obtain ⟨yn, hyn, _⟩ := iterStep_exists_of_safe_invariant step P hInv hSafe n x0 hx0
  rw [hym, hyn] at hEq
  injection hEq with hSame
  subst hSame
  have hSplit : n = m + (n - m) := by omega
  rw [hSplit] at hyn
  have hTail : iterStep step (n - m) ym = some ym := by
    rw [← iterStep_add_of_some step m (n - m) x0 ym hym]
    exact hyn
  have hPer : IsPeriodic step ym := ⟨n - m, by omega, hTail⟩
  exact no_periodic_of_strict_int_drift step P E d hd hInv hDrift ym hPm hPer

end CryptidSolvePhase4
