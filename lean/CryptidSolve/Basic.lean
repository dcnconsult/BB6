/-
  CryptidSolve.Basic
  ==================
  Core transition-system semantics, forward-invariant sets, and meta-theorems
  certifying unconditional global aperiodicity (zero periodic orbits) from:
    1. Single-step strict integer Lyapunov drift (`E x + d ≤ E x'`, `d > 0`), and
    2. Single-step lexicographic Lyapunov drift (`(E x, -rank x)`), covering
       multi-register shuttle sweeps without nested loop boilerplate.
-/

namespace CryptidSolve

/-- A deterministic partial macro-transition function:
    `some s'` denotes survival to next macro-state `s'`; `none` denotes `Halt`. -/
abbrev StepFn (S : Type) := S → Option S

/-- `n`-step iteration of a partial macro-transition function. -/
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

theorem iterStep_invariant {S : Type} (step : StepFn S) (P : S → Prop)
    (hInv : IsInvariant step P) :
    ∀ n x y, P x → iterStep step n x = some y → P y
  | 0, _, _, hx, hIter => by
      simp [iterStep] at hIter
      cases hIter
      exact hx
  | n + 1, x, y, hx, hIter => by
      simp only [iterStep] at hIter
      split at hIter
      · contradiction
      · rename_i x' hStep
        have hx' : P x' := hInv x x' hx hStep
        exact iterStep_invariant step P hInv n x' y hx' hIter

/-- Multi-step linear growth under a strict single-step integer Lyapunov functional. -/
theorem iterStep_strict_lyapunov_drift {S : Type} (step : StepFn S) (P : S → Prop)
    (E : S → Nat) (d : Nat)
    (hInv : IsInvariant step P)
    (hDrift : ∀ x x', P x → step x = some x' → E x + d ≤ E x') :
    ∀ n x y, P x → iterStep step n x = some y → E x + n * d ≤ E y
  | 0, _, _, _, hIter => by
      simp [iterStep] at hIter
      cases hIter
      omega
  | n + 1, x, y, hx, hIter => by
      simp only [iterStep] at hIter
      split at hIter
      · contradiction
      · rename_i x' hStep
        have hx' : P x' := hInv x x' hx hStep
        have h1 : E x + d ≤ E x' := hDrift x x' hx hStep
        have h2 : E x' + n * d ≤ E y :=
          iterStep_strict_lyapunov_drift step P E d hInv hDrift n x' y hx' hIter
        have hMul : (n + 1) * d = d + n * d := by
          rw [Nat.add_mul, Nat.one_mul, Nat.add_comm (n * d) d]
        omega

/-- Master Stage-3a / Stage-3b Meta-Theorem (Single-Step Strict Lyapunov):
    Any positive-drift integer Lyapunov functional `E x + d ≤ E x'` (`d > 0`)
    on a forward-invariant domain `P` unconditionally rules out all periodic orbits. -/
theorem no_periodic_of_strict_lyapunov {S : Type} (step : StepFn S) (P : S → Prop)
    (E : S → Nat) (d : Nat) (hd : d > 0)
    (hInv : IsInvariant step P)
    (hDrift : ∀ x x', P x → step x = some x' → E x + d ≤ E x')
    (x : S) (hx : P x) : ¬ IsPeriodic step x := by
  intro hPer
  cases hPer with
  | intro n hn =>
    cases hn with
    | intro hnPos hLoop =>
      cases n with
      | zero => omega
      | succ k =>
        have hStepBound : E x + (k + 1) * d ≤ E x :=
          iterStep_strict_lyapunov_drift step P E d hInv hDrift (k + 1) x x hx hLoop
        have hPosDrift : (k + 1) * d ≥ d := by
          rw [Nat.add_mul, Nat.one_mul]
          omega
        omega

/-- Strict lexicographic progress: primary energy `E` increases, or `E` stays
    constant while secondary sweep rank `rank` strictly decreases. -/
def LexProgress {S : Type} (E rank : S → Nat) (x x' : S) : Prop :=
  E x < E x' ∨ (E x = E x' ∧ rank x' < rank x)

theorem lexProgress_trans {S : Type} {E rank : S → Nat} {x y z : S}
    (h1 : LexProgress E rank x y) (h2 : LexProgress E rank y z) :
    LexProgress E rank x z := by
  unfold LexProgress at *
  omega

theorem iterStep_lex_lyapunov_drift {S : Type} (step : StepFn S) (P : S → Prop)
    (E rank : S → Nat)
    (hInv : IsInvariant step P)
    (hLex : ∀ x x', P x → step x = some x' → LexProgress E rank x x') :
    ∀ k x y, P x → iterStep step (k + 1) x = some y → LexProgress E rank x y
  | 0, x, y, hx, hIter => by
      simp only [iterStep] at hIter
      split at hIter
      · contradiction
      · rename_i x' hStep
        simp [iterStep] at hIter
        cases hIter
        exact hLex x _ hx hStep
  | k + 1, x, y, hx, hIter => by
      simp only [iterStep] at hIter
      split at hIter
      · contradiction
      · rename_i x' hStep
        have hx' : P x' := hInv x x' hx hStep
        have h1 : LexProgress E rank x x' := hLex x x' hx hStep
        have h2 : LexProgress E rank x' y :=
          iterStep_lex_lyapunov_drift step P E rank hInv hLex k x' y hx' hIter
        exact lexProgress_trans h1 h2

/-- Master Lexicographic Meta-Theorem:
    If `(E, rank)` makes strict lexicographic progress on every surviving step,
    then `x` admits zero periodic orbits (`iterStep step n x ≠ some x` for all `n > 0`). -/
theorem no_periodic_of_lex_lyapunov {S : Type} (step : StepFn S) (P : S → Prop)
    (E rank : S → Nat)
    (hInv : IsInvariant step P)
    (hLex : ∀ x x', P x → step x = some x' → LexProgress E rank x x')
    (x : S) (hx : P x) : ¬ IsPeriodic step x := by
  intro hPer
  cases hPer with
  | intro n hn =>
    cases hn with
    | intro hnPos hLoop =>
      cases n with
      | zero => omega
      | succ k =>
        have hProg : LexProgress E rank x x :=
          iterStep_lex_lyapunov_drift step P E rank hInv hLex k x x hx hLoop
        unfold LexProgress at hProg
        omega

end CryptidSolve
