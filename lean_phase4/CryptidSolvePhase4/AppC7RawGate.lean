import CryptidSolvePhase4.Transfer2PutinarSOS

/-!
Exact raw-machine refinement for the AppC7 quadratic gate.
Machine: 1RB1RC_1LC0LE_0RA1RD_1RF1LB_1LD0LA_---0RC.
The finite zipper stores cells nearest the head first on each side. Missing
cells are zero. No macro transition is built into the one-step semantics.
-/
namespace CryptidSolvePhase4.AppC7Raw

inductive State where
  | A | B | C | D | E | F
  deriving DecidableEq, Repr

def delta : State → Bool → Option (Bool × Bool × State)
  | .A, false => some (true, true, .B)
  | .A, true  => some (true, true, .C)
  | .B, false => some (true, false, .C)
  | .B, true  => some (false, false, .E)
  | .C, false => some (false, true, .A)
  | .C, true  => some (true, true, .D)
  | .D, false => some (true, true, .F)
  | .D, true  => some (true, false, .B)
  | .E, false => some (true, false, .D)
  | .E, true  => some (false, false, .A)
  | .F, false => none
  | .F, true  => some (false, true, .C)

structure Cfg where
  st : State
  left : List Bool
  right : List Bool
  deriving DecidableEq, Repr

def read : List Bool → Bool
  | [] => false
  | b :: _ => b

def step (c : Cfg) : Option Cfg :=
  match delta c.st (read c.right) with
  | none => none
  | some (w, dir, st) =>
      if dir then some ⟨st, w :: c.left, c.right.tail⟩
      else some ⟨st, c.left.tail, read c.left :: w :: c.right.tail⟩

def run : Nat → Cfg → Option Cfg
  | 0, c => some c
  | n + 1, c => (step c).bind (run n)

theorem run_add (n m : Nat) (c : Cfg) :
    run (n + m) c = (run n c).bind (run m) := by
  induction n generalizing c with
  | zero => simp [run]
  | succ n ih =>
      simp only [Nat.succ_add, run]
      cases h : step c <;> simp [h, ih]

theorem run_comp {n m : Nat} {c d e : Cfg}
    (h : run n c = some d) (h' : run m d = some e) :
    run (n + m) c = some e := by
  rw [run_add, h]
  exact h'

/-- Exactly n defined transitions, followed by the undefined F0 instruction.
    The Python simulator reports this as halting attempt n+1. -/
def HaltsAfter (n : Nat) (c : Cfg) : Prop :=
  ∃ d, run n c = some d ∧ step d = none

theorem halts_comp {n m : Nat} {c d : Cfg}
    (h : run n c = some d) (h' : HaltsAfter m d) :
    HaltsAfter (n + m) c := by
  obtain ⟨e, he, hs⟩ := h'
  exact ⟨e, run_comp h he, hs⟩

def pairs : Nat → List Bool → List Bool
  | 0, t => t
  | n + 1, t => true :: false :: pairs n t

def back : Nat → List Bool → List Bool
  | 0, t => t
  | n + 1, t => false :: true :: back n t

def blocks : Nat → List Bool → List Bool
  | 0, t => t
  | n + 1, t => true :: true :: true :: false :: blocks n t

theorem back_push (n : Nat) (t : List Bool) :
    back n (false :: true :: t) = false :: true :: back n t := by
  induction n with
  | zero => rfl
  | succ n ih => simp [back, ih]

theorem pair_push (n : Nat) (t : List Bool) :
    pairs n (true :: false :: t) = true :: false :: pairs n t := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pairs, ih]

theorem back_to_pairs (n : Nat) (t : List Bool) :
    true :: back n (false :: t) = pairs n (true :: false :: t) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [back, pairs]; rw [ih]

/-- A raw two-instruction scan across each 10 block. -/
theorem scan_right (n : Nat) (l t : List Bool) :
    run (2 * n) ⟨.A, l, pairs n t⟩ = some ⟨.A, back n l, t⟩ := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
      have first : run 2 ⟨.A, l, pairs (n+1) t⟩ =
          some ⟨.A, false :: true :: l, pairs n t⟩ := rfl
      have h := run_comp first (ih (false :: true :: l))
      rw [back_push] at h
      rw [show 2 * (n+1) = 2 + 2*n by omega]
      exact h

/-- Ten literal instructions turn the 1110 block into the return sweep. -/
theorem turn_block (x : Bool) (l t : List Bool) :
    run 10 ⟨.A, false :: x :: l, true :: true :: true :: false :: t⟩ =
      some ⟨.E, l, x :: false :: true :: false :: true :: false :: t⟩ := by
  rfl

/-- Six literal instructions move the E return sweep across one old pair. -/
theorem return_pair (x : Bool) (l t : List Bool) :
    run 6 ⟨.E, false :: x :: l, true :: t⟩ =
      some ⟨.E, l, x :: false :: true :: t⟩ := by
  rfl

theorem return_sweep (n : Nat) (t : List Bool) :
    run (6 * (n+1)) ⟨.E, back n [false, false, true], true :: t⟩ =
      some ⟨.E, [true], false :: back (n+1) t⟩ := by
  induction n generalizing t with
  | zero => exact return_pair false [true] t
  | succ n ih =>
      have first := return_pair true (back n [false, false, true]) t
      have h := run_comp first (ih (false :: true :: t))
      rw [back_push] at h
      rw [show 6 * (n+1+1) = 6 + 6*(n+1) by omega]
      exact h

theorem turn_and_return (n : Nat) (t : List Bool) :
    run (10 + 6*n) ⟨.A, back n [false, false, true],
        true :: true :: true :: false :: t⟩ =
      some ⟨.E, [true], false :: back n (false :: true :: false :: true :: false :: t)⟩ := by
  cases n with
  | zero => exact turn_block false [true] t
  | succ n =>
      have h := run_comp (turn_block true (back n [false, false, true]) t)
        (return_sweep n (false :: true :: false :: true :: false :: t))
      exact h

/-- The blank-left boundary is handled by fifteen actual instructions. -/
theorem left_boundary (t : List Bool) :
    run 15 ⟨.E, [true], false :: t⟩ =
      some ⟨.D, [], false :: true :: false :: true :: false :: true :: t⟩ := by
  rfl

theorem phase_word (n : Nat) (t : List Bool) :
    true :: false :: true :: false :: true ::
      back n (false :: true :: false :: true :: false :: t) = pairs (n+5) t := by
  rw [back_to_pairs]
  simp only [pairs]
  rw [pair_push, pair_push, pair_push]

/-- Universal raw AppC7 phase: consume one 1110 block, grow the 10 prefix by four.
    The start/end head is on the blank immediately left of the displayed word.
    This theorem applies for every positive prefix length and arbitrary right tail. -/
theorem gate_phase (n : Nat) (t : List Bool) :
    run (8*(n+1)+20)
      ⟨.D, [], false :: pairs (n+1) (true :: true :: true :: false :: t)⟩ =
      some ⟨.D, [], false :: pairs (n+5) t⟩ := by
  have first : run 3
      ⟨.D, [], false :: pairs (n+1) (true :: true :: true :: false :: t)⟩ =
      some ⟨.A, [false, false, true], pairs n (true :: true :: true :: false :: t)⟩ := rfl
  have h1 := run_comp first (scan_right n [false, false, true] (true :: true :: true :: false :: t))
  have h2 := run_comp h1 (turn_and_return n t)
  have h3 := run_comp h2 (left_boundary (back n (false :: true :: false :: true :: false :: t)))
  rw [phase_word] at h3
  rw [show 8*(n+1)+20 = 3+2*n+(10+6*n)+15 by omega]
  exact h3

theorem gate_terminal (n : Nat) :
    HaltsAfter (2*(n+1)+4) ⟨.D, [], false :: pairs (n+1) [true, true]⟩ := by
  have first : run 3 ⟨.D, [], false :: pairs (n+1) [true,true]⟩ =
      some ⟨.A, [false,false,true], pairs n [true,true]⟩ := rfl
  have h := run_comp first (scan_right n [false,false,true] [true,true])
  have last : run 3 ⟨.A, back n [false,false,true], [true,true]⟩ =
      some ⟨.F, true :: true :: true :: back n [false,false,true], []⟩ := rfl
  have done := run_comp h last
  refine ⟨⟨.F, true :: true :: true :: back n [false,false,true], []⟩, ?_, rfl⟩
  rw [show 2*(n+1)+4 = 3+2*n+3 by omega]
  exact done

theorem gate_phase_zero (t : List Bool) :
    run 20 ⟨.D, [], false :: true :: true :: true :: false :: t⟩ =
      some ⟨.D, [], false :: pairs 4 t⟩ := by
  rfl

theorem gate_phase_all (a : Nat) (t : List Bool) :
    run (8*a+20) ⟨.D, [], false :: pairs a (true :: true :: true :: false :: t)⟩ =
      some ⟨.D, [], false :: pairs (a+4) t⟩ := by
  cases a with
  | zero => exact gate_phase_zero t
  | succ n => exact gate_phase n t

theorem gate_terminal_all (a : Nat) :
    HaltsAfter (2*a+4) ⟨.D, [], false :: pairs a [true,true]⟩ := by
  cases a with
  | zero => exact ⟨⟨.F, [true,true,false,true], []⟩, rfl, rfl⟩
  | succ n => exact gate_terminal n

def gateCfg (a r : Nat) : Cfg :=
  ⟨.D, [], false :: pairs a (blocks r [true,true])⟩

/-- Full raw-to-counter refinement of the quadratic gate recurrence. -/
theorem gate_sweep (r a : Nat) :
    HaltsAfter (appC7GateSweep a r - 1) (gateCfg a r) := by
  induction r generalizing a with
  | zero =>
      simpa [gateCfg, blocks, appC7GateSweep] using gate_terminal_all a
  | succ r ih =>
      have phase : run (8*a+20) (gateCfg a (r+1)) =
          some (gateCfg (a+4) r) := gate_phase_all a (blocks r [true,true])
      have endRun := ih (a+4)
      have h := halts_comp phase endRun
      have pos : 1 ≤ appC7GateSweep (a+4) r := by
        rw [appC7GateSweep_closed_form]
        omega
      have eqCount : appC7GateSweep a (r+1) - 1 =
          (8*a+20) + (appC7GateSweep (a+4) r - 1) := by
        simp only [appC7GateSweep]
        omega
      rw [eqCount]
      exact h

def initial (b : Nat) : Cfg :=
  ⟨.A, [], false :: false :: false :: blocks b [true,true]⟩

theorem initial_prefix (b : Nat) : run 6 (initial b) = some (gateCfg 2 b) := by
  rfl

/-- All b: the actual AppC7 machine, started at <A:0> 00 (1110)^b 11,
    executes exactly 16*b*b+28*b+14 defined transitions, then halts on the
    next attempted instruction. This is not the blank-tape initial condition. -/
theorem appC7_raw_gate_halts (b : Nat) :
    HaltsAfter (16*b*b + 28*b + 14) (initial b) := by
  have h := halts_comp (initial_prefix b) (gate_sweep b 2)
  have law := appC7_parabolic_gate_step_law b
  have pos : 1 ≤ appC7GateSweep 2 b := by
    rw [appC7GateSweep_closed_form]
    omega
  have count : 6 + (appC7GateSweep 2 b - 1) = 16*b*b + 28*b + 14 := by omega
  rw [count] at h
  exact h

/-- A successful run cannot have passed an earlier undefined instruction. -/
theorem halts_prefix_defined {n : Nat} {c : Cfg} (h : HaltsAfter n c)
    (m : Nat) (hm : m ≤ n) : ∃ d, run m c = some d := by
  obtain ⟨d, hd, _⟩ := h
  have split : n = m + (n-m) := by omega
  rw [split, run_add] at hd
  cases hs : run m c with
  | none => simp [hs] at hd
  | some e => exact ⟨e, rfl⟩

theorem halts_next_none {n : Nat} {c : Cfg} (h : HaltsAfter n c) :
    run (n+1) c = none := by
  obtain ⟨d, hd, hs⟩ := h
  rw [run_add, hd]
  simp [run, hs]

/-- Every natural a,r: exact first halting attempt for the raw gate configuration,
    refining the complete recurrence, including its zero-prefix boundary. -/
theorem gate_sweep_exact_time (a r : Nat) :
    (∀ t, t < appC7GateSweep a r → ∃ c, run t (gateCfg a r) = some c) ∧
      run (appC7GateSweep a r) (gateCfg a r) = none := by
  have h := gate_sweep r a
  have pos : 1 ≤ appC7GateSweep a r := by
    rw [appC7GateSweep_closed_form]
    omega
  constructor
  · intro t ht
    exact halts_prefix_defined h t (by omega)
  · have last := halts_next_none h
    rw [show appC7GateSweep a r - 1 + 1 = appC7GateSweep a r by omega] at last
    exact last

/-- The simulator's 1-based halting-attempt count is exactly the published
    polynomial, with every preceding execution prefix defined. -/
theorem appC7_raw_gate_exact_time (b : Nat) :
    (∀ t, t < 16*b*b + 28*b + 15 → ∃ c, run t (initial b) = some c) ∧
      run (16*b*b + 28*b + 15) (initial b) = none := by
  have h := appC7_raw_gate_halts b
  constructor
  · intro t ht
    exact halts_prefix_defined h t (by omega)
  · have last := halts_next_none h
    exact last

end CryptidSolvePhase4.AppC7Raw
