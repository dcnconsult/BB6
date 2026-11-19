import CryptidSolvePhase4.Transfer4WreathBlockGauge

/-!
Universal raw AppC8 shuttle refinement.
Machine: 1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---.
The zipper represents the tape relative to the head; missing cells are zero.
Only the literal twelve-entry transition table is used by step.
-/
namespace CryptidSolvePhase4.AppC8Raw

inductive State where
  | A | B | C | D | E | F
  deriving DecidableEq, Repr

def delta : State → Bool → Option (Bool × Bool × State)
  | .A, false => some (true, true, .B)
  | .A, true  => some (true, false, .C)
  | .B, false => some (true, false, .A)
  | .B, true  => some (false, true, .D)
  | .C, false => some (false, false, .B)
  | .C, true  => some (true, false, .F)
  | .D, false => some (true, true, .E)
  | .D, true  => some (true, false, .C)
  | .E, false => some (true, false, .C)
  | .E, true  => some (false, true, .B)
  | .F, false => some (false, false, .A)
  | .F, true  => none

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
  | n+1, c => (step c).bind (run n)

theorem run_add (n m : Nat) (c : Cfg) :
    run (n+m) c = (run n c).bind (run m) := by
  induction n generalizing c with
  | zero => simp [run]
  | succ n ih =>
      simp only [Nat.succ_add, run]
      cases h : step c <;> simp [h, ih]

theorem run_comp {n m : Nat} {c d e : Cfg}
    (h : run n c = some d) (h' : run m d = some e) :
    run (n+m) c = some e := by
  rw [run_add, h]
  exact h'

def blocks : Nat → List Bool → List Bool
  | 0, t => t
  | n+1, t => true :: true :: false :: blocks n t

def back : Nat → List Bool → List Bool
  | 0, t => t
  | n+1, t => true :: false :: false :: back n t

def returnWord : Nat → List Bool → List Bool
  | 0, t => t
  | n+1, t => true :: false :: true :: returnWord n t

def ones : Nat → List Bool → List Bool
  | 0, t => t
  | n+1, t => true :: ones n t

theorem back_push (n : Nat) (t : List Bool) :
    back n (true :: false :: false :: t) = true :: false :: false :: back n t := by
  induction n with
  | zero => rfl
  | succ n ih => simp [back, ih]

theorem return_push (n : Nat) (t : List Bool) :
    returnWord n (true :: false :: true :: t) =
      true :: false :: true :: returnWord n t := by
  induction n with
  | zero => rfl
  | succ n ih => simp [returnWord, ih]

theorem back_read (n : Nat) (l : List Bool) : read (back n (true :: l)) = true := by
  cases n <;> rfl

/-- Each literal E/B/D triplet converts 110 into 001 while scanning right. -/
theorem scan_right (n : Nat) (l t : List Bool) :
    run (3*n) ⟨.E, l, blocks n t⟩ = some ⟨.E, back n l, t⟩ := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
      have first : run 3 ⟨.E, l, blocks (n+1) t⟩ =
          some ⟨.E, true :: false :: false :: l, blocks n t⟩ := rfl
      have h := run_comp first (ih (true :: false :: false :: l))
      rw [back_push] at h
      rw [show 3*(n+1) = 3+3*n by omega]
      exact h

/-- The five-instruction turn inspects only the three leading ones. -/
theorem turn (l t : List Bool) :
    run 5 ⟨.E, l, true :: true :: true :: t⟩ =
      some ⟨.A, l.tail, read l :: true :: false :: true :: t⟩ := by
  rfl

theorem return_triplet (l t : List Bool) :
    run 3 ⟨.A, false :: false :: l, true :: t⟩ =
      some ⟨.A, l.tail, read l :: true :: false :: true :: t⟩ := by
  rfl

/-- Raw return sweep, leaving the unvisited suffix unchanged. -/
theorem scan_left (n : Nat) (l t : List Bool) :
    run (3*n) ⟨.A, (back n (true :: l)).tail, true :: t⟩ =
      some ⟨.A, l, true :: returnWord n t⟩ := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      have first := return_triplet (back n (true :: l)) t
      rw [back_read] at first
      have h := run_comp first (ih (true :: false :: true :: t))
      rw [return_push] at h
      rw [show 3*(n+1) = 3+3*n by omega]
      exact h

theorem turn_and_return (n : Nat) (l t : List Bool) :
    run (5+3*n) ⟨.E, back n (true :: l), true :: true :: true :: t⟩ =
      some ⟨.A, l, true :: returnWord n (true :: false :: true :: t)⟩ := by
  have first := turn (back n (true :: l)) t
  rw [back_read] at first
  exact run_comp first (scan_left n l (true :: false :: true :: t))

theorem close_word (n : Nat) (t : List Bool) :
    true :: returnWord n (true :: false :: t) = blocks (n+1) t := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [returnWord, blocks]; rw [ih]; rfl

theorem entry (t : List Bool) :
    run 3 ⟨.A, [], false :: true :: false :: t⟩ =
      some ⟨.E, [true, false, true], t⟩ := by
  rfl

theorem middle_boundary (t : List Bool) :
    run 4 ⟨.A, [false, true], true :: t⟩ =
      some ⟨.E, [true, false], true :: t⟩ := by
  rfl

theorem final_boundary (t : List Bool) :
    run 3 ⟨.A, [false], true :: t⟩ =
      some ⟨.A, [], false :: true :: false :: true :: t⟩ := by
  rfl

/-- Complete raw shuttle for every block count and arbitrary finite right tail.
    Five leading ones are consumed down to one; the tail is untouched. -/
theorem shuttle_with_tail (k : Nat) (t : List Bool) :
    run (12*k+26)
      ⟨.A, [], false :: true :: false :: blocks k (true :: true :: true :: true :: true :: t)⟩ =
      some ⟨.A, [], false :: true :: false :: blocks (k+2) (true :: t)⟩ := by
  have h1 := run_comp (entry (blocks k (true :: true :: true :: true :: true :: t)))
    (scan_right k [true, false, true] (true :: true :: true :: true :: true :: t))
  have h2 := run_comp h1 (turn_and_return k [false, true] (true :: true :: t))
  have h3 := run_comp h2 (middle_boundary (returnWord k (true :: false :: true :: true :: true :: t)))
  rw [close_word] at h3
  have h4 := run_comp h3 (scan_right (k+1) [true, false] (true :: true :: true :: t))
  have h5 := run_comp h4 (turn_and_return (k+1) [false] t)
  have h6 := run_comp h5 (final_boundary (returnWord (k+1) (true :: false :: true :: t)))
  rw [close_word] at h6
  rw [show 12*k+26 = 3+3*k+(5+3*k)+4+3*(k+1)+(5+3*(k+1))+3 by omega]
  exact h6

def shuttleCfg (k m : Nat) : Cfg :=
  ⟨.A, [], false :: true :: false :: blocks k (ones m [])⟩

/-- The requested universal raw-TM refinement, including both boundary cases
    k=0 and m=5. The elapsed count is defined transitions, not a halting attempt. -/
theorem appC8_raw_shuttle (k m : Nat) (hm : m ≥ 5) :
    run (12*k+26) (shuttleCfg k m) = some (shuttleCfg (k+2) (m-4)) := by
  have h := shuttle_with_tail k (ones (m-5) [])
  have hm1 : m = (m-5)+5 := by omega
  have hm2 : m-4 = (m-5)+1 := by omega
  have h' : run (12*k+26) (shuttleCfg k ((m-5)+5)) =
      some (shuttleCfg (k+2) ((m-5)+1)) := h
  rw [← hm1, ← hm2] at h'
  exact h'

/-- A successful raw execution has no undefined instruction in any prefix. -/
theorem run_prefix_defined {n : Nat} {c d : Cfg} (h : run n c = some d)
    (j : Nat) (hj : j ≤ n) : ∃ e, run j c = some e := by
  rw [show n = j+(n-j) by omega, run_add] at h
  cases he : run j c with
  | none => simp [he] at h
  | some e => exact ⟨e, rfl⟩

theorem appC8_shuttle_survives (k m j : Nat) (hm : m ≥ 5) (hj : j ≤ 12*k+26) :
    ∃ e, run j (shuttleCfg k m) = some e :=
  run_prefix_defined (appC8_raw_shuttle k m hm) j hj

/-- Compose any number of actual raw shuttle rounds, provided at least one
    trailing one remains after all rounds. -/
theorem appC8_raw_shuttle_rounds (r k m : Nat) (hm : m ≥ 4*r+1) :
    run (appC8ShuttleRoundsSteps k r) (shuttleCfg k m) =
      some (shuttleCfg (k+2*r) (m-4*r)) := by
  induction r generalizing k m with
  | zero => simp [appC8ShuttleRoundsSteps, run]
  | succ r ih =>
      have h := run_comp (appC8_raw_shuttle k m (by omega))
        (ih (k+2) (m-4) (by omega))
      have hk : k+2+2*r = k+2*(r+1) := by omega
      have hm' : m-4-4*r = m-4*(r+1) := by omega
      rw [hk, hm'] at h
      exact h

theorem appC8_raw_rounds_closed_form (r k m : Nat) (hm : m ≥ 4*r+1) :
    run (12*(r*k) + 12*(r*(r-1)) + 26*r) (shuttleCfg k m) =
      some (shuttleCfg (k+2*r) (m-4*r)) := by
  have h := appC8_raw_shuttle_rounds r k m hm
  rw [appC8ShuttleRoundsSteps_closed_form] at h
  exact h

/-- The middle stage of the clean macro is now a raw theorem for all q.
    The reset and exit are proved separately in AppC8RawCleanMacro.lean. -/
theorem appC8_clean_middle_raw (q : Nat) :
    run (appC8ShuttleRoundsSteps 3 (3*q+2)) (shuttleCfg 3 (12*q+10)) =
      some (shuttleCfg (6*q+7) 2) := by
  have h := appC8_raw_shuttle_rounds (3*q+2) 3 (12*q+10) (by omega)
  have hk : 3+2*(3*q+2) = 6*q+7 := by omega
  have hm : 12*q+10-4*(3*q+2) = 2 := by omega
  rw [hk, hm] at h
  exact h

end CryptidSolvePhase4.AppC8Raw
