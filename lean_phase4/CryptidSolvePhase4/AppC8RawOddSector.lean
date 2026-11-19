import CryptidSolvePhase4.AppC8RawBlankReachability

/-! A universal AppC8 odd-sector excursion for k=4a+3, followed by
concrete composition with the proved blank trajectory. No clean-sector entry
or global survival is asserted. All execution uses the existing raw table. -/
namespace CryptidSolvePhase4.AppC8Raw

def shuttleTailCfg (k m : Nat) (t : List Bool) : Cfg :=
  ⟨.A, [], false :: true :: false :: blocks k (ones m t)⟩

/-- First half-shuttle, requiring three leading ones, with arbitrary suffix. -/
theorem odd_half (k : Nat) (t : List Bool) :
    run (6*k+12) (shuttleTailCfg k 3 t) =
      some ⟨.E, [true, false], blocks (k+1) (true :: t)⟩ := by
  have h1 := run_comp (entry (blocks k (true :: true :: true :: t)))
    (scan_right k [true, false, true] (true :: true :: true :: t))
  have h2 := run_comp h1 (turn_and_return k [false, true] t)
  have h3 := run_comp h2 (middle_boundary (returnWord k (true :: false :: true :: t)))
  rw [close_word] at h3
  rw [show 6*k+12 = 3+3*k+(5+3*k)+4 by omega]
  exact h3

theorem odd_turn (l : List Bool) :
    run 8 ⟨.E, l, [true]⟩ = some ⟨.A, l, [true, false, true, true]⟩ := by rfl

theorem odd_left_boundary (t : List Bool) :
    run 8 ⟨.A, [true, false], true :: t⟩ =
      some ⟨.A, [], false :: true :: false :: ones 4 t⟩ := by rfl

/-- Every k admits the first odd collapse, leaving the literal suffix 011. -/
theorem appC8_odd_collapse (k : Nat) :
    run (14*k+36) (shuttleCfg k 3) =
      some (shuttleTailCfg 0 (3*k+7) [false, true, true]) := by
  have h1 := run_comp (odd_half k []) (scan_right (k+1) [true, false] [true])
  have h2 := run_comp h1 (odd_turn (back (k+1) [true, false]))
  have h3 := run_comp h2 (reset_scan (k+1) [true, false] [false, true, true])
  have h4 := run_comp h3 (odd_left_boundary (ones (3*(k+1)) [false, true, true]))
  have ht : 6*k+12+3*(k+1)+8+5*(k+1)+8 = 14*k+36 := by omega
  rw [ht] at h4
  change run (14*k+36) (shuttleCfg k 3) =
    some (shuttleTailCfg 0 (3*(k+1)+4) [false, true, true]) at h4
  rw [show 3*(k+1)+4 = 3*k+7 by omega] at h4
  exact h4

theorem tail_shuttle (k m : Nat) (t : List Bool) (hm : m ≥ 5) :
    run (12*k+26) (shuttleTailCfg k m t) =
      some (shuttleTailCfg (k+2) (m-4) t) := by
  have h := shuttle_with_tail k (ones (m-5) t)
  have h' : run (12*k+26) (shuttleTailCfg k ((m-5)+5) t) =
      some (shuttleTailCfg (k+2) ((m-5)+1) t) := h
  rw [show m-5+5 = m by omega, show m-5+1 = m-4 by omega] at h'
  exact h'

theorem tail_shuttle_rounds (r k m : Nat) (t : List Bool) (hm : m ≥ 4*r+1) :
    run (appC8ShuttleRoundsSteps k r) (shuttleTailCfg k m t) =
      some (shuttleTailCfg (k+2*r) (m-4*r) t) := by
  induction r generalizing k m with
  | zero => simp [appC8ShuttleRoundsSteps, run]
  | succ r ih =>
      have h := run_comp (tail_shuttle k m t (by omega)) (ih (k+2) (m-4) (by omega))
      rw [show k+2+2*r = k+2*(r+1) by omega,
          show m-4-4*r = m-4*(r+1) by omega] at h
      exact h

theorem odd_terminal_turn (l : List Bool) :
    run 16 ⟨.E, l, [true, true, false, true, true]⟩ =
      some ⟨.A, l, ones 7 []⟩ := by rfl

/-- Collapse the four-ones endpoint with its 011 suffix, for every block count. -/
theorem appC8_odd_terminal (k : Nat) :
    run (14*k+44) (shuttleTailCfg k 4 [false, true, true]) =
      some (shuttleCfg 0 (3*k+13)) := by
  have h1 := run_comp (odd_half k [true, false, true, true])
    (scan_right (k+1) [true, false] [true, true, false, true, true])
  have h2 := run_comp h1 (odd_terminal_turn (back (k+1) [true, false]))
  have h3 := run_comp h2 (reset_scan (k+1) [true, false] (ones 6 []))
  rw [ones_add] at h3
  rw [show 3*(k+1)+1+6 = (3*(k+1)+6)+1 by omega] at h3
  have h4 := run_comp h3 (odd_left_boundary (ones (3*(k+1)+6) []))
  rw [show 6*k+12+3*(k+1)+16+5*(k+1)+8 = 14*k+44 by omega] at h4
  change run (14*k+44) (shuttleTailCfg k 4 [false, true, true]) =
    some (shuttleCfg 0 (3*(k+1)+6+4)) at h4
  rw [show 3*(k+1)+6+4 = 3*k+13 by omega] at h4
  exact h4

/-- Universal raw odd-sector law, stated first with its compositional duration. -/
theorem appC8_odd_excursion (a : Nat) :
    run ((14*(4*a+3)+36)+appC8ShuttleRoundsSteps 0 (3*a+3)+(14*(6*a+6)+44))
      (shuttleCfg (4*a+3) 3) = some (shuttleCfg 0 (18*a+31)) := by
  have h1 := appC8_odd_collapse (4*a+3)
  have h2 := tail_shuttle_rounds (3*a+3) 0 (3*(4*a+3)+7) [false, true, true] (by omega)
  rw [show 0+2*(3*a+3) = 6*a+6 by omega,
      show 3*(4*a+3)+7-4*(3*a+3) = 4 by omega] at h2
  have h := run_comp (run_comp h1 h2) (appC8_odd_terminal (6*a+6))
  rw [show 3*(6*a+6)+13 = 18*a+31 by omega] at h
  exact h

theorem odd_duration (a : Nat) :
    (14*(4*a+3)+36)+appC8ShuttleRoundsSteps 0 (3*a+3)+(14*(6*a+6)+44) =
      108*a*a+398*a+356 := by
  rw [appC8ShuttleRoundsSteps_closed_form]
  rw [show 3*a+3-1 = 3*a+2 by omega]
  simp only [Nat.mul_zero, Nat.add_zero]
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
  have h : a*(3*a) = 3*(a*a) := by
    rw [← Nat.mul_assoc, Nat.mul_comm a 3, Nat.mul_assoc]
  omega

theorem appC8_odd_excursion_closed (a : Nat) :
    run (108*a*a+398*a+356) (shuttleCfg (4*a+3) 3) =
      some (shuttleCfg 0 (18*a+31)) := by
  have h := appC8_odd_excursion a
  rw [odd_duration] at h
  exact h

theorem appC8_odd_excursion_survives (a j : Nat) (hj : j ≤ 108*a*a+398*a+356) :
    ∃ e, run j (shuttleCfg (4*a+3) 3) = some e :=
  run_prefix_defined (appC8_odd_excursion_closed a) j hj

/-- The odd-family output remains odd after any admissible shuttle rounds. -/
theorem odd_output_not_exit (a r : Nat) (h : 4*r+1 ≤ 18*a+31) :
    (18*a+31-4*r)%2 = 1 ∧ 18*a+31-4*r ≠ 2 := by omega

theorem appC8_blank_after_odd_excursion :
    run 18306 blankCfg = some (shuttleCfg 0 175) := by
  have h := run_comp appC8_blank_odd_frontier (appC8_odd_excursion_closed 8)
  exact h

theorem appC8_blank_next_odd_frontier :
    run 41096 blankCfg = some (shuttleCfg 86 3) := by
  have h := run_comp appC8_blank_after_odd_excursion (appC8_raw_shuttle_rounds 43 0 175 (by decide))
  exact h

theorem appC8_blank_prefix_41096 (j : Nat) (hj : j ≤ 41096) :
    ∃ e, run j blankCfg = some e :=
  run_prefix_defined appC8_blank_next_odd_frontier j hj

/-- The new endpoint has state A, so it is not a clean-macro input D(c). -/
theorem odd_frontier_not_clean (q : Nat) :
    shuttleCfg 86 3 ≠ cleanCfg (4*(q+1)) := by
  intro h
  have hs := congrArg Cfg.st h
  cases hs

end CryptidSolvePhase4.AppC8Raw
