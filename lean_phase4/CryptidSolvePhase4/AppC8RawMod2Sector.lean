import CryptidSolvePhase4.AppC8RawOddSector

/-! Raw modulo-four reduction and the k=16b+6 branch containing C(86,3).
The uniform k=4a+2 theorem has a nonempty suffix; only the stated subfamily
is promoted to a suffix-free excursion and carry exit. -/
namespace CryptidSolvePhase4.AppC8Raw
set_option maxRecDepth 20000
set_option maxHeartbeats 0

def defectTail (n : Nat) : List Bool := false :: ones n [false, true, true]

theorem blocks_add (a b : Nat) (t : List Bool) :
    blocks a (blocks b t) = blocks (a+b) t := by
  induction a with
  | zero => simp [blocks]
  | succ a ih => simp [blocks, ih, Nat.succ_add]

theorem return_close_prefix (n : Nat) (t : List Bool) :
    true :: returnWord n t = blocks n (true :: t) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [returnWord, blocks]; rw [ih]

theorem defect_turn_19 (l : List Bool) :
    run 19 ⟨.E, l, [true, false, true, true]⟩ =
      some ⟨.A, l.tail, read l :: false :: ones 5 []⟩ := by rfl

theorem defect_turn_66 (l : List Bool) :
    run 66 ⟨.E, back 2 l, true :: false :: ones 5 []⟩ =
      some ⟨.A, l, ones 4 (defectTail 8)⟩ := by rfl

/-- Raw one-one defect collapse for every k=n+2. -/
theorem defect_one_collapse (n : Nat) :
    run (14*(n+2)+90) (shuttleTailCfg (n+2) 1 [false, true, true]) =
      some (shuttleTailCfg 0 (3*(n+2)+1) (defectTail 8)) := by
  have h1 := run_comp (entry (blocks (n+2) [true, false, true, true]))
    (scan_right (n+2) [true, false, true] [true, false, true, true])
  have ht := defect_turn_19 (back (n+2) [true, false, true])
  rw [back_read] at ht
  have h2 := run_comp h1 ht
  have h3 := run_comp h2 (scan_left (n+2) [false, true] (false :: ones 5 []))
  have h4 := run_comp h3 (middle_boundary (returnWord (n+2) (false :: ones 5 [])))
  rw [return_close_prefix] at h4
  have h5 := run_comp h4 (scan_right (n+2) [true, false] (true :: false :: ones 5 []))
  have h6 := run_comp h5 (defect_turn_66 (back n [true, false]))
  have h7 := run_comp h6 (reset_scan n [true, false] (ones 3 (defectTail 8)))
  rw [ones_add] at h7
  rw [show 3*n+1+3 = (3*n+3)+1 by omega] at h7
  have h8 := run_comp h7 (odd_left_boundary (ones (3*n+3) (defectTail 8)))
  rw [show 3+3*(n+2)+19+3*(n+2)+4+3*(n+2)+66+5*n+8 = 14*(n+2)+90 by omega] at h8
  change run (14*(n+2)+90) (shuttleTailCfg (n+2) 1 [false, true, true]) =
    some (shuttleTailCfg 0 (3*n+3+4) (defectTail 8)) at h8
  rw [show 3*n+3+4 = 3*(n+2)+1 by omega] at h8
  exact h8

theorem defect_turn_104 (l : List Bool) :
    run 104 ⟨.E, back 3 l, true :: false :: ones 8 [false, true, true]⟩ =
      some ⟨.A, l.tail, read l :: true :: false :: true :: true :: false :: true :: false :: ones 17 []⟩ := by rfl

theorem defect_turn_334 (l : List Bool) :
    run 334 ⟨.E, back 4 l, true :: false :: ones 17 []⟩ =
      some ⟨.A, l, ones 4 (defectTail 26)⟩ := by rfl

/-- Second defect collapse for every k=n+5; the lower bound is essential here. -/
theorem defect_eight_collapse (n : Nat) :
    run (14*(n+5)+416) (shuttleTailCfg (n+5) 1 (defectTail 8)) =
      some (shuttleTailCfg 0 (3*n+7) (defectTail 26)) := by
  have h1 := run_comp (entry (blocks (n+5) (true :: defectTail 8)))
    (scan_right (n+5) [true, false, true] (true :: defectTail 8))
  have ht := defect_turn_104 (back (n+2) [true, false, true])
  rw [back_read] at ht
  have h2 := run_comp h1 ht
  have h3 := run_comp h2 (scan_left (n+2) [false, true]
    (true :: false :: true :: true :: false :: true :: false :: ones 17 []))
  have h4 := run_comp h3 (middle_boundary (returnWord (n+2)
    (true :: false :: true :: true :: false :: true :: false :: ones 17 [])))
  rw [return_close_prefix] at h4
  change run (3+3*(n+5)+104+3*(n+2)+4) (shuttleTailCfg (n+5) 1 (defectTail 8)) =
    some ⟨.E, [true, false], blocks (n+2) (blocks 2 (true :: false :: ones 17 []))⟩ at h4
  rw [blocks_add] at h4
  have h5 := run_comp h4 (scan_right (n+4) [true, false] (true :: false :: ones 17 []))
  have h6 := run_comp h5 (defect_turn_334 (back n [true, false]))
  have h7 := run_comp h6 (reset_scan n [true, false] (ones 3 (defectTail 26)))
  rw [ones_add] at h7
  rw [show 3*n+1+3 = (3*n+3)+1 by omega] at h7
  have h8 := run_comp h7 (odd_left_boundary (ones (3*n+3) (defectTail 26)))
  rw [show 3+3*(n+5)+104+3*(n+2)+4+3*(n+4)+334+5*n+8 = 14*(n+5)+416 by omega] at h8
  exact h8

/-- Absorb the exposed 110 into one more block. This is word equality, not a step. -/
theorem absorb_defect (k m : Nat) (t : List Bool) :
    shuttleTailCfg k 2 (false :: ones m t) = shuttleTailCfg (k+1) m t := by
  unfold shuttleTailCfg
  change Cfg.mk .A [] (false :: true :: false :: blocks k (blocks 1 (ones m t))) = _
  rw [blocks_add]

/-- Uniform reduction for the entire k=2 mod 4 class, with explicit remaining suffix. -/
theorem appC8_mod2_reduction (a : Nat) :
    run ((14*(4*a+2)+36)+appC8ShuttleRoundsSteps 0 (3*a+3)+(14*(6*a+6)+90))
      (shuttleCfg (4*a+2) 3) = some (shuttleTailCfg 0 (18*a+19) (defectTail 8)) := by
  have h1 := appC8_odd_collapse (4*a+2)
  have h2 := tail_shuttle_rounds (3*a+3) 0 (3*(4*a+2)+7) [false, true, true] (by omega)
  rw [show 0+2*(3*a+3) = 6*a+6 by omega,
      show 3*(4*a+2)+7-4*(3*a+3) = 1 by omega] at h2
  have h3 := defect_one_collapse (6*a+4)
  rw [show 6*a+4+2 = 6*a+6 by omega, show 3*(6*a+6)+1 = 18*a+19 by omega] at h3
  exact run_comp (run_comp h1 h2) h3

theorem mod2_duration (a : Nat) :
    (14*(4*a+2)+36)+appC8ShuttleRoundsSteps 0 (3*a+3)+(14*(6*a+6)+90) =
      108*a*a+398*a+388 := by
  have h := odd_duration a
  omega

theorem appC8_mod2_reduction_closed (a : Nat) :
    run (108*a*a+398*a+388) (shuttleCfg (4*a+2) 3) =
      some (shuttleTailCfg 0 (18*a+19) (defectTail 8)) := by
  have h := appC8_mod2_reduction a
  rw [mod2_duration] at h
  exact h

/-- Full branch containing 86: k=16b+6. Other k=2 mod 4 inputs are not covered. -/
theorem appC8_mod16_branch (b : Nat) :
    run ((108*(4*b+1)*(4*b+1)+398*(4*b+1)+388)+
        appC8ShuttleRoundsSteps 0 (18*b+9)+(14*(36*b+18)+416)+
        appC8ShuttleRoundsSteps 0 (27*b+11)+appC8ShuttleRoundsSteps (54*b+23) 6)
      (shuttleCfg (16*b+6) 3) = some (shuttleCfg (54*b+36) 2) := by
  have h1 := appC8_mod2_reduction_closed (4*b+1)
  rw [show 4*(4*b+1)+2 = 16*b+6 by omega, show 18*(4*b+1)+19 = 72*b+37 by omega] at h1
  have h2 := tail_shuttle_rounds (18*b+9) 0 (72*b+37) (defectTail 8) (by omega)
  rw [show 0+2*(18*b+9) = 36*b+18 by omega, show 72*b+37-4*(18*b+9) = 1 by omega] at h2
  have h3 := defect_eight_collapse (36*b+13)
  rw [show 36*b+13+5 = 36*b+18 by omega, show 3*(36*b+13)+7 = 108*b+46 by omega] at h3
  have h4 := tail_shuttle_rounds (27*b+11) 0 (108*b+46) (defectTail 26) (by omega)
  rw [show 0+2*(27*b+11) = 54*b+22 by omega, show 108*b+46-4*(27*b+11) = 2 by omega] at h4
  change run (appC8ShuttleRoundsSteps 0 (27*b+11)) (shuttleTailCfg 0 (108*b+46) (defectTail 26)) =
    some (shuttleTailCfg (54*b+22) 2 (false :: ones 26 [false, true, true])) at h4
  rw [absorb_defect] at h4
  have h5 := tail_shuttle_rounds 6 (54*b+23) 26 [false, true, true] (by decide)
  rw [show 54*b+23+2*6 = 54*b+35 by omega] at h5
  change run (appC8ShuttleRoundsSteps (54*b+23) 6) (shuttleTailCfg (54*b+23) 26 [false, true, true]) =
    some (shuttleTailCfg (54*b+35) 2 (false :: ones 2 [])) at h5
  rw [absorb_defect] at h5
  exact run_comp (run_comp (run_comp (run_comp h1 h2) h3) h4) h5

theorem mod16_duration (b : Nat) :
    (108*(4*b+1)*(4*b+1)+398*(4*b+1)+388)+
        appC8ShuttleRoundsSteps 0 (18*b+9)+(14*(36*b+18)+416)+
        appC8ShuttleRoundsSteps 0 (27*b+11)+appC8ShuttleRoundsSteps (54*b+23) 6 =
      14364*b*b+18494*b+6438 := by
  rw [appC8ShuttleRoundsSteps_closed_form, appC8ShuttleRoundsSteps_closed_form,
      appC8ShuttleRoundsSteps_closed_form]
  rw [show 18*b+9-1 = 18*b+8 by omega, show 27*b+11-1 = 27*b+10 by omega]
  simp only [Nat.mul_zero, Nat.add_zero]
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
  have h4 : b*(4*b) = 4*(b*b) := by rw [← Nat.mul_assoc, Nat.mul_comm b 4, Nat.mul_assoc]
  have h18 : b*(18*b) = 18*(b*b) := by rw [← Nat.mul_assoc, Nat.mul_comm b 18, Nat.mul_assoc]
  have h27 : b*(27*b) = 27*(b*b) := by rw [← Nat.mul_assoc, Nat.mul_comm b 27, Nat.mul_assoc]
  omega

theorem appC8_mod16_branch_closed (b : Nat) :
    run (14364*b*b+18494*b+6438) (shuttleCfg (16*b+6) 3) =
      some (shuttleCfg (54*b+36) 2) := by
  have h := appC8_mod16_branch b
  rw [mod16_duration] at h
  exact h

theorem appC8_mod16_carry (b : Nat) :
    run (14364*b*b+18656*b+6552) (shuttleCfg (16*b+6) 3) =
      some (cleanCfg (54*b+37)) := by
  have h := run_comp (appC8_mod16_branch_closed b) (appC8_raw_exit (54*b+36))
  rw [show 14364*b*b+18494*b+6438+(3*(54*b+36)+6) = 14364*b*b+18656*b+6552 by omega] at h
  exact h

theorem appC8_mod16_survives (b j : Nat) (hj : j ≤ 14364*b*b+18656*b+6552) :
    ∃ e, run j (shuttleCfg (16*b+6) 3) = some e :=
  run_prefix_defined (appC8_mod16_carry b) j hj

theorem mod16_carry_not_clean (b q : Nat) : 54*b+37 ≠ 4*(q+1) := by omega

theorem appC8_blank_after_mod16 : run 499104 blankCfg = some (shuttleCfg 306 2) := by
  have h := run_comp appC8_blank_next_odd_frontier (appC8_mod16_branch_closed 5)
  exact h

theorem appC8_blank_carry_307 : run 500028 blankCfg = some (cleanCfg 307) := by
  have h := run_comp appC8_blank_next_odd_frontier (appC8_mod16_carry 5)
  exact h

theorem appC8_blank_reset_307 : run 501606 blankCfg = some (shuttleCfg 3 919) := by
  have h := run_comp appC8_blank_carry_307 (appC8_raw_reset 306)
  exact h

theorem appC8_blank_frontier_461 : run 1142348 blankCfg = some (shuttleCfg 461 3) := by
  have h := run_comp appC8_blank_reset_307 (appC8_raw_shuttle_rounds 229 3 919 (by decide))
  exact h

theorem appC8_blank_prefix_1142348 (j : Nat) (hj : j ≤ 1142348) :
    ∃ e, run j blankCfg = some e :=
  run_prefix_defined appC8_blank_frontier_461 j hj

/-- The following k=4a+1 family closes the path to a genuine clean-sector input. -/
theorem appC8_mod1_branch (a : Nat) :
    run ((14*(4*a+1)+36)+appC8ShuttleRoundsSteps 0 (3*a+2))
      (shuttleCfg (4*a+1) 3) = some (shuttleCfg (6*a+5) 2) := by
  have h1 := appC8_odd_collapse (4*a+1)
  have h2 := tail_shuttle_rounds (3*a+2) 0 (3*(4*a+1)+7) [false, true, true] (by omega)
  rw [show 0+2*(3*a+2) = 6*a+4 by omega, show 3*(4*a+1)+7-4*(3*a+2) = 2 by omega] at h2
  change run (appC8ShuttleRoundsSteps 0 (3*a+2)) (shuttleTailCfg 0 (3*(4*a+1)+7) [false, true, true]) =
    some (shuttleTailCfg (6*a+4) 2 (false :: ones 2 [])) at h2
  rw [absorb_defect] at h2
  exact run_comp h1 h2

theorem mod1_duration (a : Nat) :
    (14*(4*a+1)+36)+appC8ShuttleRoundsSteps 0 (3*a+2) = 108*a*a+242*a+126 := by
  rw [appC8ShuttleRoundsSteps_closed_form]
  rw [show 3*a+2-1 = 3*a+1 by omega]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
  have h : a*(3*a) = 3*(a*a) := by rw [← Nat.mul_assoc, Nat.mul_comm a 3, Nat.mul_assoc]
  omega

theorem appC8_mod1_branch_closed (a : Nat) :
    run (108*a*a+242*a+126) (shuttleCfg (4*a+1) 3) = some (shuttleCfg (6*a+5) 2) := by
  have h := appC8_mod1_branch a
  rw [mod1_duration] at h
  exact h

theorem appC8_mod1_carry (a : Nat) :
    run (108*a*a+260*a+147) (shuttleCfg (4*a+1) 3) = some (cleanCfg (6*a+6)) := by
  have h := run_comp (appC8_mod1_branch_closed a) (appC8_raw_exit (6*a+5))
  rw [show 108*a*a+242*a+126+(3*(6*a+5)+6) = 108*a*a+260*a+147 by omega] at h
  exact h

/-- For odd a, the k=4a+1 branch really reaches the full clean-macro domain. -/
theorem appC8_mod1_clean_entry (q : Nat) :
    run (108*(2*q+1)*(2*q+1)+260*(2*q+1)+147) (shuttleCfg (8*q+5) 3) =
      some (cleanCfg (4*((3*q+2)+1))) := by
  have h := appC8_mod1_carry (2*q+1)
  rw [show 4*(2*q+1)+1 = 8*q+5 by omega, show 6*(2*q+1)+6 = 4*((3*q+2)+1) by omega] at h
  exact h

/-- Actual blank entry into the clean-macro sector, with q=173. -/
theorem appC8_blank_clean_entry : run 2600695 blankCfg = some (cleanCfg 696) := by
  have h := run_comp appC8_blank_frontier_461 (appC8_mod1_carry 115)
  exact h

/-- The previously conditional blank-to-clean-macro transfer now has a proved premise. -/
theorem appC8_blank_clean_macro_applied : run 5890701 blankCfg = some (cleanCfg 1046) := by
  have h := appC8_blank_clean_macro_transfer 2600695 173 appC8_blank_clean_entry
  exact h

theorem appC8_blank_prefix_5890701 (j : Nat) (hj : j ≤ 5890701) :
    ∃ e, run j blankCfg = some e :=
  run_prefix_defined appC8_blank_clean_macro_applied j hj

end CryptidSolvePhase4.AppC8Raw
