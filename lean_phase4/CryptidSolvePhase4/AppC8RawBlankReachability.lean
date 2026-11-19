import CryptidSolvePhase4.AppC8RawCleanMacro

/-! Blank-tape reachability for the actual AppC8 table.
The finite bridge is checked by kernel reduction. All subsequent runs compose
previously proved raw reset, shuttle, and exit theorems. This does not establish
entry into the restricted clean sector c=4(q+1), nor global non-halting.
-/
namespace CryptidSolvePhase4.AppC8Raw

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- State A scans an all-zero tape. -/
def blankCfg : Cfg := ⟨.A, [], []⟩

theorem appC8_blank_entry : run 5 blankCfg = some (shuttleCfg 0 2) := by rfl

theorem appC8_blank_carry_one : run 11 blankCfg = some (cleanCfg 1) := by
  have h := run_comp appC8_blank_entry (appC8_raw_exit 0)
  exact h

theorem appC8_blank_first_reset : run 59 blankCfg = some (shuttleCfg 3 1) := by
  have h := run_comp appC8_blank_carry_one (appC8_raw_reset 0)
  exact h

/-- A concrete 3185-instruction bridge across the first non-clean excursion.
    This is a finite execution certificate, not a rule for arbitrary odd inputs. -/
theorem appC8_first_excursion :
    run 3185 (shuttleCfg 3 1) = some (shuttleCfg 18 10) := by decide

theorem appC8_blank_shuttle_entry : run 3244 blankCfg = some (shuttleCfg 18 10) := by
  have h := run_comp appC8_blank_first_reset appC8_first_excursion
  exact h

theorem appC8_blank_two_shuttles : run 3752 blankCfg = some (shuttleCfg 22 2) := by
  have h := run_comp appC8_blank_shuttle_entry (appC8_raw_shuttle_rounds 2 18 10 (by decide))
  exact h

theorem appC8_blank_carry_twenty_three : run 3824 blankCfg = some (cleanCfg 23) := by
  have h := run_comp appC8_blank_two_shuttles (appC8_raw_exit 22)
  exact h

theorem appC8_blank_second_reset : run 3982 blankCfg = some (shuttleCfg 3 67) := by
  have h := run_comp appC8_blank_carry_twenty_three (appC8_raw_reset 22)
  exact h

theorem appC8_blank_odd_frontier : run 7854 blankCfg = some (shuttleCfg 35 3) := by
  have h := run_comp appC8_blank_second_reset (appC8_raw_shuttle_rounds 16 3 67 (by decide))
  exact h

/-- Every prefix through the certified frontier executes defined instructions. -/
theorem appC8_blank_prefix_defined (j : Nat) (hj : j ≤ 7854) :
    ∃ e, run j blankCfg = some e :=
  run_prefix_defined appC8_blank_odd_frontier j hj

/-- A valid clean-sector entry would transfer the full clean macro to the blank
    run. The premise is explicit and is NOT proved by the checkpoints above. -/
theorem appC8_blank_clean_macro_transfer (n q : Nat)
    (hEntry : run n blankCfg = some (cleanCfg (4*(q+1)))) :
    run (n+(108*q*q+332*q+238)) blankCfg = some (cleanCfg (6*q+8)) := by
  have h := run_comp hEntry (appC8_clean_macro_raw q)
  exact h

/-- The two certified carry checkpoints do not satisfy the full macro's guard. -/
theorem appC8_blank_carry_guards :
    (∀ q : Nat, 1 ≠ 4*(q+1)) ∧ (∀ q : Nat, 23 ≠ 4*(q+1)) := by
  constructor <;> intro q <;> omega

end CryptidSolvePhase4.AppC8Raw
