import BB6Interop.AppC8ResidualTraceData

/-! Residual-left-tape analysis: counterexamples to the unrestricted candidate
return language. These are nonblank witnesses, not a blank halting result. -/
namespace BB6Interop.AppC8ResidualTape
open CryptidSolvePhase4 CryptidSolvePhase4.AppC8Raw
open BB6Interop.AppC8Continuation BB6Interop.AppC8RunLists
set_option maxRecDepth 20000
set_option Elab.async false

def firstBadWord : List Bool := ones 5 (suffix [4,4,1])
def secondBadWord : List Bool := ones 2 (suffix [1,4,2,0,1])
def badFirst : Cfg := ⟨.E, back 1 firstMarker, true :: false :: firstBadWord⟩
def badSecond : Cfg := ⟨.E, back 1 secondMarker, true :: false :: secondBadWord⟩

theorem first_bad_positive : PositiveWord firstBadWord := positive_run_list 4 [4,4,1]
theorem second_bad_positive : PositiveWord secondBadWord := positive_run_list 1 [1,4,2,0,1]

set_option maxHeartbeats 2000000 in
-- Kernel reduction checks all states through the first undefined attempt.
theorem first_bad_avoids : rejectTrace (badFirst :: firstTrace.tail) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Kernel reduction checks all states through the first undefined attempt.
theorem second_bad_avoids : rejectTrace (badSecond :: secondTrace.tail) = true := by decide +kernel

/-- Each unrestricted defect-return predicate is independently false. -/
theorem not_first_defect_return : ¬ DefectReturn firstMarker := by
  intro h
  exact no_progress_of_trace first_bad_avoids (h 1 firstBadWord first_bad_positive)

theorem not_second_defect_return : ¬ DefectReturn secondMarker := by
  intro h
  exact no_progress_of_trace second_bad_avoids (h 1 secondBadWord second_bad_positive)

/-- Explicitly model the residual left tape, with no implicit emptiness assumption. -/
def residual (marker : List Bool) (k n : Nat) (ns : List Nat) : Cfg :=
  ⟨.A, back k marker, false :: true :: false :: blocks 2 (ones (n+1) (suffix ns))⟩

theorem first_bad_enters_residual : run 31 badFirst = some (residual firstMarker 0 0 [4,4,1]) :=
  defect_strip_block_param firstMarker (suffix [4,4,1]) 0

theorem second_trace_enters_residual :
    run 31 ⟨.E, back 1 secondMarker,
      true :: false :: ones 5 (suffix [3,1,1,4,0])⟩ =
      some (residual secondMarker 0 0 [3,1,1,4,0]) :=
  defect_strip_block_param secondMarker (suffix [3,1,1,4,0]) 0

set_option maxHeartbeats 2000000 in
-- This is the residual state reached from the first defect witness.
theorem residual_bad_avoids :
    rejectTrace (residual firstMarker 0 0 [4,4,1] :: residualTrace.tail) = true := by decide +kernel

theorem residual_bad_no_return : ¬ Progress (residual firstMarker 0 0 [4,4,1]) :=
  no_progress_of_trace residual_bad_avoids

/-- A guarded residual family really does make progress: terminal right run only. -/
theorem residual_terminal_local (l : List Bool) :
    run 30 ⟨.A, l, false :: true :: false :: blocks 2 [true]⟩ =
      some ⟨.A, l, true :: defectTail 8⟩ := by rfl

theorem residual_first_terminal (k : Nat) :
    run (5*k+36) (residual firstMarker k 0 []) =
      some (runListCfg 0 0 [3*k+1,7,1]) := by
  have h1 := run_comp (residual_terminal_local (back k firstMarker))
    (reset_scan k firstMarker (defectTail 8))
  have h2 := run_comp h1 (one_left_boundary (ones (3*k) (defectTail 8)))
  unfold shuttleTailCfg at h2
  rw [ones_add, show 2+3*k = 3*k+2 by omega,
      show 30+5*k+6 = 5*k+36 by omega] at h2
  exact h2

theorem residual_second_terminal (k : Nat) :
    run (5*k+38) (residual secondMarker k 0 []) =
      some (runListCfg 0 (3*k+3) [7,1]) := by
  have h1 := run_comp (residual_terminal_local (back k secondMarker))
    (reset_scan k secondMarker (defectTail 8))
  have h2 := run_comp h1 (odd_left_boundary (ones (3*k) (defectTail 8)))
  rw [show 30+5*k+8 = 5*k+38 by omega] at h2
  exact h2

theorem residual_first_terminal_progress (k : Nat) :
    Progress (residual firstMarker k 0 []) :=
  ⟨_, _, by omega, residual_first_terminal k, run_list_boundary 0 0 [3*k+1,7,1]⟩

theorem residual_second_terminal_progress (k : Nat) :
    Progress (residual secondMarker k 0 []) :=
  ⟨_, _, by omega, residual_second_terminal k, run_list_boundary 0 (3*k+3) [7,1]⟩

/-- A phase-aware candidate: original Boundary plus just the proved terminal residuals.
Including Boundary means even this union cannot be a global safe invariant. -/
def TerminalPhaseDomain (c : Cfg) : Prop :=
  Boundary c ∨ ∃ k, c = residual firstMarker k 0 [] ∨ c = residual secondMarker k 0 []

theorem residual_phase_progress {c : Cfg}
    (hc : ∃ k, c = residual firstMarker k 0 [] ∨ c = residual secondMarker k 0 []) : Progress c := by
  obtain ⟨k, h | h⟩ := hc
  · subst c; exact residual_first_terminal_progress k
  · subst c; exact residual_second_terminal_progress k


theorem first_bad_steps :
    (∃ d, run 742 badFirst = some d) ∧ run 743 badFirst = none := by
  have h := reject_trace_steps first_bad_avoids
  rw [show firstTrace.tail.length = 742 by decide +kernel] at h
  exact h

theorem second_bad_steps :
    (∃ d, run 680 badSecond = some d) ∧ run 681 badSecond = none := by
  have h := reject_trace_steps second_bad_avoids
  rw [show secondTrace.tail.length = 680 by decide +kernel] at h
  exact h

/-- A smaller boundary witness derived from the first-marker counterexample. -/
def shortBadBoundary : Cfg := runListCfg 1 0 [4,4,4,1]

theorem short_bad_member : Boundary shortBadBoundary := run_list_boundary 1 0 [4,4,4,1]

theorem short_bad_entry : run 6 shortBadBoundary = some badFirst := by rfl

theorem short_bad_prefix : ∃ d, run 748 shortBadBoundary = some d := by
  obtain ⟨d, hd⟩ := first_bad_steps.1
  exact ⟨d, run_comp short_bad_entry hd⟩

theorem run_comp_none {n m : Nat} {c d : Cfg}
    (h : run n c = some d) (h' : run m d = none) : run (n+m) c = none := by
  rw [run_add, h]
  exact h'

theorem short_bad_halts : run 749 shortBadBoundary = none :=
  run_comp_none short_bad_entry first_bad_steps.2

/-- Positive-time macro closure, suitable for a genuinely restricted replacement domain. -/
def MacroClosed (P : Cfg → Prop) : Prop :=
  ∀ c, P c → ∃ t d, 0 < t ∧ run t c = some d ∧ P d

theorem macro_closed_survives {P : Cfg → Prop} (hclosed : MacroClosed P) :
    ∀ j c, P c → ∃ d, run j c = some d := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro c hc
      obtain ⟨t, d, ht, hr, hd⟩ := hclosed c hc
      by_cases hj : j ≤ t
      · exact run_prefix_defined hr j hj
      · obtain ⟨e, he⟩ := ih (j-t) (by omega) d hd
        have h := run_comp hr he
        rw [show t+(j-t) = j by omega] at h
        exact ⟨e, h⟩

/-- Merely adding residual phases cannot repair the original overbroad language. -/
theorem no_safe_extension (P : Cfg → Prop) (hcontains : ∀ c, Boundary c → P c) :
    ¬ MacroClosed P := by
  intro hc
  obtain ⟨d, hd⟩ := macro_closed_survives hc 749 shortBadBoundary
    (hcontains shortBadBoundary short_bad_member)
  rw [short_bad_halts] at hd
  cases hd

theorem terminal_phase_not_closed : ¬ MacroClosed TerminalPhaseDomain :=
  no_safe_extension TerminalPhaseDomain (fun _ h => Or.inl h)

/-- Any replacement closed domain must exclude this halting boundary witness. -/
theorem closed_domain_excludes_witness {P : Cfg → Prop} (hc : MacroClosed P) :
    ¬ P shortBadBoundary := by
  intro hp
  obtain ⟨d, hd⟩ := macro_closed_survives hc 749 shortBadBoundary hp
  rw [short_bad_halts] at hd
  cases hd


/-- The original candidate closure is false. -/
theorem not_boundary_return : ¬ BoundaryReturn := by
  intro hreturn
  obtain ⟨d, hd⟩ := survives_of_boundary_return hreturn 749 shortBadBoundary short_bad_member
  rw [short_bad_halts] at hd
  cases hd

theorem not_both_defect_returns :
    ¬ (DefectReturn firstMarker ∧ DefectReturn secondMarker) := by
  rintro ⟨hf, hs⟩
  exact not_boundary_return (boundary_return_of_defects hf hs)

theorem upstream_nonblank_halt :
    BusyBeaver.multiStep BB6Interop.AppC8.machine
      (BB6Interop.AppC8.encode shortBadBoundary) 749 = none := by
  rw [BB6Interop.AppC8.run_commutes, short_bad_halts]
  rfl

end BB6Interop.AppC8ResidualTape
