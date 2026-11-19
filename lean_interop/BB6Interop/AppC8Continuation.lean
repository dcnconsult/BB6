import BB6Interop.AppC8

/-! Continuation beyond D(1046), and explicit obligations for an infinite orbit.
All raw execution theorems use the literal AppC 8 table. -/
namespace BB6Interop.AppC8Continuation
open CryptidSolvePhase4 CryptidSolvePhase4.AppC8Raw
set_option maxRecDepth 20000

/-- Four terminal ones use the same carry turn, but a different left marker. -/
theorem four_turn (l : List Bool) :
    run 8 ⟨.E, back 1 l, [true,true]⟩ =
      some ⟨.A, back 1 l, ones 4 []⟩ := by rfl

/-- The missing suffix-free four-one boundary, for every block count. -/
theorem four_collapse (k : Nat) :
    run (14*k+36) (shuttleCfg k 4) = some (shuttleCfg 0 (3*k+10)) := by
  have h1 := run_comp (odd_half k [true])
    (scan_right (k+1) [true,false] [true,true])
  have h2 := run_comp h1 (four_turn (back k [true,false]))
  have h3 := run_comp h2 (reset_scan (k+1) [true,false] (ones 3 []))
  rw [ones_add] at h3
  rw [show 3*(k+1)+1+3 = (3*k+6)+1 by omega] at h3
  have h4 := run_comp h3 (odd_left_boundary (ones (3*k+6) []))
  rw [show 6*k+12+3*(k+1)+8+5*(k+1)+8 = 14*k+36 by omega] at h4
  exact h4

/-- The one-one boundary creates a suffix whose size depends on k. -/
theorem one_left_boundary (t : List Bool) :
    run 6 ⟨.A, [true,false,true], true :: t⟩ =
      some (shuttleTailCfg 0 1 (false :: ones 2 t)) := by rfl

theorem one_collapse (k : Nat) :
    run (8*k+17) (shuttleCfg k 1) =
      some (shuttleTailCfg 0 1 (defectTail (3*k+2))) := by
  have h1 := run_comp (entry (blocks k [true]))
    (scan_right k [true,false,true] [true])
  have h2 := run_comp h1 (odd_turn (back k [true,false,true]))
  have h3 := run_comp h2 (reset_scan k [true,false,true] [false,true,true])
  have h4 := run_comp h3 (one_left_boundary (ones (3*k) [false,true,true]))
  rw [show 3+3*k+8+5*k+6 = 8*k+17 by omega] at h4
  unfold shuttleTailCfg at h4 ⊢
  rw [ones_add] at h4
  rw [show 2+3*k = 3*k+2 by omega] at h4
  exact h4

/-- Arbitrary untouched suffix; this closes the new large-defect boundary. -/
theorem zero_block_defect (t : List Bool) :
    run 37 (shuttleTailCfg 0 1 (false :: ones 6 t)) =
      some (shuttleTailCfg 3 2 t) := by rfl

theorem zero_block_defect_param (n : Nat) (t : List Bool) :
    run 37 (shuttleTailCfg 0 1 (false :: ones (n+6) t)) =
      some (shuttleTailCfg 3 (n+2) t) := by
  have h := zero_block_defect (ones n t)
  unfold shuttleTailCfg at h ⊢
  rw [ones_add, ones_add] at h
  simpa [Nat.add_comm] using h


/-- A complete residue class of clean configurations that the old clean macro omitted. -/
theorem even_carry_to_four (q : Nat) :
    run (108*q*q+170*q+53) (cleanCfg (4*q+2)) =
      some (shuttleCfg (6*q+3) 4) := by
  have h1 := appC8_raw_reset (4*q+1)
  rw [show 3*(4*q+1)+1 = 12*q+4 by omega] at h1
  have h2 := appC8_raw_rounds_closed_form (3*q) 3 (12*q+4) (by omega)
  have hsub : 12*q+4-4*(3*q) = 4 := by omega
  rw [show 3+2*(3*q) = 6*q+3 by omega, hsub] at h2
  have h := run_comp h1 h2
  have ht : 5*(4*q+1+1)+43+(12*(3*q*3)+12*(3*q*(3*q-1))+26*(3*q)) =
      108*q*q+170*q+53 := by
    cases q with
    | zero => decide
    | succ q => rw [show 3*(q+1)-1 = 3*q+2 by omega]; ring
  rw [ht] at h
  exact h

theorem one_to_tail (n : Nat) :
    run (8*(n+2)+54) (shuttleCfg (n+2) 1) =
      some (shuttleTailCfg 3 (3*n+4) [false,true,true]) := by
  have h1 := one_collapse (n+2)
  have h2 := zero_block_defect_param (3*n+2) [false,true,true]
  rw [show 3*n+2+6 = 3*(n+2)+2 by omega] at h2
  have h := run_comp h1 h2
  rw [show 8*(n+2)+17+37 = 8*(n+2)+54 by omega] at h
  exact h

/-- The remaining three-one boundary with suffix 011 creates a new 01^5 tail. -/
theorem three_with_tail (k : Nat) :
    run (12*k+40) (shuttleTailCfg k 3 [false,true,true]) =
      some (shuttleTailCfg (k+1) 1 (false :: ones 5 [])) := by
  have h1 := run_comp (odd_half k [false,true,true])
    (scan_right (k+1) [true,false] [true,false,true,true])
  have ht := defect_turn_19 (back (k+1) [true,false])
  rw [back_read] at ht
  have h2 := run_comp h1 ht
  have h3 := run_comp h2 (scan_left (k+1) [false] (false :: ones 5 []))
  have h4 := run_comp h3 (final_boundary (returnWord (k+1) (false :: ones 5 [])))
  change run _ _ = some ⟨.A, [], false :: true :: false ::
    (true :: returnWord (k+1) (false :: ones 5 []))⟩ at h4
  rw [return_close_prefix] at h4
  rw [show 6*k+12+3*(k+1)+19+3*(k+1)+3 = 12*k+40 by omega] at h4
  exact h4

/-- Nonempty runs of ones, separated by single zeros. No finite bound on run count. -/
inductive PositiveWord : List Bool → Prop where
  | last (n : Nat) : PositiveWord (ones (n+1) [])
  | more (n : Nat) {t : List Bool} : PositiveWord t →
      PositiveWord (ones (n+1) (false :: t))

def Boundary (c : Cfg) : Prop :=
  ∃ w, PositiveWord w ∧ c = shuttleTailCfg 0 0 w

theorem positive_blocks (k : Nat) {w : List Bool} (hw : PositiveWord w) :
    PositiveWord (blocks k w) := by
  induction k with
  | zero => exact hw
  | succ k ih => exact PositiveWord.more 1 ih

theorem boundary_pure (k m : Nat) (hm : 0 < m) : Boundary (shuttleCfg k m) := by
  refine ⟨blocks k (ones m []), ?_, rfl⟩
  have h : m = (m-1)+1 := by omega
  rw [h]
  exact positive_blocks k (PositiveWord.last (m-1))

theorem boundary_tail (k m : Nat) (hm : 0 < m) {w : List Bool} (hw : PositiveWord w) :
    Boundary (shuttleTailCfg k m (false :: w)) := by
  refine ⟨blocks k (ones m (false :: w)), ?_, rfl⟩
  have h : m = (m-1)+1 := by omega
  rw [h]
  exact positive_blocks k (PositiveWord.more (m-1) hw)

/-- Every positive suffix-free shuttle configuration makes positive-time progress
back into the larger boundary language. This does NOT prove that language closed. -/
theorem pure_boundary_progress (k m : Nat) (hm : 0 < m) :
    ∃ t d, 0 < t ∧ run t (shuttleCfg k m) = some d ∧ Boundary d := by
  by_cases h5 : 5 ≤ m
  · exact ⟨12*k+26, _, by omega, appC8_raw_shuttle k m h5,
      boundary_pure (k+2) (m-4) (by omega)⟩
  have cases_m : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
  rcases cases_m with rfl | rfl | rfl | rfl
  · refine ⟨8*k+17, _, by omega, one_collapse k, ?_⟩
    exact boundary_tail 0 1 (by omega)
      (PositiveWord.more (3*k+1) (PositiveWord.last 1))
  · have h := run_comp (appC8_raw_exit k) (appC8_raw_reset k)
    exact ⟨_, _, by omega, h, boundary_pure 3 (3*k+1) (by omega)⟩
  · refine ⟨14*k+36, _, by omega, appC8_odd_collapse k, ?_⟩
    exact boundary_tail 0 (3*k+7) (by omega) (PositiveWord.last 1)
  · exact ⟨14*k+36, _, by omega, four_collapse k,
      boundary_pure 0 (3*k+10) (by omega)⟩

/-- The precise missing induction obligation. This is a definition, not an axiom. -/
def BoundaryReturn : Prop :=
  ∀ c, Boundary c → ∃ t d, 0 < t ∧ run t c = some d ∧ Boundary d

/-- Positive macro durations suffice; growth of tape length is not required. -/
theorem survives_of_boundary_return (hreturn : BoundaryReturn) :
    ∀ j c, Boundary c → ∃ d, run j c = some d := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro c hc
      obtain ⟨t, d, ht, hrun, hd⟩ := hreturn c hc
      by_cases hj : j ≤ t
      · exact run_prefix_defined hrun j hj
      · obtain ⟨e, he⟩ := ih (j-t) (by omega) d hd
        have h := run_comp hrun he
        rw [show t+(j-t) = j by omega] at h
        exact ⟨e, h⟩

/-- Conditional only: no theorem in this module supplies hreturn. -/
theorem blank_survives_of_boundary_return (hreturn : BoundaryReturn) (j : Nat) :
    ∃ d, run j blankCfg = some d := by
  by_cases hj : j ≤ 5
  · exact run_prefix_defined appC8_blank_entry j hj
  · obtain ⟨d, hd⟩ := survives_of_boundary_return hreturn (j-5) _ (boundary_pure 0 2 (by omega))
    have h := run_comp appC8_blank_entry hd
    rw [show 5+(j-5) = j by omega] at h
    exact ⟨d, h⟩

/-- Arbitrary tails are unsafe: this concrete input reaches an undefined instruction. -/
theorem arbitrary_suffix_halts :
    run 49 (shuttleTailCfg 0 1 [false,false,true,false,true,true,true]) = none := by decide

/-- A genuine upstream nonhalting conclusion, with the missing closure premise explicit. -/
theorem upstream_nonhalting_of_boundary_return (hreturn : BoundaryReturn) :
    BusyBeaver.IsNotHalt BB6Interop.AppC8.machine := by
  intro c ⟨n, hn⟩
  obtain ⟨d, hd⟩ := blank_survives_of_boundary_return hreturn (n+1)
  have hu := BB6Interop.AppC8.blank_reaches_in hd
  change BusyBeaver.multiStep BB6Interop.AppC8.machine (BusyBeaver.init []) (n+1) =
    some (BB6Interop.AppC8.encode d) at hu
  rw [BusyBeaver.multiStep_succ', hn, Option.bind_some] at hu
  rw [hu]
  rfl

end BB6Interop.AppC8Continuation
