import BB6Interop.AppC8ContinuationCheckpoints

/-! Suffix-bearing run-list refinements. Closure hypotheses remain explicit. -/
namespace BB6Interop.AppC8RunLists
open CryptidSolvePhase4 CryptidSolvePhase4.AppC8Raw BB6Interop.AppC8Continuation
set_option maxRecDepth 20000

/-- A five-one defect consumes one left block, uniformly in the remaining left tape. -/
theorem five_turn (l : List Bool) :
    run 61 ⟨.E, back 1 l, true :: false :: ones 5 []⟩ =
      some ⟨.A, l, true :: defectTail 8⟩ := by rfl

/-- The requested frontier family, for every positive block count. -/
theorem five_collapse (n : Nat) :
    run (8*(n+1)+65) (shuttleTailCfg (n+1) 1 (false :: ones 5 [])) =
      some (shuttleTailCfg 0 1 (false :: ones (3*n+2) (defectTail 8))) := by
  have h1 := run_comp (entry (blocks (n+1) (true :: false :: ones 5 [])))
    (scan_right (n+1) [true,false,true] (true :: false :: ones 5 []))
  have h2 := run_comp h1 (five_turn (back n [true,false,true]))
  have h3 := run_comp h2 (reset_scan n [true,false,true] (defectTail 8))
  have h4 := run_comp h3 (one_left_boundary (ones (3*n) (defectTail 8)))
  unfold shuttleTailCfg at h4 ⊢
  rw [ones_add] at h4
  rw [show 2+3*n = 3*n+2 by omega,
      show 3+3*(n+1)+61+5*n+6 = 8*(n+1)+65 by omega] at h4
  exact h4

theorem five_zero :
    run 37 (shuttleTailCfg 0 1 (false :: ones 5 [])) = some (shuttleCfg 3 1) := by rfl

/-- Four ones followed by a single zero and any run of at least three ones.
The suffix t is untouched and unrestricted. -/
theorem four_long (k n : Nat) (t : List Bool) :
    run (12*k+32) (shuttleTailCfg k 4 (false :: ones (n+3) t)) =
      some (shuttleTailCfg (k+3) (n+1) t) := by
  have h1 := odd_half k (true :: false :: ones (n+3) t)
  change run (6*k+12) _ = some ⟨.E, [true,false],
    blocks (k+1) (blocks 1 (ones (n+3) t))⟩ at h1
  rw [blocks_add] at h1
  have h2 := run_comp h1 (scan_right (k+2) [true,false] (ones (n+3) t))
  have h3 := run_comp h2 (turn_and_return (k+2) [false] (ones n t))
  have h4 := run_comp h3 (final_boundary (returnWord (k+2) (true :: false :: true :: ones n t)))
  rw [close_word] at h4
  rw [show 6*k+12+3*(k+2)+(5+3*(k+2))+3 = 12*k+32 by omega] at h4
  exact h4


/-- Run lengths are stored minus one, so every encoded run is positive. -/
def suffix : List Nat → List Bool
  | [] => []
  | n :: ns => false :: ones (n+1) (suffix ns)

def runListCfg (k m : Nat) (ns : List Nat) : Cfg :=
  shuttleTailCfg k (m+1) (suffix ns)

theorem positive_run_list (n : Nat) (ns : List Nat) :
    PositiveWord (ones (n+1) (suffix ns)) := by
  induction ns generalizing n with
  | nil => exact PositiveWord.last n
  | cons a ns ih => exact PositiveWord.more n (ih a)

theorem run_list_boundary (k m : Nat) (ns : List Nat) : Boundary (runListCfg k m ns) := by
  exact ⟨blocks k (ones (m+1) (suffix ns)), positive_blocks k (positive_run_list m ns), rfl⟩

/-- Every candidate boundary has a run-list representation; no reachability is assumed. -/
theorem positive_word_run_list {w : List Bool} (hw : PositiveWord w) :
    ∃ m ns, w = ones (m+1) (suffix ns) := by
  induction hw with
  | last n => exact ⟨n, [], rfl⟩
  | more n hw ih =>
      obtain ⟨m, ns, h⟩ := ih
      exact ⟨n, m :: ns, by rw [h]; rfl⟩

theorem boundary_iff_run_list (c : Cfg) :
    Boundary c ↔ ∃ m ns, c = runListCfg 0 m ns := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨m, ns, rfl⟩ := positive_word_run_list hw
    exact ⟨m, ns, rfl⟩
  · rintro ⟨m, ns, rfl⟩
    exact run_list_boundary 0 m ns

theorem run_list_shuttle (k m : Nat) (ns : List Nat) :
    run (12*k+26) (runListCfg k (m+4) ns) = some (runListCfg (k+2) m ns) := by
  have h := tail_shuttle k (m+5) (suffix ns) (by omega)
  rw [show m+5-4 = m+1 by omega] at h
  exact h

/-- Normalization of a two-one run is a tape identity, not positive-time progress. -/
theorem run_list_absorb (k m : Nat) (ns : List Nat) :
    runListCfg k 1 (m :: ns) = runListCfg (k+1) m ns :=
  absorb_defect k (m+1) (suffix ns)

theorem run_list_four_long (k m : Nat) (ns : List Nat) :
    run (12*k+32) (runListCfg k 3 ((m+2) :: ns)) =
      some (runListCfg (k+3) m ns) :=
  four_long k m (suffix ns)

theorem run_list_five (n : Nat) :
    run (8*(n+1)+65) (runListCfg (n+1) 0 [4]) =
      some (runListCfg 0 0 [3*n+1,7,1]) := five_collapse n

/-- Existence of a positive-time return to the candidate boundary language. -/
def Progress (c : Cfg) : Prop :=
  ∃ t d, 0 < t ∧ run t c = some d ∧ Boundary d

theorem progress_prepend {t : Nat} {c d : Cfg} (h : run t c = some d)
    (hd : Progress d) : Progress c := by
  obtain ⟨u, e, hu, he, hb⟩ := hd
  exact ⟨t+u, e, by omega, run_comp h he, hb⟩

def GoodTail (t : List Bool) : Prop := t = [] ∨ ∃ w, PositiveWord w ∧ t = false :: w

theorem positive_good_tail (n : Nat) {t : List Bool} (ht : GoodTail t) :
    PositiveWord (ones (n+1) t) := by
  rcases ht with rfl | ⟨w, hw, rfl⟩
  · exact PositiveWord.last n
  · exact PositiveWord.more n hw

theorem boundary_good_tail (k n : Nat) {t : List Bool} (ht : GoodTail t) :
    Boundary (shuttleTailCfg k (n+1) t) :=
  ⟨blocks k (ones (n+1) t), positive_blocks k (positive_good_tail n ht), rfl⟩

abbrev firstMarker : List Bool := [true,false,true]
abbrev secondMarker : List Bool := [true,false]

/-- Primitive zero turn, independent of the rest of the left tape. -/
theorem zero_turn (l : List Bool) :
    run 5 ⟨.E, back 1 l, []⟩ = some ⟨.A, l, ones 4 []⟩ := by rfl

theorem second_one (k : Nat) :
    run (5*k+16) ⟨.E, back k secondMarker, [true]⟩ =
      some (shuttleTailCfg 0 (3*k+4) [false,true,true]) := by
  have h1 := run_comp (odd_turn (back k secondMarker))
    (reset_scan k secondMarker [false,true,true])
  have h2 := run_comp h1 (odd_left_boundary (ones (3*k) [false,true,true]))
  rw [show 8+5*k+8 = 5*k+16 by omega] at h2
  exact h2

theorem second_two (k : Nat) :
    run (5*k+16) ⟨.E, back k secondMarker, [true,true]⟩ =
      some (shuttleCfg 0 (3*k+7)) := by
  have h1 := run_comp (exit_boundary (back k secondMarker)) (zero_turn (back k secondMarker))
  have h2 := run_comp h1 (reset_scan k secondMarker (ones 3 []))
  rw [ones_add, show 3*k+1+3 = (3*k+3)+1 by omega] at h2
  have h3 := run_comp h2 (odd_left_boundary (ones (3*k+3) []))
  rw [show 3+5+5*k+8 = 5*k+16 by omega] at h3
  exact h3

theorem second_long (k n : Nat) (t : List Bool) :
    run (3*k+8) ⟨.E, back k secondMarker, ones (n+3) t⟩ =
      some (shuttleTailCfg (k+1) (n+1) t) := by
  have h := run_comp (turn_and_return k [false] (ones n t))
    (final_boundary (returnWord k (true :: false :: true :: ones n t)))
  rw [close_word, show 5+3*k+3 = 3*k+8 by omega] at h
  exact h

theorem first_one (k : Nat) :
    run (5*k+14) ⟨.E, back k firstMarker, [true]⟩ =
      some (shuttleTailCfg 0 1 (defectTail (3*k+2))) := by
  have h1 := run_comp (odd_turn (back k firstMarker))
    (reset_scan k firstMarker [false,true,true])
  have h2 := run_comp h1 (one_left_boundary (ones (3*k) [false,true,true]))
  unfold shuttleTailCfg at h2 ⊢
  rw [ones_add, show 2+3*k = 3*k+2 by omega,
      show 8+5*k+6 = 5*k+14 by omega] at h2
  exact h2

theorem first_two (k : Nat) :
    run (5*k+51) ⟨.E, back k firstMarker, [true,true]⟩ =
      some (shuttleCfg 3 (3*k+1)) := by
  have h := run_comp (exit_boundary (back k firstMarker)) (appC8_raw_reset k)
  rw [show 3+(5*(k+1)+43) = 5*k+51 by omega] at h
  exact h

theorem first_long (k n : Nat) (t : List Bool) :
    run (3*k+9) ⟨.E, back k firstMarker, ones (n+3) t⟩ =
      some ⟨.E, secondMarker, blocks (k+1) (ones (n+1) t)⟩ := by
  have h := run_comp (turn_and_return k [false,true] (ones n t))
    (middle_boundary (returnWord k (true :: false :: true :: ones n t)))
  rw [close_word, show 5+3*k+4 = 3*k+9 by omega] at h
  exact h

/-- These are the only unresolved cases of the run-list sweep decomposition.
They are propositions, not axioms or established closure results. -/
def DefectReturn (marker : List Bool) : Prop :=
  ∀ k w, PositiveWord w → Progress ⟨.E, back k marker, true :: false :: w⟩

theorem second_sweep_progress (hd : DefectReturn secondMarker) {w : List Bool}
    (hw : PositiveWord w) (k : Nat) : Progress ⟨.E, back k secondMarker, w⟩ := by
  induction hw generalizing k with
  | last n =>
      cases n with
      | zero => exact ⟨_, _, by omega, second_one k,
          boundary_tail 0 (3*k+4) (by omega) (PositiveWord.last 1)⟩
      | succ n =>
          cases n with
          | zero => exact ⟨_, _, by omega, second_two k, boundary_pure 0 (3*k+7) (by omega)⟩
          | succ n => exact ⟨_, _, by omega, second_long k n [],
              boundary_good_tail (k+1) n (Or.inl rfl)⟩
  | @more n w hw ih =>
      cases n with
      | zero => exact hd k w hw
      | succ n =>
          cases n with
          | zero => exact progress_prepend (scan_right 1 (back k secondMarker) w) (ih (k+1))
          | succ n => exact ⟨_, _, by omega, second_long k n (false :: w),
              boundary_good_tail (k+1) n (Or.inr ⟨w, hw, rfl⟩)⟩

theorem first_sweep_progress (hf : DefectReturn firstMarker) (hs : DefectReturn secondMarker)
    {w : List Bool} (hw : PositiveWord w) (k : Nat) : Progress ⟨.E, back k firstMarker, w⟩ := by
  induction hw generalizing k with
  | last n =>
      cases n with
      | zero => exact ⟨_, _, by omega, first_one k,
          boundary_tail 0 1 (by omega) (PositiveWord.more (3*k+1) (PositiveWord.last 1))⟩
      | succ n =>
          cases n with
          | zero => exact ⟨_, _, by omega, first_two k, boundary_pure 3 (3*k+1) (by omega)⟩
          | succ n =>
              exact progress_prepend (first_long k n [])
                (second_sweep_progress hs (positive_blocks (k+1) (PositiveWord.last n)) 0)
  | @more n w hw ih =>
      cases n with
      | zero => exact hf k w hw
      | succ n =>
          cases n with
          | zero => exact progress_prepend (scan_right 1 (back k firstMarker) w) (ih (k+1))
          | succ n =>
              exact progress_prepend (first_long k n (false :: w))
                (second_sweep_progress hs (positive_blocks (k+1) (PositiveWord.more n hw)) 0)

/-- Full run-list closure reduces to the two explicit one-one defect sweep obligations. -/
theorem boundary_return_of_defects (hf : DefectReturn firstMarker)
    (hs : DefectReturn secondMarker) : BoundaryReturn := by
  rintro c ⟨w, hw, rfl⟩
  exact progress_prepend (entry w) (first_sweep_progress hf hs hw 0)


/-- A one-one defect shifts two cells right without inspecting the positive run's tail. -/
theorem defect_push (l t : List Bool) :
    run 8 ⟨.E, l, true :: false :: true :: t⟩ =
      some ⟨.E, true :: false :: l, true :: t⟩ := by rfl

/-- Uniform local strip: arbitrary residual left tape and arbitrary untouched suffix.
The output has residual left tape l, so it need not be a Boundary configuration. -/
theorem defect_strip_block (l t : List Bool) :
    run 31 ⟨.E, back 1 l, true :: false :: ones 5 t⟩ =
      some ⟨.A, l, false :: true :: false :: blocks 2 (true :: t)⟩ := by rfl

theorem defect_strip_block_param (l t : List Bool) (n : Nat) :
    run 31 ⟨.E, back 1 l, true :: false :: ones (n+5) t⟩ =
      some ⟨.A, l, false :: true :: false :: blocks 2 (ones (n+1) t)⟩ := by
  have h := defect_strip_block l (ones n t)
  rw [ones_add] at h
  rw [show 5+n = n+5 by omega] at h
  exact h

/-- Variable-length run-list continuation into the residual-left-tape phase. -/
theorem run_list_one_long_local (k n : Nat) (ns : List Nat) :
    run (3*k+37) (runListCfg (k+1) 0 ((n+4) :: ns)) =
      some ⟨.A, back k firstMarker,
        false :: true :: false :: blocks 2 (ones (n+1) (suffix ns))⟩ := by
  have h1 := run_comp (entry (blocks (k+1) (true :: false :: ones (n+5) (suffix ns))))
    (scan_right (k+1) firstMarker (true :: false :: ones (n+5) (suffix ns)))
  have h := run_comp h1 (defect_strip_block_param (back k firstMarker) (suffix ns) n)
  rw [show 3+3*(k+1)+31 = 3*k+37 by omega] at h
  exact h

theorem five_boundary_progress (k : Nat) : Progress (runListCfg k 0 [4]) := by
  cases k with
  | zero => exact ⟨37, _, by omega, five_zero, boundary_pure 3 1 (by omega)⟩
  | succ k => exact ⟨_, _, by omega, run_list_five k, run_list_boundary 0 0 [3*k+1,7,1]⟩

/-- The requested concrete frontier is discharged by the universal family. -/
theorem blank_after_five :
    run 507474445401 blankCfg = some (runListCfg 0 0 [919663,7,1]) := by
  have hs := run_list_five 306554
  norm_num only at hs
  have h := run_comp blank_extended_frontier hs
  norm_num only at h
  exact h

/-- The variable run in the new output is immediately handled with an untouched suffix. -/
theorem blank_after_variable_defect :
    run 507474445438 blankCfg = some (runListCfg 3 919659 [7,1]) := by
  have hs := zero_block_defect_param 919658 (suffix [7,1])
  norm_num only at hs
  have h := run_comp blank_after_five hs
  norm_num only at h
  exact h


/-- No left blocks: a five-one prefix suffices, with an arbitrary untouched suffix. -/
theorem first_zero_long (t : List Bool) :
    run 34 ⟨.E, firstMarker, true :: false :: ones 5 t⟩ =
      some (shuttleTailCfg 3 1 t) := by rfl

theorem second_zero_long (t : List Bool) :
    run 31 ⟨.E, secondMarker, true :: false :: ones 5 t⟩ =
      some (shuttleTailCfg 2 1 t) := by rfl

/-- The terminal five-one case of the first defect obligation, including k=0. -/
theorem first_five_progress (k : Nat) :
    Progress ⟨.E, back k firstMarker, true :: false :: ones 5 []⟩ := by
  cases k with
  | zero => exact ⟨34, _, by omega, first_zero_long [], boundary_pure 3 1 (by omega)⟩
  | succ k =>
      have h1 := run_comp (five_turn (back k firstMarker))
        (reset_scan k firstMarker (defectTail 8))
      have h2 := run_comp h1 (one_left_boundary (ones (3*k) (defectTail 8)))
      unfold shuttleTailCfg at h2
      rw [ones_add, show 2+3*k = 3*k+2 by omega] at h2
      exact ⟨_, _, by omega, h2, run_list_boundary 0 0 [3*k+1,7,1]⟩

/-- The same terminal family for the second marker. -/
theorem second_five_progress (k : Nat) :
    Progress ⟨.E, back k secondMarker, true :: false :: ones 5 []⟩ := by
  cases k with
  | zero => exact ⟨31, _, by omega, second_zero_long [], boundary_pure 2 1 (by omega)⟩
  | succ k =>
      have h1 := run_comp (five_turn (back k secondMarker))
        (reset_scan k secondMarker (defectTail 8))
      have h2 := run_comp h1 (odd_left_boundary (ones (3*k) (defectTail 8)))
      exact ⟨_, _, by omega, h2, run_list_boundary 0 (3*k+3) [7,1]⟩

/-- Terminal two-one defect for the return sweep: every k, including zero. -/
theorem second_defect_two (k : Nat) :
    run (3*k+22) ⟨.E, back k secondMarker, [true,false,true,true]⟩ =
      some (shuttleTailCfg k 1 (false :: ones 5 [])) := by
  have ht := defect_turn_19 (back k secondMarker)
  rw [back_read] at ht
  have h1 := run_comp ht (scan_left k [false] (false :: ones 5 []))
  have h2 := run_comp h1 (final_boundary (returnWord k (false :: ones 5 [])))
  change run _ _ = some ⟨.A, [], false :: true :: false ::
    (true :: returnWord k (false :: ones 5 []))⟩ at h2
  rw [return_close_prefix, show 19+3*k+3 = 3*k+22 by omega] at h2
  exact h2

/-- This also removes the former k>=2 restriction for progress on the first two-one defect. -/
theorem first_defect_two_progress (k : Nat) :
    Progress ⟨.E, back k firstMarker, [true,false,true,true]⟩ := by
  have ht := defect_turn_19 (back k firstMarker)
  rw [back_read] at ht
  have h1 := run_comp ht (scan_left k [false,true] (false :: ones 5 []))
  have h2 := run_comp h1 (middle_boundary (returnWord k (false :: ones 5 [])))
  rw [return_close_prefix] at h2
  have h3 := run_comp h2 (scan_right k secondMarker (true :: false :: ones 5 []))
  exact progress_prepend h3 (second_five_progress k)

/-- Both unresolved defect predicates would suffice for the actual upstream classification. -/
theorem upstream_nonhalting_of_defects (hf : DefectReturn firstMarker)
    (hs : DefectReturn secondMarker) : BusyBeaver.IsNotHalt BB6Interop.AppC8.machine :=
  upstream_nonhalting_of_boundary_return (boundary_return_of_defects hf hs)


/-- The requested suffix excursion returns to a clean carry configuration. -/
theorem blank_clean_return :
    run 1141823725445 blankCfg = some (cleanCfg 459838) := by
  have hs := tail_shuttle_rounds 229914 3 919660 (suffix [7,1]) (by decide)
  norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
  have h1 := run_comp blank_after_variable_defect hs
  have h2 := run_comp h1 (run_list_four_long 459831 5 [1])
  have h3 := run_comp h2 (run_list_shuttle 459834 1 [1])
  rw [run_list_absorb] at h3
  have h4 := run_comp h3 (appC8_raw_exit 459837)
  norm_num only at h4
  exact h4

theorem blank_prefix (j : Nat) (hj : j ≤ 1141823725445) :
    ∃ d, run j blankCfg = some d :=
  run_prefix_defined blank_clean_return j hj

theorem upstream_clean_return :
    BusyBeaver.ReachesIn BB6Interop.AppC8.machine 1141823725445 (BusyBeaver.init [])
      (BB6Interop.AppC8.encode (cleanCfg 459838)) :=
  BB6Interop.AppC8.blank_reaches_in blank_clean_return

theorem upstream_prefix (j : Nat) (hj : j ≤ 1141823725445) :
    ∃ d, BusyBeaver.ReachesIn BB6Interop.AppC8.machine j (BusyBeaver.init []) d := by
  obtain ⟨d, hd⟩ := blank_prefix j hj
  exact ⟨BB6Interop.AppC8.encode d, BB6Interop.AppC8.blank_reaches_in hd⟩


/-- Zero-block one-one defect for any next run of length at least five and any run list. -/
theorem run_list_zero_long (n : Nat) (ns : List Nat) :
    run 37 (runListCfg 0 0 ((n+4) :: ns)) = some (runListCfg 3 n ns) := by
  have hs := first_zero_long (ones n (suffix ns))
  rw [ones_add, show 5+n = n+5 by omega] at hs
  have h := run_comp (entry (true :: false :: ones (n+5) (suffix ns))) hs
  exact h

/-- Normalizing any number of two-one runs is a zero-time representation change.
The subsequent Progress witness must still have a strictly positive duration. -/
theorem run_list_absorb_many (r k m : Nat) (ns : List Nat) :
    runListCfg k 1 (List.replicate r 1 ++ m :: ns) =
      runListCfg (k+r+1) m ns := by
  induction r generalizing k with
  | zero => exact run_list_absorb k m ns
  | succ r ih =>
      change runListCfg k 1 (1 :: (List.replicate r 1 ++ m :: ns)) = _
      rw [run_list_absorb, ih]
      congr 1; omega

end BB6Interop.AppC8RunLists
