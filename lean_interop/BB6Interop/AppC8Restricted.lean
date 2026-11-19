import BB6Interop.AppC8ResidualTape

/-! Restricted residual phases and blank-derived boundary candidates.
No unconditional global nonhalting theorem is asserted. -/
namespace BB6Interop.AppC8Restricted
open CryptidSolvePhase4 CryptidSolvePhase4.AppC8Raw
open BB6Interop.AppC8Continuation BB6Interop.AppC8RunLists
set_option maxRecDepth 20000

/-- A residual shuttle with arbitrary finite left tape. -/
def phase (l : List Bool) (b m : Nat) (t : List Bool) : Cfg :=
  ⟨.A, l, false :: true :: false :: blocks b (ones m t)⟩

theorem entry_left (l t : List Bool) :
    run 3 (phase l 0 0 t) = some ⟨.E, firstMarker ++ l, t⟩ := by rfl

theorem middle_left (l t : List Bool) :
    run 4 ⟨.A, false :: true :: l, true :: t⟩ =
      some ⟨.E, true :: false :: l, true :: t⟩ := by rfl

theorem third_entry (l t : List Bool) :
    run 4 ⟨.A, false :: true :: false :: false :: l, true :: t⟩ =
      some ⟨.E, true :: false :: false :: false :: l, true :: t⟩ := by rfl

theorem zero_left_finish (l t : List Bool) :
    run 3 ⟨.A, false :: false :: false :: l, true :: t⟩ =
      some (phase l 0 1 t) := by rfl

/-- One left block is consumed; three right blocks are produced and six ones spent. -/
theorem residual_cycle (l t : List Bool) (b n : Nat) :
    run (18*b+47) (phase (back 1 l) b (n+7) t) =
      some (phase l (b+3) (n+1) t) := by
  have h1 := run_comp (entry_left (back 1 l) (blocks b (ones (n+7) t)))
    (scan_right b (firstMarker ++ back 1 l) (ones (n+7) t))
  have h2 := run_comp h1 (turn_and_return b (false :: true :: back 1 l) (ones (n+4) t))
  have h3 := run_comp h2 (middle_left (back 1 l)
    (returnWord b (true :: false :: true :: ones (n+4) t)))
  rw [close_word] at h3
  have h4 := run_comp h3 (scan_right (b+1) (true :: false :: back 1 l) (ones (n+5) t))
  have h5 := run_comp h4 (turn_and_return (b+1) (false :: back 1 l) (ones (n+2) t))
  have h6 := run_comp h5 (third_entry l
    (returnWord (b+1) (true :: false :: true :: ones (n+2) t)))
  rw [close_word] at h6
  -- The arbitrary remaining left tape must be retained in the third scan.
  have h7' := run_comp h6 (scan_right (b+2) (true :: false :: false :: false :: l) (ones (n+3) t))
  have h8 := run_comp h7' (turn_and_return (b+2) (false :: false :: false :: l) (ones n t))
  have h9 := run_comp h8 (zero_left_finish l
    (returnWord (b+2) (true :: false :: true :: ones n t)))
  change run _ _ = some ⟨.A, l, false :: true :: false ::
    (true :: returnWord (b+2) (true :: false :: true :: ones n t))⟩ at h9
  rw [close_word] at h9
  convert h9 using 1 <;> congr 1 <;> omega

theorem marker_finish (marker : List Bool) (hm : marker = firstMarker ∨ marker = secondMarker)
    (b n : Nat) (t : List Bool) :
    ∃ d u, 0 < u ∧ run u (phase marker b (n+7) t) = some d ∧
      (d = shuttleTailCfg (b+4) (n+1) t ∨ d = shuttleTailCfg (b+3) (n+1) t) := by
  have h1 := run_comp (entry_left marker (blocks b (ones (n+7) t)))
    (scan_right b (firstMarker ++ marker) (ones (n+7) t))
  have h2 := run_comp h1 (turn_and_return b (false :: true :: marker) (ones (n+4) t))
  have h3 := run_comp h2 (middle_left marker
    (returnWord b (true :: false :: true :: ones (n+4) t)))
  rw [close_word] at h3
  have h4 := run_comp h3 (scan_right (b+1) (true :: false :: marker) (ones (n+5) t))
  have h5 := run_comp h4 (turn_and_return (b+1) (false :: marker) (ones (n+2) t))
  rcases hm with rfl | rfl
  · have edge (t : List Bool) :
        run 4 ⟨.A, false :: firstMarker, true :: t⟩ =
          some ⟨.E, [true,false,false,true], true :: t⟩ := by rfl
    have h6 := run_comp h5 (edge (returnWord (b+1) (true :: false :: true :: ones (n+2) t)))
    rw [close_word] at h6
    have h7 := run_comp h6 (scan_right (b+2) [true,false,false,true] (ones (n+3) t))
    rw [back_push] at h7
    have h8 := run_comp h7 (turn_and_return (b+3) [] (ones n t))
    have finish (t : List Bool) : run 3 ⟨.A, [], true :: t⟩ =
        some (phase [] 0 1 t) := by rfl
    have h9 := run_comp h8 (finish (returnWord (b+3) (true :: false :: true :: ones n t)))
    change run _ _ = some ⟨.A, [], false :: true :: false ::
      (true :: returnWord (b+3) (true :: false :: true :: ones n t))⟩ at h9
    rw [close_word] at h9
    exact ⟨_, _, by omega, h9, Or.inl rfl⟩
  · have edge (t : List Bool) :
        run 4 ⟨.A, false :: secondMarker, true :: t⟩ =
          some ⟨.E, [true,false,false], true :: t⟩ := by rfl
    have h6 := run_comp h5 (edge (returnWord (b+1) (true :: false :: true :: ones (n+2) t)))
    rw [close_word] at h6
    have h7 := run_comp h6 (scan_right (b+2) [true,false,false] (ones (n+3) t))
    have h8 := run_comp h7 (turn_and_return (b+2) [false,false] (ones n t))
    have finish (t : List Bool) : run 3 ⟨.A, [false,false], true :: t⟩ =
        some (phase [] 0 1 t) := by rfl
    have h9 := run_comp h8 (finish (returnWord (b+2) (true :: false :: true :: ones n t)))
    change run _ _ = some ⟨.A, [], false :: true :: false ::
      (true :: returnWord (b+2) (true :: false :: true :: ones n t))⟩ at h9
    rw [close_word] at h9
    exact ⟨_, _, by omega, h9, Or.inr rfl⟩

/-- A conserved margin: six right ones per remaining left block, plus seven. -/
theorem residual_drain (a b n : Nat) (l t : List Bool) :
    run (27*a*a+20*a+18*a*b) (phase (back a l) b (6*a+n+7) t) =
      some (phase l (b+3*a) (n+7) t) := by
  induction a generalizing b with
  | zero => simp [back, run]
  | succ a ih =>
      have h1 := residual_cycle (back a l) t b (6*a+n+6)
      have h2 := ih (b+3)
      rw [show 6*a+n+6+1 = 6*a+n+7 by omega] at h1
      have h := run_comp h1 h2
      rw [show b+3+3*a = b+3*(a+1) by omega] at h
      have ht : 18*b+47+(27*a*a+20*a+18*a*(b+3)) =
          27*(a+1)*(a+1)+20*(a+1)+18*(a+1)*b := by ring
      rw [ht, show 6*a+n+6+7 = 6*(a+1)+n+7 by omega] at h
      exact h

/-- This local domain is genuinely guarded by a left/right arithmetic correlation. -/
def Fueled (c : Cfg) : Prop :=
  ∃ marker a b n t, (marker = firstMarker ∨ marker = secondMarker) ∧ GoodTail t ∧
    c = phase (back a marker) b (6*a+n+7) t

theorem fueled_progress {c : Cfg} (hc : Fueled c) : Progress c := by
  obtain ⟨marker,a,b,n,t,hm,ht,rfl⟩ := hc
  obtain ⟨d,u,hu,hr,hout⟩ := marker_finish marker hm (b+3*a) n t
  have h := run_comp (residual_drain a b n marker t) hr
  refine ⟨_, d, by omega, h, ?_⟩
  rcases hout with rfl | rfl
  · exact boundary_good_tail _ n ht
  · exact boundary_good_tail _ n ht

/-- The fueled phase is preserved while its left-block rank decreases. -/
theorem fueled_cycle (a b n : Nat) (marker t : List Bool)
    (hm : marker = firstMarker ∨ marker = secondMarker) (ht : GoodTail t) :
    ∃ d, run (18*b+47) (phase (back (a+1) marker) b (6*(a+1)+n+7) t) = some d ∧
      Fueled d := by
  refine ⟨phase (back a marker) (b+3) (6*a+n+7) t, ?_, ?_⟩
  · have h := residual_cycle (back a marker) t b (6*a+n+6)
    rw [show 6*a+n+6+7 = 6*(a+1)+n+7 by omega,
      show 6*a+n+6+1 = 6*a+n+7 by omega] at h
    exact h
  · exact ⟨marker,a,b+3,n,t,hm,ht,rfl⟩

/-- Both formerly unrestricted defect predicates now have a sound guarded version. -/
theorem guarded_defect_progress (marker : List Bool)
    (hm : marker = firstMarker ∨ marker = secondMarker) (k n : Nat)
    (t : List Bool) (ht : GoodTail t) :
    Progress ⟨.E, back k marker, true :: false :: ones (6*k+n+5) t⟩ := by
  cases k with
  | zero =>
      simp only [Nat.mul_zero, Nat.zero_add]
      rcases hm with rfl | rfl
      · have h := first_zero_long (ones n t)
        rw [ones_add, show 5+n = n+5 by omega] at h
        exact ⟨34, _, by decide, h, boundary_good_tail 3 n ht⟩
      · have h := second_zero_long (ones n t)
        rw [ones_add, show 5+n = n+5 by omega] at h
        exact ⟨31, _, by decide, h, boundary_good_tail 2 n ht⟩
  | succ k =>
      have h := defect_strip_block_param (back k marker) t (6*k+n+6)
      have hp : Fueled (phase (back k marker) 2 (6*k+n+7) t) :=
        ⟨marker,k,2,n,t,hm,ht,rfl⟩
      have hr := progress_prepend h (fueled_progress hp)
      rw [show 6*k+n+6+5 = 6*(k+1)+n+5 by omega] at hr
      exact hr

/-- The residual counterexample is excluded by the proved arithmetic guard. -/
theorem bad_residual_not_fueled :
    ¬ Fueled (BB6Interop.AppC8ResidualTape.residual firstMarker 0 0 [4,4,1]) := by
  intro h
  exact BB6Interop.AppC8ResidualTape.residual_bad_no_return (fueled_progress h)

def GuardedDefect (marker : List Bool) (c : Cfg) : Prop :=
  ∃ k n t, GoodTail t ∧ c = ⟨.E, back k marker, true :: false :: ones (6*k+n+5) t⟩

theorem first_bad_excluded : ¬ GuardedDefect firstMarker BB6Interop.AppC8ResidualTape.badFirst := by
  rintro ⟨k,n,t,ht,h⟩
  have hp := guarded_defect_progress firstMarker (Or.inl rfl) k n t ht
  rw [← h] at hp
  exact BB6Interop.AppC8ResidualTape.no_progress_of_trace
    BB6Interop.AppC8ResidualTape.first_bad_avoids hp

theorem second_bad_excluded : ¬ GuardedDefect secondMarker BB6Interop.AppC8ResidualTape.badSecond := by
  rintro ⟨k,n,t,ht,h⟩
  have hp := guarded_defect_progress secondMarker (Or.inr rfl) k n t ht
  rw [← h] at hp
  exact BB6Interop.AppC8ResidualTape.no_progress_of_trace
    BB6Interop.AppC8ResidualTape.second_bad_avoids hp

set_option maxHeartbeats 2000000 in
-- Kernel reduction checks the finite 2237-step blank bridge.
theorem blank_fueled_boundary :
    run 2237 blankCfg = some (runListCfg 5 0 [43]) := by decide

theorem blank_fueled_entry :
    run 2286 blankCfg = some (phase (back 4 firstMarker) 2 40 []) := by
  have h := run_comp blank_fueled_boundary (run_list_one_long_local 4 39 [])
  exact h

theorem blank_fueled_member : Fueled (phase (back 4 firstMarker) 2 40 []) :=
  ⟨firstMarker,4,2,9,[],Or.inl rfl,Or.inl rfl,rfl⟩

end BB6Interop.AppC8Restricted
