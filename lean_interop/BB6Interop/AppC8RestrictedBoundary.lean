import BB6Interop.AppC8Restricted

namespace BB6Interop.AppC8Restricted
set_option maxRecDepth 20000
open CryptidSolvePhase4 CryptidSolvePhase4.AppC8Raw
open BB6Interop.AppC8Continuation BB6Interop.AppC8RunLists
open BB6Interop.AppC8ResidualTape

/-- The core inactive tails observed in the certified and explored blank segments.
Indices are run lengths minus one: [], [2], [8,2], [26,2]. -/
def CoreSuffix (ns : List Nat) : Prop :=
  ns = [] ∨ ns = [1] ∨ ns = [7,1] ∨ ns = [25,1]

def Admissible (k m : Nat) (ns : List Nat) : Prop :=
  CoreSuffix ns ∨
  (m = 0 ∧ (ns = [4] ∨ ns = [16] ∨ ns = [43] ∨ ns = [67])) ∨
  (k = 0 ∧ m = 0 ∧ ∃ a tail,
    (tail = [1] ∨ tail = [7,1] ∨ tail = [25,1]) ∧ ns = (3*a+1) :: tail)

def CoreBoundary (c : Cfg) : Prop :=
  ∃ k m ns, CoreSuffix ns ∧ c = runListCfg k m ns

def RestrictedBoundary (c : Cfg) : Prop :=
  ∃ k m ns, Admissible k m ns ∧ c = runListCfg k m ns

def RestrictedFuel (c : Cfg) : Prop :=
  ∃ marker a b n ns, (marker = firstMarker ∨ marker = secondMarker) ∧ CoreSuffix ns ∧
    c = phase (back a marker) b (6*a+n+7) (suffix ns)

def TerminalResidual (c : Cfg) : Prop :=
  ∃ k, c = residual firstMarker k 0 [] ∨ c = residual secondMarker k 0 []

/-- A candidate, not an assertion that all successors stay in this domain. -/
def Candidate (c : Cfg) : Prop :=
  RestrictedBoundary c ∨ RestrictedFuel c ∨ TerminalResidual c

theorem suffix_good (ns : List Nat) : GoodTail (suffix ns) := by
  cases ns with
  | nil => exact Or.inl rfl
  | cons n ns => exact Or.inr ⟨_, positive_run_list n ns, rfl⟩

theorem restricted_fuel_is_fueled {c : Cfg} (hc : RestrictedFuel c) : Fueled c := by
  obtain ⟨marker,a,b,n,ns,hm,hs,rfl⟩ := hc
  exact ⟨marker,a,b,n,suffix ns,hm,suffix_good ns,rfl⟩

theorem restricted_fuel_return {c : Cfg} (hc : RestrictedFuel c) :
    ∃ t d, 0 < t ∧ run t c = some d ∧ CoreBoundary d := by
  obtain ⟨marker,a,b,n,ns,hm,hs,rfl⟩ := hc
  obtain ⟨d,u,hu,hr,hout⟩ := marker_finish marker hm (b+3*a) n (suffix ns)
  have h := run_comp (residual_drain a b n marker (suffix ns)) hr
  refine ⟨_, d, by omega, h, ?_⟩
  rcases hout with rfl | rfl
  · exact ⟨_,n,ns,hs,rfl⟩
  · exact ⟨_,n,ns,hs,rfl⟩

theorem core_is_restricted {c : Cfg} (h : CoreBoundary c) : RestrictedBoundary c := by
  obtain ⟨k,m,ns,hs,rfl⟩ := h
  exact ⟨k,m,ns,Or.inl hs,rfl⟩

theorem restricted_fuel_cycle (a b n : Nat) (marker : List Bool) (ns : List Nat)
    (hm : marker = firstMarker ∨ marker = secondMarker) (hs : CoreSuffix ns) :
    ∃ d, run (18*b+47) (phase (back (a+1) marker) b (6*(a+1)+n+7) (suffix ns)) = some d ∧
      RestrictedFuel d := by
  refine ⟨phase (back a marker) (b+3) (6*a+n+7) (suffix ns), ?_, ?_⟩
  · have h := residual_cycle (back a marker) (suffix ns) b (6*a+n+6)
    rw [show 6*a+n+6+7 = 6*(a+1)+n+7 by omega,
      show 6*a+n+6+1 = 6*a+n+7 by omega] at h
    exact h
  · exact ⟨marker,a,b+3,n,ns,hm,hs,rfl⟩

theorem core_shuttle (k m : Nat) (ns : List Nat) (hs : CoreSuffix ns) :
    run (12*k+26) (runListCfg k (m+4) ns) = some (runListCfg (k+2) m ns) ∧
      CoreBoundary (runListCfg (k+2) m ns) :=
  ⟨run_list_shuttle k m ns, k+2,m,ns,hs,rfl⟩

theorem core_pure_one (k : Nat) :
    run (8*k+17) (shuttleCfg k 1) = some (runListCfg 0 0 [3*k+1,1]) ∧
      RestrictedBoundary (runListCfg 0 0 [3*k+1,1]) :=
  ⟨one_collapse k, 0,0,[3*k+1,1],
    Or.inr (Or.inr ⟨rfl,rfl,k,[1],Or.inl rfl,rfl⟩),rfl⟩

theorem emitted_to_core (n : Nat) (ns : List Nat) (hs : CoreSuffix ns) :
    run 37 (runListCfg 0 0 ((n+4)::ns)) = some (runListCfg 3 n ns) ∧
      CoreBoundary (runListCfg 3 n ns) :=
  ⟨run_list_zero_long n ns,3,n,ns,hs,rfl⟩

theorem ones_zero_count (n : Nat) (t : List Bool) : (ones n t).count false = t.count false := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [ones] using ih

theorem blocks_zero_count (n : Nat) (t : List Bool) :
    (blocks n t).count false = n + t.count false := by
  induction n with
  | zero => simp [blocks]
  | succ n ih => simp [blocks, ih]; omega

theorem suffix_zero_count (ns : List Nat) : (suffix ns).count false = ns.length := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp [suffix, ones_zero_count, ih]

theorem run_list_zero_count (k m : Nat) (ns : List Nat) :
    (runListCfg k m ns).right.count false = 2+k+ns.length := by
  simp [runListCfg, shuttleTailCfg, blocks_zero_count, ones_zero_count, suffix_zero_count]
  omega

theorem admissible_length {k m : Nat} {ns : List Nat} (h : Admissible k m ns) : ns.length ≤ 3 := by
  rcases h with h | ⟨hm,h⟩ | ⟨hk,hm,a,tail,h,rfl⟩
  · rcases h with rfl | rfl | rfl | rfl <;> decide
  · rcases h with rfl | rfl | rfl | rfl <;> decide
  · rcases h with rfl | rfl | rfl <;> simp

/-- Physical tape exclusion, not merely rejection of one possible code. -/
theorem short_bad_not_restricted : ¬ RestrictedBoundary shortBadBoundary := by
  rintro ⟨k,m,ns,hgood,hcfg⟩
  have hk : k ≤ 1 := by
    cases k with
    | zero => omega
    | succ k =>
        cases k with
        | zero => omega
        | succ k =>
            have h := congrArg Cfg.right hcfg
            simp [shortBadBoundary, runListCfg, shuttleTailCfg, blocks, ones, suffix] at h
  have hc := congrArg (fun c : Cfg => c.right.count false) hcfg
  rw [run_list_zero_count] at hc
  change 7 = 2+k+ns.length at hc
  have hl := admissible_length hgood
  omega

theorem blank_candidate_entry : run 5 blankCfg = some (shuttleCfg 0 2) ∧
    Candidate (shuttleCfg 0 2) :=
  ⟨appC8_blank_entry, Or.inl ⟨0,1,[],Or.inl (Or.inl rfl),rfl⟩⟩

theorem actual_restricted_fuel : RestrictedFuel (phase (back 4 firstMarker) 2 40 []) :=
  ⟨firstMarker,4,2,9,[],Or.inl rfl,Or.inl rfl,rfl⟩

theorem bad_residual_not_restricted_fuel :
    ¬ RestrictedFuel (residual firstMarker 0 0 [4,4,1]) :=
  fun h => bad_residual_not_fueled (restricted_fuel_is_fueled h)

theorem back_marker_nonempty (a : Nat) (marker : List Bool)
    (hm : marker = firstMarker ∨ marker = secondMarker) : back a marker ≠ [] := by
  cases a <;> rcases hm with rfl | rfl <;> simp [back, firstMarker, secondMarker]

theorem restricted_fuel_left_nonempty {c : Cfg} (h : RestrictedFuel c) : c.left ≠ [] := by
  obtain ⟨marker,a,b,n,ns,hm,hs,rfl⟩ := h
  exact back_marker_nonempty a marker hm

theorem terminal_left_nonempty {c : Cfg} (h : TerminalResidual c) : c.left ≠ [] := by
  obtain ⟨k,rfl | rfl⟩ := h
  · exact back_marker_nonempty k firstMarker (Or.inl rfl)
  · exact back_marker_nonempty k secondMarker (Or.inr rfl)

theorem short_bad_not_candidate : ¬ Candidate shortBadBoundary := by
  rintro (h | h | h)
  · exact short_bad_not_restricted h
  · exact restricted_fuel_left_nonempty h rfl
  · exact terminal_left_nonempty h rfl

theorem bad_residual_not_candidate : ¬ Candidate (residual firstMarker 0 0 [4,4,1]) := by
  rintro (h | h | h)
  · obtain ⟨k,m,ns,hs,he⟩ := h
    have hh := congrArg Cfg.left he
    simp [BB6Interop.AppC8ResidualTape.residual, runListCfg, shuttleTailCfg, back, firstMarker] at hh
  · exact bad_residual_not_restricted_fuel h
  · exact residual_bad_no_return (residual_phase_progress h)

theorem terminal_return_candidate {c : Cfg} (hc : TerminalResidual c) :
    ∃ t d, 0 < t ∧ run t c = some d ∧ Candidate d := by
  obtain ⟨k,rfl | rfl⟩ := hc
  · refine ⟨5*k+36,_,by omega,residual_first_terminal k,Or.inl ?_⟩
    exact ⟨0,0,[3*k+1,7,1],Or.inr (Or.inr ⟨rfl,rfl,k,[7,1],Or.inr (Or.inl rfl),rfl⟩),rfl⟩
  · refine ⟨5*k+38,_,by omega,residual_second_terminal k,Or.inl ?_⟩
    exact ⟨0,3*k+3,[7,1],Or.inl (Or.inr (Or.inr (Or.inl rfl))),rfl⟩

theorem fueled_return_candidate {c : Cfg} (hc : RestrictedFuel c) :
    ∃ t d, 0 < t ∧ run t c = some d ∧ Candidate d := by
  obtain ⟨t,d,ht,hr,hd⟩ := restricted_fuel_return hc
  exact ⟨t,d,ht,hr,Or.inl (core_is_restricted hd)⟩

/-- The next large blank frontier has a uniform return with a correlated terminal tail. -/
theorem three_eight (k : Nat) :
    run (12*(k+2)+116) (shuttleTailCfg (k+2) 3 (defectTail 8)) =
      some (shuttleTailCfg (k+2) 1 (false :: ones 17 [])) := by
  have h1 := run_comp (odd_half (k+2) (defectTail 8))
    (scan_right (k+3) secondMarker (true :: defectTail 8))
  have ht := defect_turn_104 (back k secondMarker)
  rw [back_read] at ht
  have h2 := run_comp h1 ht
  have h3 := run_comp h2 (scan_left k [false]
    (true :: false :: true :: true :: false :: true :: false :: ones 17 []))
  have h4 := run_comp h3 (final_boundary (returnWord k
    (true :: false :: true :: true :: false :: true :: false :: ones 17 [])))
  change run _ _ = some ⟨.A, [], false :: true :: false ::
    (true :: returnWord k (true :: false :: true :: true :: false :: true :: false :: ones 17 []))⟩ at h4
  rw [return_close_prefix] at h4
  change run _ _ = some ⟨.A, [], false :: true :: false ::
    blocks k (blocks 2 (true :: false :: ones 17 []))⟩ at h4
  rw [blocks_add, show 6*(k+2)+12+3*(k+3)+104+3*k+3 = 12*(k+2)+116 by omega] at h4
  exact h4

theorem seventeen_collapse (k : Nat) :
    run (8*(k+4)+323) (shuttleTailCfg (k+4) 1 (false :: ones 17 [])) =
      some (runListCfg 0 0 [3*k+4,25,1]) := by
  have h1 := run_comp (entry (blocks (k+4) (true :: false :: ones 17 [])))
    (scan_right (k+4) firstMarker (true :: false :: ones 17 []))
  have h2 := run_comp h1 (defect_turn_334 (back k firstMarker))
  have h3 := run_comp h2 (reset_scan k firstMarker (ones 3 (defectTail 26)))
  have h4 := run_comp h3 (one_left_boundary (ones (3*k) (ones 3 (defectTail 26))))
  unfold shuttleTailCfg at h4
  rw [ones_add, ones_add, show 2+3*k+3 = 3*k+5 by omega,
    show 3+3*(k+4)+334+5*k+6 = 8*(k+4)+323 by omega] at h4
  exact h4

/-- The missing global obligation is now stated on a genuinely smaller domain. -/
def CandidateClosure : Prop := MacroClosed Candidate

/-- Fixed local carry, uniformly in all unvisited left tape. -/
theorem defect_turn_641 (l : List Bool) :
    run 641 ⟨.E, back 6 l, true :: false :: ones 26 [false,true,true]⟩ =
      some ⟨.A, l.tail, CryptidSolvePhase4.AppC8Raw.read l :: true :: false :: true :: true :: false ::
        true :: false :: ones 44 []⟩ := by rfl

theorem three_twenty_six (k : Nat) :
    run (12*(k+5)+644) (shuttleTailCfg (k+5) 3 (defectTail 26)) =
      some (shuttleTailCfg (k+2) 1 (false :: ones 44 [])) := by
  have h1 := run_comp (odd_half (k+5) (defectTail 26))
    (scan_right (k+6) secondMarker (true :: defectTail 26))
  have ht := defect_turn_641 (back k secondMarker)
  rw [back_read] at ht
  have h2 := run_comp h1 ht
  have h3 := run_comp h2 (scan_left k [false]
    (true :: false :: true :: true :: false :: true :: false :: ones 44 []))
  have h4 := run_comp h3 (final_boundary (returnWord k
    (true :: false :: true :: true :: false :: true :: false :: ones 44 [])))
  change run _ _ = some ⟨.A, [], false :: true :: false ::
    (true :: returnWord k (true :: false :: true :: true :: false :: true :: false :: ones 44 []))⟩ at h4
  rw [return_close_prefix] at h4
  change run _ _ = some ⟨.A, [], false :: true :: false ::
    blocks k (blocks 2 (true :: false :: ones 44 []))⟩ at h4
  rw [blocks_add, show 6*(k+5)+12+3*(k+6)+641+3*k+3 = 12*(k+5)+644 by omega] at h4
  exact h4

theorem blank_survives_of_candidate_closure (hc : CandidateClosure) (j : Nat) :
    ∃ d, run j blankCfg = some d := by
  by_cases hj : j ≤ 5
  · exact run_prefix_defined appC8_blank_entry j hj
  · obtain ⟨d,hd⟩ := macro_closed_survives hc (j-5) _ blank_candidate_entry.2
    have h := run_comp appC8_blank_entry hd
    rw [show 5+(j-5)=j by omega] at h
    exact ⟨d,h⟩

end BB6Interop.AppC8Restricted
