import BB6Interop.AppC8TerminalGrammar

namespace BB6Interop.AppC8TerminalGrammar
open CryptidSolvePhase4 CryptidSolvePhase4.AppC8Raw
open BB6Interop.AppC8Continuation BB6Interop.AppC8RunLists BB6Interop.AppC8Restricted
open BB6Interop.AppC8ResidualTape
set_option maxRecDepth 20000

/-- Arithmetic suffix grammar. Indices encode run lengths minus one.
Terminal runs remain in the one-one phase; emitted prefixes require zero blocks. -/
inductive GeneratedCode : Nat → Nat → List Nat → Prop where
  | pure (k m : Nat) : GeneratedCode k m []
  | seed (k m : Nat) : GeneratedCode k m [1]
  | terminal (k q : Nat) : GeneratedCode k 0 [3*q+1]
  | paired (k m q : Nat) : GeneratedCode k m [9*q+7,1]
  | emitOne (a : Nat) : GeneratedCode 0 0 [3*a+1,1]
  | emitPair (a q : Nat) : GeneratedCode 0 0 [3*a+1,9*q+7,1]

def GeneratedBoundary (c : Cfg) : Prop :=
  ∃ k m ns, GeneratedCode k m ns ∧ c = runListCfg k m ns

def GProgress (c : Cfg) : Prop :=
  ∃ t d, 0 < t ∧ run t c = some d ∧ GeneratedBoundary d

theorem gprepend {t : Nat} {c d : Cfg} (h : run t c = some d) (hd : GProgress d) : GProgress c := by
  obtain ⟨u,e,hu,he,hg⟩ := hd
  exact ⟨t+u,e,by omega,run_comp h he,hg⟩

theorem old_code_generated {k m : Nat} {ns : List Nat} (h : Admissible k m ns) : GeneratedCode k m ns := by
  rcases h with h | ⟨rfl,h⟩ | ⟨rfl,rfl,a,tail,h,rfl⟩
  · rcases h with rfl | rfl | rfl | rfl
    · exact .pure k m
    · exact .seed k m
    · exact .paired k m 0
    · exact .paired k m 2
  · rcases h with rfl | rfl | rfl | rfl
    · exact .terminal k 1
    · exact .terminal k 5
    · exact .terminal k 14
    · exact .terminal k 22
  · rcases h with rfl | rfl | rfl
    · exact .emitOne a
    · exact .emitPair a 0
    · exact .emitPair a 2

theorem old_boundary_generated {c : Cfg} (h : RestrictedBoundary c) : GeneratedBoundary c := by
  obtain ⟨k,m,ns,hs,rfl⟩ := h
  exact ⟨k,m,ns,old_code_generated hs,rfl⟩

theorem core_generated {c : Cfg} (h : CoreBoundary c) : GeneratedBoundary c :=
  old_boundary_generated (core_is_restricted h)

/-- The small-budget branch returns to a pure boundary, for either marker. -/
theorem short_budget_return (marker : List Bool)
    (hm : marker = firstMarker ∨ marker = secondMarker) (k n : Nat) :
    GProgress ⟨.E,back k marker,true :: false :: ones (6*k+n+5) []⟩ := by
  cases k with
  | zero =>
      simp only [Nat.mul_zero,Nat.zero_add]
      rcases hm with rfl | rfl
      · have h := first_zero_long (ones n [])
        rw [ones_add,show 5+n=n+5 by omega] at h
        exact ⟨34,_,by decide,h,⟨3,n,[],.pure 3 n,rfl⟩⟩
      · have h := second_zero_long (ones n [])
        rw [ones_add,show 5+n=n+5 by omega] at h
        exact ⟨31,_,by decide,h,⟨2,n,[],.pure 2 n,rfl⟩⟩
  | succ k =>
      have h := defect_strip_block_param (back k marker) [] (6*k+n+6)
      obtain ⟨u,d,hu,hr,hd⟩ := restricted_fuel_return
        (show RestrictedFuel (phase (back k marker) 2 (6*k+n+7) []) from
          ⟨marker,k,2,n,[],hm,Or.inl rfl,rfl⟩)
      have hc := run_comp h hr
      rw [show 6*k+n+6+5=6*(k+1)+n+5 by omega] at hc
      exact ⟨_,d,by omega,hc,core_generated hd⟩

theorem odd_terminal_return (marker : List Bool)
    (hm : marker = firstMarker ∨ marker = secondMarker) (k q : Nat) :
    GProgress ⟨.E,back k marker,true :: false :: ones (6*q+5) []⟩ := by
  by_cases hk : k ≤ q
  · have h := short_budget_return marker hm k (6*(q-k))
    rw [show 6*k+6*(q-k)+5=6*q+5 by omega] at h
    exact h
  · let a := k-q-1
    have ha : a+q+1=k := by dsimp [a]; omega
    rcases hm with rfl | rfl
    · have h := first_odd_return a q
      rw [ha] at h
      exact ⟨_,_,by omega,h,⟨0,0,_,.emitPair a q,rfl⟩⟩
    · have h := second_odd_return a q
      rw [ha] at h
      exact ⟨_,_,by omega,h,⟨0,3*a+3,_,.paired 0 (3*a+3) q,rfl⟩⟩

theorem second_even_generated (k q : Nat) :
    GProgress ⟨.E,back k secondMarker,true :: false :: ones (6*q+2) []⟩ := by
  by_cases hk : k < q
  · have h := short_budget_return secondMarker (Or.inr rfl) k (6*(q-k)-3)
    rw [show 6*k+(6*(q-k)-3)+5=6*q+2 by omega] at h
    exact h
  · let a := k-q
    have ha : a+q=k := by dsimp [a]; omega
    have h := second_even_return a q
    rw [ha,show 9*q+5=3*(3*q+1)+2 by omega] at h
    exact ⟨_,_,by omega,h,⟨a,0,[3*(3*q+1)+1],.terminal a (3*q+1),rfl⟩⟩

/-- Every single terminal run congruent to two modulo three returns within the grammar. -/
theorem second_terminal_generated (k r : Nat) :
    GProgress ⟨.E,back k secondMarker,true :: false :: ones (3*r+2) []⟩ := by
  by_cases he : r%2=0
  · have h := second_even_generated k (r/2)
    rw [show 6*(r/2)+2=3*r+2 by omega] at h
    exact h
  · have h := odd_terminal_return secondMarker (Or.inr rfl) k (r/2)
    rw [show 6*(r/2)+5=3*r+2 by omega] at h
    exact h

theorem first_even_generated (k q : Nat) :
    GProgress ⟨.E,back k firstMarker,true :: false :: ones (6*q+2) []⟩ := by
  by_cases hk : k < q
  · have h := short_budget_return firstMarker (Or.inl rfl) k (6*(q-k)-3)
    rw [show 6*k+(6*(q-k)-3)+5=6*q+2 by omega] at h
    exact h
  · let a := k-q
    have ha : a+q=k := by dsimp [a]; omega
    have h := first_even_bridge a q
    rw [ha,show 9*q+5=3*(3*q+1)+2 by omega] at h
    exact gprepend h (second_terminal_generated a (3*q+1))

theorem first_terminal_generated (k r : Nat) :
    GProgress ⟨.E,back k firstMarker,true :: false :: ones (3*r+2) []⟩ := by
  by_cases he : r%2=0
  · have h := first_even_generated k (r/2)
    rw [show 6*(r/2)+2=3*r+2 by omega] at h
    exact h
  · have h := odd_terminal_return firstMarker (Or.inl rfl) k (r/2)
    rw [show 6*(r/2)+5=3*r+2 by omega] at h
    exact h

theorem terminal_boundary_generated (k r : Nat) :
    GProgress (runListCfg k 0 [3*r+1]) := by
  have h := run_comp (entry (blocks k (true :: false :: ones (3*r+2) [])))
    (scan_right k firstMarker (true :: false :: ones (3*r+2) []))
  exact gprepend h (first_terminal_generated k r)

theorem generated_length {k m : Nat} {ns : List Nat} (h : GeneratedCode k m ns) : ns.length ≤ 3 := by
  cases h <;> simp

/-- The generated language still excludes the old halting boundary tape. -/
theorem short_bad_not_generated : ¬ GeneratedBoundary shortBadBoundary := by
  rintro ⟨k,m,ns,hgood,hcfg⟩
  have hk : k ≤ 1 := by
    cases k with
    | zero => omega
    | succ k =>
        cases k with
        | zero => omega
        | succ k =>
            have h := congrArg Cfg.right hcfg
            simp [shortBadBoundary,runListCfg,shuttleTailCfg,blocks,ones,suffix] at h
  have hc := congrArg (fun c : Cfg => c.right.count false) hcfg
  rw [run_list_zero_count] at hc
  change 7=2+k+ns.length at hc
  have hl := generated_length hgood
  omega

theorem generated_is_boundary {c : Cfg} (h : GeneratedBoundary c) : Boundary c := by
  obtain ⟨k,m,ns,hs,rfl⟩ := h
  exact run_list_boundary k m ns

theorem pure_generated (k m : Nat) : GProgress (runListCfg k m []) := by
  rcases m with _ | _ | _ | _ | m
  · exact ⟨8*k+17,_,by omega,one_collapse k,⟨0,0,_,.emitOne k,rfl⟩⟩
  · have h := run_comp (appC8_raw_exit k) (appC8_raw_reset k)
    exact ⟨_,_,by omega,h,⟨3,3*k,[],.pure 3 (3*k),rfl⟩⟩
  · exact ⟨14*k+36,_,by omega,appC8_odd_collapse k,⟨0,3*k+6,[1],.seed 0 (3*k+6),rfl⟩⟩
  · exact ⟨14*k+36,_,by omega,four_collapse k,⟨0,3*k+9,[],.pure 0 (3*k+9),rfl⟩⟩
  · exact ⟨12*k+26,_,by omega,run_list_shuttle k m [],⟨k+2,m,[],.pure (k+2) m,rfl⟩⟩

theorem seed_generated (k m : Nat) : GProgress (runListCfg k m [1]) := by
  rcases m with _ | _ | _ | _ | m
  · exact terminal_boundary_generated k 0
  · rw [run_list_absorb]
    exact pure_generated (k+1) 1
  · exact ⟨12*k+40,_,by omega,three_with_tail k,⟨k+1,0,[4],.terminal (k+1) 1,rfl⟩⟩
  · exact ⟨14*k+44,_,by omega,appC8_odd_terminal k,⟨0,3*k+12,[],.pure 0 (3*k+12),rfl⟩⟩
  · exact ⟨12*k+26,_,by omega,run_list_shuttle k m [1],⟨k+2,m,[1],.seed (k+2) m,rfl⟩⟩

/-- A short emitted prefix can be removed without inspecting the remainder. -/
theorem short_emitted_local (n : Nat) (t : List Bool) :
    run 49 (shuttleTailCfg 0 1 (false :: ones 2 (false :: ones (n+5) t))) =
      some (shuttleTailCfg 4 (n+1) t) := by rfl

theorem emitted_one_generated (a : Nat) : GProgress (runListCfg 0 0 [3*a+1,1]) := by
  cases a with
  | zero =>
      have h : run 65 (runListCfg 0 0 [1,1]) = some (runListCfg 2 3 []) := by decide
      exact ⟨65,_,by decide,h,⟨2,3,[],.pure 2 3,rfl⟩⟩
  | succ a =>
      have h := run_list_zero_long (3*a) [1]
      rw [show 3*a+4=3*(a+1)+1 by omega] at h
      exact ⟨37,_,by decide,h,⟨3,3*a,[1],.seed 3 (3*a),rfl⟩⟩

theorem emitted_pair_generated (a q : Nat) : GProgress (runListCfg 0 0 [3*a+1,9*q+7,1]) := by
  cases a with
  | zero =>
      have h := short_emitted_local (9*q+3) [false,true,true]
      rw [show 9*q+3+5=9*q+8 by omega] at h
      exact ⟨49,_,by decide,h,⟨4,9*q+3,[1],.seed 4 (9*q+3),rfl⟩⟩
  | succ a =>
      have h := run_list_zero_long (3*a) [9*q+7,1]
      rw [show 3*a+4=3*(a+1)+1 by omega] at h
      exact ⟨37,_,by decide,h,⟨3,3*a,_,.paired 3 (3*a) q,rfl⟩⟩

/-- Only these two paired-suffix branches remain in the grammar reduction. -/
def PairedOneReturn : Prop := ∀ k q, GProgress (runListCfg k 0 [9*q+7,1])
def PairedThreeReturn : Prop := ∀ k q, GProgress (runListCfg k 2 [9*q+7,1])

theorem paired_generated (h1 : PairedOneReturn) (h3 : PairedThreeReturn)
    (k m q : Nat) : GProgress (runListCfg k m [9*q+7,1]) := by
  rcases m with _ | _ | _ | _ | m
  · exact h1 k q
  · rw [run_list_absorb]
    exact seed_generated (k+1) (9*q+7)
  · exact h3 k q
  · have h := run_list_four_long k (9*q+5) [1]
    rw [show 9*q+5+2=9*q+7 by omega] at h
    exact ⟨12*k+32,_,by omega,h,⟨k+3,9*q+5,[1],.seed (k+3) (9*q+5),rfl⟩⟩
  · exact ⟨12*k+26,_,by omega,run_list_shuttle k m [9*q+7,1],
      ⟨k+2,m,_,.paired (k+2) m q,rfl⟩⟩

theorem generated_boundary_return (h1 : PairedOneReturn) (h3 : PairedThreeReturn)
    {c : Cfg} (hc : GeneratedBoundary c) : GProgress c := by
  obtain ⟨k,m,ns,hg,rfl⟩ := hc
  cases hg with
  | pure k m => exact pure_generated k m
  | seed k m => exact seed_generated k m
  | terminal k q => exact terminal_boundary_generated k q
  | paired k m q => exact paired_generated h1 h3 k m q
  | emitOne a => exact emitted_one_generated a
  | emitPair a q => exact emitted_pair_generated a q

def GeneratedCore (ns : List Nat) : Prop := ns=[] ∨ ns=[1] ∨ ∃ q, ns=[9*q+7,1]

def GeneratedFuel (c : Cfg) : Prop :=
  ∃ marker a b n ns, (marker=firstMarker ∨ marker=secondMarker) ∧ GeneratedCore ns ∧
    c=phase (back a marker) b (6*a+n+7) (suffix ns)

def GeneratedCandidate (c : Cfg) : Prop := GeneratedBoundary c ∨ GeneratedFuel c ∨ TerminalResidual c

theorem generated_core_code {ns : List Nat} (h : GeneratedCore ns) (k m : Nat) : GeneratedCode k m ns := by
  rcases h with rfl | rfl | ⟨q,rfl⟩
  · exact .pure k m
  · exact .seed k m
  · exact .paired k m q

theorem generated_fuel_return {c : Cfg} (hc : GeneratedFuel c) : GProgress c := by
  obtain ⟨marker,a,b,n,ns,hm,hs,rfl⟩ := hc
  obtain ⟨d,u,hu,hr,hout⟩ := marker_finish marker hm (b+3*a) n (suffix ns)
  have h := run_comp (residual_drain a b n marker (suffix ns)) hr
  refine ⟨_,d,by omega,h,?_⟩
  rcases hout with rfl | rfl
  · exact ⟨_,n,ns,generated_core_code hs _ n,rfl⟩
  · exact ⟨_,n,ns,generated_core_code hs _ n,rfl⟩

theorem terminal_residual_generated {c : Cfg} (hc : TerminalResidual c) : GProgress c := by
  obtain ⟨k,rfl | rfl⟩ := hc
  · exact ⟨5*k+36,_,by omega,residual_first_terminal k,⟨0,0,_,.emitPair k 0,rfl⟩⟩
  · exact ⟨5*k+38,_,by omega,residual_second_terminal k,⟨0,3*k+3,_,.paired 0 (3*k+3) 0,rfl⟩⟩

theorem old_candidate_generated {c : Cfg} (hc : Candidate c) : GeneratedCandidate c := by
  rcases hc with h | h | h
  · exact Or.inl (old_boundary_generated h)
  · obtain ⟨marker,a,b,n,ns,hm,hs,rfl⟩ := h
    refine Or.inr (Or.inl ⟨marker,a,b,n,ns,hm,?_,rfl⟩)
    rcases hs with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨0,rfl⟩)
    · exact Or.inr (Or.inr ⟨2,rfl⟩)
  · exact Or.inr (Or.inr h)

theorem generated_closure_of_paired (h1 : PairedOneReturn) (h3 : PairedThreeReturn) :
    MacroClosed GeneratedCandidate := by
  intro c hc
  have hg : GProgress c := by
    rcases hc with h | h | h
    · exact generated_boundary_return h1 h3 h
    · exact generated_fuel_return h
    · exact terminal_residual_generated h
  obtain ⟨t,d,ht,hr,hd⟩ := hg
  exact ⟨t,d,ht,hr,Or.inl hd⟩

theorem generated_entry : GeneratedCandidate (shuttleCfg 0 2) :=
  old_candidate_generated blank_candidate_entry.2

theorem blank_survives_of_paired (h1 : PairedOneReturn) (h3 : PairedThreeReturn) (j : Nat) :
    ∃ d, run j blankCfg = some d := by
  by_cases hj : j ≤ 5
  · exact run_prefix_defined appC8_blank_entry j hj
  · obtain ⟨d,hd⟩ := macro_closed_survives (generated_closure_of_paired h1 h3) (j-5) _ generated_entry
    have h := run_comp appC8_blank_entry hd
    rw [show 5+(j-5)=j by omega] at h
    exact ⟨d,h⟩

theorem short_bad_not_generated_candidate : ¬ GeneratedCandidate shortBadBoundary := by
  rintro (h | h | h)
  · exact short_bad_not_generated h
  · obtain ⟨marker,a,b,n,ns,hm,hs,he⟩ := h
    have hl := congrArg Cfg.left he
    exact back_marker_nonempty a marker hm hl.symm
  · exact terminal_left_nonempty h rfl

theorem bad_residual_not_generated_candidate :
    ¬ GeneratedCandidate (BB6Interop.AppC8ResidualTape.residual firstMarker 0 0 [4,4,1]) := by
  rintro (h | h | h)
  · obtain ⟨k,m,ns,hs,he⟩ := h
    have hl := congrArg Cfg.left he
    simp [BB6Interop.AppC8ResidualTape.residual,runListCfg,shuttleTailCfg,back,firstMarker] at hl
  · obtain ⟨t,d,ht,hr,hd⟩ := generated_fuel_return h
    exact residual_bad_no_return ⟨t,d,ht,hr,generated_is_boundary hd⟩
  · exact residual_bad_no_return (residual_phase_progress h)

theorem upstream_nonhalting_of_paired (h1 : PairedOneReturn) (h3 : PairedThreeReturn) :
    BusyBeaver.IsNotHalt BB6Interop.AppC8.machine := by
  intro c ⟨n,hn⟩
  obtain ⟨d,hd⟩ := blank_survives_of_paired h1 h3 (n+1)
  have hu := BB6Interop.AppC8.blank_reaches_in hd
  change BusyBeaver.multiStep BB6Interop.AppC8.machine (BusyBeaver.init []) (n+1) =
    some (BB6Interop.AppC8.encode d) at hu
  rw [BusyBeaver.multiStep_succ',hn,Option.bind_some] at hu
  rw [hu]
  rfl

end BB6Interop.AppC8TerminalGrammar
