import BB6Interop.AppC8RestrictedCheckpoints

/-! Generated terminal suffixes with explicit left-block budgets.
These are macro transitions and return results, not a global nonhalting proof. -/
namespace BB6Interop.AppC8TerminalGrammar
open CryptidSolvePhase4 CryptidSolvePhase4.AppC8Raw
open BB6Interop.AppC8Continuation BB6Interop.AppC8RunLists BB6Interop.AppC8Restricted
set_option maxRecDepth 20000

/-- The residual drain needs only a positive final run, not seven final ones. -/
theorem drain_positive (a b n : Nat) (l t : List Bool) :
    run (27*a*a+20*a+18*a*b) (phase (back a l) b (6*a+n+1) t) =
      some (phase l (b+3*a) (n+1) t) := by
  induction a generalizing b with
  | zero => simp [back, run]
  | succ a ih =>
      have h1 := residual_cycle (back a l) t b (6*a+n)
      have h := run_comp h1 (ih (b+3))
      rw [show b+3+3*a = b+3*(a+1) by omega,
        show 6*a+n+7 = 6*(a+1)+n+1 by omega] at h
      have ht : 18*b+47+(27*a*a+20*a+18*a*(b+3)) =
          27*(a+1)*(a+1)+20*(a+1)+18*(a+1)*b := by ring
      rw [ht] at h
      exact h

/-- Terminal residual with one active one, preserving arbitrary unvisited left tape. -/
theorem phase_one (b : Nat) (l : List Bool) :
    run (8*b+14) (phase l b 1 []) =
      some ⟨.A, l, true :: defectTail (3*b+2)⟩ := by
  have h1 := run_comp (entry_left l (blocks b [true]))
    (scan_right b (firstMarker ++ l) [true])
  have h2 := run_comp h1 (odd_turn (back b (firstMarker ++ l)))
  have h3 := run_comp h2 (reset_scan b (firstMarker ++ l) [false,true,true])
  have edge (t : List Bool) : run 3 ⟨.A, firstMarker ++ l, true :: t⟩ =
      some ⟨.A, l, true :: false :: ones 2 t⟩ := by rfl
  have h4 := run_comp h3 (edge (ones (3*b) [false,true,true]))
  rw [ones_add, show 2+3*b=3*b+2 by omega,
    show 3+3*b+8+5*b+3=8*b+14 by omega] at h4
  exact h4

/-- Four active ones expose the next left cell, with a generated terminal run. -/
theorem phase_four (b : Nat) (l : List Bool) :
    run (14*b+31) (phase l b 4 []) =
      some ⟨.A, l.tail, CryptidSolvePhase4.AppC8Raw.read l :: false :: ones (3*b+8) []⟩ := by
  have h1 := run_comp (entry_left l (blocks b (ones 4 [])))
    (scan_right b (firstMarker ++ l) (ones 4 []))
  have h2 := run_comp h1 (turn_and_return b (false :: true :: l) [true])
  have h3 := run_comp h2 (middle_left l (returnWord b [true,false,true,true]))
  rw [close_word] at h3
  have h4 := run_comp h3 (scan_right (b+1) (secondMarker ++ l) [true,true])
  have turn2 (l : List Bool) : run 8 ⟨.E,l,[true,true]⟩ = some ⟨.A,l,ones 4 []⟩ := by rfl
  have h5 := run_comp h4 (turn2 (back (b+1) (secondMarker ++ l)))
  have h6 := run_comp h5 (reset_scan (b+1) (secondMarker ++ l) (ones 3 []))
  have edge (t : List Bool) : run 3 ⟨.A, secondMarker ++ l, true :: t⟩ =
      some ⟨.A,l.tail,CryptidSolvePhase4.AppC8Raw.read l :: false :: ones 2 t⟩ := by rfl
  have h7 := run_comp h6 (edge (ones (3*(b+1)) (ones 3 [])))
  rw [ones_add,ones_add,show 2+3*(b+1)+3=3*b+8 by omega,
    show 3+3*b+(5+3*b)+4+3*(b+1)+8+5*(b+1)+3=14*b+31 by omega] at h7
  exact h7

/-- Universal even terminal carry, with its exact left-block budget. -/
theorem terminal_even_local (q : Nat) (l : List Bool) :
    run (27*q*q+44*q+19) ⟨.E,back q l,true :: false :: ones (6*q+2) []⟩ =
      some ⟨.A,l.tail,CryptidSolvePhase4.AppC8Raw.read l :: false :: ones (9*q+5) []⟩ := by
  cases q with
  | zero => exact defect_turn_19 l
  | succ q =>
      have h1 := defect_strip_block_param (back q l) [] (6*q+3)
      have h2 := run_comp h1 (drain_positive q 2 3 l [])
      have h3 := run_comp h2 (phase_four (2+3*q) l)
      rw [show 6*q+3+5=6*(q+1)+2 by omega,
        show 3*(2+3*q)+8=9*(q+1)+5 by omega] at h3
      have ht : 31+(27*q*q+20*q+18*q*2)+(14*(2+3*q)+31) =
          27*(q+1)*(q+1)+44*(q+1)+19 := by ring
      rw [ht] at h3
      exact h3

/-- Universal odd terminal carry, producing a paired suffix instead of a lone run. -/
theorem terminal_odd_local (q : Nat) (l : List Bool) :
    run (27*q*q+80*q+61) ⟨.E,back (q+1) l,true :: false :: ones (6*q+5) []⟩ =
      some ⟨.A,l,true :: defectTail (9*q+8)⟩ := by
  have h1 := defect_strip_block_param (back q l) [] (6*q)
  have h2 := run_comp h1 (drain_positive q 2 0 l [])
  have h3 := run_comp h2 (phase_one (2+3*q) l)
  rw [show 3*(2+3*q)+2=9*q+8 by omega] at h3
  have ht : 31+(27*q*q+20*q+18*q*2)+(8*(2+3*q)+14) = 27*q*q+80*q+61 := by ring
  rw [ht] at h3
  exact h3

theorem back_join (a b : Nat) (l : List Bool) : back a (back b l) = back (a+b) l := by
  induction a with
  | zero => simp [back]
  | succ a ih => simp [back, ih, Nat.succ_add]

/-- A first-marker even carry switches marker and preserves the remaining budget. -/
theorem first_even_bridge (k q : Nat) :
    run (27*q*q+44*q+19+6*k+4)
      ⟨.E,back (k+q) firstMarker,true :: false :: ones (6*q+2) []⟩ =
      some ⟨.E,back k secondMarker,true :: false :: ones (9*q+5) []⟩ := by
  have h1 := terminal_even_local q (back k firstMarker)
  rw [back_read,back_join,Nat.add_comm q k] at h1
  have h2 := run_comp h1 (scan_left k [false,true] (false :: ones (9*q+5) []))
  have h3 := run_comp h2 (middle_boundary (returnWord k (false :: ones (9*q+5) [])))
  rw [return_close_prefix] at h3
  have h4 := run_comp h3 (scan_right k secondMarker (true :: false :: ones (9*q+5) []))
  rw [show 27*q*q+44*q+19+3*k+4+3*k=27*q*q+44*q+19+6*k+4 by omega] at h4
  exact h4

theorem second_even_return (k q : Nat) :
    run (27*q*q+44*q+19+3*k+3)
      ⟨.E,back (k+q) secondMarker,true :: false :: ones (6*q+2) []⟩ =
      some (shuttleTailCfg k 1 (false :: ones (9*q+5) [])) := by
  have h1 := terminal_even_local q (back k secondMarker)
  rw [back_read,back_join,Nat.add_comm q k] at h1
  have h2 := run_comp h1 (scan_left k [false] (false :: ones (9*q+5) []))
  have h3 := run_comp h2 (final_boundary (returnWord k (false :: ones (9*q+5) [])))
  change run _ _ = some ⟨.A,[],false :: true :: false ::
    (true :: returnWord k (false :: ones (9*q+5) []))⟩ at h3
  rw [return_close_prefix] at h3
  exact h3

theorem first_odd_return (k q : Nat) :
    run (27*q*q+80*q+61+5*k+6)
      ⟨.E,back (k+q+1) firstMarker,true :: false :: ones (6*q+5) []⟩ =
      some (runListCfg 0 0 [3*k+1,9*q+7,1]) := by
  have h1 := terminal_odd_local q (back k firstMarker)
  rw [back_join,show q+1+k=k+q+1 by omega] at h1
  have h2 := run_comp h1 (reset_scan k firstMarker (defectTail (9*q+8)))
  have h3 := run_comp h2 (one_left_boundary (ones (3*k) (defectTail (9*q+8))))
  unfold shuttleTailCfg at h3
  rw [ones_add,show 2+3*k=3*k+2 by omega] at h3
  exact h3

theorem second_odd_return (k q : Nat) :
    run (27*q*q+80*q+61+5*k+8)
      ⟨.E,back (k+q+1) secondMarker,true :: false :: ones (6*q+5) []⟩ =
      some (runListCfg 0 (3*k+3) [9*q+7,1]) := by
  have h1 := terminal_odd_local q (back k secondMarker)
  rw [back_join,show q+1+k=k+q+1 by omega] at h1
  have h2 := run_comp h1 (reset_scan k secondMarker (defectTail (9*q+8)))
  exact run_comp h2 (odd_left_boundary (ones (3*k) (defectTail (9*q+8))))

/-- Uniform terminal-to-terminal production. Its budget decreases by 5s+3. -/
theorem terminal_double_even (k s : Nat) :
    run (12*k+351*s*s+685*s+336)
      (shuttleTailCfg (k+5*s+3) 1 (false :: ones (12*s+8) [])) =
      some (shuttleTailCfg k 1 (false :: ones (27*s+23) [])) := by
  have h1 := run_comp (entry (blocks (k+5*s+3) (true :: false :: ones (12*s+8) [])))
    (scan_right (k+5*s+3) firstMarker (true :: false :: ones (12*s+8) []))
  have hb := first_even_bridge (k+3*s+2) (2*s+1)
  rw [show k+3*s+2+(2*s+1)=k+5*s+3 by omega,
    show 6*(2*s+1)+2=12*s+8 by omega,
    show 9*(2*s+1)+5=6*(3*s+2)+2 by omega] at hb
  have h2 := run_comp h1 hb
  have he := second_even_return k (3*s+2)
  rw [show k+(3*s+2)=k+3*s+2 by omega,
    show 9*(3*s+2)+5=27*s+23 by omega] at he
  have h3 := run_comp h2 he
  have ht : 3+3*(k+5*s+3)+(27*(2*s+1)*(2*s+1)+44*(2*s+1)+19+6*(k+3*s+2)+4)+
      (27*(3*s+2)*(3*s+2)+44*(3*s+2)+19+3*k+3)=12*k+351*s*s+685*s+336 := by ring
  rw [ht] at h3
  exact h3

/-- The companion even production creates a paired suffix. -/
theorem terminal_even_odd (k s : Nat) :
    run (14*k+351*s*s+361*s+104)
      (shuttleTailCfg (k+5*s+1) 1 (false :: ones (12*s+2) [])) =
      some (runListCfg 0 (3*k+3) [27*s+7,1]) := by
  have h1 := run_comp (entry (blocks (k+5*s+1) (true :: false :: ones (12*s+2) [])))
    (scan_right (k+5*s+1) firstMarker (true :: false :: ones (12*s+2) []))
  have hb := first_even_bridge (k+3*s+1) (2*s)
  rw [show k+3*s+1+2*s=k+5*s+1 by omega,
    show 6*(2*s)+2=12*s+2 by omega,
    show 9*(2*s)+5=6*(3*s)+5 by omega] at hb
  have h2 := run_comp h1 hb
  have he := second_odd_return k (3*s)
  rw [show 9*(3*s)+7=27*s+7 by omega] at he
  have h3 := run_comp h2 he
  have ht : 3+3*(k+5*s+1)+(27*(2*s)*(2*s)+44*(2*s)+19+6*(k+3*s+1)+4)+
      (27*(3*s)*(3*s)+80*(3*s)+61+5*k+8)=14*k+351*s*s+361*s+104 := by ring
  rw [ht] at h3
  exact h3

theorem terminal_odd_boundary (k q : Nat) :
    run (8*k+27*q*q+83*q+73)
      (shuttleTailCfg (k+q+1) 1 (false :: ones (6*q+5) [])) =
      some (runListCfg 0 0 [3*k+1,9*q+7,1]) := by
  have h1 := run_comp (entry (blocks (k+q+1) (true :: false :: ones (6*q+5) [])))
    (scan_right (k+q+1) firstMarker (true :: false :: ones (6*q+5) []))
  have h := run_comp h1 (first_odd_return k q)
  have ht : 3+3*(k+q+1)+(27*q*q+80*q+61+5*k+6)=8*k+27*q*q+83*q+73 := by ring
  rw [ht] at h
  exact h

theorem terminal_44_to_104 (k : Nat) :
    run (12*k+5550) (shuttleTailCfg (k+18) 1 (false :: ones 44 [])) =
      some (shuttleTailCfg k 1 (false :: ones 104 [])) := by
  have h := terminal_double_even k 3
  convert h using 1

theorem terminal_104_to_239 (k : Nat) :
    run (12*k+28280) (shuttleTailCfg (k+43) 1 (false :: ones 104 [])) =
      some (shuttleTailCfg k 1 (false :: ones 239 [])) := by
  have h := terminal_double_even k 8
  convert h using 1

theorem double_even_budget_decreases (k s : Nat) : k < k+5*s+3 := by omega

end BB6Interop.AppC8TerminalGrammar
