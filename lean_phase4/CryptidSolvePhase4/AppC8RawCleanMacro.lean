import CryptidSolvePhase4.AppC8RawShuttle

/-! Raw clean-macro reset, exit, and composition for AppC 8.
All execution uses the literal table in AppC8RawShuttle; no macro rule is assumed.
-/
namespace CryptidSolvePhase4.AppC8Raw

def cleanCfg (c : Nat) : Cfg :=
  ⟨.E, back c [true, false, true], []⟩

theorem ones_add (a b : Nat) (t : List Bool) :
    ones a (ones b t) = ones (a+b) t := by
  induction a with
  | zero => simp [ones]
  | succ a ih => simp [ones, ih, Nat.succ_add]

theorem reset_triplet (l t : List Bool) :
    run 5 ⟨.A, true :: false :: false :: l, true :: t⟩ =
      some ⟨.A, l, ones 4 t⟩ := by rfl

theorem reset_scan (n : Nat) (l t : List Bool) :
    run (5*n) ⟨.A, back n l, true :: t⟩ =
      some ⟨.A, l, ones (3*n+1) t⟩ := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      have h := run_comp (reset_triplet (back n l) t) (ih (ones 3 t))
      rw [ones_add] at h
      rw [show 5*(n+1) = 5+5*n by omega]
      rw [show 3*n+1+3 = 3*(n+1)+1 by omega] at h
      exact h

theorem reset_entry (n : Nat) :
    run 5 (cleanCfg (n+1)) =
      some ⟨.A, back n [true, false, true], ones 4 []⟩ := by
  rfl

theorem reset_boundary (t : List Bool) :
    run 43 ⟨.A, [true, false, true], ones 4 t⟩ =
      some ⟨.A, [], false :: true :: false :: blocks 3 (true :: t)⟩ := by
  rfl

/-- Every positive carry count has a raw reset, including c=1. -/
theorem appC8_raw_reset (n : Nat) :
    run (5*(n+1)+43) (cleanCfg (n+1)) = some (shuttleCfg 3 (3*n+1)) := by
  have h1 := run_comp (reset_entry n) (reset_scan n [true, false, true] (ones 3 []))
  rw [ones_add] at h1
  have he : 3*n+1+3 = (3*n)+4 := by omega
  rw [he] at h1
  have h2 := run_comp h1 (reset_boundary (ones (3*n) []))
  rw [show 5*(n+1)+43 = 5+5*n+43 by omega]
  exact h2

theorem exit_boundary (l : List Bool) :
    run 3 ⟨.E, l, [true, true]⟩ =
      some ⟨.E, true :: false :: false :: l, []⟩ := by rfl

/-- Exit for every block count, including k=0. -/
theorem appC8_raw_exit (k : Nat) :
    run (3*k+6) (shuttleCfg k 2) = some (cleanCfg (k+1)) := by
  have h1 := run_comp (entry (blocks k [true, true]))
    (scan_right k [true, false, true] [true, true])
  have h2 := run_comp h1 (exit_boundary (back k [true, false, true]))
  rw [show 3*k+6 = 3+3*k+3 by omega]
  exact h2

theorem appC8_clean_reset_raw (q : Nat) :
    run (20*q+63) (cleanCfg (4*(q+1))) = some (shuttleCfg 3 (12*q+10)) := by
  have h := appC8_raw_reset (4*q+3)
  have hc : 4*q+3+1 = 4*(q+1) := by omega
  have ht : 5*(4*q+3+1)+43 = 20*q+63 := by omega
  have hm : 3*(4*q+3)+1 = 12*q+10 := by omega
  rw [ht, hc, hm] at h
  exact h

theorem appC8_clean_exit_raw (q : Nat) :
    run (18*q+27) (shuttleCfg (6*q+7) 2) = some (cleanCfg (6*q+8)) := by
  have h := appC8_raw_exit (6*q+7)
  have ht : 3*(6*q+7)+6 = 18*q+27 := by omega
  rw [ht] at h
  exact h

/-- Universal clean-sector execution; elapsed duration, not first-return minimality. -/
theorem appC8_clean_macro_raw (q : Nat) :
    run (108*q*q+332*q+238) (cleanCfg (4*(q+1))) =
      some (cleanCfg (6*q+8)) := by
  have h := run_comp (run_comp (appC8_clean_reset_raw q) (appC8_clean_middle_raw q))
    (appC8_clean_exit_raw q)
  rw [(appC8_clean_macro_law q).1] at h
  exact h

theorem appC8_clean_macro_survives (q j : Nat) (hj : j ≤ 108*q*q+332*q+238) :
    ∃ e, run j (cleanCfg (4*(q+1))) = some e :=
  run_prefix_defined (appC8_clean_macro_raw q) j hj

/-- Connect the arithmetic ghost identity to the proved raw transition. -/
theorem appC8_clean_macro_raw_and_ghost (q : Nat) :
    run (108*q*q+332*q+238) (cleanCfg (4*(q+1))) = some (cleanCfg (6*q+8)) ∧
      2*((6*q+8)+4) = 3*((4*(q+1))+4) :=
  ⟨appC8_clean_macro_raw q, (appC8_clean_macro_law q).2⟩

end CryptidSolvePhase4.AppC8Raw
