import BB6Interop.AppC8GeneratedSuffix

namespace BB6Interop.AppC8TerminalGrammar
open CryptidSolvePhase4 CryptidSolvePhase4.AppC8Raw
open BB6Interop.AppC8RunLists BB6Interop.AppC8Restricted

theorem blank_terminal_104 :
    run 43249784536155046 blankCfg = some (runListCfg 89494214 0 [103]) := by
  have hs := terminal_44_to_104 89494214
  norm_num only at hs
  have h := run_comp blank_restricted_frontier hs
  norm_num only at h
  exact h

theorem blank_terminal_239 :
    run 43249785610113378 blankCfg = some (runListCfg 89494171 0 [238]) := by
  have hs := terminal_104_to_239 89494171
  norm_num only at hs
  have h := run_comp blank_terminal_104 hs
  norm_num only at h
  exact h

theorem blank_emitted_359 :
    run 43249786326110803 blankCfg = some (runListCfg 0 0 [268482394,358,1]) := by
  have hs := terminal_odd_boundary 89494131 39
  norm_num only at hs
  have h := run_comp blank_terminal_239 hs
  norm_num only at h
  exact h

theorem blank_paired_359 :
    run 43249786326110840 blankCfg = some (runListCfg 3 268482390 [358,1]) := by
  have hs := run_list_zero_long 268482390 [358,1]
  norm_num only at hs
  have h := run_comp blank_emitted_359 hs
  norm_num only at h
  exact h

theorem blank_generated_frontier :
    run 97311884181777598 blankCfg = some (runListCfg 134241197 2 [358,1]) := by
  have hs := tail_shuttle_rounds 67120597 3 268482391 (suffix [358,1]) (by decide)
  norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
  have h := run_comp blank_paired_359 hs
  norm_num only at h
  exact h

theorem generated_frontier_member : GeneratedBoundary (runListCfg 134241197 2 [358,1]) :=
  ⟨134241197,2,[358,1],.paired 134241197 2 39,rfl⟩

theorem blank_generated_prefix (j : Nat) (hj : j ≤ 97311884181777598) :
    ∃ d, run j blankCfg = some d := run_prefix_defined blank_generated_frontier j hj

theorem upstream_generated_frontier :
    BusyBeaver.ReachesIn BB6Interop.AppC8.machine 97311884181777598 (BusyBeaver.init [])
      (BB6Interop.AppC8.encode (runListCfg 134241197 2 [358,1])) :=
  BB6Interop.AppC8.blank_reaches_in blank_generated_frontier

end BB6Interop.AppC8TerminalGrammar
