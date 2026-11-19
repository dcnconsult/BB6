import BB6Interop.AppC8RestrictedBoundary

namespace BB6Interop.AppC8Restricted
open CryptidSolvePhase4 CryptidSolvePhase4.AppC8Raw
open BB6Interop.AppC8Continuation BB6Interop.AppC8RunLists
set_option maxRecDepth 20000

/-- Generated composition of proved macro laws, starting at the preceding certified carry. -/
theorem blank_restricted_frontier :
    run 43249783462218928 blankCfg = some (runListCfg 89494232 0 [43]) := by
  have h75 : run 1141826024678 blankCfg = some (runListCfg 3 1379511 []) := by
    have h := run_comp blank_clean_return (appC8_raw_reset 459837)
    norm_num only at h
    exact h
  have h76 : run 2569125010076 blankCfg = some (runListCfg 689757 3 []) := by
    have hs := tail_shuttle_rounds 344877 3 1379512 (suffix []) (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h75 hs
    norm_num only at h
    exact h
  have h77 : run 2569134666710 blankCfg = some (runListCfg 0 2069280 []) := by
    have hs := four_collapse 689757
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h76 hs
    norm_num only at h
    exact h
  have h78 : run 5780581697990 blankCfg = some (runListCfg 1034640 0 []) := by
    have hs := tail_shuttle_rounds 517320 0 2069281 (suffix []) (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h77 hs
    norm_num only at h
    exact h
  have h79 : run 5780589975127 blankCfg = some (runListCfg 0 0 [3103921,1]) := by
    have hs := one_collapse 1034640
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h78 hs
    norm_num only at h
    exact h
  have h80 : run 5780589975164 blankCfg = some (runListCfg 3 3103917 [1]) := by
    have hs := run_list_zero_long 3103917 [1]
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h79 hs
    norm_num only at h
    exact h
  have h81 : run 13006349675406 blankCfg = some (runListCfg 1551961 1 [1]) := by
    have hs := tail_shuttle_rounds 775979 3 3103918 (suffix [1]) (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h80 hs
    norm_num only at h
    exact h
  have h82 : run 13006349675406 blankCfg = some (runListCfg 1551962 1 []) := by
    have h := h81
    rw [run_list_absorb] at h
    exact h
  have h83 : run 13006362091156 blankCfg = some (runListCfg 3 4655886 []) := by
    have hs := run_comp (appC8_raw_exit 1551962) (appC8_raw_reset 1551962)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h82 hs
    norm_num only at h
    exact h
  have h84 : run 29264362155798 blankCfg = some (runListCfg 2327945 2 []) := by
    have hs := tail_shuttle_rounds 1163971 3 4655887 (suffix []) (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h83 hs
    norm_num only at h
    exact h
  have h85 : run 29264394747064 blankCfg = some (runListCfg 0 6983841 [1]) := by
    have hs := appC8_odd_collapse 2327945
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h84 hs
    norm_num only at h
    exact h
  have h86 : run 65844935049704 blankCfg = some (runListCfg 3491920 1 [1]) := by
    have hs := tail_shuttle_rounds 1745960 0 6983842 (suffix [1]) (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h85 hs
    norm_num only at h
    exact h
  have h87 : run 65844935049704 blankCfg = some (runListCfg 3491921 1 []) := by
    have h := h86
    rw [run_list_absorb] at h
    exact h
  have h88 : run 65844962985126 blankCfg = some (runListCfg 3 10475763 []) := by
    have hs := run_comp (appC8_raw_exit 3491921) (appC8_raw_reset 3491921)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h87 hs
    norm_num only at h
    exact h
  have h89 : run 148151254615326 blankCfg = some (runListCfg 5237883 3 []) := by
    have hs := tail_shuttle_rounds 2618940 3 10475764 (suffix []) (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h88 hs
    norm_num only at h
    exact h
  have h90 : run 148151327945724 blankCfg = some (runListCfg 0 15713658 []) := by
    have hs := four_collapse 5237883
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h89 hs
    norm_num only at h
    exact h
  have h91 : run 333340621608272 blankCfg = some (runListCfg 7856828 2 []) := by
    have hs := tail_shuttle_rounds 3928414 0 15713659 (suffix []) (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h90 hs
    norm_num only at h
    exact h
  have h92 : run 333340731603900 blankCfg = some (runListCfg 0 23570490 [1]) := by
    have hs := appC8_odd_collapse 7856828
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h91 hs
    norm_num only at h
    exact h
  have h93 : run 750016742519216 blankCfg = some (runListCfg 11785244 2 [1]) := by
    have hs := tail_shuttle_rounds 5892622 0 23570491 (suffix [1]) (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h92 hs
    norm_num only at h
    exact h
  have h94 : run 750016883942184 blankCfg = some (runListCfg 11785245 0 [4]) := by
    have hs := three_with_tail 11785244
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h93 hs
    norm_num only at h
    exact h
  have h95 : run 750016978224209 blankCfg = some (runListCfg 0 0 [35355733,7,1]) := by
    have hs := five_collapse 11785244
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h94 hs
    norm_num only at h
    exact h
  have h96 : run 750016978224246 blankCfg = some (runListCfg 3 35355729 [7,1]) := by
    have hs := run_list_zero_long 35355729 [7,1]
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h95 hs
    norm_num only at h
    exact h
  have h97 : run 1687538046978334 blankCfg = some (runListCfg 17677867 1 [7,1]) := by
    have hs := tail_shuttle_rounds 8838932 3 35355730 (suffix [7,1]) (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h96 hs
    norm_num only at h
    exact h
  have h98 : run 1687538046978334 blankCfg = some (runListCfg 17677868 7 [1]) := by
    have h := h97
    rw [run_list_absorb] at h
    exact h
  have h99 : run 1687538259112776 blankCfg = some (runListCfg 17677870 3 [1]) := by
    have hs := tail_shuttle_rounds 1 17677868 8 (suffix [1]) (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h98 hs
    norm_num only at h
    exact h
  have h100 : run 1687538506603000 blankCfg = some (runListCfg 0 53033622 []) := by
    have hs := appC8_odd_terminal 17677870
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h99 hs
    norm_num only at h
    exact h
  have h101 : run 3796962329948970 blankCfg = some (runListCfg 26516810 2 []) := by
    have hs := tail_shuttle_rounds 13258405 0 53033623 (suffix []) (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h100 hs
    norm_num only at h
    exact h
  have h102 : run 3796962701184346 blankCfg = some (runListCfg 0 79550436 [1]) := by
    have hs := appC8_odd_collapse 26516810
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h101 hs
    norm_num only at h
    exact h
  have h103 : run 8543166880453444 blankCfg = some (runListCfg 39775218 0 [1]) := by
    have hs := tail_shuttle_rounds 19887609 0 79550437 (suffix [1]) (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h102 hs
    norm_num only at h
    exact h
  have h104 : run 8543167437306586 blankCfg = some (runListCfg 0 119325654 [7,1]) := by
    have hs := defect_one_collapse 39775216
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h103 hs
    norm_num only at h
    exact h
  have h105 : run 19222126273865196 blankCfg = some (runListCfg 59662826 2 [7,1]) := by
    have hs := tail_shuttle_rounds 29831413 0 119325655 (suffix [7,1]) (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h104 hs
    norm_num only at h
    exact h
  have h106 : run 19222126989819224 blankCfg = some (runListCfg 59662826 0 [16]) := by
    have hs := three_eight 59662824
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h105 hs
    norm_num only at h
    exact h
  have h107 : run 19222127467122155 blankCfg = some (runListCfg 0 0 [178988470,25,1]) := by
    have hs := seventeen_collapse 59662822
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h106 hs
    norm_num only at h
    exact h
  have h108 : run 19222127467122192 blankCfg = some (runListCfg 3 178988466 [25,1]) := by
    have hs := run_list_zero_long 178988466 [25,1]
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h107 hs
    norm_num only at h
    exact h
  have h109 : run 43249782388287464 blankCfg = some (runListCfg 89494235 2 [25,1]) := by
    have hs := tail_shuttle_rounds 44747116 3 178988467 (suffix [25,1]) (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h108 hs
    norm_num only at h
    exact h
  have h110 : run 43249783462218928 blankCfg = some (runListCfg 89494232 0 [43]) := by
    have hs := three_twenty_six 89494230
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h109 hs
    norm_num only at h
    exact h
  exact h110

theorem restricted_frontier_member : Candidate (runListCfg 89494232 0 [43]) :=
  Or.inl ⟨89494232,0,[43],Or.inr (Or.inl ⟨rfl,Or.inr (Or.inr (Or.inl rfl))⟩),rfl⟩

theorem blank_restricted_prefix (j : Nat) (hj : j ≤ 43249783462218928) :
    ∃ d, run j blankCfg = some d := run_prefix_defined blank_restricted_frontier j hj

theorem upstream_restricted_frontier :
    BusyBeaver.ReachesIn BB6Interop.AppC8.machine 43249783462218928 (BusyBeaver.init [])
      (BB6Interop.AppC8.encode (runListCfg 89494232 0 [43])) :=
  BB6Interop.AppC8.blank_reaches_in blank_restricted_frontier

end BB6Interop.AppC8Restricted
