import BB6Interop.AppC8Continuation

namespace BB6Interop.AppC8Continuation
open CryptidSolvePhase4 CryptidSolvePhase4.AppC8Raw

/-- Composition of universal rules; no raw enumeration of this many steps. -/
theorem blank_extended_frontier :
    run 507471992896 blankCfg =
      some (shuttleTailCfg 306555 1 (false :: ones 5 [])) := by
  have h0 := appC8_blank_clean_macro_applied
  have h1 : run 5895974 blankCfg = some (shuttleCfg 3 3136) := by
    have hs := appC8_raw_reset 1045
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h0 hs
    norm_num only at h
    exact h
  have h2 : run 13292192 blankCfg = some (shuttleCfg 1569 4) := by
    have hs := tail_shuttle_rounds 783 3 3136 [] (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h1 hs
    norm_num only at h
    exact h
  have h3 : run 13314194 blankCfg = some (shuttleCfg 0 4717) := by
    have hs := four_collapse 1569
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h2 hs
    norm_num only at h
    exact h
  have h4 : run 30011192 blankCfg = some (shuttleCfg 2358 1) := by
    have hs := tail_shuttle_rounds 1179 0 4717 [] (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h3 hs
    norm_num only at h
    exact h
  have h5 : run 30030073 blankCfg =
      some (shuttleTailCfg 0 1 (false :: ones 7076 (false :: ones 2 []))) := by
    have hs := one_collapse 2358
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h4 hs
    norm_num only at h
    exact h
  have h6 : run 30030110 blankCfg =
      some (shuttleTailCfg 3 7072 (false :: ones 2 [])) := by
    have hs := zero_block_defect_param 7070 (false :: ones 2 [])
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h5 hs
    norm_num only at h
    exact h
  have h7 : run 67585928 blankCfg =
      some (shuttleTailCfg 3537 4 (false :: ones 2 [])) := by
    have hs := tail_shuttle_rounds 1767 3 7072 (false :: ones 2 []) (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h6 hs
    norm_num only at h
    exact h
  have h8 : run 67635490 blankCfg = some (shuttleCfg 0 10624) := by
    have hs := appC8_odd_terminal 3537
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h7 hs
    norm_num only at h
    exact h
  have h9 : run 152260960 blankCfg = some (shuttleCfg 5310 4) := by
    have hs := tail_shuttle_rounds 2655 0 10624 [] (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h8 hs
    norm_num only at h
    exact h
  have h10 : run 152335336 blankCfg = some (shuttleCfg 0 15940) := by
    have hs := four_collapse 5310
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h9 hs
    norm_num only at h
    exact h
  have h11 : run 342858184 blankCfg = some (shuttleCfg 7968 4) := by
    have hs := tail_shuttle_rounds 3984 0 15940 [] (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h10 hs
    norm_num only at h
    exact h
  have h12 : run 342969772 blankCfg = some (shuttleCfg 0 23914) := by
    have hs := four_collapse 7968
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h11 hs
    norm_num only at h
    exact h
  have h13 : run 771891272 blankCfg = some (shuttleCfg 11956 2) := by
    have hs := tail_shuttle_rounds 5978 0 23914 [] (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h12 hs
    norm_num only at h
    exact h
  have h14 : run 771927146 blankCfg = some (cleanCfg 11957) := by
    have hs := appC8_raw_exit 11956
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h13 hs
    norm_num only at h
    exact h
  have h15 : run 771986974 blankCfg = some (shuttleCfg 3 35869) := by
    have hs := appC8_raw_reset 11956
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h14 hs
    norm_num only at h
    exact h
  have h16 : run 1737320392 blankCfg = some (shuttleCfg 17937 1) := by
    have hs := tail_shuttle_rounds 8967 3 35869 [] (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h15 hs
    norm_num only at h
    exact h
  have h17 : run 1737463905 blankCfg =
      some (shuttleTailCfg 0 1 (false :: ones 53813 (false :: ones 2 []))) := by
    have hs := one_collapse 17937
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h16 hs
    norm_num only at h
    exact h
  have h18 : run 1737463942 blankCfg =
      some (shuttleTailCfg 3 53809 (false :: ones 2 [])) := by
    have hs := zero_block_defect_param 53807 (false :: ones 2 [])
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h17 hs
    norm_num only at h
    exact h
  have h19 : run 3909612190 blankCfg =
      some (shuttleTailCfg 26907 1 (false :: ones 2 [])) := by
    have hs := tail_shuttle_rounds 13452 3 53809 (false :: ones 2 []) (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h18 hs
    norm_num only at h
    exact h
  have h20 : run 3909988978 blankCfg =
      some (shuttleTailCfg 0 80722 (false :: ones 8 (false :: ones 2 []))) := by
    have hs := defect_one_collapse 26905
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h19 hs
    norm_num only at h
    exact h
  have h21 : run 8797060298 blankCfg =
      some (shuttleTailCfg 40360 2 (false :: ones 8 (false :: ones 2 []))) := by
    have hs := tail_shuttle_rounds 20180 0 80722 (false :: ones 8 (false :: ones 2 [])) (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h20 hs
    norm_num only at h
    exact h
  have h22 : run 8797060298 blankCfg =
      some (shuttleTailCfg 40361 8 (false :: ones 2 [])) := by
    have h := h21
    rw [absorb_defect] at h
    exact h
  have h23 : run 8797544656 blankCfg =
      some (shuttleTailCfg 40363 4 (false :: ones 2 [])) := by
    have hs := tail_shuttle_rounds 1 40361 8 (false :: ones 2 []) (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h22 hs
    norm_num only at h
    exact h
  have h24 : run 8798109782 blankCfg = some (shuttleCfg 0 121102) := by
    have hs := appC8_odd_terminal 40363
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h23 hs
    norm_num only at h
    exact h
  have h25 : run 19797441132 blankCfg = some (shuttleCfg 60550 2) := by
    have hs := tail_shuttle_rounds 30275 0 121102 [] (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h24 hs
    norm_num only at h
    exact h
  have h26 : run 19797622788 blankCfg = some (cleanCfg 60551) := by
    have hs := appC8_raw_exit 60550
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h25 hs
    norm_num only at h
    exact h
  have h27 : run 19797925586 blankCfg = some (shuttleCfg 3 181651) := by
    have hs := appC8_raw_reset 60550
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h26 hs
    norm_num only at h
    exact h
  have h28 : run 44547193114 blankCfg = some (shuttleCfg 90827 3) := by
    have hs := tail_shuttle_rounds 45412 3 181651 [] (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h27 hs
    norm_num only at h
    exact h
  have h29 : run 44548464728 blankCfg =
      some (shuttleTailCfg 0 272488 (false :: ones 2 [])) := by
    have hs := appC8_odd_collapse 90827
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h28 hs
    norm_num only at h
    exact h
  have h30 : run 100235066114 blankCfg =
      some (shuttleTailCfg 136242 4 (false :: ones 2 [])) := by
    have hs := tail_shuttle_rounds 68121 0 272488 (false :: ones 2 []) (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h29 hs
    norm_num only at h
    exact h
  have h31 : run 100236973546 blankCfg = some (shuttleCfg 0 408739) := by
    have hs := appC8_odd_terminal 136242
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h30 hs
    norm_num only at h
    exact h
  have h32 : run 225537242394 blankCfg = some (shuttleCfg 204368 3) := by
    have hs := tail_shuttle_rounds 102184 0 408739 [] (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h31 hs
    norm_num only at h
    exact h
  have h33 : run 225540103582 blankCfg =
      some (shuttleTailCfg 0 613111 (false :: ones 2 [])) := by
    have hs := appC8_odd_collapse 204368
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h32 hs
    norm_num only at h
    exact h
  have h34 : run 507468314208 blankCfg =
      some (shuttleTailCfg 306554 3 (false :: ones 2 [])) := by
    have hs := tail_shuttle_rounds 153277 0 613111 (false :: ones 2 []) (by decide)
    norm_num only [appC8ShuttleRoundsSteps_closed_form] at hs
    have h := run_comp h33 hs
    norm_num only at h
    exact h
  have h := run_comp h34 (three_with_tail 306554)
  norm_num only at h
  exact h

theorem blank_extended_prefix (j : Nat) (hj : j ≤ 507471992896) :
    ∃ d, run j blankCfg = some d :=
  run_prefix_defined blank_extended_frontier j hj

theorem upstream_extended_frontier :
    BusyBeaver.ReachesIn BB6Interop.AppC8.machine 507471992896 (BusyBeaver.init [])
      (BB6Interop.AppC8.encode (shuttleTailCfg 306555 1 (false :: ones 5 []))) :=
  BB6Interop.AppC8.blank_reaches_in blank_extended_frontier

theorem upstream_extended_prefix (j : Nat) (hj : j ≤ 507471992896) :
    ∃ d, BusyBeaver.ReachesIn BB6Interop.AppC8.machine j (BusyBeaver.init []) d := by
  obtain ⟨d, hd⟩ := blank_extended_prefix j hj
  exact ⟨BB6Interop.AppC8.encode d, BB6Interop.AppC8.blank_reaches_in hd⟩

end BB6Interop.AppC8Continuation
