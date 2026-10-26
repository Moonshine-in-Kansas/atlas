import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.Data

/-! E7 minuscule certificate component: WordSteps. -/
namespace Atlas.Chevalley.E7MinusculeTable
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem word_step_0 : (0 : Weight) ≠ 0 → weightWord 0 = weightWord (parent 0) ++ [lastStep 0] := by decide +kernel
private theorem word_step_1 : (1 : Weight) ≠ 0 → weightWord 1 = weightWord (parent 1) ++ [lastStep 1] := by decide +kernel
private theorem word_step_2 : (2 : Weight) ≠ 0 → weightWord 2 = weightWord (parent 2) ++ [lastStep 2] := by decide +kernel
private theorem word_step_3 : (3 : Weight) ≠ 0 → weightWord 3 = weightWord (parent 3) ++ [lastStep 3] := by decide +kernel
private theorem word_step_4 : (4 : Weight) ≠ 0 → weightWord 4 = weightWord (parent 4) ++ [lastStep 4] := by decide +kernel
private theorem word_step_5 : (5 : Weight) ≠ 0 → weightWord 5 = weightWord (parent 5) ++ [lastStep 5] := by decide +kernel
private theorem word_step_6 : (6 : Weight) ≠ 0 → weightWord 6 = weightWord (parent 6) ++ [lastStep 6] := by decide +kernel
private theorem word_step_7 : (7 : Weight) ≠ 0 → weightWord 7 = weightWord (parent 7) ++ [lastStep 7] := by decide +kernel
private theorem word_step_8 : (8 : Weight) ≠ 0 → weightWord 8 = weightWord (parent 8) ++ [lastStep 8] := by decide +kernel
private theorem word_step_9 : (9 : Weight) ≠ 0 → weightWord 9 = weightWord (parent 9) ++ [lastStep 9] := by decide +kernel
private theorem word_step_10 : (10 : Weight) ≠ 0 → weightWord 10 = weightWord (parent 10) ++ [lastStep 10] := by decide +kernel
private theorem word_step_11 : (11 : Weight) ≠ 0 → weightWord 11 = weightWord (parent 11) ++ [lastStep 11] := by decide +kernel
private theorem word_step_12 : (12 : Weight) ≠ 0 → weightWord 12 = weightWord (parent 12) ++ [lastStep 12] := by decide +kernel
private theorem word_step_13 : (13 : Weight) ≠ 0 → weightWord 13 = weightWord (parent 13) ++ [lastStep 13] := by decide +kernel
private theorem word_step_14 : (14 : Weight) ≠ 0 → weightWord 14 = weightWord (parent 14) ++ [lastStep 14] := by decide +kernel
private theorem word_step_15 : (15 : Weight) ≠ 0 → weightWord 15 = weightWord (parent 15) ++ [lastStep 15] := by decide +kernel
private theorem word_step_16 : (16 : Weight) ≠ 0 → weightWord 16 = weightWord (parent 16) ++ [lastStep 16] := by decide +kernel
private theorem word_step_17 : (17 : Weight) ≠ 0 → weightWord 17 = weightWord (parent 17) ++ [lastStep 17] := by decide +kernel
private theorem word_step_18 : (18 : Weight) ≠ 0 → weightWord 18 = weightWord (parent 18) ++ [lastStep 18] := by decide +kernel
private theorem word_step_19 : (19 : Weight) ≠ 0 → weightWord 19 = weightWord (parent 19) ++ [lastStep 19] := by decide +kernel
private theorem word_step_20 : (20 : Weight) ≠ 0 → weightWord 20 = weightWord (parent 20) ++ [lastStep 20] := by decide +kernel
private theorem word_step_21 : (21 : Weight) ≠ 0 → weightWord 21 = weightWord (parent 21) ++ [lastStep 21] := by decide +kernel
private theorem word_step_22 : (22 : Weight) ≠ 0 → weightWord 22 = weightWord (parent 22) ++ [lastStep 22] := by decide +kernel
private theorem word_step_23 : (23 : Weight) ≠ 0 → weightWord 23 = weightWord (parent 23) ++ [lastStep 23] := by decide +kernel
private theorem word_step_24 : (24 : Weight) ≠ 0 → weightWord 24 = weightWord (parent 24) ++ [lastStep 24] := by decide +kernel
private theorem word_step_25 : (25 : Weight) ≠ 0 → weightWord 25 = weightWord (parent 25) ++ [lastStep 25] := by decide +kernel
private theorem word_step_26 : (26 : Weight) ≠ 0 → weightWord 26 = weightWord (parent 26) ++ [lastStep 26] := by decide +kernel
private theorem word_step_27 : (27 : Weight) ≠ 0 → weightWord 27 = weightWord (parent 27) ++ [lastStep 27] := by decide +kernel
private theorem word_step_28 : (28 : Weight) ≠ 0 → weightWord 28 = weightWord (parent 28) ++ [lastStep 28] := by decide +kernel
private theorem word_step_29 : (29 : Weight) ≠ 0 → weightWord 29 = weightWord (parent 29) ++ [lastStep 29] := by decide +kernel
private theorem word_step_30 : (30 : Weight) ≠ 0 → weightWord 30 = weightWord (parent 30) ++ [lastStep 30] := by decide +kernel
private theorem word_step_31 : (31 : Weight) ≠ 0 → weightWord 31 = weightWord (parent 31) ++ [lastStep 31] := by decide +kernel
private theorem word_step_32 : (32 : Weight) ≠ 0 → weightWord 32 = weightWord (parent 32) ++ [lastStep 32] := by decide +kernel
private theorem word_step_33 : (33 : Weight) ≠ 0 → weightWord 33 = weightWord (parent 33) ++ [lastStep 33] := by decide +kernel
private theorem word_step_34 : (34 : Weight) ≠ 0 → weightWord 34 = weightWord (parent 34) ++ [lastStep 34] := by decide +kernel
private theorem word_step_35 : (35 : Weight) ≠ 0 → weightWord 35 = weightWord (parent 35) ++ [lastStep 35] := by decide +kernel
private theorem word_step_36 : (36 : Weight) ≠ 0 → weightWord 36 = weightWord (parent 36) ++ [lastStep 36] := by decide +kernel
private theorem word_step_37 : (37 : Weight) ≠ 0 → weightWord 37 = weightWord (parent 37) ++ [lastStep 37] := by decide +kernel
private theorem word_step_38 : (38 : Weight) ≠ 0 → weightWord 38 = weightWord (parent 38) ++ [lastStep 38] := by decide +kernel
private theorem word_step_39 : (39 : Weight) ≠ 0 → weightWord 39 = weightWord (parent 39) ++ [lastStep 39] := by decide +kernel
private theorem word_step_40 : (40 : Weight) ≠ 0 → weightWord 40 = weightWord (parent 40) ++ [lastStep 40] := by decide +kernel
private theorem word_step_41 : (41 : Weight) ≠ 0 → weightWord 41 = weightWord (parent 41) ++ [lastStep 41] := by decide +kernel
private theorem word_step_42 : (42 : Weight) ≠ 0 → weightWord 42 = weightWord (parent 42) ++ [lastStep 42] := by decide +kernel
private theorem word_step_43 : (43 : Weight) ≠ 0 → weightWord 43 = weightWord (parent 43) ++ [lastStep 43] := by decide +kernel
private theorem word_step_44 : (44 : Weight) ≠ 0 → weightWord 44 = weightWord (parent 44) ++ [lastStep 44] := by decide +kernel
private theorem word_step_45 : (45 : Weight) ≠ 0 → weightWord 45 = weightWord (parent 45) ++ [lastStep 45] := by decide +kernel
private theorem word_step_46 : (46 : Weight) ≠ 0 → weightWord 46 = weightWord (parent 46) ++ [lastStep 46] := by decide +kernel
private theorem word_step_47 : (47 : Weight) ≠ 0 → weightWord 47 = weightWord (parent 47) ++ [lastStep 47] := by decide +kernel
private theorem word_step_48 : (48 : Weight) ≠ 0 → weightWord 48 = weightWord (parent 48) ++ [lastStep 48] := by decide +kernel
private theorem word_step_49 : (49 : Weight) ≠ 0 → weightWord 49 = weightWord (parent 49) ++ [lastStep 49] := by decide +kernel
private theorem word_step_50 : (50 : Weight) ≠ 0 → weightWord 50 = weightWord (parent 50) ++ [lastStep 50] := by decide +kernel
private theorem word_step_51 : (51 : Weight) ≠ 0 → weightWord 51 = weightWord (parent 51) ++ [lastStep 51] := by decide +kernel
private theorem word_step_52 : (52 : Weight) ≠ 0 → weightWord 52 = weightWord (parent 52) ++ [lastStep 52] := by decide +kernel
private theorem word_step_53 : (53 : Weight) ≠ 0 → weightWord 53 = weightWord (parent 53) ++ [lastStep 53] := by decide +kernel
private theorem word_step_54 : (54 : Weight) ≠ 0 → weightWord 54 = weightWord (parent 54) ++ [lastStep 54] := by decide +kernel
private theorem word_step_55 : (55 : Weight) ≠ 0 → weightWord 55 = weightWord (parent 55) ++ [lastStep 55] := by decide +kernel
theorem word_step : ∀ a : Weight, a ≠ 0 → weightWord a = weightWord (parent a) ++ [lastStep a] := by
  intro a
  fin_cases a
  · exact word_step_0
  · exact word_step_1
  · exact word_step_2
  · exact word_step_3
  · exact word_step_4
  · exact word_step_5
  · exact word_step_6
  · exact word_step_7
  · exact word_step_8
  · exact word_step_9
  · exact word_step_10
  · exact word_step_11
  · exact word_step_12
  · exact word_step_13
  · exact word_step_14
  · exact word_step_15
  · exact word_step_16
  · exact word_step_17
  · exact word_step_18
  · exact word_step_19
  · exact word_step_20
  · exact word_step_21
  · exact word_step_22
  · exact word_step_23
  · exact word_step_24
  · exact word_step_25
  · exact word_step_26
  · exact word_step_27
  · exact word_step_28
  · exact word_step_29
  · exact word_step_30
  · exact word_step_31
  · exact word_step_32
  · exact word_step_33
  · exact word_step_34
  · exact word_step_35
  · exact word_step_36
  · exact word_step_37
  · exact word_step_38
  · exact word_step_39
  · exact word_step_40
  · exact word_step_41
  · exact word_step_42
  · exact word_step_43
  · exact word_step_44
  · exact word_step_45
  · exact word_step_46
  · exact word_step_47
  · exact word_step_48
  · exact word_step_49
  · exact word_step_50
  · exact word_step_51
  · exact word_step_52
  · exact word_step_53
  · exact word_step_54
  · exact word_step_55

end Atlas.Chevalley.E7MinusculeTable
