import Atlas.LinearGroups.Chevalley.Integral.E6MinusculeTable.Data

/-! E6 minuscule certificate component: WordSteps. -/
namespace Atlas.Chevalley.E6MinusculeTable
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

end Atlas.Chevalley.E6MinusculeTable
