import Atlas.LinearGroups.Chevalley.Integral.E6MinusculeTable.Data

/-! E6 minuscule certificate component: ParentLt. -/
namespace Atlas.Chevalley.E6MinusculeTable
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem parent_lt_0 : (0 : Weight) ≠ 0 → parent 0 < 0 := by decide +kernel
private theorem parent_lt_1 : (1 : Weight) ≠ 0 → parent 1 < 1 := by decide +kernel
private theorem parent_lt_2 : (2 : Weight) ≠ 0 → parent 2 < 2 := by decide +kernel
private theorem parent_lt_3 : (3 : Weight) ≠ 0 → parent 3 < 3 := by decide +kernel
private theorem parent_lt_4 : (4 : Weight) ≠ 0 → parent 4 < 4 := by decide +kernel
private theorem parent_lt_5 : (5 : Weight) ≠ 0 → parent 5 < 5 := by decide +kernel
private theorem parent_lt_6 : (6 : Weight) ≠ 0 → parent 6 < 6 := by decide +kernel
private theorem parent_lt_7 : (7 : Weight) ≠ 0 → parent 7 < 7 := by decide +kernel
private theorem parent_lt_8 : (8 : Weight) ≠ 0 → parent 8 < 8 := by decide +kernel
private theorem parent_lt_9 : (9 : Weight) ≠ 0 → parent 9 < 9 := by decide +kernel
private theorem parent_lt_10 : (10 : Weight) ≠ 0 → parent 10 < 10 := by decide +kernel
private theorem parent_lt_11 : (11 : Weight) ≠ 0 → parent 11 < 11 := by decide +kernel
private theorem parent_lt_12 : (12 : Weight) ≠ 0 → parent 12 < 12 := by decide +kernel
private theorem parent_lt_13 : (13 : Weight) ≠ 0 → parent 13 < 13 := by decide +kernel
private theorem parent_lt_14 : (14 : Weight) ≠ 0 → parent 14 < 14 := by decide +kernel
private theorem parent_lt_15 : (15 : Weight) ≠ 0 → parent 15 < 15 := by decide +kernel
private theorem parent_lt_16 : (16 : Weight) ≠ 0 → parent 16 < 16 := by decide +kernel
private theorem parent_lt_17 : (17 : Weight) ≠ 0 → parent 17 < 17 := by decide +kernel
private theorem parent_lt_18 : (18 : Weight) ≠ 0 → parent 18 < 18 := by decide +kernel
private theorem parent_lt_19 : (19 : Weight) ≠ 0 → parent 19 < 19 := by decide +kernel
private theorem parent_lt_20 : (20 : Weight) ≠ 0 → parent 20 < 20 := by decide +kernel
private theorem parent_lt_21 : (21 : Weight) ≠ 0 → parent 21 < 21 := by decide +kernel
private theorem parent_lt_22 : (22 : Weight) ≠ 0 → parent 22 < 22 := by decide +kernel
private theorem parent_lt_23 : (23 : Weight) ≠ 0 → parent 23 < 23 := by decide +kernel
private theorem parent_lt_24 : (24 : Weight) ≠ 0 → parent 24 < 24 := by decide +kernel
private theorem parent_lt_25 : (25 : Weight) ≠ 0 → parent 25 < 25 := by decide +kernel
private theorem parent_lt_26 : (26 : Weight) ≠ 0 → parent 26 < 26 := by decide +kernel
theorem parent_lt : ∀ a : Weight, a ≠ 0 → parent a < a := by
  intro a
  fin_cases a
  · exact parent_lt_0
  · exact parent_lt_1
  · exact parent_lt_2
  · exact parent_lt_3
  · exact parent_lt_4
  · exact parent_lt_5
  · exact parent_lt_6
  · exact parent_lt_7
  · exact parent_lt_8
  · exact parent_lt_9
  · exact parent_lt_10
  · exact parent_lt_11
  · exact parent_lt_12
  · exact parent_lt_13
  · exact parent_lt_14
  · exact parent_lt_15
  · exact parent_lt_16
  · exact parent_lt_17
  · exact parent_lt_18
  · exact parent_lt_19
  · exact parent_lt_20
  · exact parent_lt_21
  · exact parent_lt_22
  · exact parent_lt_23
  · exact parent_lt_24
  · exact parent_lt_25
  · exact parent_lt_26

end Atlas.Chevalley.E6MinusculeTable
