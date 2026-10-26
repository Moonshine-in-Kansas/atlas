import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.Data

/-! E7 minuscule certificate component: ParentLt. -/
namespace Atlas.Chevalley.E7MinusculeTable
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
private theorem parent_lt_27 : (27 : Weight) ≠ 0 → parent 27 < 27 := by decide +kernel
private theorem parent_lt_28 : (28 : Weight) ≠ 0 → parent 28 < 28 := by decide +kernel
private theorem parent_lt_29 : (29 : Weight) ≠ 0 → parent 29 < 29 := by decide +kernel
private theorem parent_lt_30 : (30 : Weight) ≠ 0 → parent 30 < 30 := by decide +kernel
private theorem parent_lt_31 : (31 : Weight) ≠ 0 → parent 31 < 31 := by decide +kernel
private theorem parent_lt_32 : (32 : Weight) ≠ 0 → parent 32 < 32 := by decide +kernel
private theorem parent_lt_33 : (33 : Weight) ≠ 0 → parent 33 < 33 := by decide +kernel
private theorem parent_lt_34 : (34 : Weight) ≠ 0 → parent 34 < 34 := by decide +kernel
private theorem parent_lt_35 : (35 : Weight) ≠ 0 → parent 35 < 35 := by decide +kernel
private theorem parent_lt_36 : (36 : Weight) ≠ 0 → parent 36 < 36 := by decide +kernel
private theorem parent_lt_37 : (37 : Weight) ≠ 0 → parent 37 < 37 := by decide +kernel
private theorem parent_lt_38 : (38 : Weight) ≠ 0 → parent 38 < 38 := by decide +kernel
private theorem parent_lt_39 : (39 : Weight) ≠ 0 → parent 39 < 39 := by decide +kernel
private theorem parent_lt_40 : (40 : Weight) ≠ 0 → parent 40 < 40 := by decide +kernel
private theorem parent_lt_41 : (41 : Weight) ≠ 0 → parent 41 < 41 := by decide +kernel
private theorem parent_lt_42 : (42 : Weight) ≠ 0 → parent 42 < 42 := by decide +kernel
private theorem parent_lt_43 : (43 : Weight) ≠ 0 → parent 43 < 43 := by decide +kernel
private theorem parent_lt_44 : (44 : Weight) ≠ 0 → parent 44 < 44 := by decide +kernel
private theorem parent_lt_45 : (45 : Weight) ≠ 0 → parent 45 < 45 := by decide +kernel
private theorem parent_lt_46 : (46 : Weight) ≠ 0 → parent 46 < 46 := by decide +kernel
private theorem parent_lt_47 : (47 : Weight) ≠ 0 → parent 47 < 47 := by decide +kernel
private theorem parent_lt_48 : (48 : Weight) ≠ 0 → parent 48 < 48 := by decide +kernel
private theorem parent_lt_49 : (49 : Weight) ≠ 0 → parent 49 < 49 := by decide +kernel
private theorem parent_lt_50 : (50 : Weight) ≠ 0 → parent 50 < 50 := by decide +kernel
private theorem parent_lt_51 : (51 : Weight) ≠ 0 → parent 51 < 51 := by decide +kernel
private theorem parent_lt_52 : (52 : Weight) ≠ 0 → parent 52 < 52 := by decide +kernel
private theorem parent_lt_53 : (53 : Weight) ≠ 0 → parent 53 < 53 := by decide +kernel
private theorem parent_lt_54 : (54 : Weight) ≠ 0 → parent 54 < 54 := by decide +kernel
private theorem parent_lt_55 : (55 : Weight) ≠ 0 → parent 55 < 55 := by decide +kernel
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
  · exact parent_lt_27
  · exact parent_lt_28
  · exact parent_lt_29
  · exact parent_lt_30
  · exact parent_lt_31
  · exact parent_lt_32
  · exact parent_lt_33
  · exact parent_lt_34
  · exact parent_lt_35
  · exact parent_lt_36
  · exact parent_lt_37
  · exact parent_lt_38
  · exact parent_lt_39
  · exact parent_lt_40
  · exact parent_lt_41
  · exact parent_lt_42
  · exact parent_lt_43
  · exact parent_lt_44
  · exact parent_lt_45
  · exact parent_lt_46
  · exact parent_lt_47
  · exact parent_lt_48
  · exact parent_lt_49
  · exact parent_lt_50
  · exact parent_lt_51
  · exact parent_lt_52
  · exact parent_lt_53
  · exact parent_lt_54
  · exact parent_lt_55

end Atlas.Chevalley.E7MinusculeTable
