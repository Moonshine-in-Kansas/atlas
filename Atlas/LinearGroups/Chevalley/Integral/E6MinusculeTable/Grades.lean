import Atlas.LinearGroups.Chevalley.Integral.E6MinusculeTable.Data

/-! E6 minuscule certificate component: Grades. -/
namespace Atlas.Chevalley.E6MinusculeTable
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem all_root_grades_0 : ∀ r : CorootIndex, grade 0 r = -1 ∨ grade 0 r = 0 ∨ grade 0 r = 1 := by decide +kernel
private theorem all_root_grades_1 : ∀ r : CorootIndex, grade 1 r = -1 ∨ grade 1 r = 0 ∨ grade 1 r = 1 := by decide +kernel
private theorem all_root_grades_2 : ∀ r : CorootIndex, grade 2 r = -1 ∨ grade 2 r = 0 ∨ grade 2 r = 1 := by decide +kernel
private theorem all_root_grades_3 : ∀ r : CorootIndex, grade 3 r = -1 ∨ grade 3 r = 0 ∨ grade 3 r = 1 := by decide +kernel
private theorem all_root_grades_4 : ∀ r : CorootIndex, grade 4 r = -1 ∨ grade 4 r = 0 ∨ grade 4 r = 1 := by decide +kernel
private theorem all_root_grades_5 : ∀ r : CorootIndex, grade 5 r = -1 ∨ grade 5 r = 0 ∨ grade 5 r = 1 := by decide +kernel
private theorem all_root_grades_6 : ∀ r : CorootIndex, grade 6 r = -1 ∨ grade 6 r = 0 ∨ grade 6 r = 1 := by decide +kernel
private theorem all_root_grades_7 : ∀ r : CorootIndex, grade 7 r = -1 ∨ grade 7 r = 0 ∨ grade 7 r = 1 := by decide +kernel
private theorem all_root_grades_8 : ∀ r : CorootIndex, grade 8 r = -1 ∨ grade 8 r = 0 ∨ grade 8 r = 1 := by decide +kernel
private theorem all_root_grades_9 : ∀ r : CorootIndex, grade 9 r = -1 ∨ grade 9 r = 0 ∨ grade 9 r = 1 := by decide +kernel
private theorem all_root_grades_10 : ∀ r : CorootIndex, grade 10 r = -1 ∨ grade 10 r = 0 ∨ grade 10 r = 1 := by decide +kernel
private theorem all_root_grades_11 : ∀ r : CorootIndex, grade 11 r = -1 ∨ grade 11 r = 0 ∨ grade 11 r = 1 := by decide +kernel
private theorem all_root_grades_12 : ∀ r : CorootIndex, grade 12 r = -1 ∨ grade 12 r = 0 ∨ grade 12 r = 1 := by decide +kernel
private theorem all_root_grades_13 : ∀ r : CorootIndex, grade 13 r = -1 ∨ grade 13 r = 0 ∨ grade 13 r = 1 := by decide +kernel
private theorem all_root_grades_14 : ∀ r : CorootIndex, grade 14 r = -1 ∨ grade 14 r = 0 ∨ grade 14 r = 1 := by decide +kernel
private theorem all_root_grades_15 : ∀ r : CorootIndex, grade 15 r = -1 ∨ grade 15 r = 0 ∨ grade 15 r = 1 := by decide +kernel
private theorem all_root_grades_16 : ∀ r : CorootIndex, grade 16 r = -1 ∨ grade 16 r = 0 ∨ grade 16 r = 1 := by decide +kernel
private theorem all_root_grades_17 : ∀ r : CorootIndex, grade 17 r = -1 ∨ grade 17 r = 0 ∨ grade 17 r = 1 := by decide +kernel
private theorem all_root_grades_18 : ∀ r : CorootIndex, grade 18 r = -1 ∨ grade 18 r = 0 ∨ grade 18 r = 1 := by decide +kernel
private theorem all_root_grades_19 : ∀ r : CorootIndex, grade 19 r = -1 ∨ grade 19 r = 0 ∨ grade 19 r = 1 := by decide +kernel
private theorem all_root_grades_20 : ∀ r : CorootIndex, grade 20 r = -1 ∨ grade 20 r = 0 ∨ grade 20 r = 1 := by decide +kernel
private theorem all_root_grades_21 : ∀ r : CorootIndex, grade 21 r = -1 ∨ grade 21 r = 0 ∨ grade 21 r = 1 := by decide +kernel
private theorem all_root_grades_22 : ∀ r : CorootIndex, grade 22 r = -1 ∨ grade 22 r = 0 ∨ grade 22 r = 1 := by decide +kernel
private theorem all_root_grades_23 : ∀ r : CorootIndex, grade 23 r = -1 ∨ grade 23 r = 0 ∨ grade 23 r = 1 := by decide +kernel
private theorem all_root_grades_24 : ∀ r : CorootIndex, grade 24 r = -1 ∨ grade 24 r = 0 ∨ grade 24 r = 1 := by decide +kernel
private theorem all_root_grades_25 : ∀ r : CorootIndex, grade 25 r = -1 ∨ grade 25 r = 0 ∨ grade 25 r = 1 := by decide +kernel
private theorem all_root_grades_26 : ∀ r : CorootIndex, grade 26 r = -1 ∨ grade 26 r = 0 ∨ grade 26 r = 1 := by decide +kernel
theorem all_root_grades : ∀ a : Weight, ∀ r : CorootIndex, grade a r = -1 ∨ grade a r = 0 ∨ grade a r = 1 := by
  intro a
  fin_cases a
  · exact all_root_grades_0
  · exact all_root_grades_1
  · exact all_root_grades_2
  · exact all_root_grades_3
  · exact all_root_grades_4
  · exact all_root_grades_5
  · exact all_root_grades_6
  · exact all_root_grades_7
  · exact all_root_grades_8
  · exact all_root_grades_9
  · exact all_root_grades_10
  · exact all_root_grades_11
  · exact all_root_grades_12
  · exact all_root_grades_13
  · exact all_root_grades_14
  · exact all_root_grades_15
  · exact all_root_grades_16
  · exact all_root_grades_17
  · exact all_root_grades_18
  · exact all_root_grades_19
  · exact all_root_grades_20
  · exact all_root_grades_21
  · exact all_root_grades_22
  · exact all_root_grades_23
  · exact all_root_grades_24
  · exact all_root_grades_25
  · exact all_root_grades_26

end Atlas.Chevalley.E6MinusculeTable
