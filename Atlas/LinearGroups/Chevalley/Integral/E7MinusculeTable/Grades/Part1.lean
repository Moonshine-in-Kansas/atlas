import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.Data

/-! Full-126-root finite certificates, Grades part 1. -/
namespace Atlas.Chevalley.E7MinusculeTable.CertificateParts
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem all_root_grades_8 : ∀ r : CorootIndex, grade 8 r = -1 ∨ grade 8 r = 0 ∨ grade 8 r = 1 := by decide +kernel
theorem all_root_grades_9 : ∀ r : CorootIndex, grade 9 r = -1 ∨ grade 9 r = 0 ∨ grade 9 r = 1 := by decide +kernel
theorem all_root_grades_10 : ∀ r : CorootIndex, grade 10 r = -1 ∨ grade 10 r = 0 ∨ grade 10 r = 1 := by decide +kernel
theorem all_root_grades_11 : ∀ r : CorootIndex, grade 11 r = -1 ∨ grade 11 r = 0 ∨ grade 11 r = 1 := by decide +kernel
theorem all_root_grades_12 : ∀ r : CorootIndex, grade 12 r = -1 ∨ grade 12 r = 0 ∨ grade 12 r = 1 := by decide +kernel
theorem all_root_grades_13 : ∀ r : CorootIndex, grade 13 r = -1 ∨ grade 13 r = 0 ∨ grade 13 r = 1 := by decide +kernel
theorem all_root_grades_14 : ∀ r : CorootIndex, grade 14 r = -1 ∨ grade 14 r = 0 ∨ grade 14 r = 1 := by decide +kernel
theorem all_root_grades_15 : ∀ r : CorootIndex, grade 15 r = -1 ∨ grade 15 r = 0 ∨ grade 15 r = 1 := by decide +kernel

end Atlas.Chevalley.E7MinusculeTable.CertificateParts
