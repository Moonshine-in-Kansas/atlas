import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.Data

/-! Full-126-root finite certificates, Grades part 0. -/
namespace Atlas.Chevalley.E7MinusculeTable.CertificateParts
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem all_root_grades_0 : ∀ r : CorootIndex, grade 0 r = -1 ∨ grade 0 r = 0 ∨ grade 0 r = 1 := by decide +kernel
theorem all_root_grades_1 : ∀ r : CorootIndex, grade 1 r = -1 ∨ grade 1 r = 0 ∨ grade 1 r = 1 := by decide +kernel
theorem all_root_grades_2 : ∀ r : CorootIndex, grade 2 r = -1 ∨ grade 2 r = 0 ∨ grade 2 r = 1 := by decide +kernel
theorem all_root_grades_3 : ∀ r : CorootIndex, grade 3 r = -1 ∨ grade 3 r = 0 ∨ grade 3 r = 1 := by decide +kernel
theorem all_root_grades_4 : ∀ r : CorootIndex, grade 4 r = -1 ∨ grade 4 r = 0 ∨ grade 4 r = 1 := by decide +kernel
theorem all_root_grades_5 : ∀ r : CorootIndex, grade 5 r = -1 ∨ grade 5 r = 0 ∨ grade 5 r = 1 := by decide +kernel
theorem all_root_grades_6 : ∀ r : CorootIndex, grade 6 r = -1 ∨ grade 6 r = 0 ∨ grade 6 r = 1 := by decide +kernel
theorem all_root_grades_7 : ∀ r : CorootIndex, grade 7 r = -1 ∨ grade 7 r = 0 ∨ grade 7 r = 1 := by decide +kernel

end Atlas.Chevalley.E7MinusculeTable.CertificateParts
