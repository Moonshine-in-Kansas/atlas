import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.Data

/-! Full-126-root finite certificates, Grades part 2. -/
namespace Atlas.Chevalley.E7MinusculeTable.CertificateParts
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem all_root_grades_16 : ∀ r : CorootIndex, grade 16 r = -1 ∨ grade 16 r = 0 ∨ grade 16 r = 1 := by decide +kernel
theorem all_root_grades_17 : ∀ r : CorootIndex, grade 17 r = -1 ∨ grade 17 r = 0 ∨ grade 17 r = 1 := by decide +kernel
theorem all_root_grades_18 : ∀ r : CorootIndex, grade 18 r = -1 ∨ grade 18 r = 0 ∨ grade 18 r = 1 := by decide +kernel
theorem all_root_grades_19 : ∀ r : CorootIndex, grade 19 r = -1 ∨ grade 19 r = 0 ∨ grade 19 r = 1 := by decide +kernel
theorem all_root_grades_20 : ∀ r : CorootIndex, grade 20 r = -1 ∨ grade 20 r = 0 ∨ grade 20 r = 1 := by decide +kernel
theorem all_root_grades_21 : ∀ r : CorootIndex, grade 21 r = -1 ∨ grade 21 r = 0 ∨ grade 21 r = 1 := by decide +kernel
theorem all_root_grades_22 : ∀ r : CorootIndex, grade 22 r = -1 ∨ grade 22 r = 0 ∨ grade 22 r = 1 := by decide +kernel
theorem all_root_grades_23 : ∀ r : CorootIndex, grade 23 r = -1 ∨ grade 23 r = 0 ∨ grade 23 r = 1 := by decide +kernel

end Atlas.Chevalley.E7MinusculeTable.CertificateParts
