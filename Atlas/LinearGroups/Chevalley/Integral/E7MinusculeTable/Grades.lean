import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.Grades.Part0
import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.Grades.Part1
import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.Grades.Part2
import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.Grades.Part3
import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.Grades.Part4
import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.Grades.Part5
import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.Grades.Part6
import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.Data

/-! E7 minuscule certificate component: Grades. -/
namespace Atlas.Chevalley.E7MinusculeTable
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem all_root_grades : ∀ a : Weight, ∀ r : CorootIndex, grade a r = -1 ∨ grade a r = 0 ∨ grade a r = 1 := by
  intro a
  fin_cases a
  · exact CertificateParts.all_root_grades_0
  · exact CertificateParts.all_root_grades_1
  · exact CertificateParts.all_root_grades_2
  · exact CertificateParts.all_root_grades_3
  · exact CertificateParts.all_root_grades_4
  · exact CertificateParts.all_root_grades_5
  · exact CertificateParts.all_root_grades_6
  · exact CertificateParts.all_root_grades_7
  · exact CertificateParts.all_root_grades_8
  · exact CertificateParts.all_root_grades_9
  · exact CertificateParts.all_root_grades_10
  · exact CertificateParts.all_root_grades_11
  · exact CertificateParts.all_root_grades_12
  · exact CertificateParts.all_root_grades_13
  · exact CertificateParts.all_root_grades_14
  · exact CertificateParts.all_root_grades_15
  · exact CertificateParts.all_root_grades_16
  · exact CertificateParts.all_root_grades_17
  · exact CertificateParts.all_root_grades_18
  · exact CertificateParts.all_root_grades_19
  · exact CertificateParts.all_root_grades_20
  · exact CertificateParts.all_root_grades_21
  · exact CertificateParts.all_root_grades_22
  · exact CertificateParts.all_root_grades_23
  · exact CertificateParts.all_root_grades_24
  · exact CertificateParts.all_root_grades_25
  · exact CertificateParts.all_root_grades_26
  · exact CertificateParts.all_root_grades_27
  · exact CertificateParts.all_root_grades_28
  · exact CertificateParts.all_root_grades_29
  · exact CertificateParts.all_root_grades_30
  · exact CertificateParts.all_root_grades_31
  · exact CertificateParts.all_root_grades_32
  · exact CertificateParts.all_root_grades_33
  · exact CertificateParts.all_root_grades_34
  · exact CertificateParts.all_root_grades_35
  · exact CertificateParts.all_root_grades_36
  · exact CertificateParts.all_root_grades_37
  · exact CertificateParts.all_root_grades_38
  · exact CertificateParts.all_root_grades_39
  · exact CertificateParts.all_root_grades_40
  · exact CertificateParts.all_root_grades_41
  · exact CertificateParts.all_root_grades_42
  · exact CertificateParts.all_root_grades_43
  · exact CertificateParts.all_root_grades_44
  · exact CertificateParts.all_root_grades_45
  · exact CertificateParts.all_root_grades_46
  · exact CertificateParts.all_root_grades_47
  · exact CertificateParts.all_root_grades_48
  · exact CertificateParts.all_root_grades_49
  · exact CertificateParts.all_root_grades_50
  · exact CertificateParts.all_root_grades_51
  · exact CertificateParts.all_root_grades_52
  · exact CertificateParts.all_root_grades_53
  · exact CertificateParts.all_root_grades_54
  · exact CertificateParts.all_root_grades_55

end Atlas.Chevalley.E7MinusculeTable
