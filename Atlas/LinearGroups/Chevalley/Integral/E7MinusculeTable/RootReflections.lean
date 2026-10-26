import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.RootReflections.Part0
import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.RootReflections.Part1
import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.RootReflections.Part2
import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.RootReflections.Part3
import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.RootReflections.Part4
import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.RootReflections.Part5
import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.RootReflections.Part6
import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.Data

/-! E7 minuscule certificate component: RootReflections. -/
namespace Atlas.Chevalley.E7MinusculeTable
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem root_reflection_coordinates : ∀ a : Weight, ∀ r : CorootIndex, coordinates (rootReflectionIndex r a) = reflectRoot r (coordinates a) := by
  intro a
  fin_cases a
  · exact CertificateParts.root_reflection_coordinates_0
  · exact CertificateParts.root_reflection_coordinates_1
  · exact CertificateParts.root_reflection_coordinates_2
  · exact CertificateParts.root_reflection_coordinates_3
  · exact CertificateParts.root_reflection_coordinates_4
  · exact CertificateParts.root_reflection_coordinates_5
  · exact CertificateParts.root_reflection_coordinates_6
  · exact CertificateParts.root_reflection_coordinates_7
  · exact CertificateParts.root_reflection_coordinates_8
  · exact CertificateParts.root_reflection_coordinates_9
  · exact CertificateParts.root_reflection_coordinates_10
  · exact CertificateParts.root_reflection_coordinates_11
  · exact CertificateParts.root_reflection_coordinates_12
  · exact CertificateParts.root_reflection_coordinates_13
  · exact CertificateParts.root_reflection_coordinates_14
  · exact CertificateParts.root_reflection_coordinates_15
  · exact CertificateParts.root_reflection_coordinates_16
  · exact CertificateParts.root_reflection_coordinates_17
  · exact CertificateParts.root_reflection_coordinates_18
  · exact CertificateParts.root_reflection_coordinates_19
  · exact CertificateParts.root_reflection_coordinates_20
  · exact CertificateParts.root_reflection_coordinates_21
  · exact CertificateParts.root_reflection_coordinates_22
  · exact CertificateParts.root_reflection_coordinates_23
  · exact CertificateParts.root_reflection_coordinates_24
  · exact CertificateParts.root_reflection_coordinates_25
  · exact CertificateParts.root_reflection_coordinates_26
  · exact CertificateParts.root_reflection_coordinates_27
  · exact CertificateParts.root_reflection_coordinates_28
  · exact CertificateParts.root_reflection_coordinates_29
  · exact CertificateParts.root_reflection_coordinates_30
  · exact CertificateParts.root_reflection_coordinates_31
  · exact CertificateParts.root_reflection_coordinates_32
  · exact CertificateParts.root_reflection_coordinates_33
  · exact CertificateParts.root_reflection_coordinates_34
  · exact CertificateParts.root_reflection_coordinates_35
  · exact CertificateParts.root_reflection_coordinates_36
  · exact CertificateParts.root_reflection_coordinates_37
  · exact CertificateParts.root_reflection_coordinates_38
  · exact CertificateParts.root_reflection_coordinates_39
  · exact CertificateParts.root_reflection_coordinates_40
  · exact CertificateParts.root_reflection_coordinates_41
  · exact CertificateParts.root_reflection_coordinates_42
  · exact CertificateParts.root_reflection_coordinates_43
  · exact CertificateParts.root_reflection_coordinates_44
  · exact CertificateParts.root_reflection_coordinates_45
  · exact CertificateParts.root_reflection_coordinates_46
  · exact CertificateParts.root_reflection_coordinates_47
  · exact CertificateParts.root_reflection_coordinates_48
  · exact CertificateParts.root_reflection_coordinates_49
  · exact CertificateParts.root_reflection_coordinates_50
  · exact CertificateParts.root_reflection_coordinates_51
  · exact CertificateParts.root_reflection_coordinates_52
  · exact CertificateParts.root_reflection_coordinates_53
  · exact CertificateParts.root_reflection_coordinates_54
  · exact CertificateParts.root_reflection_coordinates_55

end Atlas.Chevalley.E7MinusculeTable
