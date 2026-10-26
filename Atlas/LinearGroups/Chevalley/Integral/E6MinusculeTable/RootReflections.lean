import Atlas.LinearGroups.Chevalley.Integral.E6MinusculeTable.Data

/-! E6 minuscule certificate component: RootReflections. -/
namespace Atlas.Chevalley.E6MinusculeTable
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem root_reflection_coordinates_0 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 0) = reflectRoot r (coordinates 0) := by decide +kernel
private theorem root_reflection_coordinates_1 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 1) = reflectRoot r (coordinates 1) := by decide +kernel
private theorem root_reflection_coordinates_2 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 2) = reflectRoot r (coordinates 2) := by decide +kernel
private theorem root_reflection_coordinates_3 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 3) = reflectRoot r (coordinates 3) := by decide +kernel
private theorem root_reflection_coordinates_4 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 4) = reflectRoot r (coordinates 4) := by decide +kernel
private theorem root_reflection_coordinates_5 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 5) = reflectRoot r (coordinates 5) := by decide +kernel
private theorem root_reflection_coordinates_6 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 6) = reflectRoot r (coordinates 6) := by decide +kernel
private theorem root_reflection_coordinates_7 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 7) = reflectRoot r (coordinates 7) := by decide +kernel
private theorem root_reflection_coordinates_8 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 8) = reflectRoot r (coordinates 8) := by decide +kernel
private theorem root_reflection_coordinates_9 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 9) = reflectRoot r (coordinates 9) := by decide +kernel
private theorem root_reflection_coordinates_10 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 10) = reflectRoot r (coordinates 10) := by decide +kernel
private theorem root_reflection_coordinates_11 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 11) = reflectRoot r (coordinates 11) := by decide +kernel
private theorem root_reflection_coordinates_12 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 12) = reflectRoot r (coordinates 12) := by decide +kernel
private theorem root_reflection_coordinates_13 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 13) = reflectRoot r (coordinates 13) := by decide +kernel
private theorem root_reflection_coordinates_14 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 14) = reflectRoot r (coordinates 14) := by decide +kernel
private theorem root_reflection_coordinates_15 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 15) = reflectRoot r (coordinates 15) := by decide +kernel
private theorem root_reflection_coordinates_16 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 16) = reflectRoot r (coordinates 16) := by decide +kernel
private theorem root_reflection_coordinates_17 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 17) = reflectRoot r (coordinates 17) := by decide +kernel
private theorem root_reflection_coordinates_18 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 18) = reflectRoot r (coordinates 18) := by decide +kernel
private theorem root_reflection_coordinates_19 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 19) = reflectRoot r (coordinates 19) := by decide +kernel
private theorem root_reflection_coordinates_20 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 20) = reflectRoot r (coordinates 20) := by decide +kernel
private theorem root_reflection_coordinates_21 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 21) = reflectRoot r (coordinates 21) := by decide +kernel
private theorem root_reflection_coordinates_22 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 22) = reflectRoot r (coordinates 22) := by decide +kernel
private theorem root_reflection_coordinates_23 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 23) = reflectRoot r (coordinates 23) := by decide +kernel
private theorem root_reflection_coordinates_24 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 24) = reflectRoot r (coordinates 24) := by decide +kernel
private theorem root_reflection_coordinates_25 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 25) = reflectRoot r (coordinates 25) := by decide +kernel
private theorem root_reflection_coordinates_26 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 26) = reflectRoot r (coordinates 26) := by decide +kernel
theorem root_reflection_coordinates : ∀ a : Weight, ∀ r : CorootIndex, coordinates (rootReflectionIndex r a) = reflectRoot r (coordinates a) := by
  intro a
  fin_cases a
  · exact root_reflection_coordinates_0
  · exact root_reflection_coordinates_1
  · exact root_reflection_coordinates_2
  · exact root_reflection_coordinates_3
  · exact root_reflection_coordinates_4
  · exact root_reflection_coordinates_5
  · exact root_reflection_coordinates_6
  · exact root_reflection_coordinates_7
  · exact root_reflection_coordinates_8
  · exact root_reflection_coordinates_9
  · exact root_reflection_coordinates_10
  · exact root_reflection_coordinates_11
  · exact root_reflection_coordinates_12
  · exact root_reflection_coordinates_13
  · exact root_reflection_coordinates_14
  · exact root_reflection_coordinates_15
  · exact root_reflection_coordinates_16
  · exact root_reflection_coordinates_17
  · exact root_reflection_coordinates_18
  · exact root_reflection_coordinates_19
  · exact root_reflection_coordinates_20
  · exact root_reflection_coordinates_21
  · exact root_reflection_coordinates_22
  · exact root_reflection_coordinates_23
  · exact root_reflection_coordinates_24
  · exact root_reflection_coordinates_25
  · exact root_reflection_coordinates_26

end Atlas.Chevalley.E6MinusculeTable
