import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.Data

/-! Full-126-root finite certificates, RootReflections part 0. -/
namespace Atlas.Chevalley.E7MinusculeTable.CertificateParts
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem root_reflection_coordinates_0 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 0) = reflectRoot r (coordinates 0) := by decide +kernel
theorem root_reflection_coordinates_1 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 1) = reflectRoot r (coordinates 1) := by decide +kernel
theorem root_reflection_coordinates_2 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 2) = reflectRoot r (coordinates 2) := by decide +kernel
theorem root_reflection_coordinates_3 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 3) = reflectRoot r (coordinates 3) := by decide +kernel
theorem root_reflection_coordinates_4 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 4) = reflectRoot r (coordinates 4) := by decide +kernel
theorem root_reflection_coordinates_5 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 5) = reflectRoot r (coordinates 5) := by decide +kernel
theorem root_reflection_coordinates_6 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 6) = reflectRoot r (coordinates 6) := by decide +kernel
theorem root_reflection_coordinates_7 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 7) = reflectRoot r (coordinates 7) := by decide +kernel

end Atlas.Chevalley.E7MinusculeTable.CertificateParts
