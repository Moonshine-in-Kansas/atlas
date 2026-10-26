import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.Data

/-! Full-126-root finite certificates, RootReflections part 1. -/
namespace Atlas.Chevalley.E7MinusculeTable.CertificateParts
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem root_reflection_coordinates_8 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 8) = reflectRoot r (coordinates 8) := by decide +kernel
theorem root_reflection_coordinates_9 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 9) = reflectRoot r (coordinates 9) := by decide +kernel
theorem root_reflection_coordinates_10 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 10) = reflectRoot r (coordinates 10) := by decide +kernel
theorem root_reflection_coordinates_11 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 11) = reflectRoot r (coordinates 11) := by decide +kernel
theorem root_reflection_coordinates_12 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 12) = reflectRoot r (coordinates 12) := by decide +kernel
theorem root_reflection_coordinates_13 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 13) = reflectRoot r (coordinates 13) := by decide +kernel
theorem root_reflection_coordinates_14 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 14) = reflectRoot r (coordinates 14) := by decide +kernel
theorem root_reflection_coordinates_15 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 15) = reflectRoot r (coordinates 15) := by decide +kernel

end Atlas.Chevalley.E7MinusculeTable.CertificateParts
