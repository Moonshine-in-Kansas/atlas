import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.Data

/-! Full-126-root finite certificates, RootReflections part 3. -/
namespace Atlas.Chevalley.E7MinusculeTable.CertificateParts
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem root_reflection_coordinates_24 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 24) = reflectRoot r (coordinates 24) := by decide +kernel
theorem root_reflection_coordinates_25 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 25) = reflectRoot r (coordinates 25) := by decide +kernel
theorem root_reflection_coordinates_26 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 26) = reflectRoot r (coordinates 26) := by decide +kernel
theorem root_reflection_coordinates_27 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 27) = reflectRoot r (coordinates 27) := by decide +kernel
theorem root_reflection_coordinates_28 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 28) = reflectRoot r (coordinates 28) := by decide +kernel
theorem root_reflection_coordinates_29 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 29) = reflectRoot r (coordinates 29) := by decide +kernel
theorem root_reflection_coordinates_30 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 30) = reflectRoot r (coordinates 30) := by decide +kernel
theorem root_reflection_coordinates_31 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 31) = reflectRoot r (coordinates 31) := by decide +kernel

end Atlas.Chevalley.E7MinusculeTable.CertificateParts
