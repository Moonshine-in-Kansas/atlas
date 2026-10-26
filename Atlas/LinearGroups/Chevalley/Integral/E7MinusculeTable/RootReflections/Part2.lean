import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.Data

/-! Full-126-root finite certificates, RootReflections part 2. -/
namespace Atlas.Chevalley.E7MinusculeTable.CertificateParts
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem root_reflection_coordinates_16 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 16) = reflectRoot r (coordinates 16) := by decide +kernel
theorem root_reflection_coordinates_17 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 17) = reflectRoot r (coordinates 17) := by decide +kernel
theorem root_reflection_coordinates_18 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 18) = reflectRoot r (coordinates 18) := by decide +kernel
theorem root_reflection_coordinates_19 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 19) = reflectRoot r (coordinates 19) := by decide +kernel
theorem root_reflection_coordinates_20 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 20) = reflectRoot r (coordinates 20) := by decide +kernel
theorem root_reflection_coordinates_21 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 21) = reflectRoot r (coordinates 21) := by decide +kernel
theorem root_reflection_coordinates_22 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 22) = reflectRoot r (coordinates 22) := by decide +kernel
theorem root_reflection_coordinates_23 : ∀ r : CorootIndex, coordinates (rootReflectionIndex r 23) = reflectRoot r (coordinates 23) := by decide +kernel

end Atlas.Chevalley.E7MinusculeTable.CertificateParts
