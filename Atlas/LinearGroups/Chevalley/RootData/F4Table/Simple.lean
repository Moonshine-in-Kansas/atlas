import Atlas.LinearGroups.Chevalley.RootData.F4Table.Data

/-! F4 root certificate component: Simple. -/
namespace Atlas.Chevalley.F4Table
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem simple_coordinates : ∀ i : Fin 4, coordinates (simpleIndex i) = Pi.single i 1 := by decide +kernel
theorem simple_coroot_coefficients : ∀ i : Fin 4, corootCoefficientCoordinates (simpleIndex i) = Pi.single i 1 := by decide +kernel
theorem simple_dual_coordinates : ∀ i j : Fin 4, dualCoordinates (simpleIndex i) j = cartan j i := by decide +kernel

end Atlas.Chevalley.F4Table
