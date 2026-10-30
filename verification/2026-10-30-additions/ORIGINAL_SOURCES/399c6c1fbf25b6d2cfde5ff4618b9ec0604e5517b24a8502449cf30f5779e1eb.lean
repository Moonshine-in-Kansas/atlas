import Atlas.LinearGroups.Chevalley.Comparison.G2.IntegralBasisData

namespace Atlas.Chevalley.Comparison.G2
open scoped Matrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- Unimodular left inverse; hence no loss of dimension at p=2 or p=3. -/
theorem readCoordinates_basis : ∀ (i j : Fin 14),
    readCoordinates (basisMatrix j) i = if i=j then 1 else 0 := by
  decide +kernel

end Atlas.Chevalley.Comparison.G2
