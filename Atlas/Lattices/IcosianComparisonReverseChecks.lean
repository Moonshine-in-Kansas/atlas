import Atlas.Lattices.IcosianComparisonGeneratorsData
import Atlas.Lattices.IcosianComparisonSpace

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped Matrix

theorem icosianComparisonPreimage_mem (j : Fin 38) :
    icosianComparisonPreimage j ∈ icosianLeechModule := by
  rw [icosianLeechModule_mem,icosianP_mem,icosianP_mem,icosianPZero_mem]
  simp only [icosianComparisonPreimage,map_sub,map_add,icosianModuloTwo_synthesis,
    Matrix.sub_apply,Matrix.add_apply]
  revert j
  decide +kernel

theorem icosianComparison_preimage_arithmetic : ∀ j : Fin 38,
    icosianComparisonMatrix *ᵥ icosianRealCoordinates
      (icosianCoordinateEmbedding (icosianComparisonPreimage j)) =
    rationalEmbedding (icosianComparisonTargetGenerator j) := by
  decide +kernel

theorem icosianComparison_preimage_check (j : Fin 38) :
    icosianComparison (icosianCoordinateEmbedding (icosianComparisonPreimage j)) =
      rationalEmbedding (icosianComparisonTargetGenerator j) :=
  icosianComparison_preimage_arithmetic j

end Atlas.Lattices
