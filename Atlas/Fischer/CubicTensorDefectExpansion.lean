import Atlas.Fischer.CubicTensorRootNorm
import Atlas.Fischer.CubicOperatorContractionTwist

noncomputable section
namespace Atlas.Fischer
open scoped BigOperators

/-- The actual weighted defect norm expands into both tensor norms and their two
conjugate comparison terms; no root or antiunitarity assumption is used. -/
theorem rootCubicDefectNorm_expansion (r : Coordinates) :
    rootCubicDefectNorm r = cubicImageNorm (rootMap r) (rootMap r) (rootMap r) +
      coordinateCubicNorm - cubicOperatorContraction (rootMap r) (rootMap r) (rootMap r) -
        star (cubicOperatorContraction (rootMap r) (rootMap r) (rootMap r)) := by
  simp only [rootCubicDefectNorm, weightedHermitian, rootCubicDefect, rootTwistedCubic,
    cubicImageNorm, coordinateCubicNorm, coordinateCubicSlice, cubicOperatorContraction,
    Fintype.sum_prod_type, cubicTensorWeight, Rat.cast_inv, Rat.cast_mul,
    inverseCoordinateMetric, mul_inv_rev, star_sub, star_star, star_sum, star_mul, star_inv₀, star_ratCast,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The defect norm formula after antiunitarity, still with its comparison scalar explicit. -/
theorem rootCubicDefectNorm_antiunitary (r : Coordinates) (ha : RootMapAntiunitary r) :
    rootCubicDefectNorm r = 2 * coordinateCubicNorm -
      cubicOperatorContraction (rootMap r) (rootMap r) (rootMap r) -
        star (cubicOperatorContraction (rootMap r) (rootMap r) (rootMap r)) := by
  rw [rootCubicDefectNorm_expansion, cubicImageNorm_rootMap r ha, cubicImageNorm_id]
  ring

end Atlas.Fischer
