import Atlas.Fischer.CubicOperatorContractionRankOne
import Atlas.Fischer.CubicDefectCriterion

noncomputable section
namespace Atlas.Fischer
open scoped BigOperators

/-- The exact operator contraction is the weighted Hermitian tensor comparison
with the conjugated, transformed cubic. The double conjugation is explicit. -/
theorem cubicOperatorContraction_rootTwisted (r : Coordinates) :
    cubicOperatorContraction (rootMap r) (rootMap r) (rootMap r) =
      ∑ i, ∑ j, ∑ k, inverseCoordinateMetric i * inverseCoordinateMetric j *
        inverseCoordinateMetric k * coordinateCubic i j k *
          star (rootTwistedCubic r (coordinateVector i) (coordinateVector j) (coordinateVector k)) := by
  simp only [cubicOperatorContraction, rootTwistedCubic, star_star]

end Atlas.Fischer
