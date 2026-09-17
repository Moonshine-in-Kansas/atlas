import Atlas.Fischer.CubicMetricNormalization
import Atlas.Algebra.HermitianQuadraticBound

noncomputable section
namespace Atlas.Fischer
open scoped BigOperators

/-- The actual weighted coordinates in the retained complex orthonormal basis. -/
def reflectingRootEuclidean (x : Coordinates) : EuclideanSpace ℂ CoordinateIndex :=
  WithLp.toLp 2 (fun i => scalarToComplex (x i) / cubicMetricScale i)

/-- Mathlib conjugates the first entry; the retained form conjugates the second. -/
theorem reflectingRootEuclidean_inner (x y : Coordinates) :
    inner ℂ (reflectingRootEuclidean x) (reflectingRootEuclidean y) =
      scalarToComplex (hermitian y x) := by
  rw [← complexCoordinateHermitian_embedding]
  simp only [PiLp.inner_apply, RCLike.inner_apply', complexCoordinateHermitian]
  apply Finset.sum_congr rfl
  intro i _
  change star (scalarToComplex (x i) / cubicMetricScale i) *
    (scalarToComplex (y i) / cubicMetricScale i) = _
  rw [star_div₀, cubicMetricScale_star]
  have hm : cubicMetricScale i ^ 2 * (coordinateWeight i : ℂ) = 1 := by
    rw [cubicMetricScale_sq]
    simpa only [map_mul, map_one, map_ratCast] using
      congrArg scalarToComplex (inverseCoordinateMetric_mul i)
  have hs := cubicMetricScale_ne_zero i
  field_simp
  linear_combination -(scalarToComplex (y i) * star (scalarToComplex (x i))) * hm

end Atlas.Fischer
