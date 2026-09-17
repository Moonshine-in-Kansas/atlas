import Atlas.Fischer.CubicSymmetry
import Atlas.Fischer.CoordinateHermitianSums

noncomputable section
namespace Atlas.Fischer
open scoped BigOperators

/-- The cubic coefficients in the actual, unnormalized retained coordinate basis. -/
def coordinateCubic (i j k : CoordinateIndex) : Scalar :=
  cubic (coordinateVector i) (coordinateVector j) (coordinateVector k)

/-- Inverse diagonal metric. This is 8 on point coordinates and 1 on octads. -/
def inverseCoordinateMetric (i : CoordinateIndex) : Scalar :=
  (coordinateWeight i : Scalar)⁻¹

theorem coordinateMetric_ne_zero (i : CoordinateIndex) :
    (coordinateWeight i : Scalar) ≠ 0 := by
  cases i <;> norm_num [coordinateWeight]

theorem inverseCoordinateMetric_mul (i : CoordinateIndex) :
    inverseCoordinateMetric i * (coordinateWeight i : Scalar) = 1 :=
  inv_mul_cancel₀ (coordinateMetric_ne_zero i)

theorem inverseCoordinateMetric_star (i : CoordinateIndex) :
    star (inverseCoordinateMetric i) = inverseCoordinateMetric i := by
  simp only [inverseCoordinateMetric, star_inv₀, star_ratCast]

theorem coordinateCubic_swap_first (i j k : CoordinateIndex) :
    coordinateCubic i j k = coordinateCubic j i k := cubic_swap_first _ _ _

theorem coordinateCubic_swap_last (i j k : CoordinateIndex) :
    coordinateCubic i j k = coordinateCubic i k j := cubic_swap_last _ _ _

/-- The exact coefficient table recovers multiplication, with the first-slot
Hermitian convention and its required conjugation. -/
theorem basisProduct_from_coordinateCubic (i j k : CoordinateIndex) :
    basisProduct j k i = inverseCoordinateMetric i * star (coordinateCubic i j k) := by
  rw [coordinateCubic, cubic, product_coordinateVector, hermitian_coordinateVector_left]
  simp only [star_mul, star_star, star_ratCast]
  rw [mul_comm (basisProduct j k i), ← mul_assoc, inverseCoordinateMetric_mul, one_mul]

/-- Weighted contraction of two slices in the retained E-coordinate basis.
Each summed index contributes the inverse of its actual metric weight. -/
def coordinateCubicSlice (i j : CoordinateIndex) : Scalar :=
  ∑ a, ∑ b, inverseCoordinateMetric a * inverseCoordinateMetric b *
    coordinateCubic i a b * star (coordinateCubic j a b)

/-- Squared tensor norm expressed over E, without adjoining square roots of weights. -/
def coordinateCubicNorm : Scalar :=
  ∑ i, inverseCoordinateMetric i * coordinateCubicSlice i i

/-- The source's ordered six-index contraction, in the original weighted basis.
Every contracted index occurs twice and carries exactly one inverse metric. -/
def coordinateQuintic (p q r : CoordinateIndex) : Scalar :=
  ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
    inverseCoordinateMetric i * inverseCoordinateMetric j * inverseCoordinateMetric k *
    inverseCoordinateMetric a * inverseCoordinateMetric b * inverseCoordinateMetric c *
    star (coordinateCubic i j k) * star (coordinateCubic a b c) *
    coordinateCubic a i p * coordinateCubic b j q * coordinateCubic c k r

end Atlas.Fischer
