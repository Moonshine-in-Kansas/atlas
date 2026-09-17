import Atlas.Fischer.CubicMetricNormalizationTensor

noncomputable section
namespace Atlas.Fischer
open scoped BigOperators

/-- Complex multilinear extension of the actual retained cubic coefficient table. -/
def complexCoordinateCubic (x y z : CoordinateIndex → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, x i * y j * z k * scalarToComplex (coordinateCubic i j k)

theorem cubic_coordinate_expansion (x y z : Coordinates) :
    cubic x y z = ∑ i, ∑ j, ∑ k, x i * y j * z k * coordinateCubic i j k := by
  classical
  have hx : (∑ i, x i • coordinateVector i) = x := by
    simpa only [Pi.basisFun_apply, Pi.basisFun_repr, coordinateVector] using
      (Pi.basisFun Scalar CoordinateIndex).sum_repr x
  have hy : (∑ j, y j • coordinateVector j) = y := by
    simpa only [Pi.basisFun_apply, Pi.basisFun_repr, coordinateVector] using
      (Pi.basisFun Scalar CoordinateIndex).sum_repr y
  have hz : (∑ k, z k • coordinateVector k) = z := by
    simpa only [Pi.basisFun_apply, Pi.basisFun_repr, coordinateVector] using
      (Pi.basisFun Scalar CoordinateIndex).sum_repr z
  have hfirst : cubic x y z = ∑ i, x i * cubic (coordinateVector i) y z := by
    change cubicTrilinear x y z = _
    conv_lhs => rw [← hx]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rfl
  have hsecond (i : CoordinateIndex) :
      cubic (coordinateVector i) y z = ∑ j, y j * cubic (coordinateVector i) (coordinateVector j) z := by
    change cubicTrilinear (coordinateVector i) y z = _
    conv_lhs => rw [← hy]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rfl
  have hthird (i j : CoordinateIndex) :
      cubic (coordinateVector i) (coordinateVector j) z =
        ∑ k, z k * cubic (coordinateVector i) (coordinateVector j) (coordinateVector k) := by
    change cubicTrilinear (coordinateVector i) (coordinateVector j) z = _
    conv_lhs => rw [← hz]
    simp only [map_sum, map_smul, smul_eq_mul]
    rfl
  rw [hfirst]
  simp only [hsecond, hthird, Finset.mul_sum, coordinateCubic, mul_assoc]

/-- This complex cubic extends precisely the project's existing cubic over E. -/
theorem complexCoordinateCubic_embedding (x y z : Coordinates) :
    complexCoordinateCubic (fun i => scalarToComplex (x i))
      (fun i => scalarToComplex (y i)) (fun i => scalarToComplex (z i)) = scalarToComplex (cubic x y z) := by
  rw [cubic_coordinate_expansion]
  simp only [complexCoordinateCubic, map_sum, map_mul]

/-- The normalized coefficients are evaluations of the actual extended cubic on
its actual orthonormal basis. -/
theorem complexCoordinateCubic_normalizedBasis (i j k : CoordinateIndex) :
    complexCoordinateCubic (cubicNormalizedBasis i) (cubicNormalizedBasis j) (cubicNormalizedBasis k) =
      normalizedCoordinateCubic i j k := by
  classical
  simp [complexCoordinateCubic, cubicNormalizedBasis_apply, Pi.single_apply,
    normalizedCoordinateCubic]

end Atlas.Fischer
