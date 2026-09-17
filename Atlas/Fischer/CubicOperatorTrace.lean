import Atlas.Fischer.CubicOperatorContractionRankOne

noncomputable section
namespace Atlas.Fischer
open scoped BigOperators

theorem cubic_third_basis_expansion (x y r : Coordinates) :
    cubic x y r = ∑ k, r k * cubic x y (coordinateVector k) := by
  have hr : (∑ k, r k • coordinateVector k) = r := by
    simpa only [Pi.basisFun_apply, Pi.basisFun_repr, coordinateVector] using
      (Pi.basisFun Scalar CoordinateIndex).sum_repr r
  change cubicTrilinear x y r = _
  conv_lhs => rw [← hr]
  simp only [map_sum, map_smul, smul_eq_mul]
  rfl

/-- One actual rank-one slot contracts the third cubic index against r. -/
theorem cubicOperatorContraction_rankOne_last (r : Coordinates) (f g : Coordinates → Coordinates) :
    cubicOperatorContraction f g (rootAntilinearRankOne r) =
      ∑ i, ∑ j, inverseCoordinateMetric i * inverseCoordinateMetric j *
        cubic (coordinateVector i) (coordinateVector j) r *
          cubic (f (coordinateVector i)) (g (coordinateVector j)) r := by
  unfold cubicOperatorContraction
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [cubic_third_basis_expansion (coordinateVector i) (coordinateVector j) r]
  simp only [rootAntilinearRankOne, cubic_smul_third, rootHermitian_basis_right,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  change inverseCoordinateMetric i * inverseCoordinateMetric j * inverseCoordinateMetric k *
      coordinateCubic i j k * ((coordinateWeight k : Scalar) * r k * _) = _
  calc
    _ = inverseCoordinateMetric i * inverseCoordinateMetric j *
        (inverseCoordinateMetric k * (coordinateWeight k : Scalar)) *
        (r k * coordinateCubic i j k) * cubic (f (coordinateVector i)) (g (coordinateVector j)) r := by ring
    _ = _ := by rw [inverseCoordinateMetric_mul]; simp only [coordinateCubic]; ring

/-- Actual multiplication is conjugate-linear in basis coordinates. -/
theorem rootMultiplication_basis_expansion (r x : Coordinates) :
    product x r = ∑ i, star (x i) • product (coordinateVector i) r := by
  have hx : (∑ i, x i • coordinateVector i) = x := by
    simpa only [Pi.basisFun_apply, Pi.basisFun_repr, coordinateVector] using
      (Pi.basisFun Scalar CoordinateIndex).sum_repr x
  conv_lhs => rw [← hx]
  rw [product_sum_left]
  simp only [product_smul_left]

/-- Cubic symmetry makes L_r squared self-adjoint for the actual Hermitian form. -/
theorem rootMultiplication_square_selfAdjoint (r x y : Coordinates) :
    hermitian (product (product x r) r) y = hermitian x (product (product y r) r) := by
  calc
    _ = star (hermitian y (product (product x r) r)) := (hermitian_star _ _).symm
    _ = star (hermitian (product x r) (product y r)) :=
      congrArg star (cubic_swap_first y (product x r) r)
    _ = hermitian (product y r) (product x r) := hermitian_star _ _
    _ = _ := (cubic_swap_first x (product y r) r).symm

/-- The two-multiplication/one-rank-one contraction is the squared Hilbert--Schmidt
norm of the actual linear map L_r squared, in the retained weighted basis. -/
theorem cubicOperatorContraction_two_multiplication_norm (r : Coordinates) :
    cubicOperatorContraction (rootMultiplicationOperator r) (rootMultiplicationOperator r)
      (rootAntilinearRankOne r) =
      ∑ j, inverseCoordinateMetric j *
        hermitian (productLeftComposite r r (coordinateVector j))
          (productLeftComposite r r (coordinateVector j)) := by
  rw [cubicOperatorContraction_rankOne_last, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hs : (∑ i, star ((product (coordinateVector j) r) i) *
      hermitian (product (coordinateVector i) r) (productLeftComposite r r (coordinateVector j))) =
      hermitian (productLeftComposite r r (coordinateVector j))
        (productLeftComposite r r (coordinateVector j)) := by
    have hm := rootMultiplication_basis_expansion r (product (coordinateVector j) r)
    have he : (∑ i, star ((product (coordinateVector j) r) i) • product (coordinateVector i) r) =
        productLeftComposite r r (coordinateVector j) := hm.symm
    simpa only [hermitian_sum_left, hermitian_smul_left] using congrArg
      (fun x => hermitian x (productLeftComposite r r (coordinateVector j))) he
  rw [← hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change inverseCoordinateMetric i * inverseCoordinateMetric j *
    hermitian (coordinateVector i) (product (coordinateVector j) r) *
      hermitian (product (coordinateVector i) r) (productLeftComposite r r (coordinateVector j)) = _
  rw [hermitian_coordinateVector_left]
  calc
    _ = (inverseCoordinateMetric i * (coordinateWeight i : Scalar)) * inverseCoordinateMetric j *
        (star ((product (coordinateVector j) r) i) *
          hermitian (product (coordinateVector i) r) (productLeftComposite r r (coordinateVector j))) := by ring
    _ = _ := by rw [inverseCoordinateMetric_mul, one_mul]

/-- Exact convention: this operator contraction is the conjugate of tr(L_r^4).
No root equation or antiunitarity is required for the identity. -/
theorem cubicOperatorContraction_two_multiplication_trace (r : Coordinates) :
    cubicOperatorContraction (rootMultiplicationOperator r) (rootMultiplicationOperator r)
      (rootAntilinearRankOne r) =
      star (LinearMap.trace Scalar Coordinates ((productLeftComposite r r) ^ 2)) := by
  rw [cubicOperatorContraction_two_multiplication_norm, coordinateLinearMap_trace, star_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change inverseCoordinateMetric j * hermitian (product (product (coordinateVector j) r) r)
    (productLeftComposite r r (coordinateVector j)) = _
  rw [rootMultiplication_square_selfAdjoint, hermitian_coordinateVector_left]
  change inverseCoordinateMetric j * ((coordinateWeight j : Scalar) *
    star (((productLeftComposite r r) ^ 2) (coordinateVector j) j)) = _
  rw [← mul_assoc, inverseCoordinateMetric_mul, one_mul]

theorem cubicOperatorContraction_two_multiplication_eq (r : Coordinates) (hn : hermitian r r = 9)
    (he : product r r = (10 : Scalar) • r) (ha : RootMapAntiunitary r) :
    cubicOperatorContraction (rootMultiplicationOperator r) (rootMultiplicationOperator r)
      (rootAntilinearRankOne r) = 10782 := by
  rw [cubicOperatorContraction_two_multiplication_trace, rootProduct_square_trace_square r hn he ha]
  norm_num

end Atlas.Fischer
