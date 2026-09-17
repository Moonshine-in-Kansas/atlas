import Atlas.Fischer.CubicOperatorContraction

noncomputable section
namespace Atlas.Fischer
open scoped BigOperators

/-- The actual conjugate-linear rank-one part subtracted from multiplication. -/
def rootAntilinearRankOne (r x : Coordinates) : Coordinates := hermitian r x • r

def rootMultiplicationOperator (r x : Coordinates) : Coordinates := product x r

theorem rootMap_eq_operator_difference (r : Coordinates) :
    rootMap r = fun x => rootMultiplicationOperator r x - rootAntilinearRankOne r x := rfl

theorem rootHermitian_basis_right (r : Coordinates) (i : CoordinateIndex) :
    hermitian r (coordinateVector i) = (coordinateWeight i : Scalar) * r i := by
  rw [← hermitian_star (coordinateVector i) r, hermitian_coordinateVector_left,
    star_mul, star_ratCast, star_star]
  ring

/-- Contraction of three actual rank-one coefficients recovers cubic evaluation. -/
theorem cubic_rankOne_coefficient_sum (r : Coordinates) :
    (∑ i, ∑ j, ∑ k, inverseCoordinateMetric i * inverseCoordinateMetric j *
      inverseCoordinateMetric k * coordinateCubic i j k * hermitian r (coordinateVector i) *
        hermitian r (coordinateVector j) * hermitian r (coordinateVector k)) = cubic r r r := by
  rw [cubic_coordinate_expansion]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  simp only [rootHermitian_basis_right]
  calc
    _ = (inverseCoordinateMetric i * (coordinateWeight i : Scalar)) *
        (inverseCoordinateMetric j * (coordinateWeight j : Scalar)) *
        (inverseCoordinateMetric k * (coordinateWeight k : Scalar)) *
        (r i * r j * r k * coordinateCubic i j k) := by ring
    _ = _ := by simp only [inverseCoordinateMetric_mul, one_mul]

theorem cubicOperatorContraction_all_rankOne (r : Coordinates) :
    cubicOperatorContraction (rootAntilinearRankOne r) (rootAntilinearRankOne r)
      (rootAntilinearRankOne r) = cubic r r r ^ 2 := by
  simp only [cubicOperatorContraction, rootAntilinearRankOne,
    cubic_smul_first, cubic_smul_second, cubic_smul_third]
  have he : (∑ i, ∑ j, ∑ k, inverseCoordinateMetric i * inverseCoordinateMetric j *
      inverseCoordinateMetric k * coordinateCubic i j k *
      (hermitian r (coordinateVector k) * (hermitian r (coordinateVector j) *
        (hermitian r (coordinateVector i) * cubic r r r)))) =
      (∑ i, ∑ j, ∑ k, inverseCoordinateMetric i * inverseCoordinateMetric j *
        inverseCoordinateMetric k * coordinateCubic i j k * hermitian r (coordinateVector i) *
          hermitian r (coordinateVector j) * hermitian r (coordinateVector k)) * cubic r r r := by
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he, cubic_rankOne_coefficient_sum, pow_two]

theorem cubic_root_value (r : Coordinates) (hn : hermitian r r = 9)
    (he : product r r = (10 : Scalar) • r) : cubic r r r = 90 := by
  rw [cubic, he, hermitian_smul_right, hn]
  norm_num

theorem cubicOperatorContraction_all_rankOne_eq (r : Coordinates) (hn : hermitian r r = 9)
    (he : product r r = (10 : Scalar) • r) :
    cubicOperatorContraction (rootAntilinearRankOne r) (rootAntilinearRankOne r)
      (rootAntilinearRankOne r) = 8100 := by
  rw [cubicOperatorContraction_all_rankOne, cubic_root_value r hn he]
  norm_num

theorem cubic_rootMultiplication_two_roots (r x : Coordinates)
    (he : product r r = (10 : Scalar) • r) :
    cubic (rootMultiplicationOperator r x) r r = (100 : Scalar) * hermitian r x := by
  change hermitian (product x r) (product r r) = _
  rw [he, hermitian_smul_right, ← hermitian_star r (product x r), rootProduct_pairing r x he,
    star_mul, hermitian_star]
  norm_num
  ring

theorem cubicOperatorContraction_one_multiplication (r : Coordinates)
    (he : product r r = (10 : Scalar) • r) :
    cubicOperatorContraction (rootMultiplicationOperator r) (rootAntilinearRankOne r)
      (rootAntilinearRankOne r) = (100 : Scalar) * cubic r r r := by
  simp only [cubicOperatorContraction, rootAntilinearRankOne, cubic_smul_second,
    cubic_smul_third, cubic_rootMultiplication_two_roots r _ he]
  rw [← cubic_rankOne_coefficient_sum r]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem cubicOperatorContraction_one_multiplication_eq (r : Coordinates) (hn : hermitian r r = 9)
    (he : product r r = (10 : Scalar) • r) :
    cubicOperatorContraction (rootMultiplicationOperator r) (rootAntilinearRankOne r)
      (rootAntilinearRankOne r) = 9000 := by
  rw [cubicOperatorContraction_one_multiplication r he, cubic_root_value r hn he]
  norm_num

/-- The actual root-map comparison with the two completed rank-one term families.
The three-L and two-L terms are deliberately still explicit obligations. -/
theorem cubicOperatorContraction_rootMap_partial (r : Coordinates) (hn : hermitian r r = 9)
    (he : product r r = (10 : Scalar) • r) :
    cubicOperatorContraction (rootMap r) (rootMap r) (rootMap r) =
      cubicOperatorContraction (rootMultiplicationOperator r) (rootMultiplicationOperator r)
        (rootMultiplicationOperator r) -
      3 * cubicOperatorContraction (rootMultiplicationOperator r) (rootMultiplicationOperator r)
        (rootAntilinearRankOne r) + 18900 := by
  rw [rootMap_eq_operator_difference, cubicOperatorContraction_sub_symmetric,
    cubicOperatorContraction_one_multiplication_eq r hn he,
    cubicOperatorContraction_all_rankOne_eq r hn he]
  ring

end Atlas.Fischer
