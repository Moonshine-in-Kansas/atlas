import Atlas.Fischer.CubicOperatorTrace

noncomputable section
namespace Atlas.Fischer
open scoped BigOperators

/-- Evaluation of the actual weighted quintic coefficient tensor on three vectors. -/
def coordinateQuinticEvaluation (x y z : Coordinates) : Scalar :=
  ∑ p, ∑ q, ∑ r, x p * y q * z r * coordinateQuintic p q r

/-- The actual multiplication coefficients are recovered from the retained cubic. -/
theorem rootMultiplication_coordinate (r : Coordinates) (i a : CoordinateIndex) :
    product (coordinateVector i) r a =
      inverseCoordinateMetric a * ∑ p, star (coordinateCubic a i p) * star (r p) := by
  have h : cubic (coordinateVector a) (coordinateVector i) r =
      (coordinateWeight a : Scalar) * star (product (coordinateVector i) r a) :=
    hermitian_coordinateVector_left a _
  rw [cubic_third_basis_expansion] at h
  have hs := congrArg star h
  simp only [star_sum, star_mul, star_ratCast, star_star] at hs
  calc
    _ = inverseCoordinateMetric a * ((coordinateWeight a : Scalar) * product (coordinateVector i) r a) := by
      rw [← mul_assoc, inverseCoordinateMetric_mul, one_mul]
    _ = inverseCoordinateMetric a * (product (coordinateVector i) r a * (coordinateWeight a : Scalar)) := by ring
    _ = _ := by rw [← hs]; rfl

/-- Reordering a finite six-by-three sum. No cardinality or coordinate enumeration is used. -/
theorem sum_six_three_swap {ι A : Type*} [Fintype ι] [AddCommMonoid A]
    (F : ι → ι → ι → ι → ι → ι → ι → ι → ι → A) :
    (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, ∑ p, ∑ q, ∑ r, F i j k a b c p q r) =
      ∑ p, ∑ q, ∑ r, ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, F i j k a b c p q r := by
  have h : (∑ u : ι × ι × ι × ι × ι × ι, ∑ v : ι × ι × ι,
      F u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2.1 u.2.2.2.2.2 v.1 v.2.1 v.2.2) =
      ∑ v : ι × ι × ι, ∑ u : ι × ι × ι × ι × ι × ι,
      F u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2.1 u.2.2.2.2.2 v.1 v.2.1 v.2.2 := Finset.sum_comm
  simpa only [Fintype.sum_prod_type] using h


theorem sum_three_reverse {ι A : Type*} [Fintype ι] [AddCommMonoid A]
    (F : ι → ι → ι → A) : (∑ p, ∑ q, ∑ s, F p q s) = ∑ p, ∑ q, ∑ s, F s q p := by
  calc
    _ = ∑ q, ∑ p, ∑ s, F p q s := Finset.sum_comm
    _ = ∑ q, ∑ s, ∑ p, F p q s := by
      apply Finset.sum_congr rfl
      intro q hq
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Exact convention for the zero-rank-one contraction.
 This is the conjugate
of quintic evaluation, not quintic evaluation itself. -/
theorem cubicOperatorContraction_three_multiplication (r : Coordinates) :
    cubicOperatorContraction (rootMultiplicationOperator r) (rootMultiplicationOperator r)
      (rootMultiplicationOperator r) = star (coordinateQuinticEvaluation r r r) := by
  unfold cubicOperatorContraction
  simp only [rootMultiplicationOperator, cubic_coordinate_expansion,
    rootMultiplication_coordinate, Finset.mul_sum, Finset.sum_mul]
  rw [sum_six_three_swap]
  conv_rhs => rw [coordinateQuinticEvaluation, sum_three_reverse]
  simp only [coordinateQuinticEvaluation, coordinateQuintic, star_sum, star_mul,
    star_star, inverseCoordinateMetric_star, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem coordinateQuinticEvaluation_eq_cubic (hK : ∀ p q r,
    coordinateQuintic p q r = (1002 : Scalar) * coordinateCubic p q r)
    (x y z : Coordinates) : coordinateQuinticEvaluation x y z = (1002 : Scalar) * cubic x y z := by
  simp only [coordinateQuinticEvaluation, hK, cubic_coordinate_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem cubicOperatorContraction_three_multiplication_eq
    (hK : ∀ p q r, coordinateQuintic p q r = (1002 : Scalar) * coordinateCubic p q r)
    (r : Coordinates) (hn : hermitian r r = 9) (he : product r r = (10 : Scalar) • r) :
    cubicOperatorContraction (rootMultiplicationOperator r) (rootMultiplicationOperator r)
      (rootMultiplicationOperator r) = 90180 := by
  rw [cubicOperatorContraction_three_multiplication, coordinateQuinticEvaluation_eq_cubic hK,
    cubic_root_value r hn he]
  norm_num

/-- All four contraction families combine, with the unproved global quintic identity explicit. -/
theorem cubicOperatorContraction_rootMap_eq
    (hK : ∀ p q r, coordinateQuintic p q r = (1002 : Scalar) * coordinateCubic p q r)
    (r : Coordinates) (hn : hermitian r r = 9) (he : product r r = (10 : Scalar) • r)
    (ha : RootMapAntiunitary r) : cubicOperatorContraction (rootMap r) (rootMap r) (rootMap r) = 76734 := by
  rw [cubicOperatorContraction_rootMap_partial r hn he,
    cubicOperatorContraction_three_multiplication_eq hK r hn he,
    cubicOperatorContraction_two_multiplication_eq r hn he ha]
  norm_num

end Atlas.Fischer
