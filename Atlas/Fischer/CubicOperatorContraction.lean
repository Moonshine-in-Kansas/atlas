import Atlas.Fischer.CubicMetricNormalizationForm
import Atlas.Fischer.RootProductSquare

noncomputable section
namespace Atlas.Fischer
open scoped BigOperators

/-- Exact weighted tensor comparison for three actual coordinate maps. No linearity
of those maps is assumed: cubic multilinearity supplies the operator-slot laws. -/
def cubicOperatorContraction (f g h : Coordinates → Coordinates) : Scalar :=
  ∑ i, ∑ j, ∑ k, inverseCoordinateMetric i * inverseCoordinateMetric j *
    inverseCoordinateMetric k * coordinateCubic i j k *
      cubic (f (coordinateVector i)) (g (coordinateVector j)) (h (coordinateVector k))

theorem cubicOperatorContraction_add_first (f f' g h : Coordinates → Coordinates) :
    cubicOperatorContraction (fun x => f x + f' x) g h =
      cubicOperatorContraction f g h + cubicOperatorContraction f' g h := by
  simp [cubicOperatorContraction, cubic_add_first, mul_add, Finset.sum_add_distrib]

theorem cubicOperatorContraction_add_second (f g g' h : Coordinates → Coordinates) :
    cubicOperatorContraction f (fun x => g x + g' x) h =
      cubicOperatorContraction f g h + cubicOperatorContraction f g' h := by
  simp [cubicOperatorContraction, cubic_add_second, mul_add, Finset.sum_add_distrib]

theorem cubicOperatorContraction_add_third (f g h h' : Coordinates → Coordinates) :
    cubicOperatorContraction f g (fun x => h x + h' x) =
      cubicOperatorContraction f g h + cubicOperatorContraction f g h' := by
  simp [cubicOperatorContraction, cubic_add_third, mul_add, Finset.sum_add_distrib]

theorem cubicOperatorContraction_smul_first (a : Scalar) (f g h : Coordinates → Coordinates) :
    cubicOperatorContraction (fun x => a • f x) g h = a * cubicOperatorContraction f g h := by
  simp only [cubicOperatorContraction, cubic_smul_first, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem cubicOperatorContraction_smul_second (a : Scalar) (f g h : Coordinates → Coordinates) :
    cubicOperatorContraction f (fun x => a • g x) h = a * cubicOperatorContraction f g h := by
  simp only [cubicOperatorContraction, cubic_smul_second, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem cubicOperatorContraction_smul_third (a : Scalar) (f g h : Coordinates → Coordinates) :
    cubicOperatorContraction f g (fun x => a • h x) = a * cubicOperatorContraction f g h := by
  simp only [cubicOperatorContraction, cubic_smul_third, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem cubicOperatorContraction_swap_first (f g h : Coordinates → Coordinates) :
    cubicOperatorContraction f g h = cubicOperatorContraction g f h := by
  unfold cubicOperatorContraction
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [coordinateCubic_swap_first j i k, cubic_swap_first]
  ring

theorem cubicOperatorContraction_swap_last (f g h : Coordinates → Coordinates) :
    cubicOperatorContraction f g h = cubicOperatorContraction f h g := by
  unfold cubicOperatorContraction
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [coordinateCubic_swap_last i k j, cubic_swap_last]
  ring

theorem cubicOperatorContraction_sub_first (f f' g h : Coordinates → Coordinates) :
    cubicOperatorContraction (fun x => f x - f' x) g h =
      cubicOperatorContraction f g h - cubicOperatorContraction f' g h := by
  simp only [cubicOperatorContraction, cubic, hermitian_sub_left, mul_sub, Finset.sum_sub_distrib]

theorem cubicOperatorContraction_sub_second (f g g' h : Coordinates → Coordinates) :
    cubicOperatorContraction f (fun x => g x - g' x) h =
      cubicOperatorContraction f g h - cubicOperatorContraction f g' h := by
  simp only [cubicOperatorContraction, cubic, product_sub_left, hermitian_sub_right,
    mul_sub, Finset.sum_sub_distrib]

theorem cubicOperatorContraction_sub_third (f g h h' : Coordinates → Coordinates) :
    cubicOperatorContraction f g (fun x => h x - h' x) =
      cubicOperatorContraction f g h - cubicOperatorContraction f g h' := by
  simp only [cubicOperatorContraction, cubic, product_sub_right, hermitian_sub_right,
    mul_sub, Finset.sum_sub_distrib]

/-- Full eight-term operator-slot expansion, before any terms are evaluated. -/
theorem cubicOperatorContraction_sub_expansion (L A : Coordinates → Coordinates) :
    cubicOperatorContraction (fun x => L x - A x) (fun x => L x - A x) (fun x => L x - A x) =
      cubicOperatorContraction L L L - cubicOperatorContraction A L L -
      cubicOperatorContraction L A L - cubicOperatorContraction L L A +
      cubicOperatorContraction A A L + cubicOperatorContraction A L A +
      cubicOperatorContraction L A A - cubicOperatorContraction A A A := by
  simp only [cubicOperatorContraction_sub_first, cubicOperatorContraction_sub_second,
    cubicOperatorContraction_sub_third]
  ring

/-- Symmetry collects the full expansion into its rank-one multiplicities. -/
theorem cubicOperatorContraction_sub_symmetric (L A : Coordinates → Coordinates) :
    cubicOperatorContraction (fun x => L x - A x) (fun x => L x - A x) (fun x => L x - A x) =
      cubicOperatorContraction L L L - 3 * cubicOperatorContraction L L A +
        3 * cubicOperatorContraction L A A - cubicOperatorContraction A A A := by
  rw [cubicOperatorContraction_sub_expansion,
    cubicOperatorContraction_swap_first A L L, cubicOperatorContraction_swap_last L A L,
    cubicOperatorContraction_swap_last A A L, cubicOperatorContraction_swap_first A L A]
  ring

end Atlas.Fischer

