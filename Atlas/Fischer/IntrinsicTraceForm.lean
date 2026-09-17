import Atlas.Fischer.ProductTraceCoordinates
import Atlas.Fischer.ProductTraceOffDiagonal
import Atlas.Fischer.ProductTraceAutomorphisms
import Atlas.Fischer.CubicSlicePoints
import Atlas.Fischer.CubicSliceOctads

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

/-- Every actual weighted cubic slice, with its full orthogonality statement. -/
theorem coordinateCubicSlice_eq (i j : CoordinateIndex) :
    coordinateCubicSlice i j = if i = j then 98 * (coordinateWeight i : Scalar) else 0 := by
  classical
  cases i with
  | inl i => cases j with
    | inl j => rw [coordinateCubicSlice_points]; norm_num [coordinateWeight]
    | inr D =>
      rw [← productTrace_coordinateVector, productTrace_octad_point_zero]
      simp
  | inr D => cases j with
    | inl j =>
      rw [← productTrace_coordinateVector, productTrace_point_octad_zero]
      simp
    | inr E =>
      by_cases h : D = E
      · subst E
        rw [coordinateCubicSlice_octad_self]
        norm_num [coordinateWeight]
      · rw [← productTrace_coordinateVector, productTrace_distinct_octads_zero E D (Ne.symm h)]
        simp [h]

/-- The source trace identity for the actual algebra and arbitrary vectors. -/
theorem productTrace_eq_hermitian (x y : Coordinates) :
    productTrace x y = (98 : Scalar) * hermitian y x := by
  classical
  rw [productTrace_coordinate_expansion]
  simp_rw [coordinateCubicSlice_eq]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change (∑ i, star (x i) * y i * (98 * (coordinateWeight i : Scalar))) =
    98 * ∑ i, (coordinateWeight i : Scalar) * y i * star (x i)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem coordinateCubicNorm_eq : coordinateCubicNorm = (76734 : Scalar) := by
  classical
  rw [coordinateCubicNorm]
  simp_rw [coordinateCubicSlice_eq]
  have h (i : CoordinateIndex) :
      inverseCoordinateMetric i * (98 * (coordinateWeight i : Scalar)) = 98 := by
    rw [mul_left_comm, inverseCoordinateMetric_mul, mul_one]
  simp only [ite_true]
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, coordinateIndex_card]
  norm_num

/-- The Hermitian form is intrinsic to the actual algebra multiplication. -/
theorem semilinearAlgebraAutomorphism_hermitian (e : SemilinearAlgebraAutomorphism)
    (x y : Coordinates) : hermitian (e.val x) (e.val y) =
      scalarParityAut (semilinearAlgebraParity e) (hermitian x y) :=
  productTrace_intrinsic_form_of_identity productTrace_eq_hermitian e x y

end Atlas.Fischer
