import Atlas.Fischer.OctadicHyperplaneAxisPairings
import Atlas.Fischer.OctadicCharacterPairings

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem hermitian_hyperplanePart_pair {O : Octad} (Q : OctadCalibration O)
    (χ ψ : OctadicCharacter O) :
    hermitian (octadicHyperplanePart Q χ) (octadicHyperplanePart Q ψ) =
      ∑ b : OctadShortenedHyperplane O, parkerScalarSign (χ b.val) * parkerScalarSign (ψ b.val) := by
  simp only [octadicHyperplanePart, hermitian_sum_left, hermitian_sum_right,
    hermitian_smul_left, hermitian_smul_right, parkerScalarSign_star,
    calibratedHyperplaneVector_orthonormal, mul_ite, mul_one, mul_zero, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_comm]

theorem hermitian_axisSum_hyperplanePart (A : Finset Omega) {O : Octad}
    (Q : OctadCalibration O) (χ : OctadicCharacter O) :
    hermitian (∑ i ∈ A, u i) (octadicHyperplanePart Q χ) = 0 := by
  simp only [octadicHyperplanePart, hermitian_sum_left, hermitian_sum_right,
    hermitian_smul_right, calibratedHyperplaneVector, hermitian_u_signedOctad,
    mul_zero, Finset.sum_const_zero]

theorem hermitian_hyperplanePart_axisSum {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (A : Finset Omega) :
    hermitian (octadicHyperplanePart Q χ) (∑ i ∈ A, u i) = 0 := by
  rw [← hermitian_star, hermitian_axisSum_hyperplanePart, star_zero]

/-- Pairings of the sixteen actual exterior axes after applying the reflection. -/
theorem rootMap_octadic_exterior_axis_pairing {O : Octad} (Q : OctadCalibration O)
    (i j : OctadExterior O) :
    hermitian (rootMap (octadicRoot Q 0) (u i.val))
      (rootMap (octadicRoot Q 0) (u j.val)) = star (hermitian (u i.val) (u j.val)) := by
  rw [rootMap_octadic_outside_axis, rootMap_octadic_outside_axis]
  simp only [hermitian_smul_left, hermitian_smul_right, hermitian_sub_left,
    hermitian_sub_right, octadExteriorAxisSum_norm,
    show hermitian (octadExteriorAxisSum O) (octadicHyperplanePart Q (octadEvaluation O j)) = 0 from
      hermitian_axisSum_hyperplanePart _ Q _,
    show hermitian (octadicHyperplanePart Q (octadEvaluation O i)) (octadExteriorAxisSum O) = 0 from
      hermitian_hyperplanePart_axisSum Q _ _, hermitian_hyperplanePart_pair,
    octadEvaluation_hyperplane_sign_pair_sum, hermitian_u]
  have he : i.val = j.val ↔ i = j := Subtype.ext_iff.symm
  simp only [he]
  split_ifs <;> norm_num


theorem hermitian_hyperplanePart_hyperplane {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (b : OctadShortenedHyperplane O) :
    hermitian (octadicHyperplanePart Q χ) (calibratedHyperplaneVector Q b) =
      parkerScalarSign (χ b.val) := by
  simp only [octadicHyperplanePart, hermitian_sum_left, hermitian_smul_left,
    calibratedHyperplaneVector_orthonormal, mul_ite, mul_one, mul_zero, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_comm]

theorem octadEvaluation_sign_complement (O : Octad) (i : OctadExterior O)
    (b : OctadShortenedHyperplane O) :
    parkerScalarSign (octadEvaluation O i (octadHyperplaneComplement O b).val) =
      -parkerScalarSign (octadEvaluation O i b.val) := by
  change parkerScalarSign (octadEvaluation O i (b.val + octadShortenedOne O)) = _
  rw [map_add, octadEvaluation_one, add_comm, parkerScalarSign_one_add]

theorem hermitian_exterior_hyperplaneAxisVector {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    hermitian (octadExteriorAxisSum O) (octadicHyperplaneAxisVector Q b) = 0 := by
  rw [octadicHyperplaneAxisVector, hermitian_sub_right, hermitian_smul_right,
    hermitian_exterior_hyperplaneAxis, octadExteriorAxisSum_norm]
  norm_num

theorem hermitian_hyperplanePart_hyperplaneAxisVector {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (b : OctadShortenedHyperplane O) :
    hermitian (octadicHyperplanePart Q χ) (octadicHyperplaneAxisVector Q b) = 0 := by
  rw [octadicHyperplaneAxisVector, hermitian_sub_right, hermitian_smul_right]
  change star (2 : Scalar) * hermitian (octadicHyperplanePart Q χ)
    (∑ i ∈ (signedOctadSupport (calibratedHyperplaneLift Q b)).val, u i) -
    hermitian (octadicHyperplanePart Q χ) (∑ i ∈ O.valᶜ, u i) = 0
  rw [hermitian_hyperplanePart_axisSum, hermitian_hyperplanePart_axisSum]
  ring

/-- Exterior-axis and hyperplane images remain orthogonal in the actual coordinates. -/
theorem rootMap_octadic_exterior_hyperplane_pairing {O : Octad} (Q : OctadCalibration O)
    (i : OctadExterior O) (b : OctadShortenedHyperplane O) :
    hermitian (rootMap (octadicRoot Q 0) (u i.val))
      (rootMap (octadicRoot Q 0) (calibratedHyperplaneVector Q b)) = 0 := by
  rw [rootMap_octadic_outside_axis, rootMap_octadic_hyperplane]
  change hermitian ((1 / 16 : Scalar) • (octadExteriorAxisSum O -
      octadicHyperplanePart Q (octadEvaluation O i)))
    ((1 / 2 : Scalar) • (octadicHyperplaneAxisVector Q b + calibratedHyperplaneVector Q b +
      calibratedHyperplaneVector Q (octadHyperplaneComplement O b))) = 0
  simp only [hermitian_smul_left, hermitian_smul_right, hermitian_sub_left,
    hermitian_add_right, hermitian_exterior_hyperplaneAxisVector,
    hermitian_hyperplanePart_hyperplaneAxisVector]
  have hz (c : OctadShortenedHyperplane O) :
      hermitian (octadExteriorAxisSum O) (calibratedHyperplaneVector Q c) = 0 := by
    simp only [octadExteriorAxisSum, hermitian_sum_left, calibratedHyperplaneVector,
      hermitian_u_signedOctad, Finset.sum_const_zero]
  rw [hz, hz, hermitian_hyperplanePart_hyperplane, hermitian_hyperplanePart_hyperplane,
    octadEvaluation_sign_complement]
  ring

end Atlas.Fischer

