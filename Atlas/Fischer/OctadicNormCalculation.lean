import Atlas.Fischer.OctadicOrthogonality
import Atlas.Fischer.OctadHyperplaneCounts
import Atlas.Fischer.SignedMonomialGeometry

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

def octadicHyperplanePart {O : Octad} (Q : OctadCalibration O) (χ : OctadicCharacter O) :
    Coordinates := ∑ b : OctadShortenedHyperplane O,
      parkerScalarSign (χ b.val) • calibratedHyperplaneVector Q b

theorem octadicHyperplanePart_norm {O : Octad} (Q : OctadCalibration O) (χ : OctadicCharacter O) :
    hermitian (octadicHyperplanePart Q χ) (octadicHyperplanePart Q χ) =
      (Fintype.card (OctadShortenedHyperplane O) : Scalar) := by
  rw [octadicHyperplanePart, hermitian_orthonormal_sum _ (by
    intro b c
    by_cases h : b = c <;> simpa only [h, ite_true, ite_false] using
      calibratedHyperplaneVector_orthonormal Q b c)]
  simp only [parkerScalarSign_star, parkerScalarSign_square, Finset.sum_const, Finset.card_univ]
  simp

theorem hermitian_octadicAxis_hyperplanePart {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) : hermitian (octadicAxisPart O) (octadicHyperplanePart Q χ) = 0 := by
  simp only [octadicHyperplanePart, hermitian_sum_right, hermitian_smul_right,
    calibratedHyperplaneVector, hermitian_octadicAxis_signedOctad, mul_zero, Finset.sum_const_zero]

theorem hermitian_octad_hyperplanePart {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) :
    hermitian (signedOctadVector Q.octadLift) (octadicHyperplanePart Q χ) = 0 := by
  simp only [octadicHyperplanePart, hermitian_sum_right, hermitian_smul_right,
    hermitian_octad_calibratedHyperplane, mul_zero, Finset.sum_const_zero]

theorem octadicThetaPart_norm {O : Octad} (Q : OctadCalibration O) (χ : OctadicCharacter O) :
    hermitian ((theta * parkerScalarSign (χ (octadShortenedOne O))) • signedOctadVector Q.octadLift)
      ((theta * parkerScalarSign (χ (octadShortenedOne O))) • signedOctadVector Q.octadLift) = 3 := by
  rw [hermitian_smul_left, hermitian_smul_right, signedOctadVector_norm, mul_one,
    star_mul, parkerScalarSign_star, theta_conjugate]
  calc
    _ = -(theta ^ 2) * (parkerScalarSign (χ (octadShortenedOne O)) *
      parkerScalarSign (χ (octadShortenedOne O))) := by ring
    _ = 3 := by rw [theta_sq, parkerScalarSign_square]; norm_num

/-- The norm calculation is independent of the splitting and of the character.
The actual shortened-code cardinality supplies the final value nine. -/
theorem octadicRoot_norm_formula {O : Octad} (Q : OctadCalibration O) (χ : OctadicCharacter O) :
    hermitian (octadicRoot Q χ) (octadicRoot Q χ) =
      (6 + (Fintype.card (OctadShortenedHyperplane O) : Scalar)) / 4 := by
  let U := octadicAxisPart O
  let T := (theta * parkerScalarSign (χ (octadShortenedOne O))) • signedOctadVector Q.octadLift
  let Y := octadicHyperplanePart Q χ
  have hUT : hermitian U T = 0 := by
    dsimp [U, T]
    rw [hermitian_smul_right, hermitian_octadicAxis_signedOctad, mul_zero]
  have hUY : hermitian U Y = 0 := hermitian_octadicAxis_hyperplanePart Q χ
  have hTY : hermitian T Y = 0 := by
    dsimp [T, Y]
    rw [hermitian_smul_left, hermitian_octad_hyperplanePart, mul_zero]
  have hTU : hermitian T U = 0 := by rw [← hermitian_star, hUT, star_zero]
  have hYU : hermitian Y U = 0 := by rw [← hermitian_star, hUY, star_zero]
  have hYT : hermitian Y T = 0 := by rw [← hermitian_star, hTY, star_zero]
  change hermitian ((1 / 2 : Scalar) • (U + T + Y)) ((1 / 2 : Scalar) • (U + T + Y)) = _
  rw [hermitian_smul_left, hermitian_smul_right]
  simp only [hermitian_add_left, hermitian_add_right, hUT, hUY, hTY, hTU, hYU, hYT,
    show hermitian U U = 3 from octadicAxisPart_norm O,
    show hermitian T T = 3 from octadicThetaPart_norm Q χ,
    show hermitian Y Y = _ from octadicHyperplanePart_norm Q χ]
  norm_num
  ring

theorem octadicRoot_norm {O : Octad} (Q : OctadCalibration O) (χ : OctadicCharacter O) :
    hermitian (octadicRoot Q χ) (octadicRoot Q χ) = 9 := by
  rw [octadicRoot_norm_formula, octadShortenedHyperplane_card]
  norm_num

end Atlas.Fischer
