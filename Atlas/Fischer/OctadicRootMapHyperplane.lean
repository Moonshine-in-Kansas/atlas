import Atlas.Fischer.OctadicLocalProduct

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The actual eight-point hyperplane coordinate sum. -/
def octadicHyperplaneAxisSum {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) : Coordinates :=
  octadAxisSum (signedOctadSupport (calibratedHyperplaneLift Q b))

theorem hermitian_octadicRoot_hyperplane {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    hermitian (octadicRoot Q 0) (calibratedHyperplaneVector Q b) = 1 / 2 := by
  have hY : hermitian (octadicHyperplanePart Q 0) (calibratedHyperplaneVector Q b) = 1 := by
    rw [octadicHyperplanePart_zero, hermitian_sum_left]
    simp [calibratedHyperplaneVector_orthonormal]
  rw [octadicRoot_zero_formula, hermitian_smul_left, hermitian_add_left,
    hermitian_add_left, hermitian_smul_left, hermitian_octad_calibratedHyperplane,
    show hermitian (octadicAxisPart O) (calibratedHyperplaneVector Q b) = 0 from
      hermitian_octadicAxis_signedOctad O _, hY]
  ring

theorem product_calibratedHyperplane_diagonal_formula {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    product (calibratedHyperplaneVector Q b) (calibratedHyperplaneVector Q b) =
      (2 : Scalar) • octadicHyperplaneAxisSum Q b - (1 / 2 : Scalar) • axisSum := by
  rw [product_calibratedHyperplane_self, octadBasisProduct, if_pos rfl]
  have hS := octadAxisSum_add_exterior (signedOctadSupport (calibratedHyperplaneLift Q b))
  change (1 / 2 : Scalar) • ((3 : Scalar) • octadicHyperplaneAxisSum Q b -
    octadExteriorAxisSum (signedOctadSupport (calibratedHyperplaneLift Q b))) = _
  rw [← hS]
  change _ = (2 : Scalar) • octadicHyperplaneAxisSum Q b - (1 / 2 : Scalar) •
    (octadicHyperplaneAxisSum Q b + octadExteriorAxisSum
      (signedOctadSupport (calibratedHyperplaneLift Q b)))
  module

/-- Source (5.13), derived from the actual local shortened-code convolution. -/
theorem rootMap_octadic_hyperplane {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    rootMap (octadicRoot Q 0) (calibratedHyperplaneVector Q b) =
      (1 / 2 : Scalar) • ((2 : Scalar) • octadicHyperplaneAxisSum Q b -
        octadExteriorAxisSum O + calibratedHyperplaneVector Q b +
        calibratedHyperplaneVector Q (octadHyperplaneComplement O b)) := by
  have hp : product (calibratedHyperplaneVector Q b)
      (theta • signedOctadVector Q.octadLift) =
      (3 / 2 : Scalar) • calibratedHyperplaneVector Q (octadHyperplaneComplement O b) := by
    have hh := product_theta_octad_hyperplane Q b
      (octadHyperplaneComplement O b) (add_comm _ _)
    rw [product_comm] at hh
    calc
      _ = (1 / 2 : Scalar) • ((2 : Scalar) • product
        (calibratedHyperplaneVector Q b) (theta • signedOctadVector Q.octadLift)) := by
        rw [smul_smul]; norm_num
      _ = _ := by rw [hh, smul_smul]; congr 1; ring
  rw [rootMap, hermitian_octadicRoot_hyperplane]
  conv_lhs => lhs; rhs; rw [octadicRoot_zero_formula]
  rw [product_smul_right, product_add_right, product_add_right,
    product_comm (calibratedHyperplaneVector Q b) (octadicAxisPart O),
    product_octadicAxisPart_hyperplane, hp, product_calibratedHyperplane_hyperplanePart,
    product_calibratedHyperplane_diagonal_formula, octadicRoot_zero_formula,
    ← octadAxisSum_add_exterior O]
  change _ = _
  have hU : octadicAxisPart O = -octadAxisSum O + octadExteriorAxisSum O := rfl
  rw [hU]
  norm_num
  module

end Atlas.Fischer
