import Atlas.Fischer.OctadicCrossingAxis
import Atlas.Fischer.SignedOctadCrossingProducts
import Atlas.Fischer.OctadicRootEquations

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem crossingSignedOctad_ne_calibration {O : Octad} (Q : OctadCalibration O)
    (d : SignedOctad) (h : signedOctadIntersection d Q.octadLift ≠ 8) :
    signedOctadSupport d ≠ signedOctadSupport Q.octadLift :=
  signedOctadSupport_ne_of_intersection d Q.octadLift h

theorem crossingSignedOctad_ne_hyperplane {O : Octad} (Q : OctadCalibration O)
    (d : SignedOctad) (h : signedOctadIntersection d Q.octadLift ≠ 0)
    (b : OctadShortenedHyperplane O) :
    signedOctadSupport d ≠ signedOctadSupport (calibratedHyperplaneLift Q b) := by
  intro he
  apply h
  have ho : signedOctadSupport Q.octadLift = O :=
    (signedOctadSupport_eq_iff _ _).mpr Q.lift_code
  unfold signedOctadIntersection
  rw [he,ho,Finset.inter_comm,
    Finset.disjoint_iff_inter_eq_empty.mp (calibratedHyperplaneSupport_disjoint Q b)]
  rfl

theorem hermitian_signedOctads_distinct (d f : SignedOctad)
    (h : signedOctadSupport d ≠ signedOctadSupport f) :
    hermitian (signedOctadVector d) (signedOctadVector f) = 0 := by
  simp only [signedOctadVector,hermitian_smul_left,hermitian_smul_right,
    hermitian_xOctad,ite_eq_right h,mul_zero]

theorem hermitian_octadicRoot_crossing {O : Octad} (Q : OctadCalibration O)
    (d : SignedOctad) (h0 : signedOctadIntersection d Q.octadLift ≠ 0)
    (h8 : signedOctadIntersection d Q.octadLift ≠ 8) :
    hermitian (octadicRoot Q 0) (signedOctadVector d) = 0 := by
  have ho := hermitian_signedOctads_distinct Q.octadLift d
    (Ne.symm (crossingSignedOctad_ne_calibration Q d h8))
  have hb (b : OctadShortenedHyperplane O) :
      hermitian (calibratedHyperplaneVector Q b) (signedOctadVector d) = 0 :=
    hermitian_signedOctads_distinct _ d (Ne.symm (crossingSignedOctad_ne_hyperplane Q d h0 b))
  rw [octadicRoot_zero_formula,hermitian_smul_left,hermitian_add_left,
    hermitian_add_left,hermitian_octadicAxis_signedOctad,hermitian_smul_left,ho,
    octadicHyperplanePart_zero,hermitian_sum_left]
  simp only [hb,Finset.sum_const_zero,mul_zero,zero_add]

end Atlas.Fischer
