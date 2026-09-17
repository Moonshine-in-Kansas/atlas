import Atlas.Fischer.OctadicCalibratedProducts
import Atlas.Fischer.OctadicNormCalculation
import Atlas.Fischer.OctadHyperplanePairs
import Atlas.Fischer.ProductMaps

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem octadicHyperplanePart_zero {O : Octad} (Q : OctadCalibration O) :
    octadicHyperplanePart Q 0 = ∑ b : OctadShortenedHyperplane O, calibratedHyperplaneVector Q b := by
  simp [octadicHyperplanePart, parkerScalarSign]

theorem calibratedHyperplaneVector_sum_complement {O : Octad} (Q : OctadCalibration O) :
    (∑ b : OctadShortenedHyperplane O, calibratedHyperplaneVector Q (octadHyperplaneComplement O b)) =
      ∑ b : OctadShortenedHyperplane O, calibratedHyperplaneVector Q b :=
  Fintype.sum_equiv ((octadHyperplaneComplement_involutive O).toPerm _) _ _ (fun _ => rfl)

/-- Fifth row of the source square table, with the exact calibrated Parker sign. -/
theorem product_theta_octad_hyperplanePart {O : Octad} (Q : OctadCalibration O) :
    (2 : Scalar) • product (theta • signedOctadVector Q.octadLift) (octadicHyperplanePart Q 0) =
      (3 : Scalar) • octadicHyperplanePart Q 0 := by
  rw [octadicHyperplanePart_zero, product_sum_right, Finset.smul_sum]
  have hh (b : OctadShortenedHyperplane O) :
      (2 : Scalar) • product (theta • signedOctadVector Q.octadLift) (calibratedHyperplaneVector Q b) =
        (3 : Scalar) • calibratedHyperplaneVector Q (octadHyperplaneComplement O b) :=
    product_theta_octad_hyperplane Q b _ (add_comm _ _)
  simp_rw [hh]
  rw [← Finset.smul_sum, calibratedHyperplaneVector_sum_complement]

end Atlas.Fischer
