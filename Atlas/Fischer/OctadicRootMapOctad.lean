import Atlas.Fischer.OctadicRootMapAxes
import Atlas.Fischer.BasicCocodeComparison

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem rootMap_sum {ι : Type*} (r : Coordinates) (s : Finset ι) (f : ι → Coordinates) :
    rootMap r (∑ i ∈ s, f i) = ∑ i ∈ s, rootMap r (f i) :=
  map_sum (rootMapSemilinear r) f s

theorem hermitian_octadicRoot_calibratedOctad {O : Octad} (Q : OctadCalibration O) :
    hermitian (octadicRoot Q 0) (signedOctadVector Q.octadLift) = theta / 2 := by
  have hY : hermitian (octadicHyperplanePart Q 0) (signedOctadVector Q.octadLift) = 0 := by
    rw [← hermitian_star, hermitian_octad_hyperplanePart, star_zero]
  rw [octadicRoot_zero_formula, hermitian_smul_left, hermitian_add_left,
    hermitian_add_left, hermitian_octadicAxis_signedOctad, hermitian_smul_left,
    signedOctadVector_norm, hY]
  ring

theorem product_calibratedOctad_hyperplanePart {O : Octad} (Q : OctadCalibration O) :
    product (signedOctadVector Q.octadLift) (octadicHyperplanePart Q 0) =
      (theta / 2) • octadicHyperplanePart Q 0 := by
  have hs : (2 : Scalar) • product (signedOctadVector Q.octadLift) (octadicHyperplanePart Q 0) =
      theta • octadicHyperplanePart Q 0 := by
    rw [octadicHyperplanePart_zero, product_sum_right, Finset.smul_sum]
    have hh (b : OctadShortenedHyperplane O) :
        (2 : Scalar) • product (signedOctadVector Q.octadLift) (calibratedHyperplaneVector Q b) =
          theta • calibratedHyperplaneVector Q (octadHyperplaneComplement O b) :=
      product_calibrated_octad_hyperplane Q b _ (add_comm _ _)
    simp_rw [hh]
    rw [← Finset.smul_sum, calibratedHyperplaneVector_sum_complement]
  calc
    _ = (1 / 2 : Scalar) • ((2 : Scalar) • product
      (signedOctadVector Q.octadLift) (octadicHyperplanePart Q 0)) := by
      rw [smul_smul]; norm_num
    _ = _ := by rw [hs, smul_smul]; congr 1; ring

theorem theta_half_smul_octadicRoot {O : Octad} (Q : OctadCalibration O) :
    (theta / 2) • octadicRoot Q 0 = (theta / 4) • octadicAxisPart O -
      (3 / 4 : Scalar) • signedOctadVector Q.octadLift +
      (theta / 4) • octadicHyperplanePart Q 0 := by
  rw [octadicRoot_zero_formula]
  simp only [smul_add, smul_smul]
  have hθ : theta / 2 * (1 / 2 * theta) = (-3 / 4 : Scalar) := by
    calc
      _ = theta ^ 2 / 4 := by ring
      _ = _ := by rw [theta_sq]
  rw [hθ]
  module

/-- Source (5.11), on the actual calibrated signed-octad coordinate. -/
theorem rootMap_octadic_octad {O : Octad} (Q : OctadCalibration O) :
    rootMap (octadicRoot Q 0) (signedOctadVector Q.octadLift) =
      (-theta / 2) • octadAxisSum O - (1 / 2 : Scalar) • signedOctadVector Q.octadLift := by
  have hp : product (signedOctadVector Q.octadLift) (signedOctadVector Q.octadLift) =
      (1 / 2 : Scalar) • ((3 : Scalar) • octadAxisSum O - octadExteriorAxisSum O) := by
    rw [← product_calibratedOctad_self Q, smul_smul]
    norm_num
  rw [rootMap, hermitian_octadicRoot_calibratedOctad, theta_half_smul_octadicRoot]
  conv_lhs => lhs; rhs; rw [octadicRoot_zero_formula]
  rw [product_smul_right, product_add_right, product_add_right,
    product_comm (signedOctadVector Q.octadLift) (octadicAxisPart O),
    product_octadicAxisPart_octad, product_smul_right, hp, theta_conjugate,
    product_calibratedOctad_hyperplanePart]
  change _ = _
  have hU : octadicAxisPart O = -octadAxisSum O + octadExteriorAxisSum O := rfl
  rw [hU]
  norm_num
  module

theorem rootMap_octadic_octadAxisSum {O : Octad} (Q : OctadCalibration O) :
    rootMap (octadicRoot Q 0) (octadAxisSum O) =
      (-1 / 2 : Scalar) • octadAxisSum O - (theta / 2) • signedOctadVector Q.octadLift := by
  rw [octadAxisSum, rootMap_sum]
  rw [Finset.sum_congr rfl (rootMap_octadic_inside_axis Q)]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, octad_size O.val O.property]
  change octadAxisSum O - (8 : ℕ) • ((3 / 16 : Scalar) • octadAxisSum O) -
    (8 : ℕ) • ((theta / 16) • signedOctadVector Q.octadLift) =
      (-1 / 2 : Scalar) • octadAxisSum O - (theta / 2) • signedOctadVector Q.octadLift
  module

end Atlas.Fischer
