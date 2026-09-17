import Atlas.Fischer.OctadicCrossingOrthogonality

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Literal Parker labels in the intersection-four branch of the product table. -/
def signedOctadFourContribution (d f : SignedOctad) : Coordinates :=
  if h : signedOctadIntersection d f = 4 then
    signedOctadVector (octadProductFour d f h) else 0

/-- Literal Parker labels in the disjoint branch, before its theta coefficient. -/
def signedOctadDisjointContribution (d f : SignedOctad) : Coordinates :=
  if h : signedOctadIntersection d f = 0 then
    signedOctadVector (octadProductDisjoint d f h) else 0

theorem product_signedOctads_contributions (d f : SignedOctad)
    (hne : signedOctadSupport d ≠ signedOctadSupport f) :
    product (signedOctadVector d) (signedOctadVector f) =
      (1 / 2 : Scalar) • (signedOctadFourContribution d f +
        theta • signedOctadDisjointContribution d f) := by
  have h := product_signedOctads_distinct d f hne
  have hd : (if h : signedOctadIntersection d f = 0 then
        theta • signedOctadVector (octadProductDisjoint d f h) else 0) =
      theta • signedOctadDisjointContribution d f := by
    unfold signedOctadDisjointContribution
    split_ifs <;> simp
  rw [hd] at h
  change (2 : Scalar) • product (signedOctadVector d) (signedOctadVector f) =
    signedOctadFourContribution d f + theta • signedOctadDisjointContribution d f at h
  rw [← h,smul_smul]
  norm_num

/-- Source (5.14): the actual root map on every crossing signed octad.
The two finite sums retain the actual Parker products, including all signs. -/
theorem rootMap_octadic_crossing {O : Octad} (Q : OctadCalibration O)
    (d : SignedOctad) (h0 : signedOctadIntersection d Q.octadLift ≠ 0)
    (h8 : signedOctadIntersection d Q.octadLift ≠ 8) :
    rootMap (octadicRoot Q 0) (signedOctadVector d) =
      ((3 - (signedOctadIntersection d Q.octadLift : Scalar)) / 4) • signedOctadVector d -
      (theta / 4) • signedOctadFourContribution d Q.octadLift +
      (1 / 4 : Scalar) • (∑ b : OctadShortenedHyperplane O,
        signedOctadFourContribution d (calibratedHyperplaneLift Q b)) +
      (theta / 4) • (∑ b : OctadShortenedHyperplane O,
        signedOctadDisjointContribution d (calibratedHyperplaneLift Q b)) := by
  have ho : signedOctadSupport Q.octadLift = O :=
    (signedOctadSupport_eq_iff _ _).mpr Q.lift_code
  have hi : (O.val ∩ (signedOctadSupport d).val).card =
      signedOctadIntersection d Q.octadLift := by
    unfold signedOctadIntersection
    rw [ho,Finset.inter_comm]
  have hd : signedOctadDisjointContribution d Q.octadLift = 0 := by
    simp only [signedOctadDisjointContribution,dif_neg h0]
  have hp := product_signedOctads_contributions d Q.octadLift
    (crossingSignedOctad_ne_calibration Q d h8)
  rw [hd,smul_zero,add_zero] at hp
  have hb (b : OctadShortenedHyperplane O) :=
    product_signedOctads_contributions d (calibratedHyperplaneLift Q b)
      (crossingSignedOctad_ne_hyperplane Q d h0 b)
  rw [rootMap,hermitian_octadicRoot_crossing Q d h0 h8,zero_smul,sub_zero,
    octadicRoot_zero_formula,product_smul_right,product_add_right,product_add_right,
    product_comm (signedOctadVector d) (octadicAxisPart O),
    product_octadicAxisPart_signedOctad,hi,product_smul_right,theta_conjugate,hp,
    octadicHyperplanePart_zero,product_sum_right]
  simp only [calibratedHyperplaneVector,hb,Finset.sum_add_distrib,
    smul_add,← Finset.smul_sum]
  norm_num only [star_div₀,star_one,star_ofNat]
  module

end Atlas.Fischer
