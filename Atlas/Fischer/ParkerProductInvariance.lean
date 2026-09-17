import Atlas.Fischer.ParkerOctadAction
import Atlas.Fischer.ProductMaps

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Fischer
open Atlas.Codes

theorem parkerCoordinateAction_two_smul (e : ParkerStandardGroup) (x : Coordinates) :
    parkerCoordinateAction e ((2 : Scalar) • x) = (2 : Scalar) • parkerCoordinateAction e x := by
  rw [map_smulₛₗ]
  simp [map_ofNat]

theorem parkerCoordinateAction_octadFourProduct (e : ParkerStandardGroup) (O P : Octad)
    (hne : O ≠ P)
    (h : signedOctadIntersection (canonicalOctadLift O) (canonicalOctadLift P) = 4) :
    parkerCoordinateAction e (product (xOctad O) (xOctad P)) =
      product (parkerCoordinateAction e (xOctad O)) (parkerCoordinateAction e (xOctad P)) := by
  have h' : signedOctadIntersection (parkerSignedOctadAction e (canonicalOctadLift O))
      (parkerSignedOctadAction e (canonicalOctadLift P)) = 4 := by
    rw [signedOctadIntersection_action]
    exact h
  apply smul_right_injective Coordinates (by norm_num : (2 : Scalar) ≠ 0)
  change (2 : Scalar) • parkerCoordinateAction e (product (xOctad O) (xOctad P)) =
    (2 : Scalar) • product (parkerCoordinateAction e (xOctad O))
      (parkerCoordinateAction e (xOctad P))
  rw [← parkerCoordinateAction_two_smul, product_octad_four O P hne h,
    parkerCoordinateAction_signedOctad,
    parkerOctadProductFour_action e _ _ h h', parkerCoordinateAction_xOctad,
    parkerCoordinateAction_xOctad]
  exact (product_transformed_octads_four e O P hne h h').symm

theorem parkerCoordinateAction_octadDisjointProduct (e : ParkerStandardGroup) (O P : Octad)
    (hne : O ≠ P)
    (h : signedOctadIntersection (canonicalOctadLift O) (canonicalOctadLift P) = 0) :
    parkerCoordinateAction e (product (xOctad O) (xOctad P)) =
      product (parkerCoordinateAction e (xOctad O)) (parkerCoordinateAction e (xOctad P)) := by
  have h' : signedOctadIntersection (parkerSignedOctadAction e (canonicalOctadLift O))
      (parkerSignedOctadAction e (canonicalOctadLift P)) = 0 := by
    rw [signedOctadIntersection_action]
    exact h
  have ht : (parkerScalarSign (parkerStandardParity e).toAdd * theta) *
      parkerScalarSign (parkerStandardParity e).toAdd = theta := by
    calc
      _ = (parkerScalarSign (parkerStandardParity e).toAdd *
          parkerScalarSign (parkerStandardParity e).toAdd) * theta := by ring
      _ = _ := by rw [parkerScalarSign_square, one_mul]
  have hφ : (scalarParityAut (parkerStandardParity e).toAdd).toRingHom theta =
      parkerScalarSign (parkerStandardParity e).toAdd * theta := scalarParityAut_theta _
  apply smul_right_injective Coordinates (by norm_num : (2 : Scalar) ≠ 0)
  change (2 : Scalar) • parkerCoordinateAction e (product (xOctad O) (xOctad P)) =
    (2 : Scalar) • product (parkerCoordinateAction e (xOctad O))
      (parkerCoordinateAction e (xOctad P))
  rw [← parkerCoordinateAction_two_smul, product_octad_disjoint O P hne h,
    map_smulₛₗ, hφ, parkerCoordinateAction_signedOctad,
    parkerOctadProductDisjoint_action e _ _ h h', signedOctadSign_vector,
    smul_smul, ht, parkerCoordinateAction_xOctad, parkerCoordinateAction_xOctad]
  exact (product_transformed_octads_disjoint e O P hne h h').symm

theorem parkerCoordinateAction_octadOtherProduct (e : ParkerStandardGroup) (O P : Octad)
    (hne : O ≠ P)
    (h4 : signedOctadIntersection (canonicalOctadLift O) (canonicalOctadLift P) ≠ 4)
    (h0 : signedOctadIntersection (canonicalOctadLift O) (canonicalOctadLift P) ≠ 0) :
    parkerCoordinateAction e (product (xOctad O) (xOctad P)) =
      product (parkerCoordinateAction e (xOctad O)) (parkerCoordinateAction e (xOctad P)) := by
  classical
  have hi : signedOctadIntersection (canonicalOctadLift (parkerOctadAction e O))
      (canonicalOctadLift (parkerOctadAction e P)) =
        signedOctadIntersection (canonicalOctadLift O) (canonicalOctadLift P) := by
    have hh := signedOctadIntersection_action e (canonicalOctadLift O) (canonicalOctadLift P)
    simpa only [parkerSignedOctadAction_canonical, signedOctadIntersection_sign] using hh
  rw [product_xOctad]
  simp only [octadBasisProduct, if_neg hne, dif_neg h4, dif_neg h0, map_zero]
  rw [parkerCoordinateAction_xOctad, parkerCoordinateAction_xOctad,
    parkerSignedOctadAction_canonical, parkerSignedOctadAction_canonical,
    signedOctadSign_vector, signedOctadSign_vector, signedOctadVector_canonical,
    signedOctadVector_canonical, product_smul_left, product_smul_right, product_xOctad]
  simp [octadBasisProduct, parkerOctadAction_ne e O P hne, hi, h4, h0]

theorem parkerCoordinateAction_octadProduct (e : ParkerStandardGroup) (O P : Octad) :
    parkerCoordinateAction e (product (xOctad O) (xOctad P)) =
      product (parkerCoordinateAction e (xOctad O)) (parkerCoordinateAction e (xOctad P)) := by
  classical
  by_cases he : O = P
  · subst P
    exact parkerCoordinateAction_octadSelfProduct e O
  by_cases h4 : signedOctadIntersection (canonicalOctadLift O) (canonicalOctadLift P) = 4
  · exact parkerCoordinateAction_octadFourProduct e O P he h4
  by_cases h0 : signedOctadIntersection (canonicalOctadLift O) (canonicalOctadLift P) = 0
  · exact parkerCoordinateAction_octadDisjointProduct e O P he h0
  exact parkerCoordinateAction_octadOtherProduct e O P he h4 h0

end Atlas.Fischer
