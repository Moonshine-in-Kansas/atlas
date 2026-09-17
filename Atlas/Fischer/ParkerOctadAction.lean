import Atlas.Fischer.ParkerAxisAction
import Atlas.Fischer.ParkerSignedProductTable

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Fischer
open Atlas.Codes

theorem parkerSignedOctadAction_canonical (e : ParkerStandardGroup) (O : Octad) :
    parkerSignedOctadAction e (canonicalOctadLift O) =
      signedOctadSign (parkerCoordinateSign e (.inr O)) (canonicalOctadLift (parkerOctadAction e O)) := by
  apply Subtype.ext
  exact parkerStandard_canonical_octad e O

theorem product_signedOctad_self (d : SignedOctad) :
    product (signedOctadVector d) (signedOctadVector d) =
      octadBasisProduct (signedOctadSupport d) (signedOctadSupport d) := by
  rw [signedOctadVector, product_smul_left, product_smul_right, parkerScalarSign_star,
    product_xOctad, smul_smul, parkerScalarSign_square, one_smul]

theorem parkerCoordinateAction_octadSelfProduct (e : ParkerStandardGroup) (O : Octad) :
    parkerCoordinateAction e (product (xOctad O) (xOctad O)) =
      product (parkerCoordinateAction e (xOctad O)) (parkerCoordinateAction e (xOctad O)) := by
  classical
  rw [product_xOctad, parkerCoordinateAction_xOctad, product_signedOctad_self,
    parkerSignedOctadAction_support, parkerSignedOctadSupport_canonical]
  funext k
  obtain ⟨l, rfl⟩ := (parkerCoordinateEquiv e).surjective k
  rw [parkerCoordinateAction_at_image]
  cases l with
  | inl i =>
    change parkerScalarSign 0 * scalarParityAut (parkerStandardParity e).toAdd
      (octadBasisProduct O O (.inl i)) =
      octadBasisProduct (parkerOctadAction e O) (parkerOctadAction e O)
        (.inl ((parkerStandardProjection e).val i))
    simp only [octadBasisProduct_axis_apply, ite_true, parkerOctadAction_mem]
    by_cases hi : i ∈ O.val <;> simp [hi, parkerScalarSign, map_ofNat]
  | inr P =>
    change _ = octadBasisProduct (parkerOctadAction e O) (parkerOctadAction e O)
      (.inr (parkerOctadAction e P))
    simp [octadBasisProduct, Finset.sum_apply]

theorem parkerOctadAction_ne (e : ParkerStandardGroup) (O P : Octad) (h : O ≠ P) :
    parkerOctadAction e O ≠ parkerOctadAction e P :=
  (parkerOctadEquiv e).injective.ne h

theorem product_transformed_octads_four (e : ParkerStandardGroup) (O P : Octad) (hne : O ≠ P)
    (h : signedOctadIntersection (canonicalOctadLift O) (canonicalOctadLift P) = 4)
    (h' : signedOctadIntersection (parkerSignedOctadAction e (canonicalOctadLift O))
      (parkerSignedOctadAction e (canonicalOctadLift P)) = 4) :
    (2 : Scalar) • product
      (signedOctadVector (parkerSignedOctadAction e (canonicalOctadLift O)))
      (signedOctadVector (parkerSignedOctadAction e (canonicalOctadLift P))) =
      signedOctadVector (octadProductFour
        (parkerSignedOctadAction e (canonicalOctadLift O))
        (parkerSignedOctadAction e (canonicalOctadLift P)) h') := by
  have ht := h'
  rw [parkerSignedOctadAction_canonical, parkerSignedOctadAction_canonical,
    signedOctadIntersection_sign] at ht
  simpa only [parkerSignedOctadAction_canonical] using
    product_signed_sections_four (parkerCoordinateSign e (.inr O))
      (parkerCoordinateSign e (.inr P)) _ _ (parkerOctadAction_ne e O P hne) ht

theorem product_transformed_octads_disjoint (e : ParkerStandardGroup) (O P : Octad) (hne : O ≠ P)
    (h : signedOctadIntersection (canonicalOctadLift O) (canonicalOctadLift P) = 0)
    (h' : signedOctadIntersection (parkerSignedOctadAction e (canonicalOctadLift O))
      (parkerSignedOctadAction e (canonicalOctadLift P)) = 0) :
    (2 : Scalar) • product
      (signedOctadVector (parkerSignedOctadAction e (canonicalOctadLift O)))
      (signedOctadVector (parkerSignedOctadAction e (canonicalOctadLift P))) =
      theta • signedOctadVector (octadProductDisjoint
        (parkerSignedOctadAction e (canonicalOctadLift O))
        (parkerSignedOctadAction e (canonicalOctadLift P)) h') := by
  have ht := h'
  rw [parkerSignedOctadAction_canonical, parkerSignedOctadAction_canonical,
    signedOctadIntersection_sign] at ht
  simpa only [parkerSignedOctadAction_canonical] using
    product_signed_sections_disjoint (parkerCoordinateSign e (.inr O))
      (parkerCoordinateSign e (.inr P)) _ _ (parkerOctadAction_ne e O P hne) ht

end Atlas.Fischer
