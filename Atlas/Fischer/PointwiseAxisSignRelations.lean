import Atlas.Fischer.PointwiseAxisSignCharacter
import Atlas.Fischer.SignedOctadProductFormulas
import Atlas.Fischer.CubicTriangleModels

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The diagonal sign action also holds for the retained signed Parker labels. -/
theorem pointwiseAxis_signedOctad_action (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i)=u i) (d : SignedOctad) :
    e.val (signedOctadVector d)=
      parkerScalarSign (pointwiseAxisOctadSign e (signedOctadSupport d)) • signedOctadVector d := by
  rw [signedOctadVector,semilinearAlgebraParity_spec,scalarParityAut_sign,
    pointwiseAxisOctadSign_action e he]
  rw [smul_smul,smul_smul,mul_comm]

/-- Actual intersection-four products force the additive relation on signs. -/
theorem pointwiseAxis_signed_four_relation (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i)=u i) (d f : SignedOctad)
    (h4 : signedOctadIntersection d f=4) :
    pointwiseAxisOctadSign e (signedOctadSupport (octadProductFour d f h4))=
      pointwiseAxisOctadSign e (signedOctadSupport d)+
        pointwiseAxisOctadSign e (signedOctadSupport f) := by
  have hp := product_signedOctads_four d f h4
  have h := congrArg (productTraceAlgebraEquiv e) hp
  simp only [map_smulₛₗ] at h
  change scalarParityAut (semilinearAlgebraParity e) 2 •
    e.val (product (signedOctadVector d) (signedOctadVector f))=
      e.val (signedOctadVector (octadProductFour d f h4)) at h
  rw [map_ofNat,e.property.2.1,pointwiseAxis_signedOctad_action e he,
    pointwiseAxis_signedOctad_action e he,pointwiseAxis_signedOctad_action e he,
    product_smul_left,product_smul_right,parkerScalarSign_star,parkerScalarSign_star] at h
  have hh : (parkerScalarSign (pointwiseAxisOctadSign e (signedOctadSupport d)) *
      parkerScalarSign (pointwiseAxisOctadSign e (signedOctadSupport f))) •
      signedOctadVector (octadProductFour d f h4)=
    parkerScalarSign (pointwiseAxisOctadSign e (signedOctadSupport (octadProductFour d f h4))) •
      signedOctadVector (octadProductFour d f h4) := by
    calc
      _ = (parkerScalarSign (pointwiseAxisOctadSign e (signedOctadSupport d)) *
        parkerScalarSign (pointwiseAxisOctadSign e (signedOctadSupport f))) •
        ((2 : Scalar) • product (signedOctadVector d) (signedOctadVector f)) := by rw [hp]
      _ = (2 : Scalar) • parkerScalarSign (pointwiseAxisOctadSign e (signedOctadSupport d)) •
        parkerScalarSign (pointwiseAxisOctadSign e (signedOctadSupport f)) •
        product (signedOctadVector d) (signedOctadVector f) := by module
      _ = _ := h
  have hn : signedOctadVector (octadProductFour d f h4) ≠ 0 := by
    intro hz
    have hh := signedOctadVector_norm (octadProductFour d f h4)
    rw [hz] at hh
    simp at hh
  have hs := smul_left_injective Scalar hn hh
  apply parkerScalarSign_injective
  rw [parkerScalarSign_add]
  exact hs.symm

/-- The exact sign relation in the source's actual sextet-completion interface. -/
theorem pointwiseAxisOctadSign_four (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i)=u i) (D E : Octad) (h : (D.val ∩ E.val).card=4) :
    pointwiseAxisOctadSign e (cubicSextetCompletion D E h)=
      pointwiseAxisOctadSign e D+pointwiseAxisOctadSign e E := by
  have h4 : signedOctadIntersection (canonicalOctadLift D) (canonicalOctadLift E)=4 := by
    simpa [signedOctadIntersection,parkerSignedOctadSupport_canonical] using h
  have hs : signedOctadSupport (octadProductFour (canonicalOctadLift D) (canonicalOctadLift E) h4)=
      cubicSextetCompletion D E h := by
    apply octadWord_injective
    rw [cubicSextetCompletion_word]
    apply Subtype.ext
    apply support_injective
    exact octadWord_support _
  have hh := pointwiseAxis_signed_four_relation e he (canonicalOctadLift D) (canonicalOctadLift E) h4
  rw [hs] at hh
  simpa only [parkerSignedOctadSupport_canonical] using hh

end Atlas.Fischer
