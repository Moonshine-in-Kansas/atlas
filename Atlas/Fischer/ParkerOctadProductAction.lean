import Atlas.Fischer.ParkerMonomialData
import Atlas.Fischer.OctadProducts

namespace Atlas.Fischer
open Atlas.Codes

noncomputable def signedOctadSign (s : Bit) (d : SignedOctad) : SignedOctad :=
  ⟨parkerSign s d.val, d.property⟩

theorem signedOctadSign_support (s : Bit) (d : SignedOctad) :
    signedOctadSupport (signedOctadSign s d) = signedOctadSupport d := rfl

theorem signedOctadSign_vector (s : Bit) (d : SignedOctad) :
    signedOctadVector (signedOctadSign s d) = parkerScalarSign s • signedOctadVector d := by
  change parkerScalarSign (d.val.2 + s) • xOctad (signedOctadSupport d) =
    parkerScalarSign s • (parkerScalarSign d.val.2 • xOctad (signedOctadSupport d))
  rw [parkerScalarSign_add, smul_smul]
  rw [mul_comm]

theorem signedOctad_sign_section (d : SignedOctad) :
    d = signedOctadSign d.val.2 (canonicalOctadLift (signedOctadSupport d)) := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply support_injective
    exact (octadWord_support (signedOctadSupport d)).symm
  · change d.val.2 = 0 + d.val.2
    simp

theorem signedOctadIntersection_sign (s t : Bit) (d f : SignedOctad) :
    signedOctadIntersection (signedOctadSign s d) (signedOctadSign t f) =
      signedOctadIntersection d f := rfl

theorem octadProductFour_sign (s t : Bit) (d f : SignedOctad)
    (h : signedOctadIntersection d f = 4)
    (h' : signedOctadIntersection (signedOctadSign s d) (signedOctadSign t f) = 4) :
    octadProductFour (signedOctadSign s d) (signedOctadSign t f) h' =
      signedOctadSign (s + t) (octadProductFour d f h) := by
  apply Subtype.ext
  change parkerLoopMultiply (parkerSign s d.val) (parkerSign t f.val) = _
  rw [parkerLoopMultiply_sign_left, parkerLoopMultiply_sign_right, parkerSign_add]
  rfl

theorem octadProductDisjoint_sign (s t : Bit) (d f : SignedOctad)
    (h : signedOctadIntersection d f = 0)
    (h' : signedOctadIntersection (signedOctadSign s d) (signedOctadSign t f) = 0) :
    octadProductDisjoint (signedOctadSign s d) (signedOctadSign t f) h' =
      signedOctadSign (s + t) (octadProductDisjoint d f h) := by
  apply Subtype.ext
  change parkerLoopMultiply (parkerLoopMultiply (parkerSign s d.val) (parkerSign t f.val))
    parkerOmega = _
  rw [parkerLoopMultiply_sign_left, parkerLoopMultiply_sign_right, parkerSign_add,
    parkerLoopMultiply_sign_left]
  rfl

theorem signedOctadIntersection_action (e : ParkerStandardGroup) (d f : SignedOctad) :
    signedOctadIntersection (parkerSignedOctadAction e d) (parkerSignedOctadAction e f) =
      signedOctadIntersection d f := by
  unfold signedOctadIntersection
  rw [parkerSignedOctadAction_support, parkerSignedOctadAction_support]
  change ((support (d.val.1 : BinaryWord)).image (parkerStandardProjection e).val ∩
    (support (f.val.1 : BinaryWord)).image (parkerStandardProjection e).val).card = _
  rw [← Finset.image_inter _ _ (parkerStandardProjection e).val.injective,
    Finset.card_image_of_injective _ (parkerStandardProjection e).val.injective]
  rfl

theorem parkerOctadProductFour_action (e : ParkerStandardGroup) (d f : SignedOctad)
    (h : signedOctadIntersection d f = 4)
    (h' : signedOctadIntersection (parkerSignedOctadAction e d)
      (parkerSignedOctadAction e f) = 4) :
    parkerSignedOctadAction e (octadProductFour d f h) =
      octadProductFour (parkerSignedOctadAction e d) (parkerSignedOctadAction e f) h' := by
  apply Subtype.ext
  exact e.property.1 d.val f.val

theorem parkerOctadProductDisjoint_action (e : ParkerStandardGroup) (d f : SignedOctad)
    (h : signedOctadIntersection d f = 0)
    (h' : signedOctadIntersection (parkerSignedOctadAction e d)
      (parkerSignedOctadAction e f) = 0) :
    parkerSignedOctadAction e (octadProductDisjoint d f h) =
      signedOctadSign (parkerStandardParity e).toAdd
        (octadProductDisjoint (parkerSignedOctadAction e d) (parkerSignedOctadAction e f) h') := by
  apply Subtype.ext
  change e.val (parkerLoopMultiply (parkerLoopMultiply d.val f.val) parkerOmega) =
    parkerSign (parkerStandardParity e).toAdd
      (parkerLoopMultiply (parkerLoopMultiply (e.val d.val) (e.val f.val)) parkerOmega)
  rw [e.property.1, e.property.1, parkerStandard_omega e, parkerLoopMultiply_sign_right]
  rfl

end Atlas.Fischer
