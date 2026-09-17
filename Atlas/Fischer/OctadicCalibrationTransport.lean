import Atlas.Fischer.OctadicRootCoordinates
import Atlas.Fischer.OctadSectionTransport

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Transporting a calibration includes the parity correction on the octad
lift, since the actual standard group need not fix Ω. -/
def octadCalibrationTransport (e : ParkerStandardGroup) {O : Octad} (Q : OctadCalibration O) :
    OctadCalibration (parkerOctadAction e O) where
  octadLift := signedOctadSign (e.val parkerOmega).2 (parkerSignedOctadAction e Q.octadLift)
  lift_code := by
    change (e.val Q.octadLift.val).1 = _
    rw [parkerStandardProjection_spec, Q.lift_code, parkerOctadWord_action]
  parkerSection := octadSectionTransport e O Q.parkerSection
  calibrated := octadSectionTransport_calibration e O Q.parkerSection Q.octadLift.val Q.calibrated

def octadHyperplaneTransport (e : ParkerStandardGroup) (O : Octad) :
    OctadShortenedHyperplane O ≃ OctadShortenedHyperplane (parkerOctadAction e O) :=
  (octadShortenedTransport e O).toEquiv.subtypeEquiv (by
    intro b
    change (b ≠ 0 ∧ b ≠ octadShortenedOne O) ↔
      (octadShortenedTransport e O b ≠ 0 ∧
        octadShortenedTransport e O b ≠ octadShortenedOne (parkerOctadAction e O))
    constructor
    · rintro ⟨hz, hX⟩
      constructor
      · intro h
        exact hz ((octadShortenedTransport e O).injective
          (h.trans (map_zero (octadShortenedTransport e O)).symm))
      · intro h
        exact hX ((octadShortenedTransport e O).injective
          (h.trans (octadShortenedTransport_one e O).symm))
    · rintro ⟨hz, hX⟩
      constructor
      · intro h
        apply hz
        rw [h, map_zero]
      · intro h
        apply hX
        rw [h, octadShortenedTransport_one])

@[simp] theorem octadHyperplaneTransport_val (e : ParkerStandardGroup) (O : Octad)
    (b : OctadShortenedHyperplane O) :
    (octadHyperplaneTransport e O b).val = octadShortenedTransport e O b.val := rfl

theorem octadicCharacterTransport_apply (e : ParkerStandardGroup) (O : Octad)
    (χ : OctadicCharacter O) (b : octadShortenedCode O) :
    (octadCharacterPullback e O).symm χ (octadShortenedTransport e O b) = χ b := by
  change χ ((octadShortenedTransport e O).symm (octadShortenedTransport e O b)) = χ b
  rw [LinearEquiv.symm_apply_apply]

theorem octadicCharacterTransport_one (e : ParkerStandardGroup) (O : Octad)
    (χ : OctadicCharacter O) :
    (octadCharacterPullback e O).symm χ (octadShortenedOne (parkerOctadAction e O)) =
      χ (octadShortenedOne O) := by
  rw [← octadShortenedTransport_one e O, octadicCharacterTransport_apply]

theorem calibratedHyperplaneLift_transport (e : ParkerStandardGroup) {O : Octad}
    (Q : OctadCalibration O) (b : OctadShortenedHyperplane O) :
    calibratedHyperplaneLift (octadCalibrationTransport e Q) (octadHyperplaneTransport e O b) =
      parkerSignedOctadAction e (calibratedHyperplaneLift Q b) :=
  Subtype.ext (octadSectionTransport_lift_image e O Q.parkerSection b.val)

end Atlas.Fischer
