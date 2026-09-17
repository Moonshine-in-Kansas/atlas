import Atlas.Fischer.OctadicCalibrationTransport
import Atlas.Fischer.OctadicRootFibres

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem parkerCoordinateAction_octadicAxisPart (e : ParkerStandardGroup) (O : Octad) :
    parkerCoordinateAction e (octadicAxisPart O) = octadicAxisPart (parkerOctadAction e O) := by
  classical
  let g := (parkerStandardProjection e).val
  have hc : O.valᶜ.image g = (O.val.image g)ᶜ := by
    ext i
    obtain ⟨j, rfl⟩ := g.surjective i
    simp [g.injective.eq_iff]
  simp only [octadicAxisPart, map_add, map_neg, map_sum, parkerCoordinateAction_u]
  change -(∑ i ∈ O.val, u (g i)) + ∑ i ∈ O.valᶜ, u (g i) =
    -(∑ i ∈ O.val.image g, u i) + ∑ i ∈ (O.val.image g)ᶜ, u i
  rw [← hc, Finset.sum_image g.injective.injOn, Finset.sum_image g.injective.injOn]

theorem parkerCoordinateAction_calibratedHyperplane (e : ParkerStandardGroup) {O : Octad}
    (Q : OctadCalibration O) (b : OctadShortenedHyperplane O) :
    parkerCoordinateAction e (calibratedHyperplaneVector Q b) =
      calibratedHyperplaneVector (octadCalibrationTransport e Q) (octadHyperplaneTransport e O b) := by
  rw [calibratedHyperplaneVector, parkerCoordinateAction_signedOctad]
  exact congrArg signedOctadVector (calibratedHyperplaneLift_transport e Q b).symm

theorem parkerCoordinateAction_octadicHyperplanePart (e : ParkerStandardGroup) {O : Octad}
    (Q : OctadCalibration O) (χ : OctadicCharacter O) :
    parkerCoordinateAction e (octadicHyperplanePart Q χ) =
      octadicHyperplanePart (octadCalibrationTransport e Q) ((octadCharacterPullback e O).symm χ) := by
  classical
  simp only [octadicHyperplanePart, map_sum, map_smulₛₗ,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, scalarParityAut_sign,
    parkerCoordinateAction_calibratedHyperplane]
  apply Fintype.sum_equiv (octadHyperplaneTransport e O)
  intro b
  rw [octadHyperplaneTransport_val, octadicCharacterTransport_apply]
  rw [parkerCoordinateAction_calibratedHyperplane e Q b]

/-- Full transport of the literal octadic vector formula by the actual standard
group, with the required parity correction on the calibrated lift. -/
theorem parkerCoordinateAction_octadicRoot (e : ParkerStandardGroup) {O : Octad}
    (Q : OctadCalibration O) (χ : OctadicCharacter O) :
    parkerCoordinateAction e (octadicRoot Q χ) =
      octadicRoot (octadCalibrationTransport e Q) ((octadCharacterPullback e O).symm χ) := by
  change parkerCoordinateAction e ((1 / 2 : Scalar) • (octadicAxisPart O +
    (theta * parkerScalarSign (χ (octadShortenedOne O))) • signedOctadVector Q.octadLift +
    octadicHyperplanePart Q χ)) = _
  simp only [map_smulₛₗ, map_add, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    parkerCoordinateAction_octadicAxisPart, parkerCoordinateAction_octadicHyperplanePart,
    parkerCoordinateAction_signedOctad, map_mul, scalarParityAut_theta, scalarParityAut_sign]
  rw [octadicRoot, octadicCharacterTransport_one]
  change _ = (1 / 2 : Scalar) • (octadicAxisPart (parkerOctadAction e O) +
    (theta * parkerScalarSign (χ (octadShortenedOne O))) •
      signedOctadVector (signedOctadSign (e.val parkerOmega).2 (parkerSignedOctadAction e Q.octadLift)) +
    octadicHyperplanePart (octadCalibrationTransport e Q) ((octadCharacterPullback e O).symm χ))
  rw [signedOctadSign_vector]
  rw [parkerCoordinateAction_octadicAxisPart e O,
    parkerCoordinateAction_octadicHyperplanePart e Q χ,
    parkerCoordinateAction_signedOctad e Q.octadLift]
  have hhalf : scalarParityAut (parkerStandardParity e).toAdd (1 / 2 : Scalar) = 1 / 2 := by
    have hcast : ((1 / 2 : ℚ) : Scalar) = 1 / 2 := by norm_num
    rw [← hcast]
    exact scalarParityAut_rat _ _
  rw [hhalf]
  have hp : (parkerStandardParity e).toAdd = (e.val parkerOmega).2 := rfl
  rw [hp]
  module

end Atlas.Fischer
