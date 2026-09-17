import Atlas.Fischer.OctadicNormCalculation
import Atlas.Fischer.OctadCocode
import Atlas.Fischer.ParkerCoordinateAction
import Atlas.Fischer.ParkerStandardOrder

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem parkerCocodeAction_smul (d : Cocode) (a : Scalar) (x : Coordinates) :
    parkerCoordinateAction (parkerCocodeStandard d) (a • x) =
      scalarParityAut (cocodeParity d) a • parkerCoordinateAction (parkerCocodeStandard d) x := by
  have hs : (scalarParityAut (parkerStandardParity (parkerCocodeStandard d)).toAdd).toRingHom a =
      scalarParityAut (cocodeParity d) a := by
    rw [parkerStandardParity_cocode]
    rfl
  rw [map_smulₛₗ, hs]

theorem parkerCocodeAction_signedOctad (d : Cocode) (x : SignedOctad) :
    parkerCoordinateAction (parkerCocodeStandard d) (signedOctadVector x) =
      parkerScalarSign (cocodePairing x.val.1 d) • signedOctadVector x := by
  rw [parkerCoordinateAction_signedOctad]
  have he : parkerSignedOctadAction (parkerCocodeStandard d) x =
      signedOctadSign (cocodePairing x.val.1 d) x := rfl
  rw [he, signedOctadSign_vector]

theorem parkerCocodeAction_octadicAxisPart (d : Cocode) (O : Octad) :
    parkerCoordinateAction (parkerCocodeStandard d) (octadicAxisPart O) = octadicAxisPart O := by
  simp only [octadicAxisPart, map_add, map_neg, map_sum, parkerCoordinateAction_u,
    parkerCocodeStandard_projection]
  rfl

theorem parkerCocodeAction_calibratedHyperplane (d : Cocode) {O : Octad}
    (Q : OctadCalibration O) (b : OctadShortenedHyperplane O) :
    parkerCoordinateAction (parkerCocodeStandard d) (calibratedHyperplaneVector Q b) =
      parkerScalarSign (octadCocodeRestriction O d b.val) • calibratedHyperplaneVector Q b :=
  parkerCocodeAction_signedOctad d (calibratedHyperplaneLift Q b)

theorem cocodePairing_octadComplement (d : Cocode) (O : Octad) :
    cocodePairing (octadComplementWord O) d = cocodeParity d + cocodePairing (octadWord O) d :=
  map_add (cocodeDualEquiv d) _ _

/-- Actual cocode transport of the displayed octadic phases, including the
conjugation sign on θ. -/
theorem parkerCocodeAction_octadicRoot (d : Cocode) {O : Octad}
    (Q : OctadCalibration O) (χ : OctadicCharacter O) :
    parkerCoordinateAction (parkerCocodeStandard d) (octadicRoot Q χ) =
      octadicRoot Q (χ + octadCocodeRestriction O d) := by
  simp only [octadicRoot, parkerCocodeAction_smul, map_add, map_sum,
    parkerCocodeAction_octadicAxisPart, parkerCocodeAction_calibratedHyperplane,
    parkerCocodeAction_signedOctad, map_mul, scalarParityAut_theta, scalarParityAut_sign,
    Q.lift_code, LinearMap.add_apply, parkerScalarSign_add, smul_smul]
  have hc : octadCocodeRestriction O d (octadShortenedOne O) =
      cocodeParity d + cocodePairing (octadWord O) d := cocodePairing_octadComplement d O
  rw [hc, parkerScalarSign_add]
  norm_num only [map_div₀, map_one, map_ofNat]
  congr 2
  congr 1
  congr 1
  ring

theorem octadicRoot_cocode_transitive {O : Octad} (Q : OctadCalibration O)
    (χ ψ : OctadicCharacter O) : ∃ d : Cocode,
    parkerCoordinateAction (parkerCocodeStandard d) (octadicRoot Q χ) = octadicRoot Q ψ := by
  obtain ⟨d, hd⟩ := octadCocodeRestriction_surjective O (ψ - χ)
  refine ⟨d, ?_⟩
  rw [parkerCocodeAction_octadicRoot, hd]
  congr 1
  abel

end Atlas.Fischer
