import Atlas.Fischer.DuadWeightCoordinates
import Atlas.Fischer.OctadicCocodeAction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The fixed global Parker section is the literal zero-sign section. In
weight16 the source vector uses its actual product with Ω, retaining that sign. -/
def golayCoordinateVector (c : golay)
    (hc : hammingNorm c.val=8 ∨ hammingNorm c.val=16) : Coordinates :=
  if h8 : hammingNorm c.val=8 then signedOctadVector ⟨(c,0),h8⟩
  else theta • signedOctadVector ⟨parkerLoopMultiply (c,0) parkerOmega,
    golayComplement_weight_sixteen c (hc.resolve_left h8)⟩

/-- Actual cocode covariance includes cancellation between conjugation of θ
and the extra all-one character in the weight16 Parker label. -/
theorem parkerCocodeAction_golayCoordinateVector (d : Cocode) (c : golay)
    (hc : hammingNorm c.val=8 ∨ hammingNorm c.val=16) :
    parkerCoordinateAction (parkerCocodeStandard d) (golayCoordinateVector c hc)=
      parkerScalarSign (cocodePairing c d) • golayCoordinateVector c hc := by
  unfold golayCoordinateVector
  split_ifs with h8
  · exact parkerCocodeAction_signedOctad d _
  · rw [parkerCocodeAction_smul,scalarParityAut_theta,parkerCocodeAction_signedOctad]
    have hp : cocodePairing (parkerLoopMultiply (c,0) parkerOmega).1 d=
        cocodePairing c d+cocodeParity d := map_add (cocodeDualEquiv d) _ _
    rw [hp,parkerScalarSign_add,smul_smul,smul_smul]
    congr 1
    calc
      _ = parkerScalarSign (cocodePairing c d)*theta*
          (parkerScalarSign (cocodeParity d)*parkerScalarSign (cocodeParity d)) := by ring
      _ = _ := by rw [parkerScalarSign_square,mul_one]

/-- The coordinate vector attached to an actual shortened-duad word. -/
def duadWordVector (p : Finset Omega) (c : DuadCoordinateWord p) : Coordinates :=
  golayCoordinateVector c.val.val c.property

theorem parkerCocodeAction_duadWordVector (d : Cocode) (p : Finset Omega)
    (c : DuadCoordinateWord p) :
    parkerCoordinateAction (parkerCocodeStandard d) (duadWordVector p c)=
      parkerScalarSign (cocodePairing c.val.val d) • duadWordVector p c :=
  parkerCocodeAction_golayCoordinateVector d c.val.val c.property

end Atlas.Fischer
