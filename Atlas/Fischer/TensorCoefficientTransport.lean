import Atlas.Fischer.TensorParkerCovariance
import Atlas.Fischer.OctadicRootFibres
import Atlas.Fischer.CubicTriangleAction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- A rational proportionality between the actual quintic and cubic tensors
is invariant under the actual standard Parker group. -/
theorem coordinateQuintic_proportional_parker (e : ParkerStandardGroup)
    (p q r : CoordinateIndex) (c : ℚ) :
    coordinateQuintic (parkerCoordinateEquiv e p) (parkerCoordinateEquiv e q)
      (parkerCoordinateEquiv e r) = (c : Scalar) *
        coordinateCubic (parkerCoordinateEquiv e p) (parkerCoordinateEquiv e q)
          (parkerCoordinateEquiv e r) ↔
      coordinateQuintic p q r = (c : Scalar) * coordinateCubic p q r := by
  let a := scalarParityAut (parkerStandardParity e).toAdd
  have hs : parkerTripleSign e p q r ≠ 0 := parkerScalarSign_ne_zero _
  constructor
  · intro h
    apply a.injective
    change a (coordinateQuintic p q r) = a ((c : Scalar) * coordinateCubic p q r)
    rw [map_mul,map_ratCast,← coordinateQuintic_parker,← coordinateCubic_parker,h]
    ring
  · intro h
    apply mul_left_cancel₀ hs
    rw [coordinateQuintic_parker,h,map_mul,map_ratCast,← coordinateCubic_parker]
    ring

 theorem parkerCoordinateEquiv_octad_smul (e : ParkerStandardGroup) (D : Octad) :
    parkerCoordinateEquiv e (.inr D) = .inr (parkerStandardProjection e • D) := rfl

/-- Every actual Mathieu coordinate symmetry lifts, with the necessary Parker
signs and scalar conjugation, so rational tensor proportionality transports. -/
theorem coordinateQuintic_proportional_mathieu (g : Mathieu24CodeModel)
    (D E F : Octad) (c : ℚ) :
    coordinateQuintic (.inr (g • D)) (.inr (g • E)) (.inr (g • F)) =
      (c : Scalar) * coordinateCubic (.inr (g • D)) (.inr (g • E)) (.inr (g • F)) ↔
    coordinateQuintic (.inr D) (.inr E) (.inr F) =
      (c : Scalar) * coordinateCubic (.inr D) (.inr E) (.inr F) := by
  obtain ⟨e,he⟩ := parkerStandardProjection_surjective g
  have h := coordinateQuintic_proportional_parker e (.inr D) (.inr E) (.inr F) c
  simpa only [parkerCoordinateEquiv_octad_smul,he] using h

end Atlas.Fischer
