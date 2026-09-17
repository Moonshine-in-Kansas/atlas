import Atlas.Fischer.OctadAnnihilatorReflection
import Atlas.Fischer.OctadicRootEquations
import Atlas.Fischer.RootMapSymmetry

namespace Atlas.Fischer

/-- Transport uses the previously verified Parker action, not octadic multiplicativity. -/
theorem parker_rootMap_antiunitary (g : ParkerStandardGroup) (r : Coordinates)
    (h : RootMapAntiunitary r) : RootMapAntiunitary (parkerCoordinateAction g r) := by
  intro x y
  obtain ⟨x, rfl⟩ := (parkerCoordinateAction g).surjective x
  obtain ⟨y, rfl⟩ := (parkerCoordinateAction g).surjective y
  rw [← parkerCoordinateAction_rootMap, ← parkerCoordinateAction_rootMap,
    parkerCoordinateAction_hermitian, h, parkerCoordinateAction_hermitian,
    scalarParityAut_star]

/-- Every actual phase inherits antiunitarity from the trivial phase. -/
theorem octadicRoot_antiunitary_of_zero {O : Atlas.Codes.Octad} (Q : OctadCalibration O)
    (h : RootMapAntiunitary (octadicRoot Q 0)) (χ : OctadicCharacter O) :
    RootMapAntiunitary (octadicRoot Q χ) := by
  obtain ⟨d, hd⟩ := octadicRoot_cocode_transitive Q 0 χ
  rw [← hd]
  exact parker_rootMap_antiunitary _ _ h

/-- The complete local conclusion, conditional only on the remaining zero-phase block proof. -/
theorem octadicRoot_involutive_of_zero_antiunitary {O : Atlas.Codes.Octad}
    (Q : OctadCalibration O) (h : RootMapAntiunitary (octadicRoot Q 0))
    (χ : OctadicCharacter O) : Function.Involutive (rootMap (octadicRoot Q χ)) :=
  rootMap_involutive_of_antiunitary _ (octadicRoot_antiunitary_of_zero Q h χ)

end Atlas.Fischer
