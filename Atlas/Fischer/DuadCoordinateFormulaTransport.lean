import Atlas.Fischer.DuadZeroWordExpansion

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The literal duadic coordinate expression with a fixed sign function on the
407 actual weight-eight and weight-sixteen words. -/
def duadSignedCoordinateExpression (p : Finset Omega) (η : DuadCoordinateWord p → Bit)
    (ξ : Module.Dual Bit (duadShortenedCode p)) : Coordinates :=
  (1/8 : Scalar) • (duadicAxisPart p + ∑ c : DuadCoordinateWord p,
    parkerScalarSign (η c + ξ c.val) • duadWordVector p c)

theorem parkerCocodeAction_duadicAxisPart (d : Cocode) (p : Finset Omega) :
    parkerCoordinateAction (parkerCocodeStandard d) (duadicAxisPart p) = duadicAxisPart p := by
  simp only [duadicAxisPart,axisSum,map_sub,map_sum,parkerCocodeAction_smul,
    map_ofNat,parkerCoordinateAction_u,parkerCocodeStandard_projection]
  rfl

/-- Cocode covariance transports a fixed zero-character sign formula to every
character without changing the chosen global Parker section. -/
theorem parkerCocodeAction_duadSignedCoordinateExpression (d : Cocode)
    (p : Finset Omega) (η : DuadCoordinateWord p → Bit)
    (ξ : Module.Dual Bit (duadShortenedCode p)) :
    parkerCoordinateAction (parkerCocodeStandard d) (duadSignedCoordinateExpression p η ξ) =
      duadSignedCoordinateExpression p η (duadCocodeCharacterAction p d ξ) := by
  simp only [duadSignedCoordinateExpression,parkerCocodeAction_smul,map_add,map_sum,
    parkerCocodeAction_duadicAxisPart,scalarParityAut_sign,parkerCocodeAction_duadWordVector,
    smul_smul,duadCocodeCharacterAction,LinearMap.add_apply,duadCocodeRestriction_apply,
    ← parkerScalarSign_add,add_assoc]
  norm_num only [map_div₀,map_one,map_ofNat]

theorem duadCharacterProduct_formula_of_zero (p : Finset Omega) (hp : p.card = 2)
    (F G : Octad) (hFG : F.val ∩ G.val = p)
    (Q : OctadCalibration F) (R : OctadCalibration G)
    (η : DuadCoordinateWord p → Bit)
    (hzero : duadCharacterProduct p hp F G hFG Q R 0 = duadSignedCoordinateExpression p η 0)
    (ξ : Module.Dual Bit (duadShortenedCode p)) :
    duadCharacterProduct p hp F G hFG Q R ξ = duadSignedCoordinateExpression p η ξ := by
  obtain ⟨d,hd⟩ := duadCocodeCharacterAction_transitive p 0 ξ
  have he := congrArg (parkerCoordinateAction (parkerCocodeStandard d)) hzero
  rw [duadCharacterProduct_cocode,parkerCocodeAction_duadSignedCoordinateExpression,hd] at he
  exact he

end Atlas.Fischer
