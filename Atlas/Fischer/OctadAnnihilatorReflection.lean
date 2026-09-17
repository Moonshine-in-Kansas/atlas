import Atlas.Fischer.OctadicCocodeAction
import Atlas.Fischer.BasicCocodeComparison
import Atlas.Fischer.ParkerMultiplicativity

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual shortened-code annihilator fixes every octadic phase. -/
theorem octadAnnihilator_fixes_root {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (d : octadCocodeAnnihilator O) :
    parkerCoordinateAction (parkerCocodeStandard d.val) (octadicRoot Q χ) =
      octadicRoot Q χ := by
  rw [parkerCocodeAction_octadicRoot]
  have hd : octadCocodeRestriction O d.val = 0 := d.prop
  rw [hd, add_zero]

/-- Root-map covariance for the retained full semilinear Parker action. -/
theorem parkerCoordinateAction_rootMap (g : ParkerStandardGroup) (r x : Coordinates) :
    parkerCoordinateAction g (rootMap r x) =
      rootMap (parkerCoordinateAction g r) (parkerCoordinateAction g x) := by
  simp only [rootMap, map_sub, map_smulₛₗ]
  rw [← parkerCoordinateAction_product, parkerCoordinateAction_hermitian]
  rfl

/-- Commutation is proved for the actual root map, before its antiunitarity. -/
theorem octadAnnihilator_commutes_rootMap {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (d : octadCocodeAnnihilator O) (x : Coordinates) :
    parkerCoordinateAction (parkerCocodeStandard d.val) (rootMap (octadicRoot Q χ) x) =
      rootMap (octadicRoot Q χ) (parkerCoordinateAction (parkerCocodeStandard d.val) x) := by
  rw [parkerCoordinateAction_rootMap, octadAnnihilator_fixes_root]

end Atlas.Fischer
