import Atlas.Fischer.ReflectionCalculus
import Atlas.Fischer.ReflectingRootBasicSupport
import Atlas.Fischer.OctadicCocodeAction
import Atlas.Fischer.OctadicReflectingRoots

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Every octadic phase fixes the eight basic roots of its actual octad. -/
theorem octadicRoot_switch_inside {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (i : Omega) (hi : i ∈ O.val) :
    rootMap (octadicRoot Q χ) (basicAxis i)=basicAxis i := by
  have hp : hermitian (octadicRoot Q χ) (basicAxis i)=1 := by
    rw [← hermitian_star,hermitian_basicAxis_octadic,if_pos hi,star_one]
  have h := nonorthogonal_root_rigidity _ _ (octadicRoot_isRoot Q χ)
    (basicAxis_isRoot i) (octadicRoot_antiunitary Q χ) (by rw [hp]; norm_num)
  simpa only [hp,star_one,one_smul] using h

/-- A coordinate singleton restricts to the actual exterior evaluation character. -/
theorem octadCocodeRestriction_coordinate (O : Octad) (i : OctadExterior O) :
    octadCocodeRestriction O (coordinateCocode i.val)=octadEvaluation O i := by
  ext c
  rw [octadCocodeRestriction_apply,cocodePairing_coordinate]
  rfl

/-- The actual switch sends each exterior basic root to the corresponding
translated octadic character root, for every calibrated phase. -/
theorem octadicRoot_switch_outside {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (i : OctadExterior O) :
    rootMap (octadicRoot Q χ) (basicAxis i.val)=octadicRoot Q (χ+octadEvaluation O i) := by
  have hp : hermitian (basicAxis i.val) (octadicRoot Q χ)=0 := by
    rw [hermitian_basicAxis_octadic,if_neg i.property]
  have hp0 : hermitian (octadicRoot Q χ) (basicAxis i.val)=0 := by
    rw [← hermitian_star,hp,star_zero]
  rw [rootMap_zero_pairing _ _ hp0,product_comm,
    ← rootMap_zero_pairing _ _ hp,rootMap_basicAxis_eq_cocode,
    parkerCocodeAction_octadicRoot,octadCocodeRestriction_coordinate]

end Atlas.Fischer
