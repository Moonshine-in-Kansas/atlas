import Atlas.Tits.PointTranslationGeometry
import Atlas.Tits.LocalGroups

namespace Atlas.Tits
open Atlas.Rudvalis

theorem rowMatrix_coordinates (g : codeRowKernel) :
    codePermutationHom g.val = coordinateTranslationHom (codeRowMatrixHom g) := by
  exact congrArg Subtype.val
    (binaryTranslationEquiv.apply_symm_apply (codeRowTranslationHom g)).symm

theorem rowMatrix_fixes_reference_iff (g : codeRowKernel) :
    g.val ∈ codeReferenceStabilizer ↔ (codeRowMatrixHom g).toAdd ∈ pointMatrixSpace := by
  change g.val • localReferenceCross = localReferenceCross ↔ _
  rw [localReferenceCross_eq, coordinateCross_action]
  have hg := congrArg (fun p => p.val (rowLabel 0, 0)) (rowMatrix_coordinates g)
  change g.val.val.right (rowLabel 0, 0) =
    coordinateTranslation (codeRowMatrixHom g).toAdd (rowLabel 0, 0) at hg
  rw [hg, ← pointMatrixSpace_iff_fixes_cross]

theorem pointMatrix_lift (M : pointMatrixSpace) :
    ∃ g : codeRowKernel, g.val ∈ codeReferenceStabilizer ∧
      codeRowMatrixHom g = Multiplicative.ofAdd M.val := by
  obtain ⟨g, hg⟩ := codeRowMatrixHom_surjective (Multiplicative.ofAdd M.val)
  refine ⟨g, (rowMatrix_fixes_reference_iff g).mpr ?_, hg⟩
  rw [hg]
  exact M.prop

end Atlas.Tits
