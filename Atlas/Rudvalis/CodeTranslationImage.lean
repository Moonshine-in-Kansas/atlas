import Atlas.Rudvalis.CodeBlockImage
import Atlas.Rudvalis.NineTranslations

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

set_option maxHeartbeats 2000000 in
theorem nineOriginalPermutation_translation (i : Fin 9) (z : SeedCoordinate) :
    originalCoordinateEquiv (nineOriginalPermutation i z)=
      coordinateTranslation (nineTranslationMatrix i) (originalCoordinateEquiv z) := by
  change (rowLabel (nineOriginalPermutation i z).1,
    seedInnerLabel (nineOriginalPermutation i z).1 (signedPositionIndex (nineOriginalPermutation i z).2))=
    (rowLabel z.1,seedInnerLabel z.1 (signedPositionIndex z.2)+
      matrixAt (nineTranslationMatrix i) (rowLabel z.1).val)
  decide +kernel +revert

theorem nineCodeGenerator_projection (i : Fin 9) :
    codePermutationHom (nineCodeGenerator i)=coordinateTranslationHom (Multiplicative.ofAdd (nineTranslationMatrix i)) := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  obtain ⟨z,rfl⟩ := originalCoordinateEquiv.surjective z
  change (nineCodeGenerator i).val.right (originalCoordinateEquiv z)=_
  rw [nineCodeGenerator_right]
  rw [original_congr_apply]
  change originalCoordinateEquiv (nineOriginalPermutation i z)=_
  exact nineOriginalPermutation_translation i z

end Atlas.Rudvalis
