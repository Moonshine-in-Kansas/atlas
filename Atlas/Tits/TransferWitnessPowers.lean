import Atlas.Tits.NormalIndexReduction

/-! The actual transfer witness alpha=qW: its power identities and marked
translation matrix. Only the inherited 56 coordinates are checked. -/

namespace Atlas.Tits
open Atlas.Rudvalis Atlas.Codes.Quaternary
set_option maxRecDepth 16384

noncomputable def localOriginalAlpha : SignedCoordinates SeedCoordinate :=
  localOriginalQ * seedWMonomial
noncomputable def localCodeAlpha : codeGroup := localCodeQ * codeW
noncomputable def pointW : codeReferenceStabilizer := ⟨codeW,localCodeW_fixes_reference⟩
noncomputable def pointAlpha : codeReferenceStabilizer := pointQ * pointW
noncomputable def localAlpha : Ambient := codePointHom pointAlpha

set_option maxHeartbeats 4000000 in
-- A power identity on the existing signed 56-coordinate model.
theorem originalAlpha_square : localOriginalAlpha^2 =
    seedOriginalRowSign (binaryLabel 3) := by
  ext z
  all_goals decide +kernel +revert

set_option maxHeartbeats 4000000 in
theorem originalE3_square : (seedOriginalRowSign (binaryLabel 3))^2 = 1 := by
  ext z
  all_goals decide +kernel +revert

theorem localCodeAlpha_transport : localCodeAlpha.val = seedConjugateHom localOriginalAlpha := by
  change localCodeQ.val * codeW.val = seedConjugateHom (localOriginalQ*seedWMonomial)
  rw [localCodeQ_transport,codeW_transport,map_mul]

theorem localCodeAlpha_square : localCodeAlpha^2 = seedARowSign (binaryLabel 3) := by
  apply Subtype.ext
  change localCodeAlpha.val^2 = (seedARowSign (binaryLabel 3)).val
  rw [localCodeAlpha_transport,seedARowSign_conjugate,← map_pow,originalAlpha_square]

theorem pointE3_square : pointE3^2 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change (seedARowSign (binaryLabel 3)).val^2 = 1
  rw [seedARowSign_conjugate,← map_pow,originalE3_square,map_one]

theorem pointAlpha_square : pointAlpha^2 = pointE3 :=
  Subtype.ext localCodeAlpha_square

theorem localAlpha_square : localAlpha^2 = codePointHom pointE3 := by
  rw [localAlpha,← map_pow,pointAlpha_square]

theorem pointAlpha_fourth : pointAlpha^4 = 1 := by
  rw [show 4=2*2 by decide,pow_mul,pointAlpha_square,pointE3_square]

theorem localAlpha_fourth : localAlpha^4 = 1 := by
  rw [localAlpha,← map_pow,pointAlpha_fourth,map_one]

/-- Columns (2,5,3) in the inherited binary marking. -/
def alphaTranslationMatrix : BinaryMatrix := !![0,1,1; 1,0,1; 0,1,0]

theorem alphaTranslationMatrix_columns (i : Fin 3) :
    (fun j => alphaTranslationMatrix j i) = binaryLabel (![2,5,3] i) := by
  decide +kernel +revert

theorem alphaTranslationMatrix_sum :
    qTranslationMatrix + localUVWMatrix 2 = alphaTranslationMatrix := by decide +kernel

theorem localCodeAlpha_translation : codePermutationHom localCodeAlpha =
    coordinateTranslationHom (Multiplicative.ofAdd alphaTranslationMatrix) := by
  rw [localCodeAlpha,map_mul,localCodeQ_translation,localCodeW_translation,← map_mul]
  change coordinateTranslationHom (Multiplicative.ofAdd (qTranslationMatrix+localUVWMatrix 2)) = _
  rw [alphaTranslationMatrix_sum]

theorem alphaTranslationMatrix_point_trace :
    pointMatrixConstraints alphaTranslationMatrix = 0 ∧
      pointTraceRaw alphaTranslationMatrix = 1 := by decide +kernel

end Atlas.Tits
