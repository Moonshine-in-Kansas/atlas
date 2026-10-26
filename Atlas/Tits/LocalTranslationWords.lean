import Atlas.Tits.MonomialNormalClosure
import Atlas.Tits.PointRowRestriction

namespace Atlas.Tits
open Atlas.Rudvalis Atlas.Codes.Quaternary
set_option maxRecDepth 16384

noncomputable def localOriginalQ : SignedCoordinates SeedCoordinate :=
  seedPMonomial⁻¹ * seedVMonomial * seedUnitMonomial 2 * seedPMonomial
noncomputable def localCodeQ : codeGroup := codeP⁻¹ * codeV * codeSigma * codeP
noncomputable def localOriginalUWord : SignedCoordinates SeedCoordinate :=
  (coupleOriginalD ^ 4 * seedRMonomial) ^ 4
noncomputable def localCodeUWord : codeGroup := (coupleCodeD ^ 4 * codeR) ^ 4

theorem localCodeQ_transport : localCodeQ.val = seedConjugateHom localOriginalQ := by
  simp only [localCodeQ, localOriginalQ, Subgroup.coe_mul, Subgroup.coe_inv,
    map_mul, map_inv, codeV_transport]
  rfl

theorem localCodeUWord_transport : localCodeUWord.val = seedConjugateHom localOriginalUWord := by
  simp only [localCodeUWord, localOriginalUWord, Subgroup.coe_mul, Subgroup.coe_pow,
    map_mul, map_pow, coupleCodeD_transport]
  rfl

def qTranslationMatrix : BinaryMatrix := !![0,0,0; 1,0,1; 0,1,0]
def dCubeTranslationMatrix : BinaryMatrix := !![1,0,0; 0,1,1; 0,0,0]
def uTranslationMatrix : BinaryMatrix := !![1,1,1; 0,1,1; 1,0,0]

set_option maxHeartbeats 4000000 in
-- Checking only the inherited 56 coordinate permutations, not enumerating a group.
theorem originalQ_translation (z : SeedCoordinate) :
    originalCoordinateEquiv (localOriginalQ.right z) =
      coordinateTranslation qTranslationMatrix (originalCoordinateEquiv z) := by
  decide +kernel +revert

set_option maxHeartbeats 4000000 in
-- The same small coordinate certificate for the cube of the inherited d.
theorem originalDCube_translation (z : SeedCoordinate) :
    originalCoordinateEquiv ((coupleOriginalD ^ 3).right z) =
      coordinateTranslation dCubeTranslationMatrix (originalCoordinateEquiv z) := by
  decide +kernel +revert

set_option maxHeartbeats 4000000 in
-- The normal-closure word is checked on the existing coordinate representation.
theorem originalUWord_translation (z : SeedCoordinate) :
    originalCoordinateEquiv (localOriginalUWord.right z) =
      coordinateTranslation uTranslationMatrix (originalCoordinateEquiv z) := by
  decide +kernel +revert

theorem code_projection_of_original_translation (g : codeGroup)
    (h : SignedCoordinates SeedCoordinate) (M : BinaryMatrix)
    (hg : g.val = seedConjugateHom h)
    (ht : ∀ z, originalCoordinateEquiv (h.right z) =
      coordinateTranslation M (originalCoordinateEquiv z)) :
    codePermutationHom g = coordinateTranslationHom (Multiplicative.ofAdd M) := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  obtain ⟨z, rfl⟩ := originalCoordinateEquiv.surjective z
  change g.val.right (originalCoordinateEquiv z) = _
  rw [hg]
  change (seedConjugateMonomial h).right (originalCoordinateEquiv z) = _
  rw [seedConjugateMonomial_right, original_congr_apply]
  exact ht z

theorem localCodeQ_translation : codePermutationHom localCodeQ =
    coordinateTranslationHom (Multiplicative.ofAdd qTranslationMatrix) :=
  code_projection_of_original_translation _ _ _ localCodeQ_transport originalQ_translation

theorem localCodeDCube_translation : codePermutationHom (coupleCodeD ^ 3) =
    coordinateTranslationHom (Multiplicative.ofAdd dCubeTranslationMatrix) := by
  apply code_projection_of_original_translation _ (coupleOriginalD ^ 3) _
  · simp only [Subgroup.coe_pow, coupleCodeD_transport, map_pow]
  · exact originalDCube_translation

theorem localCodeUWord_translation : codePermutationHom localCodeUWord =
    coordinateTranslationHom (Multiplicative.ofAdd uTranslationMatrix) :=
  code_projection_of_original_translation _ _ _ localCodeUWord_transport originalUWord_translation

theorem local_translation_traces :
    pointTraceRaw qTranslationMatrix = 1 ∧ pointTraceRaw dCubeTranslationMatrix = 0 ∧
      pointTraceRaw uTranslationMatrix = 0 := by decide +kernel

theorem local_translation_point_constraints :
    qTranslationMatrix ∈ pointMatrixSpace ∧ dCubeTranslationMatrix ∈ pointMatrixSpace ∧
      uTranslationMatrix ∈ pointMatrixSpace := by
  change pointMatrixConstraints qTranslationMatrix = 0 ∧
    pointMatrixConstraints dCubeTranslationMatrix = 0 ∧ pointMatrixConstraints uTranslationMatrix = 0
  decide +kernel

end Atlas.Tits
