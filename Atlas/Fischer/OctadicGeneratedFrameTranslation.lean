import Atlas.Fischer.OctadicPhaseTranslations
import Atlas.Fischer.BasicFrameStabilizer
import Atlas.Fischer.GeneratedRootGroups

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Extend the exterior affine translation by the identity on the octad. -/
def octadicFrameTranslation (O : Octad) (t : OctadTranslationSpace O) : Equiv.Perm Omega :=
  Equiv.Perm.ofSubtype (octadCharacterTranslation O t)

/-- An actual product of two displayed root generators, with no external H input. -/
def octadicGeneratedPhasePair (O : Octad) (χ ψ : OctadicCharacter O) : SemilinearAlgebraAutomorphism :=
  displayedRootAutomorphism (.inr (.inl ⟨O,ψ⟩)) *
    displayedRootAutomorphism (.inr (.inl ⟨O,χ⟩))

theorem octadicGeneratedPhasePair_mem (O : Octad) (χ ψ : OctadicCharacter O) :
    octadicGeneratedPhasePair O χ ψ ∈ rootGeneratedAlgebraGroup :=
  rootGeneratedAlgebraGroup.mul_mem (displayedRootAutomorphism_mem _)
    (displayedRootAutomorphism_mem _)

/-- The generated phase pair realizes the exact affine translation on the full
basic frame, fixing every point of the octad. -/
theorem octadicGeneratedPhasePair_basic (O : Octad) (χ ψ : OctadicCharacter O)
    (hp : χ (octadShortenedOne O)=ψ (octadShortenedOne O)) (i : Omega) :
    (octadicGeneratedPhasePair O χ ψ).val (basicAxis i)=
      basicAxis (octadicFrameTranslation O (octadicPhaseDifference O χ ψ hp) i) := by
  change rootMap (octadicRoot (chosenOctadCalibration O) ψ)
    (rootMap (octadicRoot (chosenOctadCalibration O) χ) (basicAxis i))=_
  by_cases hi : i ∈ O.val
  · rw [octadicRoot_switch_inside _ _ _ hi,octadicRoot_switch_inside _ _ _ hi]
    rw [octadicFrameTranslation,Equiv.Perm.ofSubtype_apply_of_not_mem (a := i) (f := octadCharacterTranslation O (octadicPhaseDifference O χ ψ hp)) (ha := not_not.mpr hi)]
  · rw [octadicFrameTranslation,Equiv.Perm.ofSubtype_apply_of_mem (a := i) (f := octadCharacterTranslation O (octadicPhaseDifference O χ ψ hp)) (ha := hi)]
    exact octadicRoot_phase_pair_outside (chosenOctadCalibration O) χ ψ hp ⟨i,hi⟩

theorem octadicGeneratedPhasePair_frame (O : Octad) (χ ψ : OctadicCharacter O)
    (hp : χ (octadShortenedOne O)=ψ (octadShortenedOne O)) :
    octadicGeneratedPhasePair O χ ψ ∈ basicFrameStabilizer := by
  refine ⟨octadicFrameTranslation O (octadicPhaseDifference O χ ψ hp),?_⟩
  intro i
  rw [octadicGeneratedPhasePair_basic O χ ψ hp]

theorem octadicFrameTranslation_nontrivial (O : Octad) (t : OctadTranslationSpace O)
    (ht : t ≠ 0) : octadicFrameTranslation O t ≠ 1 := by
  intro h
  apply octadCharacterTranslation_nontrivial O t ht
  apply Equiv.ext
  intro i
  apply Subtype.ext
  have hi := congrArg (fun f : Equiv.Perm Omega => f i.val) h
  simpa only [octadicFrameTranslation,Equiv.Perm.ofSubtype_apply_coe,Equiv.Perm.one_apply] using hi

end Atlas.Fischer
