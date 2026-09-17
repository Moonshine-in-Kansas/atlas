import Atlas.Fischer.OctadicBasicFrameSwitch
import Atlas.Fischer.OctadCharacterTranslations

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The difference of equal-parity octadic characters is a genuine affine direction. -/
def octadicPhaseDifference (O : Octad) (χ ψ : OctadicCharacter O)
    (hp : χ (octadShortenedOne O)=ψ (octadShortenedOne O)) : OctadTranslationSpace O :=
  ⟨χ+ψ,by
    change χ (octadShortenedOne O)+ψ (octadShortenedOne O)=0
    rw [hp,CharTwo.add_self_eq_zero]⟩

theorem octadCharacterTranslation_evaluation (O : Octad) (t : OctadTranslationSpace O)
    (i : OctadExterior O) :
    octadEvaluation O (octadCharacterTranslation O t i)=octadEvaluation O i+t.val := by
  ext c
  exact octadCharacterTranslation_word O t i c

/-- The two actual octadic reflections of equal character parity induce the
specified affine translation on exterior basic roots. -/
theorem octadicRoot_phase_pair_outside {O : Octad} (Q : OctadCalibration O)
    (χ ψ : OctadicCharacter O) (hp : χ (octadShortenedOne O)=ψ (octadShortenedOne O))
    (i : OctadExterior O) :
    rootMap (octadicRoot Q ψ) (rootMap (octadicRoot Q χ) (basicAxis i.val))=
      basicAxis (octadCharacterTranslation O (octadicPhaseDifference O χ ψ hp) i).val := by
  let k := octadCharacterTranslation O (octadicPhaseDifference O χ ψ hp) i
  have hχ : ψ+octadEvaluation O k=χ+octadEvaluation O i := by
    rw [show k=octadCharacterTranslation O (octadicPhaseDifference O χ ψ hp) i from rfl,
      octadCharacterTranslation_evaluation]
    change ψ+(octadEvaluation O i+(χ+ψ))=χ+octadEvaluation O i
    have hh : ψ+ψ=0 := by
      ext c
      exact CharTwo.add_self_eq_zero (ψ c)
    calc
      _ = χ+octadEvaluation O i+(ψ+ψ) := by abel
      _ = _ := by rw [hh,add_zero]
  have h := octadicRoot_switch_outside Q ψ k
  rw [hχ] at h
  rw [octadicRoot_switch_outside,← h]
  exact (octadicRoot_isReflectingRoot Q ψ).2.2.1 _

theorem octadCharacterTranslation_nontrivial (O : Octad) (t : OctadTranslationSpace O)
    (ht : t ≠ 0) : octadCharacterTranslation O t ≠ 1 := by
  intro h
  let i : OctadExterior O := Classical.choice inferInstance
  have he := congrArg (fun f : Equiv.Perm (OctadExterior O) => octadExteriorCoordinates O (f i)) h
  rw [octadCharacterTranslation_coordinates] at he
  have hz : octadDirectionCoordinates O t=0 := add_left_cancel (he.trans (add_zero _).symm)
  exact ht ((octadDirectionCoordinates O).injective (hz.trans (map_zero _).symm))

end Atlas.Fischer
