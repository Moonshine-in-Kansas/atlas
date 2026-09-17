import Atlas.Fischer.OctadicGeneratedFrameTranslation
import Atlas.Fischer.MathieuOctadTranslations
import Atlas.Fischer.OctadAvoidance
import Atlas.Fischer.BasicFrameCoordinateHom

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem mathieuOctadPointwise_exists_character (O : Octad)
    (g : mathieuOctadPointwise O) :
    ∃ t : OctadTranslationSpace O, mathieuOctadCharacterLift O t=g.val := by
  let i : OctadExterior O := Classical.choice inferInstance
  obtain ⟨t,ht,_⟩ := octadCharacterTranslation_regular O i (mathieuOctadExteriorPerm O g.val i)
  obtain ⟨u,hu,hunique⟩ := mathieuOctadPointwise_regular O i
    (mathieuOctadExteriorPerm O g.val i)
  have he : (⟨mathieuOctadCharacterLift O t,mathieuOctadCharacterLift_mem O t⟩ :
      mathieuOctadPointwise O)=g := by
    apply (hunique _ ?_).trans (hunique g rfl).symm
    rw [mathieuOctadCharacterLift_exterior]
    exact ht
  exact ⟨t,congrArg Subtype.val he⟩

theorem octadicFrameTranslation_eq_mathieu (O : Octad) (t : OctadTranslationSpace O) :
    octadicFrameTranslation O t=(mathieuOctadCharacterLift O t).val.val := by
  classical
  apply Equiv.ext
  intro i
  by_cases hi : i ∈ O.val
  · rw [octadicFrameTranslation,Equiv.Perm.ofSubtype_apply_of_not_mem
      (a := i) (f := octadCharacterTranslation O t) (ha := not_not.mpr hi)]
    exact (octadPointwiseEmbedding_fixes O
      ⟨mathieuOctadCharacterLift O t,mathieuOctadCharacterLift_mem O t⟩ i hi).symm
  · have he := congrArg (fun f : Equiv.Perm (OctadExterior O) => (f ⟨i,hi⟩).val)
      (mathieuOctadCharacterLift_exterior O t)
    rw [octadicFrameTranslation,Equiv.Perm.ofSubtype_apply_of_mem
      (a := i) (f := octadCharacterTranslation O t) (ha := hi)]
    exact he.symm

theorem octadicGeneratedPhasePair_coordinate (O : Octad) (t : OctadTranslationSpace O)
    (hp : (0 : OctadicCharacter O) (octadShortenedOne O)=t.val (octadShortenedOne O)) :
    basicFrameCoordinateHom
      ⟨octadicGeneratedPhasePair O 0 t.val,octadicGeneratedPhasePair_frame O 0 t.val hp⟩=
      (mathieuOctadCharacterLift O t).val := by
  apply basicFrameCoordinate_eq_of_ray
  intro i
  rw [octadicGeneratedPhasePair_basic O 0 t.val hp]
  have ht : octadicPhaseDifference O 0 t.val hp=t := by
    apply Subtype.ext
    exact zero_add _
  rw [ht,octadicFrameTranslation_eq_mathieu]

end Atlas.Fischer
