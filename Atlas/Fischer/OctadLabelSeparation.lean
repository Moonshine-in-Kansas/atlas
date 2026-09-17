import Atlas.Fischer.OctadLabelCharacters

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Every character of the actual even octad code comes from the actual
annihilator in the retained Golay cocode. -/
theorem octadLabelCharacter_surjective (O : Octad) :
    Function.Surjective (octadLabelCharacter O) := by
  intro l
  let d : Cocode := cocodeDualEquiv.symm (l.comp (octadEvenRestriction O))
  have hd : d ∈ octadCocodeAnnihilator O := by
    rw [mem_octadCocodeAnnihilator]
    intro c
    change cocodeDualEquiv d c.val=0
    rw [LinearEquiv.apply_symm_apply]
    have hc : octadEvenRestriction O c.val=0 := by
      exact (octadEvenRestriction_kernel O).ge c.prop
    change l (octadEvenRestriction O c.val)=0
    rw [hc,map_zero]
  refine ⟨⟨d,hd⟩,?_⟩
  apply LinearMap.ext
  intro a
  obtain ⟨c,rfl⟩ := octadEvenRestriction_surjective O a
  rw [octadLabelCharacter_restriction]
  change cocodeDualEquiv d c = l (octadEvenRestriction O c)
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- These are distinct simultaneous eigencharacters, not merely formal labels. -/
theorem octadLabelCharacter_separates (O : Octad) (a b : octadEvenCode O)
    (h : ∀ d : octadCocodeAnnihilator O, octadLabelCharacter O d a=octadLabelCharacter O d b) :
    a=b := by
  apply Subtype.ext
  funext i
  let l : Module.Dual Bit (octadEvenCode O) :=
    (LinearMap.proj i).comp (octadEvenCode O).subtype
  obtain ⟨d,hd⟩ := octadLabelCharacter_surjective O l
  have he := h d
  rw [hd] at he
  exact he

end Atlas.Fischer
