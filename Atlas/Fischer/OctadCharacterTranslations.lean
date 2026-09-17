import Atlas.Fischer.OctadAffineCode

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Translation by a character trivial on X, on the actual exterior coordinates. -/
def octadCharacterTranslation (O : Octad) (t : OctadTranslationSpace O) :
    Equiv.Perm (OctadExterior O) :=
  ((octadExteriorCoordinates O).trans
    (Equiv.addRight (octadDirectionCoordinates O t))).trans (octadExteriorCoordinates O).symm

theorem octadCharacterTranslation_coordinates (O : Octad) (t : OctadTranslationSpace O)
    (i : OctadExterior O) :
    octadExteriorCoordinates O (octadCharacterTranslation O t i) =
      octadExteriorCoordinates O i + octadDirectionCoordinates O t := by
  simp [octadCharacterTranslation]

theorem octadCharacterTranslation_zero (O : Octad) : octadCharacterTranslation O 0 = 1 := by
  apply Equiv.ext
  intro i
  apply (octadExteriorCoordinates O).injective
  simp [octadCharacterTranslation_coordinates]

theorem octadCharacterTranslation_add (O : Octad) (s t : OctadTranslationSpace O) :
    octadCharacterTranslation O (s+t) =
      octadCharacterTranslation O s * octadCharacterTranslation O t := by
  apply Equiv.ext
  intro i
  apply (octadExteriorCoordinates O).injective
  simp only [Equiv.Perm.mul_apply,octadCharacterTranslation_coordinates,map_add]
  abel

/-- The actual sixteen translations act regularly on the sixteen retained coordinates. -/
theorem octadCharacterTranslation_regular (O : Octad) (i j : OctadExterior O) :
    ∃! t : OctadTranslationSpace O, octadCharacterTranslation O t i = j := by
  refine ⟨(octadDirectionCoordinates O).symm
    (octadExteriorCoordinates O j - octadExteriorCoordinates O i), ?_, ?_⟩
  · apply (octadExteriorCoordinates O).injective
    rw [octadCharacterTranslation_coordinates,LinearEquiv.apply_symm_apply]
    abel
  · intro t ht
    apply (octadDirectionCoordinates O).injective
    rw [LinearEquiv.apply_symm_apply]
    have h := congrArg (octadExteriorCoordinates O) ht
    rw [octadCharacterTranslation_coordinates] at h
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h)

theorem octadCharacterTranslation_word (O : Octad) (t : OctadTranslationSpace O)
    (i : OctadExterior O) (c : octadShortenedCode O) :
    c.val.val (octadCharacterTranslation O t i).val = c.val.val i.val + t.val c := by
  have hf (j : OctadExterior O) : c.val.val j.val =
      (octadAffineOrigin O).val c +
        ((octadDirectionCoordinates O).symm (octadExteriorCoordinates O j)).val c := by
    have h := octadAffineWord_formula O c (octadExteriorCoordinates O j)
    change c.val.val ((octadExteriorCoordinates O).symm (octadExteriorCoordinates O j)).val = _ at h
    simpa only [Equiv.symm_apply_apply] using h
  rw [hf,hf,octadCharacterTranslation_coordinates,map_add,LinearEquiv.symm_apply_apply]
  exact (add_assoc _ _ _).symm

end Atlas.Fischer
