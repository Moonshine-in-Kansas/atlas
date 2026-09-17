import Atlas.Fischer.OctadPunctureFibres
import Atlas.Fischer.MathieuOctadTranslations
import Atlas.Algebra.BinaryQuadraticTranslation

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra

/-- The actual Mathieu lift of translation by the displayed affine coordinate. -/
def octadVectorTranslation (O : Octad) (t : BinaryFour) : MathieuOctadStabilizer O :=
  mathieuOctadCharacterLift O ((octadDirectionCoordinates O).symm t)

theorem octadVectorTranslation_coordinates (O : Octad) (t v : BinaryFour) :
    mathieuOctadCoordinatePerm O (octadVectorTranslation O t) v=v+t := by
  have h := congrArg (fun p : Equiv.Perm (OctadExterior O) =>
      octadExteriorCoordinates O (p ((octadExteriorCoordinates O).symm v)))
    (mathieuOctadCharacterLift_exterior O ((octadDirectionCoordinates O).symm t))
  simpa only [octadVectorTranslation,mathieuOctadCoordinatePerm,Equiv.trans_apply,
    octadCharacterTranslation_coordinates,Equiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply] using h

/-- Pullback by an actual Mathieu translation, on the full retained Golay code. -/
def octadTranslatedWord (O : Octad) (t : BinaryFour) (c : golay) : golay :=
  parkerCodeEquiv (octadVectorTranslation O t).val⁻¹ c

theorem octadTranslatedWord_exterior (O : Octad) (t : BinaryFour) (c : golay)
    (v : BinaryFour) :
    octadExteriorWord O (octadTranslatedWord O t c) v=octadExteriorWord O c (v+t) := by
  change c.val ((octadVectorTranslation O t).val.val
    ((octadExteriorCoordinates O).symm v).val)=
    c.val ((octadExteriorCoordinates O).symm (v+t)).val
  rw [← octadVectorTranslation_coordinates O t v,
    mathieuOctadCoordinatePerm_coordinates]

theorem octadTranslatedWord_weight (O : Octad) (t : BinaryFour) (c : golay) :
    hammingNorm (octadTranslatedWord O t c).val=hammingNorm c.val :=
  parkerCodeEquiv_weight _ _

/-- The actual Golay translates of a duad representative have distinct punctures. -/
theorem octadTranslatedWord_duad_injective (O : Octad) (c : golay)
    (hc : (support c.val ∩ O.val).card=2) :
    Function.Injective (fun t : BinaryFour => octadTranslatedWord O t c) := by
  intro s t h
  apply binaryQuadraticWord_translation_injective (octadQuadraticRestriction O c)
    (octadQuadraticWord_rank_duad O c hc)
  funext v
  have he := congrArg (fun z : golay => octadExteriorWord O z v) h
  change octadExteriorWord O c (v+s)=octadExteriorWord O c (v+t)
  simpa only [octadTranslatedWord_exterior] using he

end Atlas.Fischer
