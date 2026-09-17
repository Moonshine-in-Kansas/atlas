import Atlas.Fischer.OctadDuadIntersections
import Atlas.Fischer.OctadDuadBasis
import Atlas.Fischer.OctadFibreHyperplaneEquiv

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra

def octadDuadCoordinateEquiv (O : Octad) (d : SignedOctad)
    (hd : (support d.val.1.val ∩ O.val).card=2) :
    BinaryFour ≃ OctadIntersectionFibre O (support d.val.1.val ∩ O.val) :=
  octadDuadTranslationEquiv O _ ⟨signedOctadSupport d,rfl⟩ hd

theorem octadDuadCoordinateEquiv_word (O : Octad) (d : SignedOctad)
    (hd : (support d.val.1.val ∩ O.val).card=2) (t : BinaryFour) :
    octadWord ((octadDuadCoordinateEquiv O d hd) t).val=octadTranslatedWord O t d.val.1 := by
  change octadWord (octadTranslatedOctad O (signedOctadSupport d) t)=_
  rw [octadTranslatedOctad_word,octadWord_signedSupport]

def octadDuadOffDiagonalEquiv (O : Octad) (d : SignedOctad)
    (hd : (support d.val.1.val ∩ O.val).card=2) (s : BinaryFour) :
    {t : BinaryFour // t ≠ s} ≃
      {F : OctadIntersectionFibre O (support d.val.1.val ∩ O.val) //
        F ≠ octadDuadCoordinateEquiv O d hd s} :=
  (octadDuadCoordinateEquiv O d hd).subtypeEquiv (by
    intro t
    change t ≠ s ↔ octadDuadCoordinateEquiv O d hd t ≠ octadDuadCoordinateEquiv O d hd s
    exact not_congr (octadDuadCoordinateEquiv O d hd).injective.eq_iff.symm)

def octadDuadRowIndexEquiv (O : Octad) (d : SignedOctad)
    (hd : (support d.val.1.val ∩ O.val).card=2) (s : BinaryFour) :
    OctadFibreRowHyperplanes O _ (octadDuadCoordinateEquiv O d hd s) ≃
      {t : BinaryFour // t ≠ s} :=
  (octadFibreRowHyperplaneEquiv O _ (octadDuadCoordinateEquiv O d hd s)
    (fun F hF => octadDuadFibre_intersection_four O _ _ F hd (Ne.symm hF))).trans
      (octadDuadOffDiagonalEquiv O d hd s).symm

/-- The reindexing retains the literal code sum, not merely the support count. -/
theorem octadDuadRowIndex_code (O : Octad) (d : SignedOctad)
    (hd : (support d.val.1.val ∩ O.val).card=2) (s : BinaryFour)
    (b : OctadFibreRowHyperplanes O _ (octadDuadCoordinateEquiv O d hd s)) :
    octadTranslatedWord O s d.val.1+b.val.val.val=
      octadTranslatedWord O (octadDuadRowIndexEquiv O d hd s b).val d.val.1 := by
  let e := octadDuadCoordinateEquiv O d hd
  let f := octadFibreRowHyperplaneEquiv O _ (e s)
    (fun F hF => octadDuadFibre_intersection_four O _ _ F hd (Ne.symm hF))
  have h := e.apply_symm_apply (f b).val
  have hc := congrArg (fun E => octadWord E.val) h
  change octadWord (e (octadDuadRowIndexEquiv O d hd s b).val).val=
    octadWord (octadFibreRowOctad O _ (e s) b) at hc
  rw [octadFibreRowOctad_word] at hc
  dsimp only [e] at hc
  simpa only [octadDuadCoordinateEquiv_word] using hc.symm

end Atlas.Fischer
