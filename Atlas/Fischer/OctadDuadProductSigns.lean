import Atlas.Fischer.OctadDuadSigns
import Atlas.Fischer.OctadDuadBasis
import Atlas.Fischer.SignedOctadCrossingProducts

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra

/-- A row-to-column shortened word is uniquely the sum of the two actual
translation differences. -/
theorem octadTranslationDifference_pair (O : Octad) (c : golay) (s t : BinaryFour)
    (b : octadShortenedCode O)
    (hb : octadTranslatedWord O s c+b.val=octadTranslatedWord O t c) :
    b=octadTranslationDifference O c s+octadTranslationDifference O c t := by
  apply Subtype.ext
  apply add_left_cancel (a := octadTranslatedWord O s c)
  rw [hb]
  change octadTranslatedWord O t c=
    octadTranslatedWord O s c+
      ((octadTranslatedWord O s c-c)+(octadTranslatedWord O t c-c))
  have hc := parkerGolay_add_self c
  have hs := parkerGolay_add_self (octadTranslatedWord O s c)
  have hn : -c=c := by
    exact (neg_eq_iff_add_eq_zero).mpr hc
  simp only [sub_eq_add_neg,hn]
  calc
    _ = (octadTranslatedWord O t c)+(octadTranslatedWord O s c+
      octadTranslatedWord O s c)+(c+c) := by rw [hs,hc,add_zero,add_zero]
    _ = _ := by abel

/-- Literal four-intersection output, with its proved actual polar sign. -/
theorem octadDuadProductFour_sign {O : Octad} (Q : OctadCalibration O) (d : SignedOctad)
    (hd : (support d.val.1.val ∩ O.val).card=2) (s t : BinaryFour)
    (b : OctadShortenedHyperplane O)
    (h4 : signedOctadIntersection (octadTranslatedSignedOctad Q d s)
      (calibratedHyperplaneLift Q b)=4)
    (hb : octadTranslatedWord O s d.val.1+b.val.val=octadTranslatedWord O t d.val.1) :
    signedOctadVector (octadProductFour (octadTranslatedSignedOctad Q d s)
      (calibratedHyperplaneLift Q b) h4)=
      parkerScalarSign ((binaryQuadraticWordForm (octadQuadraticRestriction O d.val.1)).polarBilin s t) •
        octadDuadSignedFamily Q d t := by
  have he := octadTranslationDifference_pair O d.val.1 s t b.val hb
  have hp := octadDuadCoset_matrix_sign Q d hd s t
  rw [← he] at hp
  have hl : octadProductFour (octadTranslatedSignedOctad Q d s)
      (calibratedHyperplaneLift Q b) h4=
      signedOctadSign ((binaryQuadraticWordForm (octadQuadraticRestriction O d.val.1)).polarBilin s t)
        (octadTranslatedSignedOctad Q d t) := by
    apply Subtype.ext
    exact hp
  rw [hl,signedOctadSign_vector]
  rfl

end Atlas.Fischer
