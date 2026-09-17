import Atlas.Fischer.OctadTranslationTriple
import Atlas.Fischer.ParkerCosetMatrixSigns
import Atlas.Algebra.BinaryQuadraticWordContraction

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra

/-- The actual Parker triple is precisely the nondegenerate duad polar form. -/
theorem octadDuadTranslation_triple (O : Octad) (c : golay)
    (hc : (support c.val ∩ O.val).card=2) (s t : BinaryFour) :
    parkerTripleIntersection c.val (octadTranslationDifference O c s).val.val
      (octadTranslationDifference O c t).val.val =
      (binaryQuadraticWordForm (octadQuadraticRestriction O c)).polarBilin s t := by
  rw [octadTranslationDifference_triple]
  exact binaryQuadraticWord_polar_contraction (octadQuadraticRestriction O c)
    (octadQuadraticWord_rank_duad O c hc) s t

/-- The complete literal row-to-column sign in the actual translated signed basis. -/
theorem octadDuadCoset_matrix_sign {O : Octad} (Q : OctadCalibration O) (d : SignedOctad)
    (hd : (support d.val.1.val ∩ O.val).card=2) (s t : BinaryFour) :
    parkerLoopMultiply (octadTranslatedSignedOctad Q d s).val
      (Q.parkerSection.lift (octadTranslationDifference O d.val.1 s+
        octadTranslationDifference O d.val.1 t)) =
      parkerSign ((binaryQuadraticWordForm (octadQuadraticRestriction O d.val.1)).polarBilin s t)
        (octadTranslatedSignedOctad Q d t).val := by
  change parkerLoopMultiply
    (Q.parkerSection.cosetLift d.val (octadTranslationDifference O d.val.1 s))
    (Q.parkerSection.lift (octadTranslationDifference O d.val.1 s+
      octadTranslationDifference O d.val.1 t))=_
  rw [ParkerSection.cosetLift_matrix_sign,octadDuadTranslation_triple O d.val.1 hd]
  rfl

end Atlas.Fischer
