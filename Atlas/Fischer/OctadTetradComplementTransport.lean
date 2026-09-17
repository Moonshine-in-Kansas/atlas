import Atlas.Fischer.OctadTetradPairedLabels
import Atlas.Fischer.CalibratedShortenedLabels

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem octadTetradDifference_flip (O : Octad) (T : Finset Omega)
    (hTO : T ⊆ O.val) (hT : T.card = 4) (D E : OctadTetradFibre O T) :
    octadTetradDifference O (O.val \ T) (octadTetradFlipEquiv O T hTO hT D)
      (octadTetradFlipEquiv O T hTO hT E) = octadTetradDifference O T D E := by
  apply Subtype.ext
  change octadWord (octadTetradFlip O T hT E) - octadWord (octadTetradFlip O T hT D) = _
  rw [octadTetradFlip_word, octadTetradFlip_word, add_sub_add_right_eq_sub]
  rfl

theorem octadTetradComplementBase_code {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hTO : T ⊆ O.val) (hT : T.card = 4) (D : OctadTetradFibre O T)
    (d : ParkerLoop) (hd : d.1 = octadWord D.val) :
    (parkerLoopMultiply d Q.octadLift.val).1 =
      octadWord (octadTetradFlipEquiv O T hTO hT D).val := by
  change d.1 + Q.octadLift.val.1 = octadWord (octadTetradFlip O T hT D)
  rw [hd, Q.lift_code, octadTetradFlip_word]

/-- Applying the same actual coset construction at the complementary signed base
produces exactly the already chosen second half of the eight-vector family. -/
theorem octadTetradCosetLabel_flip {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hTO : T ⊆ O.val) (hT : T.card = 4) (D : OctadTetradFibre O T)
    (d : ParkerLoop) (hd : d.1 = octadWord D.val) (E : OctadTetradFibre O T) :
    octadTetradCosetLabel Q (O.val \ T) (octadTetradFlipEquiv O T hTO hT D)
      (parkerLoopMultiply d Q.octadLift.val) (octadTetradComplementBase_code Q T hTO hT D d hd)
      (octadTetradFlipEquiv O T hTO hT E) = octadTetradComplementLabel Q T hT D d hd E := by
  apply Subtype.ext
  change parkerLoopMultiply (parkerLoopMultiply d Q.octadLift.val)
    (Q.parkerSection.lift (octadTetradDifference O (O.val \ T)
      (octadTetradFlipEquiv O T hTO hT D) (octadTetradFlipEquiv O T hTO hT E))) = _
  rw [octadTetradDifference_flip, calibratedShortened_coset_right]
  rfl

theorem octadTetradComplementLabel_flip {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hTO : T ⊆ O.val) (hT : T.card = 4) (D : OctadTetradFibre O T)
    (d : ParkerLoop) (hd : d.1 = octadWord D.val) (E : OctadTetradFibre O T) :
    octadTetradComplementLabel Q (O.val \ T) (octadTetrad_complement_card O T hTO hT)
      (octadTetradFlipEquiv O T hTO hT D) (parkerLoopMultiply d Q.octadLift.val)
      (octadTetradComplementBase_code Q T hTO hT D d hd)
      (octadTetradFlipEquiv O T hTO hT E) = octadTetradCosetLabel Q T D d hd E := by
  apply Subtype.ext
  change parkerLoopMultiply (octadTetradCosetLabel Q (O.val \ T)
    (octadTetradFlipEquiv O T hTO hT D) (parkerLoopMultiply d Q.octadLift.val)
    (octadTetradComplementBase_code Q T hTO hT D d hd)
    (octadTetradFlipEquiv O T hTO hT E)).val Q.octadLift.val = _
  rw [octadTetradCosetLabel_flip]
  exact calibratedOctad_right_involutive Q _

end Atlas.Fischer
