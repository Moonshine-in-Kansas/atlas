import Atlas.Fischer.OctadTetradCosetLabels
import Atlas.Fischer.OctadFibreContributionSums

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem octadTetradDifference_sum (O : Octad) (T : Finset Omega)
    (D E F : OctadTetradFibre O T) :
    octadTetradDifference O T D E + octadTetradDifference O T D F = octadFibreSum O T E F := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  change ((octadWord E.val).val i - (octadWord D.val).val i) +
    ((octadWord F.val).val i - (octadWord D.val).val i) =
    (octadWord E.val).val i + (octadWord F.val).val i
  rw [sub_eq_add_neg, sub_eq_add_neg, CharTwo.neg_eq,
    add_add_add_comm, CharTwo.add_self_eq_zero, add_zero]

theorem octadTetradCosetLabel_fourContribution {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hT : T.card = 4) (D : OctadTetradFibre O T)
    (d : ParkerLoop) (hd : d.1 = octadWord D.val) (E F : OctadTetradFibre O T) (hFE : F ≠ E) :
    signedOctadFourContribution (octadTetradCosetLabel Q T D d hd E)
      (calibratedHyperplaneLift Q (octadFibreSumHyperplane O T E F
        (by rw [octadTetradFibre_intersection O T hT E F (Ne.symm hFE), hT]))) =
      signedOctadVector (octadTetradCosetLabel Q T D d hd F) := by
  let b := octadFibreSumHyperplane O T E F
    (by rw [octadTetradFibre_intersection O T hT E F (Ne.symm hFE), hT])
  have hI : signedOctadIntersection (octadTetradCosetLabel Q T D d hd E)
      (calibratedHyperplaneLift Q b) = 4 := by
    rw [signedOctadIntersection_overlap, octadTetradCosetLabel_code]
    exact octadFibreSumHyperplane_overlap O T E F
      (by rw [octadTetradFibre_intersection O T hT E F (Ne.symm hFE), hT])
  change signedOctadFourContribution _ (calibratedHyperplaneLift Q b) = _
  rw [signedOctadFourContribution, dif_pos hI]
  have hp : octadProductFour (octadTetradCosetLabel Q T D d hd E)
      (calibratedHyperplaneLift Q b) hI = octadTetradCosetLabel Q T D d hd F := by
    apply Subtype.ext
    change parkerLoopMultiply (octadTetradCosetLabel Q T D d hd E).val
      (Q.parkerSection.lift (octadFibreSum O T E F)) = _
    rw [← octadTetradDifference_sum O T D E F]
    exact octadTetradCosetLabel_multiply Q T hT D d hd E F
  rw [hp]

/-- Exact scalar-part sum in source (5.14), including every actual Parker label. -/
theorem octadTetrad_scalar_contribution_sum {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hT : T.card = 4) (D : OctadTetradFibre O T)
    (d : ParkerLoop) (hd : d.1 = octadWord D.val) (E : OctadTetradFibre O T) :
    (∑ b : OctadShortenedHyperplane O,
      signedOctadFourContribution (octadTetradCosetLabel Q T D d hd E) (calibratedHyperplaneLift Q b)) =
      (∑ F : OctadTetradFibre O T, signedOctadVector (octadTetradCosetLabel Q T D d hd F)) -
        signedOctadVector (octadTetradCosetLabel Q T D d hd E) := by
  rw [sum_signedOctadFourContribution_subtype Q T E _ (octadTetradCosetLabel_code Q T D d hd E)]
  refine octadFibreRow_sum O T E (fun F hF => by
    rw [octadTetradFibre_intersection O T hT E F (Ne.symm hF), hT])
    (fun b => signedOctadFourContribution (octadTetradCosetLabel Q T D d hd E)
      (calibratedHyperplaneLift Q b))
    (fun F => signedOctadVector (octadTetradCosetLabel Q T D d hd F)) ?_
  intro F hF
  exact octadTetradCosetLabel_fourContribution Q T hT D d hd E F hF

end Atlas.Fischer
