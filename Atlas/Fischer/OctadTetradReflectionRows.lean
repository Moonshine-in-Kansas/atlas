import Atlas.Fischer.OctadTetradThetaContributions

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual first four rows of the eight-dimensional reflection, with every
scalar and theta coefficient fixed by the calibrated Parker labels. -/
theorem rootMap_octadic_tetrad_first_row {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hT : T.card = 4) (D : OctadTetradFibre O T)
    (d : ParkerLoop) (hd : d.1 = octadWord D.val) (E : OctadTetradFibre O T) :
    rootMap (octadicRoot Q 0) (signedOctadVector (octadTetradCosetLabel Q T D d hd E)) =
      (1 / 4 : Scalar) •
        ((∑ F : OctadTetradFibre O T, signedOctadVector (octadTetradCosetLabel Q T D d hd F)) -
          (2 : Scalar) • signedOctadVector (octadTetradCosetLabel Q T D d hd E)) +
      (theta / 4) •
        ((∑ F : OctadTetradFibre O T, signedOctadVector (octadTetradComplementLabel Q T hT D d hd F)) -
          (2 : Scalar) • signedOctadVector (octadTetradComplementLabel Q T hT D d hd E)) := by
  have hI := octadTetradCosetLabel_intersection Q T hT D d hd E
  rw [rootMap_octadic_crossing Q _ (by omega) (by omega), hI,
    signedOctadFourContribution, dif_pos hI,
    octadTetrad_scalar_contribution_sum Q T hT D d hd E,
    octadTetrad_theta_contribution_sum Q T hT D d hd E]
  change ((3 - (4 : Scalar)) / 4) • signedOctadVector (octadTetradCosetLabel Q T D d hd E) -
    (theta / 4) • signedOctadVector (octadTetradComplementLabel Q T hT D d hd E) + _ + _ = _
  module

end Atlas.Fischer
