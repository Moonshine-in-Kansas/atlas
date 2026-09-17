import Atlas.Fischer.OctadTetradScalarContributions
import Atlas.Fischer.OctadTetradPairedLabels
import Atlas.Fischer.CalibratedComplementIntersections

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Complementation reindexes the actual disjoint branch onto the same four-intersection row. -/
theorem sum_signedOctadDisjointContribution_complement {O : Octad} (Q : OctadCalibration O)
    (d : SignedOctad) :
    (∑ b : OctadShortenedHyperplane O, signedOctadDisjointContribution d (calibratedHyperplaneLift Q b)) =
      ∑ b : OctadShortenedHyperplane O, signedOctadDisjointContribution d
        (calibratedHyperplaneLift Q (octadHyperplaneComplement O b)) := by
  let e : OctadShortenedHyperplane O ≃ OctadShortenedHyperplane O :=
    ⟨octadHyperplaneComplement O, octadHyperplaneComplement O,
      octadHyperplaneComplement_involutive O, octadHyperplaneComplement_involutive O⟩
  exact (e.sum_comp _).symm

theorem octadTetradCosetLabel_disjointContribution {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hT : T.card = 4) (D : OctadTetradFibre O T)
    (d : ParkerLoop) (hd : d.1 = octadWord D.val) (E F : OctadTetradFibre O T) (hFE : F ≠ E) :
    signedOctadDisjointContribution (octadTetradCosetLabel Q T D d hd E)
      (calibratedHyperplaneLift Q (octadHyperplaneComplement O
        (octadFibreSumHyperplane O T E F
          (by rw [octadTetradFibre_intersection O T hT E F (Ne.symm hFE), hT])))) =
      signedOctadVector (octadTetradComplementLabel Q T hT D d hd F) := by
  let b := octadFibreSumHyperplane O T E F
    (by rw [octadTetradFibre_intersection O T hT E F (Ne.symm hFE), hT])
  have hD : ((signedOctadSupport (octadTetradCosetLabel Q T D d hd E)).val ∩ O.val).card = 4 := by
    rw [octadTetradCosetLabel_support, E.property, hT]
  have hI : signedOctadIntersection (octadTetradCosetLabel Q T D d hd E)
      (calibratedHyperplaneLift Q b) = 4 := by
    rw [signedOctadIntersection_overlap, octadTetradCosetLabel_code]
    exact octadFibreSumHyperplane_overlap O T E F
      (by rw [octadTetradFibre_intersection O T hT E F (Ne.symm hFE), hT])
  have h0 := (calibratedHyperplane_complement_disjoint_iff Q _ hD b).mpr hI
  change signedOctadDisjointContribution _ (calibratedHyperplaneLift Q (octadHyperplaneComplement O b)) = _
  rw [signedOctadDisjointContribution, dif_pos h0]
  congr 1
  apply Subtype.ext
  change parkerLoopMultiply (parkerLoopMultiply (octadTetradCosetLabel Q T D d hd E).val
    (Q.parkerSection.lift (octadHyperplaneComplement O b).val)) parkerOmega = _
  rw [calibratedComplement_product_label]
  change parkerLoopMultiply (parkerLoopMultiply (octadTetradCosetLabel Q T D d hd E).val
    (Q.parkerSection.lift (octadFibreSum O T E F))) Q.octadLift.val = _
  rw [← octadTetradDifference_sum O T D E F,
    octadTetradCosetLabel_multiply Q T hT D d hd E F]
  rfl


/-- Exact theta-part sum, with the same off-diagonal index set and actual product labels. -/
theorem octadTetrad_theta_contribution_sum {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hT : T.card = 4) (D : OctadTetradFibre O T)
    (d : ParkerLoop) (hd : d.1 = octadWord D.val) (E : OctadTetradFibre O T) :
    (∑ b : OctadShortenedHyperplane O,
      signedOctadDisjointContribution (octadTetradCosetLabel Q T D d hd E)
        (calibratedHyperplaneLift Q b)) =
      (∑ F : OctadTetradFibre O T, signedOctadVector (octadTetradComplementLabel Q T hT D d hd F)) -
        signedOctadVector (octadTetradComplementLabel Q T hT D d hd E) := by
  rw [sum_signedOctadDisjointContribution_complement]
  have hD : ((signedOctadSupport (octadTetradCosetLabel Q T D d hd E)).val ∩ O.val).card = 4 := by
    rw [octadTetradCosetLabel_support, E.property, hT]
  let G := fun b : OctadShortenedHyperplane O =>
    signedOctadDisjointContribution (octadTetradCosetLabel Q T D d hd E)
      (calibratedHyperplaneLift Q (octadHyperplaneComplement O b))
  have hs : (∑ b : OctadShortenedHyperplane O, G b) =
      ∑ b : OctadFibreRowHyperplanes O T E, G b.val := by
    symm
    apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
    · intro b hb
      have hn : signedOctadIntersection (octadTetradCosetLabel Q T D d hd E)
          (calibratedHyperplaneLift Q (octadHyperplaneComplement O b)) ≠ 0 := by
        intro h
        have h4 := (calibratedHyperplane_complement_disjoint_iff Q _ hD b).mp h
        rw [signedOctadIntersection_overlap, octadTetradCosetLabel_code] at h4
        exact hb ⟨⟨b, h4⟩, rfl⟩
      exact dif_neg hn
    · intro b
      rfl
  change (∑ b, G b) = _
  rw [hs]
  refine octadFibreRow_sum O T E (fun F hF => by
    rw [octadTetradFibre_intersection O T hT E F (Ne.symm hF), hT]) G
    (fun F => signedOctadVector (octadTetradComplementLabel Q T hT D d hd F)) ?_
  intro F hF
  exact octadTetradCosetLabel_disjointContribution Q T hT D d hd E F hF

end Atlas.Fischer
