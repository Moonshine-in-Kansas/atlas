import Atlas.Fischer.OctadDuadRowIndex
import Atlas.Fischer.OctadDuadProductSigns
import Atlas.Fischer.OctadDuadMatrixIsometry
import Atlas.Fischer.OctadFibreContributionSums

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The literal hyperplane sum is the off-diagonal polar-character row. -/
theorem octadDuadFourContribution_sum {O : Octad} (Q : OctadCalibration O) (d : SignedOctad)
    (hd : (support d.val.1.val ∩ O.val).card=2) (s : BinaryFour) :
    (∑ b : OctadShortenedHyperplane O,
      signedOctadFourContribution (octadTranslatedSignedOctad Q d s) (calibratedHyperplaneLift Q b)) =
      (∑ t : BinaryFour,
        parkerScalarSign ((binaryQuadraticWordForm (octadQuadraticRestriction O d.val.1)).polarBilin s t) •
          octadDuadSignedFamily Q d t) - octadDuadSignedFamily Q d s := by
  let E := octadDuadCoordinateEquiv O d hd s
  let e := octadDuadRowIndexEquiv O d hd s
  let v : BinaryFour → Coordinates := fun t =>
    parkerScalarSign ((binaryQuadraticWordForm (octadQuadraticRestriction O d.val.1)).polarBilin s t) •
      octadDuadSignedFamily Q d t
  have hcode : (octadTranslatedSignedOctad Q d s).val.1=octadWord E.val := by
    rw [octadTranslatedSignedOctad_code,octadDuadCoordinateEquiv_word]
  rw [sum_signedOctadFourContribution_subtype Q _ E _ hcode]
  have hv (b : OctadFibreRowHyperplanes O _ E) :
      signedOctadFourContribution (octadTranslatedSignedOctad Q d s)
        (calibratedHyperplaneLift Q b.val)=v (e b).val := by
    rw [signedOctadFourContribution_row Q _ E _ hcode]
    exact octadDuadProductFour_sign Q d hd s (e b).val b.val
      (octadFibreRow_signed_intersection Q _ E _ hcode b) (octadDuadRowIndex_code O d hd s b)
  simp_rw [hv]
  rw [e.sum_comp (fun t : {t : BinaryFour // t ≠ s} => v t.val)]
  have he : (∑ t : {t : BinaryFour // t ≠ s},v t.val)=
      ∑ t ∈ (Finset.univ.erase s : Finset BinaryFour),v t := by
    symm
    apply Finset.sum_subtype
    intro t
    simp
  rw [he]
  have hs : v s=octadDuadSignedFamily Q d s := by
    have hz : (binaryQuadraticWordForm (octadQuadraticRestriction O d.val.1)).polarBilin s s=0 := by
      simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar_self,
        two_nsmul,CharTwo.add_self_eq_zero]
    simp [v,hz,parkerScalarSign]
  have hsum := eq_sub_iff_add_eq.mpr (Finset.sum_erase_add Finset.univ v (Finset.mem_univ s))
  rw [hs] at hsum
  exact hsum

end Atlas.Fischer
