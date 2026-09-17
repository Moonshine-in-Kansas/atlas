import Atlas.Fischer.OctadDuadCosetLabels
import Atlas.Fischer.OctadScalarBlockGeometry
import Atlas.Fischer.SignedCoordinateIndependence

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra

theorem octadTranslatedSignedOctad_support {O : Octad} (Q : OctadCalibration O)
    (d : SignedOctad) (t : BinaryFour) :
    signedOctadSupport (octadTranslatedSignedOctad Q d t)=
      octadTranslatedOctad O (signedOctadSupport d) t := by
  apply (signedOctadSupport_eq_iff _ _).mpr
  rw [octadTranslatedSignedOctad_code,octadTranslatedOctad_word,octadWord_signedSupport]

def octadDuadSignedFamily {O : Octad} (Q : OctadCalibration O) (d : SignedOctad) :
    BinaryFour → Coordinates := fun t => signedOctadVector (octadTranslatedSignedOctad Q d t)

theorem octadDuadSignedFamily_independent {O : Octad} (Q : OctadCalibration O)
    (d : SignedOctad) (hd : (support d.val.1.val ∩ O.val).card=2) :
    LinearIndependent Scalar (octadDuadSignedFamily Q d) := by
  let j : BinaryFour → CoordinateIndex := fun t =>
    Sum.inr (signedOctadSupport (octadTranslatedSignedOctad Q d t))
  have hj : Function.Injective j := by
    intro s t h
    have hs := Sum.inr.inj h
    have hc := congrArg octadWord hs
    simp only [octadWord_signedSupport,octadTranslatedSignedOctad_code] at hc
    exact octadTranslatedWord_duad_injective O d.val.1 hd hc
  exact signedCoordinate_linearIndependent j hj
    (fun t => (octadTranslatedSignedOctad Q d t).val.2)

theorem octadDuadSignedFamily_mem {O : Octad} (Q : OctadCalibration O) (d : SignedOctad)
    (t : BinaryFour) : octadDuadSignedFamily Q d t ∈
      octadScalarBlock O (support d.val.1.val ∩ O.val) := by
  apply Submodule.smul_mem
  apply coordinateVector_mem_octadScalarBlock
  refine ⟨0,?_⟩
  change (signedOctadSupport (octadTranslatedSignedOctad Q d t)).val ∩ O.val=_
  rw [octadTranslatedSignedOctad_support,octadTranslatedOctad_intersection]
  rfl

/-- The actual translated signed octads are a basis of the intended 16-block. -/
theorem octadDuadSignedFamily_span {O : Octad} (Q : OctadCalibration O) (d : SignedOctad)
    (hd : (support d.val.1.val ∩ O.val).card=2) :
    Submodule.span Scalar (Set.range (octadDuadSignedFamily Q d))=
      octadScalarBlock O (support d.val.1.val ∩ O.val) := by
  apply Submodule.eq_of_le_of_finrank_le
  · apply Submodule.span_le.mpr
    rintro x ⟨t,rfl⟩
    exact octadDuadSignedFamily_mem Q d t
  · rw [finrank_span_eq_card (octadDuadSignedFamily_independent Q d hd),
      octadScalarBlock_duad_dimension O _ Finset.inter_subset_right hd]
    decide

end Atlas.Fischer
