import Atlas.Fischer.OctadDuadRowSum
import Atlas.Fischer.OctadDuadDisjointExclusion

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra
attribute [local instance] Classical.propDecidable

/-- The actual octadic root map is the nondegenerate polar-character matrix in
the actual translated signed basis. All Parker signs are retained. -/
theorem rootMap_octadic_duad_row {O : Octad} (Q : OctadCalibration O) (d : SignedOctad)
    (hd : (support d.val.1.val ∩ O.val).card=2) (s : BinaryFour) :
    rootMap (octadicRoot Q 0) (octadDuadSignedFamily Q d s)=octadDuadCharacterRow Q d s := by
  let ds := octadTranslatedSignedOctad Q d s
  have ho : signedOctadSupport Q.octadLift=O :=
    (signedOctadSupport_eq_iff _ _).mpr Q.lift_code
  have hi : ((signedOctadSupport ds).val ∩ O.val).card=2 := by
    rw [octadTranslatedSignedOctad_support,octadTranslatedOctad_intersection]
    exact hd
  have h2 : signedOctadIntersection ds Q.octadLift=2 := by
    unfold signedOctadIntersection
    rw [ho]
    exact hi
  have hfour : signedOctadFourContribution ds Q.octadLift=0 := by
    simp [signedOctadFourContribution,h2]
  have hdisjoint (b : OctadShortenedHyperplane O) :
      signedOctadDisjointContribution ds (calibratedHyperplaneLift Q b)=0 := by
    have hn := octadDuad_shortened_overlap_ne_zero O (signedOctadSupport ds) hi b
    rw [octadWord_signedSupport] at hn
    have hh : signedOctadIntersection ds (calibratedHyperplaneLift Q b) ≠ 0 := by
      rw [signedOctadIntersection_overlap]
      exact hn
    simp [signedOctadDisjointContribution,hh]
  change rootMap (octadicRoot Q 0) (signedOctadVector ds)=_
  rw [rootMap_octadic_crossing Q ds (by omega) (by omega),h2,hfour,smul_zero,sub_zero]
  simp only [hdisjoint,Finset.sum_const_zero,smul_zero,add_zero]
  rw [octadDuadFourContribution_sum Q d hd s]
  change _=octadDuadCharacterRow Q d s
  unfold octadDuadCharacterRow
  norm_num
  dsimp only [ds,octadDuadSignedFamily]
  module

/-- Invariance of the intended actual duad scalar block. -/
theorem rootMap_octadic_duad_invariant {O : Octad} (Q : OctadCalibration O) (d : SignedOctad)
    (hd : (support d.val.1.val ∩ O.val).card=2) :
    Set.MapsTo (rootMap (octadicRoot Q 0))
      (octadScalarBlock O (support d.val.1.val ∩ O.val))
      (octadScalarBlock O (support d.val.1.val ∩ O.val)) := by
  rw [← octadDuadSignedFamily_span Q d hd]
  apply rootMap_invariant_span
  rintro x ⟨s,rfl⟩
  rw [rootMap_octadic_duad_row Q d hd s]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro t _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨t,rfl⟩

/-- Antiunitarity on the actual duad block follows from the verified literal rows. -/
theorem rootMap_octadic_duad_antiunitary {O : Octad} (Q : OctadCalibration O) (d : SignedOctad)
    (hd : (support d.val.1.val ∩ O.val).card=2) :
    RootMapAntiunitaryOn (octadicRoot Q 0) (octadScalarBlock O (support d.val.1.val ∩ O.val)) := by
  rw [← octadDuadSignedFamily_span Q d hd]
  apply rootMap_antiunitary_span
  rintro x ⟨s,rfl⟩ y ⟨t,rfl⟩
  rw [rootMap_octadic_duad_row Q d hd s,rootMap_octadic_duad_row Q d hd t,
    octadDuadCharacterRow_orthonormal Q d hd s t,octadDuadSignedFamily_orthonormal Q d hd s t]
  split_ifs <;> simp

end Atlas.Fischer
