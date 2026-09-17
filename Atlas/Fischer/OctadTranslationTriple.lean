import Atlas.Fischer.OctadDuadCosetLabels
import Atlas.Algebra.BinaryQuadraticContractionConstants

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra
open scoped BigOperators

/-- The actual Parker triple on a shortened pair is the literal exterior sum. -/
theorem parkerTriple_shortened_exterior (O : Octad) (c : golay)
    (a b : octadShortenedCode O) :
    parkerTripleIntersection c.val a.val.val b.val.val =
      ∑ v : BinaryFour, octadExteriorWord O c v * octadAffineWord O a v *
        octadAffineWord O b v := by
  change (∑ i : Omega, c.val i*a.val.val i*b.val.val i)=_
  symm
  change (∑ v, c.val ((octadExteriorCoordinates O).symm v).val *
    a.val.val ((octadExteriorCoordinates O).symm v).val *
    b.val.val ((octadExteriorCoordinates O).symm v).val)=_
  rw [Equiv.sum_comp (octadExteriorCoordinates O).symm
    (fun i : OctadExterior O => c.val i.val*a.val.val i.val*b.val.val i.val)]
  have h := Fintype.sum_subtype_add_sum_subtype (fun i : Omega => i ∈ O.val)
    (fun i => c.val i*a.val.val i*b.val.val i)
  have hzfun : (fun i : {i : Omega // i ∈ O.val} =>
      c.val i.val*a.val.val i.val*b.val.val i.val)=0 := by
    funext i
    rw [(mem_octadShortenedCode O a.val).mp a.property i.val i.property,mul_zero,zero_mul]
    rfl
  simpa only [hzfun,Pi.zero_apply,Finset.sum_const_zero,zero_add] using h

/-- The shortened translation difference is the actual polar functional plus
its required quadratic constant. -/
theorem octadTranslationDifference_affine (O : Octad) (c : golay) (t v : BinaryFour) :
    octadAffineWord O (octadTranslationDifference O c t) v =
      (binaryQuadraticWordForm (octadQuadraticRestriction O c)).polarBilin t v +
        binaryQuadraticWordForm (octadQuadraticRestriction O c) t := by
  change (octadTranslatedWord O t c).val ((octadExteriorCoordinates O).symm v).val-
    c.val ((octadExteriorCoordinates O).symm v).val=_
  change octadExteriorWord O (octadTranslatedWord O t c) v-octadExteriorWord O c v=_
  rw [octadTranslatedWord_exterior]
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
    binaryQuadraticWordForm_apply,sub_eq_add_neg,CharTwo.neg_eq]
  change octadExteriorWord O c (v+t)+octadExteriorWord O c v =
    (octadExteriorWord O c (t+v)+octadExteriorWord O c 0+
      (octadExteriorWord O c t+octadExteriorWord O c 0)+
      (octadExteriorWord O c v+octadExteriorWord O c 0))+
      (octadExteriorWord O c t+octadExteriorWord O c 0)
  rw [add_comm t v]
  ring_nf
  simp only [show (2 : Bit)=0 from rfl,show (4 : Bit)=0 from rfl,
    mul_zero,add_zero,zero_add]

/-- The complete actual Parker sign reduces to a quadratic polar contraction;
no matrix sign equivalence is postulated. -/
theorem octadTranslationDifference_triple (O : Octad) (c : golay) (s t : BinaryFour) :
    parkerTripleIntersection c.val (octadTranslationDifference O c s).val.val
      (octadTranslationDifference O c t).val.val =
      ∑ v : BinaryFour, octadExteriorWord O c v *
        (binaryQuadraticWordForm (octadQuadraticRestriction O c)).polarBilin s v *
        (binaryQuadraticWordForm (octadQuadraticRestriction O c)).polarBilin t v := by
  rw [parkerTriple_shortened_exterior]
  simp_rw [octadTranslationDifference_affine]
  exact binaryQuadraticWord_contraction_constants (octadQuadraticRestriction O c) _ _ _ _

end Atlas.Fischer
