import Atlas.Fischer.PointwiseAxisCocodeClassification
import Atlas.Fischer.ParkerStandardSurjectivity

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- A prescribed scalar times actual Golay coordinate permutation lifts to the
retained Parker representation; the remaining pointwise stabilizer is cocode. -/
theorem axisPermutation_scalar_parker_factor (e : SemilinearAlgebraAutomorphism)
    (a : Mu3) (g : Mathieu24CodeModel)
    (he : ∀ i, e.val (u i)=a.val.val • u (g.val i)) :
    ∃ h : ParkerStandardGroup,
      e=scalarAlgebraRepresentation a * parkerAlgebraRepresentation h := by
  obtain ⟨h,hh⟩ := parkerStandardProjection_surjective g
  let b := scalarAlgebraRepresentation a * parkerAlgebraRepresentation h
  have hb (i : Omega) : b.val (u i)=e.val (u i) := by
    change a.val.val • parkerCoordinateAction h (u i)=e.val (u i)
    rw [parkerCoordinateAction_u,hh]
    exact (he i).symm
  let f := b⁻¹ * e
  have hf : ∀ i, f.val (u i)=u i := by
    intro i
    change b.val.symm (e.val (u i))=u i
    rw [← hb i]
    exact b.val.symm_apply_apply _
  obtain ⟨d,hd,_⟩ := pointwiseAxis_unique_cocode f hf
  refine ⟨h * parkerCocodeEmbedding d,?_⟩
  rw [map_mul,← mul_assoc]
  change e=b * cocodeAlgebraHom d
  rw [← hd]
  change e=b * (b⁻¹ * e)
  simp

end Atlas.Fischer
