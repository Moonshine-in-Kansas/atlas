import Atlas.Fischer.GeneratedFrameMathieuFull
import Atlas.Fischer.GeneratedRayPreimageEquality
import Atlas.Fischer.GeneratedCocode

noncomputable section
namespace Atlas.Fischer

/-- The actual coordinate kernel of the full frame stabilizer already lies in
the generated algebra subgroup: its factors are retained scalars and cocode. -/
theorem basicFrameCoordinate_kernel_generated (e : basicFrameStabilizer)
    (he : basicFrameCoordinateHom e=1) : e.val ∈ rootGeneratedAlgebraGroup := by
  obtain ⟨a,h,hh⟩ := (mem_basicFrameStabilizer_iff_scalar_parker e.val).mp e.property
  have heq : e=⟨scalarAlgebraRepresentation a * parkerAlgebraRepresentation h,
      scalar_parker_mem_basicFrameStabilizer a h⟩ := Subtype.ext hh
  rw [heq,basicFrameCoordinateHom_scalar_parker] at he
  have hk : h ∈ parkerCocodeEmbedding.range := by
    rw [parkerCocodeEmbedding_range]
    exact he
  obtain ⟨d,hd⟩ := hk
  rw [hh,← hd]
  exact rootGeneratedAlgebraGroup.mul_mem (scalarAlgebraRepresentation_mem_generated a)
    (cocodeAlgebraHom_mem d)

/-- Every full standard-frame stabilizer belongs to the root-generated algebra
group. Equality follows from actual quotient image and kernel containment. -/
theorem basicFrameStabilizer_le_generated : basicFrameStabilizer ≤ rootGeneratedAlgebraGroup := by
  intro e he
  let E : basicFrameStabilizer := ⟨e,he⟩
  have hm : basicFrameCoordinateHom E ∈ generatedFrameMathieuImage := by
    rw [generatedFrameMathieuImage_eq_top]
    trivial
  obtain ⟨f,hf,hfe⟩ := hm
  have hfg : f.val ∈ rootGeneratedAlgebraGroup := by
    rw [← generatedRayPreimage_eq]
    exact hf
  have hk : basicFrameCoordinateHom (f⁻¹*E)=1 := by
    rw [map_mul,map_inv,hfe,inv_mul_cancel]
  have h := rootGeneratedAlgebraGroup.mul_mem hfg (basicFrameCoordinate_kernel_generated _ hk)
  change f.val * (f.val⁻¹*e) ∈ rootGeneratedAlgebraGroup at h
  simpa only [mul_inv_cancel_left] using h

theorem generatedBasicFrameStabilizer_eq_top : generatedBasicFrameStabilizer=⊤ := by
  apply top_unique
  intro e _
  change e.val ∈ generatedRayPreimage
  rw [generatedRayPreimage_eq]
  exact basicFrameStabilizer_le_generated e.property

/-- Parker containment is a conclusion of actual frame geometry. -/
theorem parkerAlgebraRepresentation_mem_generated (h : ParkerStandardGroup) :
    parkerAlgebraRepresentation h ∈ rootGeneratedAlgebraGroup := by
  apply basicFrameStabilizer_le_generated
  simpa only [map_one,one_mul] using scalar_parker_mem_basicFrameStabilizer 1 h

end Atlas.Fischer
