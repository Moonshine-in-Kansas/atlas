import Atlas.Fischer.ResidueFrameKernel
import Atlas.Fischer.ResidueFrameMathieuImage

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem fullFrameProjection_basic (e : basicFrameStabilizer) (i : Omega) :
    (fullSemilinearRayProjection e.val).val (displayedRayOfParameter (.inl i))=
      displayedRayOfParameter (.inl ((basicFrameCoordinateHom e).val i)) := by
  apply Subtype.ext
  change (semilinearDisplayedRayAction e.val (displayedRayOfParameter (.inl i))).val=_
  rw [semilinearDisplayedRayAction_parameter_value]
  exact basicFrameCoordinate_ray e i

theorem residueFrameCoordinate_kernel (S : Finset Omega) (e : basicFrameStabilizer)
    (he : basicFrameCoordinateHom e=1) :
    fullSemilinearRayProjection e.val ∈ residueGenerated S := by
  apply basicFramePointwiseRayStabilizer_le_residueGenerated S
  rw [mem_basicFramePointwiseRayStabilizer_iff]
  intro i
  rw [fullFrameProjection_basic,he]
  rfl

theorem residueFullFrame_mem_generated (S : Finset Omega) (hS : S.card ≤ 2)
    (e : basicFrameStabilizer)
    (he : basicFrameCoordinateHom e ∈ fixingSubgroup Mathieu24CodeModel (S : Set Omega)) :
    fullSemilinearRayProjection e.val ∈ residueGenerated S := by
  obtain ⟨f,hf,hfe⟩ := mathieuFixing_le_residueFrameMathieuImage S hS he
  have hk : basicFrameCoordinateHom (f⁻¹*e)=1 := by
    rw [map_mul,map_inv,hfe,inv_mul_cancel]
  have hh := (residueGenerated S).mul_mem hf (residueFrameCoordinate_kernel S _ hk)
  change fullSemilinearRayProjection f.val *
    fullSemilinearRayProjection (f.val⁻¹*e.val) ∈ residueGenerated S at hh
  simpa only [map_mul,map_inv,mul_inv_cancel_left] using hh

/-- The full marked standard-frame stabilizer is contained in the actual
residue-generated subgroup, by its coordinate image and literal cocode kernel. -/
theorem residueMarkedFrame_le_generated (S : Finset Omega) (hS : S.card ≤ 2) :
    standardFrameRayStabilizer ⊓ residueCentralizer S ≤ residueGenerated S := by
  intro g hg
  have hp := hg.1
  rw [← parkerRayHom_range] at hp
  obtain ⟨h,rfl⟩ := hp
  let e : basicFrameStabilizer :=
    ⟨scalarAlgebraRepresentation 1 * parkerAlgebraRepresentation h,
      scalar_parker_mem_basicFrameStabilizer 1 h⟩
  have hc : basicFrameCoordinateHom e ∈
      fixingSubgroup Mathieu24CodeModel (S : Set Omega) := by
    rw [basicFrameCoordinateHom_scalar_parker]
    intro i
    exact (parkerRayHom_commutes_basic_iff h i.val).mp
      ((hg.2 _ ⟨i.val,i.property,rfl⟩).symm)
  have he := residueFullFrame_mem_generated S hS e hc
  simpa only [e,map_one,one_mul,parkerRayHom,MonoidHom.comp_apply] using he

end Atlas.Fischer
