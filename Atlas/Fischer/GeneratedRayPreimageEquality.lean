import Atlas.Fischer.SemilinearGeneratedNormalizer
import Atlas.Fischer.GeneratedCubicScalars
import Atlas.Fischer.RayKernelScalarSubgroup

noncomputable section
namespace Atlas.Fischer

/-- Scalar containment makes the full inverse image of the generated ray group
exactly the originally generated algebra subgroup. -/
theorem generatedRayPreimage_eq : generatedRayPreimage=rootGeneratedAlgebraGroup := by
  apply le_antisymm
  · intro e he
    have hm : semilinearDisplayedRayAction e ∈ rootGeneratedAlgebraGroup.map semilinearDisplayedRayAction := by
      rw [rootGeneratedAlgebraGroup_ray_image]
      exact he
    obtain ⟨g,hg,hge⟩ := hm
    have hk : g⁻¹*e ∈ semilinearRayKernel := by
      change semilinearDisplayedRayAction (g⁻¹*e)=1
      rw [map_mul,map_inv,hge,inv_mul_cancel]
    rw [semilinearRayKernel_eq_scalar_range] at hk
    have hk' := scalarAlgebraRepresentation_range_le_generated hk
    have h := rootGeneratedAlgebraGroup.mul_mem hg hk'
    simpa only [mul_inv_cancel_left] using h
  · intro e he
    change semilinearDisplayedRayAction e ∈ rootGeneratedRayGroup
    rw [← rootGeneratedAlgebraGroup_ray_image]
    exact ⟨e,he,rfl⟩

end Atlas.Fischer
