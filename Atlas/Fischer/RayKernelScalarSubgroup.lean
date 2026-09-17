import Atlas.Fischer.RayKernelScalarRigidity
import Atlas.Fischer.ParkerAlgebraRepresentation

namespace Atlas.Fischer

/-- The actual ray kernel is the image of the retained cubic scalar embedding. -/
theorem semilinearRayKernel_eq_scalar_range :
    semilinearRayKernel = scalarAlgebraRepresentation.range := by
  ext e
  rw [mem_semilinearRayKernel_scalar_iff]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨a,?_⟩
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact (ha x).symm
  · rintro ⟨a,rfl⟩
    exact ⟨a,fun _ => rfl⟩

/-- The scalar subgroup is normal in the full semilinear algebra group.
No centrality in that larger group is asserted. -/
theorem scalarAlgebraRepresentation_range_normal :
    scalarAlgebraRepresentation.range.Normal := by
  rw [← semilinearRayKernel_eq_scalar_range]
  change semilinearDisplayedRayAction.ker.Normal
  infer_instance

end Atlas.Fischer
