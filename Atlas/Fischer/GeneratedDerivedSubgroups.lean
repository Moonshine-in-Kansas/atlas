import Atlas.Fischer.GeneratedPositivePerfect
import Atlas.Algebra.PerfectKernelDerived

namespace Atlas.Fischer

/-- The generated algebra group's derived subgroup is exactly its actual
linear, even-parity subgroup. -/
theorem rootGeneratedAlgebra_commutator : commutator rootGeneratedAlgebraGroup =
    rootGeneratedAlgebraParity.ker := by
  letI := rootGeneratedAlgebraParity_kernel_perfect
  exact Atlas.Algebra.commutator_eq_perfect_kernel rootGeneratedAlgebraParity

/-- The ray group's derived subgroup is exactly the descended parity kernel. -/
theorem rootGeneratedRay_commutator : commutator rootGeneratedRayGroup = rootGeneratedRayParity.ker := by
  letI := rootGeneratedRayParity_kernel_perfect
  exact Atlas.Algebra.commutator_eq_perfect_kernel rootGeneratedRayParity

theorem rootGeneratedAlgebraParity_index : rootGeneratedAlgebraParity.ker.index=2 :=
  Atlas.Algebra.binary_parity_kernel_index rootGeneratedAlgebraParity rootGeneratedAlgebraParity_surjective

theorem rootGeneratedRayParity_index : rootGeneratedRayParity.ker.index=2 :=
  Atlas.Algebra.binary_parity_kernel_index rootGeneratedRayParity rootGeneratedRayParity_surjective

theorem rootGeneratedAlgebra_commutator_index : (commutator rootGeneratedAlgebraGroup).index=2 := by
  rw [rootGeneratedAlgebra_commutator]
  exact rootGeneratedAlgebraParity_index

theorem rootGeneratedRay_commutator_index : (commutator rootGeneratedRayGroup).index=2 := by
  rw [rootGeneratedRay_commutator]
  exact rootGeneratedRayParity_index

end Atlas.Fischer
