import Atlas.Fischer.FischerPositiveSimplicity
import Atlas.Fischer.GeneratedCentralNonsplit
import Atlas.GroupTheory.CenterKernel

noncomputable section
namespace Atlas.Fischer

theorem rootGeneratedRayPositive_center :
    Subgroup.center rootGeneratedRayParity.ker=⊥ := by
  letI := rootGeneratedRayPositive_simple
  rcases (inferInstance : (Subgroup.center rootGeneratedRayParity.ker).Normal).eq_bot_or_eq_top
    with h | h
  · exact h
  · exact (rootGeneratedRayPositive_noncommutative (Subgroup.center_eq_top_iff.mp h)).elim

/-- The center of the actual faithful linear triple cover is precisely its
retained scalar subgroup, using the now proved nonabelian simple quotient. -/
theorem rootGeneratedAlgebraPositive_center :
    Subgroup.center rootGeneratedAlgebraParity.ker=positiveScalarHom.range := by
  rw [← rootGeneratedPositiveProjection_kernel]
  exact Atlas.GroupTheory.center_eq_kernel_of_surjective rootGeneratedPositiveProjection
    rootGeneratedPositiveProjection_surjective rootGeneratedRayPositive_center
    rootGeneratedPositiveProjection_kernel_central

theorem rootGeneratedAlgebraPositive_order_triple :
    Nat.card rootGeneratedAlgebraParity.ker=3*Nat.card rootGeneratedRayParity.ker := by
  rw [rootGeneratedAlgebraPositive_order,rootGeneratedRayPositive_order]

theorem fullSemilinearAlgebra_order_triple :
    Nat.card SemilinearAlgebraAutomorphism=3*Nat.card rootGeneratedRayGroup := by
  rw [fullSemilinearAlgebra_order,rootGeneratedRayGroup_order_value]

end Atlas.Fischer
