import Atlas.Fischer.FischerGroupOrder
import Atlas.Fischer.GeneratedCentralExtension

noncomputable section
namespace Atlas.Fischer

/-- Order of the actual perfect parity kernel; simplicity is a later job. -/
theorem rootGeneratedRayPositive_order :
    Nat.card rootGeneratedRayParity.ker=1255205709190661721292800 := by
  have hc := rootGeneratedRayParity.ker.card_mul_index
  rw [rootGeneratedRayParity_index,rootGeneratedRayGroup_order_value] at hc
  omega

theorem fullSemilinearAlgebra_order :
    Nat.card SemilinearAlgebraAutomorphism=7531234255143970327756800 := by
  have hk : Nat.card fullSemilinearRayProjection.ker=3 := by
    rw [fullSemilinearRayProjection_kernel,
      ← Nat.card_congr (MonoidHom.ofInjective scalarAlgebraRepresentation_injective).toEquiv,mu3_card]
  have hc := fullSemilinearRayProjection.ker.card_mul_index
  rw [hk,Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr fullSemilinearRayProjection_surjective,Subgroup.card_top,
    rootGeneratedRayGroup_order_value] at hc
  exact hc.symm

theorem rootGeneratedAlgebraPositive_order :
    Nat.card rootGeneratedAlgebraParity.ker=3765617127571985163878400 := by
  have hc := rootGeneratedPositiveProjection.ker.card_mul_index
  rw [rootGeneratedPositiveProjection_kernel_card,Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr rootGeneratedPositiveProjection_surjective,Subgroup.card_top,
    rootGeneratedRayPositive_order] at hc
  exact hc.symm

end Atlas.Fischer
