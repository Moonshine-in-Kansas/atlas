import Atlas.LinearGroups.Chevalley.TwistedE6.CompanionTwist
import Atlas.LinearGroups.Chevalley.TwistedE6.CubicKernel
import Atlas.GroupTheory.GraphFieldCubicKernel

/-! A proved surjection between the two actual fixed groups. The proof uses
an explicit cubic-kernel correction of lifts. The kernel is central, but its
size and equality with the full center of the fixed group are not assumed. -/
noncomputable section
namespace Atlas.Chevalley.TwistedE6
open Atlas.GroupTheory
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem companionFixedProjection_surjective (hdeg : Module.finrank F K = 2) :
    Function.Surjective (companionFixedProjection F K) :=
  fixedSubgroupMap_surjective_of_cubic_kernel (companionTwist F K) (adjointTwist F K)
    (selectedWeightCompanionRho .E6 K) (companionTwist_involutive F K hdeg)
    (companionTwist_rho F K) (selectedWeightCompanionRho_surjective .E6 K)
    (companion_rhoKernel_cube K)

theorem companionFixedProjection_kernel_central :
    (companionFixedProjection F K).ker ≤ Subgroup.center (companionFixedSubgroup F K) := by
  intro g hg
  have hrho : g.val ∈ (selectedWeightCompanionRho .E6 K).ker :=
    congrArg Subtype.val hg
  have hcentral : g.val ∈ Subgroup.center (SelectedWeightCompanion .E6 K) := by
    rw [selectedWeightCompanion_center_eq_rhoKernel]
    exact hrho
  apply Subgroup.mem_center_iff.mpr
  intro h
  exact Subtype.ext ((Subgroup.mem_center_iff.mp hcentral) h.val)

theorem companionFixedProjection_kernel_cube (g : companionFixedSubgroup F K)
    (hg : g ∈ (companionFixedProjection F K).ker) : g ^ 3 = 1 :=
  Subtype.ext (companion_rhoKernel_cube K g.val (congrArg Subtype.val hg))

/-- Quotient by the proved central kernel, without asserting that it is yet
the entire center of the fixed group. -/
def companionFixedQuotientEquiv (hdeg : Module.finrank F K = 2) :
    companionFixedSubgroup F K ⧸ (companionFixedProjection F K).ker ≃*
      adjointFixedSubgroup F K :=
  QuotientGroup.quotientKerEquivOfSurjective (companionFixedProjection F K)
    (companionFixedProjection_surjective F K hdeg)

@[simp] theorem companionFixedQuotientEquiv_mk (hdeg : Module.finrank F K = 2)
    (g : companionFixedSubgroup F K) :
    companionFixedQuotientEquiv F K hdeg (QuotientGroup.mk g) =
      companionFixedProjection F K g := rfl

end Atlas.Chevalley.TwistedE6
