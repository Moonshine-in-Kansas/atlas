import Atlas.LinearGroups.Chevalley.WeightCompanionAdjointKernelTorus
import Atlas.LinearGroups.Chevalley.WeightCompanionCentralTorusConverse

/-! The full adjoint projection has central kernel over every field.
Its kernel equals the central part of the actual torus. This does not yet
assert that every central element of the full group lies in that torus. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (K : Type*) [Field K]

theorem weightCompanion_rhoKernel_le_center
    (hdiamond : SimpleDiamondProducts P b) :
    (weightCompanionRho P b O hc hm K).ker ≤
      Subgroup.center (WeightCompanion P b O hc hm K) := by
  intro g hg
  exact weightCompanion_torus_kernel_central P b O hc hm K g
    (weightCompanion_rhoKernel_le_torus P b O hc hm K hdiamond hg) hg

theorem weightCompanion_rhoKernel_eq_torus_inf_center
    (hdiamond : SimpleDiamondProducts P b) :
    (weightCompanionRho P b O hc hm K).ker =
      weightCompanionTorusSubgroup P b O hc hm K ⊓
        Subgroup.center (WeightCompanion P b O hc hm K) := by
  rw [weightCompanion_torus_inf_center_eq_inf_kernel]
  exact weightCompanion_rhoKernel_eq_torus_inf_kernel P b O hc hm K hdiamond

end Atlas.Chevalley
