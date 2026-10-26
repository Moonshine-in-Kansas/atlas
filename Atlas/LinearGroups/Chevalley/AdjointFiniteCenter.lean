import Atlas.LinearGroups.Chevalley.WeightCompanionFiniteCenter
import Atlas.LinearGroups.Chevalley.WeightCompanionEmpty

/-! Centerlessness of the actual adjoint root-operator group over finite
fields. This uses the empty-family companion and its literal faithful rho,
not the invalid general claim that a quotient by a center is centerless. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule

/-- The empty weight family recovers the actual adjoint model. Its full center
is the kernel of the already injective literal projection. -/
theorem adjoint_center_eq_bot_finiteField
    {ι M N : Type u} [Fintype ι] [DecidableEq ι]
    [AddCommGroup M] [AddCommGroup N]
    (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (K : Type*) [Field K] [Finite K]
    (hdiamond : SimpleDiamondProducts P b) :
    Subgroup.center (Adjoint P b K) = ⊥ := by
  let O : PEmpty.{u+1} → Finset (WeightLattice P) := fun a => PEmpty.elim a
  have hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a := by
    intro a
    exact PEmpty.elim a
  have hm : ∀ a μ, μ ∈ O a → ∀ i,
      μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
        μ (corootElement P i) = 1 := by
    intro a
    exact PEmpty.elim a
  let e := weightCompanionAdjointEquivOfIsEmpty P b O hc hm K
  have hz : Subgroup.center (WeightCompanion P b O hc hm K) = ⊥ := by
    rw [weightCompanion_center_eq_rhoKernel_finiteField P b O hc hm K hdiamond]
    exact (weightCompanionRho P b O hc hm K).ker_eq_bot
      (weightCompanionRho_injective_of_isEmpty P b O hc hm K)
  rw [← Subgroup.map_center_eq e, hz, Subgroup.map_bot]

end Atlas.Chevalley
