import Atlas.LinearGroups.Chevalley.PositiveWitnessedSelfNormalizer
import Atlas.LinearGroups.Chevalley.PositiveWitnessedOppositeTorusIntersection
import Atlas.LinearGroups.Chevalley.WeightCompanionAdjointCentralKernel

/-! Over finite fields, the entire center of the actual companion is exactly
its adjoint projection kernel. No whole-group order or recognition is used. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData Atlas.GroupTheory
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (K : Type*) [Field K] [Finite K] [Fintype κ]

theorem weightCompanion_center_le_torus_finiteField
    (hdiamond : SimpleDiamondProducts P b) :
    Subgroup.center (WeightCompanion P b O hc hm K) ≤
      weightCompanionTorusSubgroup P b O hc hm K := by
  intro g hg
  have hb := weightCompanion_center_le_positiveWitnessedTorusJoin
    P b O hc hm K hdiamond hg
  apply mem_torus_of_mem_positiveWitnessed_and_opposite_join
    P b O hc hm K hdiamond g hb
  refine ⟨g, hb, ?_⟩
  let n := (weightCompanionTitsLift P b O hc hm K (rootWeylLongest P b)).val
  change n * g * n⁻¹ = g
  rw [Subgroup.mem_center_iff.mp hg n]
  group

theorem weightCompanion_center_le_rhoKernel_finiteField
    (hdiamond : SimpleDiamondProducts P b) :
    Subgroup.center (WeightCompanion P b O hc hm K) ≤
      (weightCompanionRho P b O hc hm K).ker := by
  intro g hg
  exact weightCompanion_torus_center_rho_eq_one P b O hc hm K g
    (weightCompanion_center_le_torus_finiteField P b O hc hm K hdiamond hg) hg

theorem weightCompanion_center_eq_rhoKernel_finiteField
    (hdiamond : SimpleDiamondProducts P b) :
    Subgroup.center (WeightCompanion P b O hc hm K) =
      (weightCompanionRho P b O hc hm K).ker :=
  le_antisymm (weightCompanion_center_le_rhoKernel_finiteField P b O hc hm K hdiamond)
    (weightCompanion_rhoKernel_le_center P b O hc hm K hdiamond)

end Atlas.Chevalley
