import Atlas.GroupTheory.SolvableSemidirect
import Atlas.LinearGroups.Chevalley.PositiveWitnessedNilpotent
import Atlas.LinearGroups.Chevalley.PositiveWitnessedTorusJoin
import Atlas.LinearGroups.Chevalley.WeightCompanionTorusOrder

/-! Solvability of the actual torus and positive/torus subgroup. The latter
uses its proved internal semidirect product and nilpotence of the actual U. -/
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

theorem weightCompanionTorusSubgroup_isSolvable (R : Type*) [CommRing R] :
    Group.IsSolvable (weightCompanionTorusSubgroup P b O hc hm R) := by
  rw [weightCompanionTorusSubgroup_eq_range]
  exact Group.isSolvable_of_surjective
    (weightCompanionTorusParameters P b O hc hm R).rangeRestrict_surjective

theorem positiveWitnessedTorusJoin_isSolvable (K : Type*) [Field K] [Finite K]
    [Fintype κ] (hdiamond : SimpleDiamondProducts P b) :
    Group.IsSolvable (positiveWitnessedTorusJoin P b O hc hm K) := by
  letI := positiveWitnessedWeightCompanionSubgroup_isSolvable P b O hc hm K hdiamond
  letI := weightCompanionTorusSubgroup_isSolvable P b O hc hm K
  letI := Atlas.GroupTheory.semidirectProduct_isSolvable
    (positiveWitnessedTorusAction P b O hc hm K)
  exact Group.isSolvable_of_surjective
    (positiveWitnessedTorusJoinMulEquiv P b O hc hm K hdiamond).surjective

end Atlas.Chevalley
