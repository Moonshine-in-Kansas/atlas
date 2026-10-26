import Atlas.LinearGroups.Chevalley.NegativeRootOppositeMembership
import Atlas.LinearGroups.Chevalley.PositiveRootSubsetCollection
import Atlas.LinearGroups.Chevalley.RootData.PositiveRootWeylPartition

/-! Inverse-Weyl sign partitions control actual conjugation of the restricted
positive subgroups. The direction is explicitly w inverse, for a lift of w. -/
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
  (R : Type*) [CommRing R] [Nontrivial R]

theorem positiveRootNoninversionSubset_conjugate_le_positive
    (w : P.weylGroupToPerm.range)
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm R)
    (hn : weightCompanionNRootPermHom P b O hc hm R n = w.val) :
    conjugateSubgroup n.val⁻¹
      (positiveRootSubsetSubgroup P b O hc hm R (positiveRootNoninversionSubset P b w⁻¹)) ≤
        positiveWitnessedWeightCompanionSubgroup P b O hc hm R := by
  unfold conjugateSubgroup positiveRootSubsetSubgroup
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro β
  rintro g ⟨u, hu, rfl⟩
  change u ∈ (weightCompanionRootLiftHom P b O hc hm R
    (positiveRootChosenLift P b O hc hm R β.val)).range at hu
  obtain ⟨t, rfl⟩ := hu
  let L := positiveRootChosenLift P b O hc hm R β.val
  have hpos : b.IsPos (weightCompanionNRootPermHom P b O hc hm R n⁻¹ β.val.val) := by
    rw [map_inv, hn]
    exact β.property
  have h := rootLiftHom_mem_positiveWitnessedWeightCompanionSubgroup P b O hc hm R hpos
    (weightCompanionRootLift_normalizerMul P b O hc hm R L n⁻¹) t
  rw [weightCompanionRootLiftHom_normalizerMul] at h
  exact h

theorem positiveRootInversionSubset_conjugate_le_opposite
    (w : P.weylGroupToPerm.range)
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm R)
    (hn : weightCompanionNRootPermHom P b O hc hm R n = w.val) :
    conjugateSubgroup n.val⁻¹
      (positiveRootSubsetSubgroup P b O hc hm R (positiveRootInversionSubset P b w⁻¹)) ≤
        oppositePositiveWitnessedWeightCompanionSubgroup P b O hc hm R := by
  unfold conjugateSubgroup positiveRootSubsetSubgroup
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro β
  rintro g ⟨u, hu, rfl⟩
  change u ∈ (weightCompanionRootLiftHom P b O hc hm R
    (positiveRootChosenLift P b O hc hm R β.val)).range at hu
  obtain ⟨t, rfl⟩ := hu
  let L := positiveRootChosenLift P b O hc hm R β.val
  have hneg : ¬ b.IsPos (weightCompanionNRootPermHom P b O hc hm R n⁻¹ β.val.val) := by
    rw [map_inv, hn]
    exact β.property
  have h := rootLiftHom_mem_oppositePositiveWitnessed P b O hc hm R hneg
    (weightCompanionRootLift_normalizerMul P b O hc hm R L n⁻¹) t
  rw [weightCompanionRootLiftHom_normalizerMul] at h
  exact h

end Atlas.Chevalley
