import Atlas.LinearAlgebra.MatrixConnectivity
import Atlas.LinearGroups.Chevalley.PositiveWitnessedNormalOvergroupAdjacency
import Atlas.LinearGroups.Chevalley.PositiveWitnessedParabolicMaximality
import Atlas.LinearGroups.Chevalley.PositiveWitnessedNormalCore

/-! A connected actual Cartan diagram makes every normal subgroup either
central or a supplement to B. Connectivity is an explicit root-data premise;
no perfectness, finite-field cardinality or simplicity is assumed. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (K : Type*) [Field K]

theorem normal_sup_positiveWitnessedTorusJoin_eq_self_or_top
    (hdiamond : SimpleDiamondProducts P b)
    (hconnected : Atlas.LinearAlgebra.MatrixAdjacencyConnected b.cartanMatrix)
    (A : Subgroup (WeightCompanion P b O hc hm K)) [A.Normal] :
    A ⊔ positiveWitnessedTorusJoin P b O hc hm K =
        positiveWitnessedTorusJoin P b O hc hm K ∨
      A ⊔ positiveWitnessedTorusJoin P b O hc hm K = ⊤ := by
  let B := positiveWitnessedTorusJoin P b O hc hm K
  let J := positiveWitnessedOvergroupSimpleSet P b O hc hm K (A ⊔ B)
  have hJ : A ⊔ B = positiveWitnessedStandardParabolic P b O hc hm K J :=
    positiveWitnessedOvergroup_eq_standardParabolic
      P b O hc hm K hdiamond (A ⊔ B) le_sup_right
  have hclosed : ∀ i ∈ J, ∀ j, b.cartanMatrix i j ≠ 0 → j ∈ J :=
    normal_sup_positiveWitnessedTorusJoin_parabolic_adjacent_closed
      P b O hc hm K hdiamond A J hJ
  have hcases : J = ∅ ∨ J = Finset.univ := by
    rcases hconnected (J : Set b.support) hclosed with h | h
    · exact Or.inl (Finset.coe_injective (by simpa using h))
    · exact Or.inr (Finset.coe_injective (by simpa using h))
  rcases hcases with he | he
  · left
    change A ⊔ B = B
    rw [hJ, he]
    simp [positiveWitnessedStandardParabolic, B]
  · right
    change A ⊔ B = ⊤
    rw [hJ, he]
    exact positiveWitnessedStandardParabolic_univ P b O hc hm K hdiamond

theorem normal_le_positiveWitnessedTorusJoin_core_or_sup_eq_top
    (hdiamond : SimpleDiamondProducts P b)
    (hconnected : Atlas.LinearAlgebra.MatrixAdjacencyConnected b.cartanMatrix)
    (A : Subgroup (WeightCompanion P b O hc hm K)) [A.Normal] :
    A ≤ (positiveWitnessedTorusJoin P b O hc hm K).normalCore ∨
      A ⊔ positiveWitnessedTorusJoin P b O hc hm K = ⊤ := by
  rcases normal_sup_positiveWitnessedTorusJoin_eq_self_or_top
    P b O hc hm K hdiamond hconnected A with h | h
  · left
    apply Subgroup.normal_le_normalCore.mpr
    exact (show A ≤ A ⊔ positiveWitnessedTorusJoin P b O hc hm K from le_sup_left).trans h.le
  · exact Or.inr h

theorem weightCompanion_normal_le_center_or_positiveJoin_sup_eq_top
    (hdiamond : SimpleDiamondProducts P b)
    (hconnected : Atlas.LinearAlgebra.MatrixAdjacencyConnected b.cartanMatrix)
    (A : Subgroup (WeightCompanion P b O hc hm K)) [A.Normal] :
    A ≤ Subgroup.center (WeightCompanion P b O hc hm K) ∨
      A ⊔ positiveWitnessedTorusJoin P b O hc hm K = ⊤ := by
  rcases normal_sup_positiveWitnessedTorusJoin_eq_self_or_top
    P b O hc hm K hdiamond hconnected A with h | h
  · left
    apply weightCompanion_normal_le_center_of_le_positiveJoin P b O hc hm K hdiamond A
    exact (show A ≤ A ⊔ positiveWitnessedTorusJoin P b O hc hm K from le_sup_left).trans h.le
  · exact Or.inr h

end Atlas.Chevalley
