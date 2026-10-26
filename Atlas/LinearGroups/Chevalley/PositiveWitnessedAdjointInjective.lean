import Atlas.LinearGroups.Chevalley.PositiveRootCollection
import Atlas.LinearGroups.Chevalley.PositiveWitnessedNormalizerIntersection

/-! The actual adjoint projection is faithful on the positive subgroup.
This uses its established scalar coordinates, not global projection faithfulness. -/
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
  (R : Type*) [CommRing R] [Nontrivial R]

theorem positiveWitnessedWeightCompanion_adjoint_injective
    (hdiamond : SimpleDiamondProducts P b) :
    Function.Injective (fun g : positiveWitnessedWeightCompanionSubgroup P b O hc hm R =>
      weightCompanionRho P b O hc hm R g.val) := by
  intro g h heq
  obtain ⟨s,rfl⟩ := positiveRootChosenProduct_surjective P b O hc hm R hdiamond g
  obtain ⟨t,rfl⟩ := positiveRootChosenProduct_surjective P b O hc hm R hdiamond h
  exact congrArg (positiveRootChosenProduct P b O hc hm R)
    (positiveRootChosenProduct_adjoint_injective P b O hc hm R heq)

theorem positiveWitnessedWeightCompanion_eq_one_of_rho_eq_one
    (hdiamond : SimpleDiamondProducts P b) (g : WeightCompanion P b O hc hm R)
    (hu : g ∈ positiveWitnessedWeightCompanionSubgroup P b O hc hm R)
    (heq : weightCompanionRho P b O hc hm R g = 1) : g = 1 := by
  have h : (⟨g,hu⟩ : positiveWitnessedWeightCompanionSubgroup P b O hc hm R) = 1 :=
    positiveWitnessedWeightCompanion_adjoint_injective P b O hc hm R hdiamond
      (by simpa only [Subgroup.coe_one, map_one] using heq)
  exact congrArg Subtype.val h

/-- A positive element with diagonal adjoint matrix is already trivial in the
full companion, including every retained minuscule block. -/
theorem positiveWitnessedWeightCompanion_eq_one_of_adjoint_diagonal
    (hdiamond : SimpleDiamondProducts P b) (g : WeightCompanion P b O hc hm R)
    (hu : g ∈ positiveWitnessedWeightCompanionSubgroup P b O hc hm R)
    (hdiag : ∀ row col, row ≠ col →
      (weightCompanionRho P b O hc hm R g).val.val row col = 0) : g = 1 := by
  apply positiveWitnessedWeightCompanion_eq_one_of_rho_eq_one P b O hc hm R hdiamond g hu
  apply Subtype.ext
  apply Units.ext
  exact Atlas.Matrix.HeightUnitriangular.eq_one_of_offDiagonal_zero
    (positiveWitnessedWeightCompanion_adjointHeightUnitriangular P b O hc hm R g hu) hdiag

end Atlas.Chevalley
