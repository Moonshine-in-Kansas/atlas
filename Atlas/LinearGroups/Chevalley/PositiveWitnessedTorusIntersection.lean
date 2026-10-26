import Atlas.LinearGroups.Chevalley.PositiveWitnessedSubgroup
import Atlas.LinearGroups.Chevalley.WeightCompanionTorusDiagonal

/-! Trivial intersection of the actual all-witness positive subgroup and torus.
The proof compares diagonal and unitriangular matrices in the existing faithful
companion representation, without a global assertion about the adjoint kernel. -/

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
  (R : Type*) [CommRing R] [Nontrivial R] [Fintype κ]

theorem positiveWitnessedWeightCompanion_eq_one_of_mem_torus
    (hdiamond : SimpleDiamondProducts P b) (g : WeightCompanion P b O hc hm R)
    (hu : g ∈ positiveWitnessedWeightCompanionSubgroup P b O hc hm R)
    (ht : g ∈ weightCompanionTorusSubgroup P b O hc hm R) : g = 1 :=
  positiveWitnessedWeightCompanion_eq_one_of_diagonal P b O hc hm R hdiamond g hu
    (weightCompanionTorus_matrix_offDiagonal_zero P b O hc hm R g ht)

theorem positiveWitnessedWeightCompanion_inf_torus_eq_bot
    (hdiamond : SimpleDiamondProducts P b) :
    positiveWitnessedWeightCompanionSubgroup P b O hc hm R ⊓
      weightCompanionTorusSubgroup P b O hc hm R = ⊥ := by
  apply bot_unique
  rintro g ⟨hu, ht⟩
  exact Subgroup.mem_bot.mpr
    (positiveWitnessedWeightCompanion_eq_one_of_mem_torus P b O hc hm R hdiamond g hu ht)

end Atlas.Chevalley
