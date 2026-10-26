import Atlas.LinearGroups.Chevalley.PositiveWitnessedTorusIntersection
import Atlas.LinearGroups.Chevalley.WeightCompanionWeylQuotientIdentification

/-! The actual positive witnessed subgroup has trivial intersection with the
extended Weyl subgroup. Its root diagonal is one, whereas a nontrivial root
permutation moves at least one literal root column. No collection or Bruhat
decomposition is used. -/

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

/-- Adjoint triangularity of all products of positive witnessed roots needs
neither finiteness of the chosen weight family nor the diamond premise. -/
theorem positiveWitnessedWeightCompanion_le_adjointHeightUnitriangular :
    positiveWitnessedWeightCompanionSubgroup P b O hc hm R ≤
      (Atlas.Matrix.heightUnitriangularSubgroup (geckHeight P b)).comap
        ((adjointSubgroup P b R).subtype.comp (weightCompanionRho P b O hc hm R)) := by
  rw [positiveWitnessedWeightCompanionSubgroup, Subgroup.closure_le]
  rintro g ⟨β, hβ, L, t, rfl⟩
  exact weightCompanionRho_rootLiftHom_mem_heightUnitriangular P b R O hc hm hβ L t

theorem positiveWitnessedWeightCompanion_adjointHeightUnitriangular
    (g : WeightCompanion P b O hc hm R)
    (hu : g ∈ positiveWitnessedWeightCompanionSubgroup P b O hc hm R) :
    Atlas.Matrix.HeightUnitriangular (geckHeight P b)
      (weightCompanionRho P b O hc hm R g).val.val :=
  (positiveWitnessedWeightCompanion_le_adjointHeightUnitriangular P b O hc hm R hu).1

/-- The actual Weyl action of an element in U∩N fixes every root label.
The proof uses only the adjoint diagonal and literal monomial root columns. -/
theorem weightCompanionNRootPermHom_eq_one_of_mem_positiveWitnessed
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm R)
    (hu : n.val ∈ positiveWitnessedWeightCompanionSubgroup P b O hc hm R) :
    weightCompanionNRootPermHom P b O hc hm R n = 1 := by
  apply Equiv.ext
  intro β
  change weightCompanionNRootPerm P b O hc hm R n β = β
  have hdiag :=
    (positiveWitnessedWeightCompanion_adjointHeightUnitriangular P b O hc hm R n.val hu).diagonal
      (Sum.inr β)
  have hnz : (weightCompanionRho P b O hc hm R n.val).val.val
      (Sum.inr β) (Sum.inr β) ≠ 0 := by
    rw [hdiag]
    exact one_ne_zero
  have hlabel := adjointRootPermutation_nonzero_rootColumn P b R
    (weightCompanionNRootPerm_spec P b O hc hm R n).2 (Sum.inr β) β hnz
  exact (Sum.inr.inj hlabel).symm

variable [Fintype κ]

/-- On the actual companion, U∩N is trivial: the root-action kernel in N is
the actual torus, whose intersection with U is already known to be trivial. -/
theorem positiveWitnessedWeightCompanion_eq_one_of_mem_extendedWeyl
    (hdiamond : SimpleDiamondProducts P b) (g : WeightCompanion P b O hc hm R)
    (hu : g ∈ positiveWitnessedWeightCompanionSubgroup P b O hc hm R)
    (hn : g ∈ weightCompanionExtendedWeylSubgroup P b O hc hm R) : g = 1 := by
  let n : weightCompanionExtendedWeylSubgroup P b O hc hm R := ⟨g, hn⟩
  have hk : n ∈ (weightCompanionNRootPermHom P b O hc hm R).ker :=
    weightCompanionNRootPermHom_eq_one_of_mem_positiveWitnessed P b O hc hm R n hu
  have ht : g ∈ weightCompanionTorusSubgroup P b O hc hm R := by
    have hnt : n ∈ (weightCompanionTorusSubgroup P b O hc hm R).subgroupOf
        (weightCompanionExtendedWeylSubgroup P b O hc hm R) := by
      rw [← weightCompanionNRootPermHom_ker_eq_torus P b O hc hm R hdiamond]
      exact hk
    exact hnt
  exact positiveWitnessedWeightCompanion_eq_one_of_mem_torus P b O hc hm R hdiamond g hu ht

theorem positiveWitnessedWeightCompanion_inf_extendedWeyl_eq_bot
    (hdiamond : SimpleDiamondProducts P b) :
    positiveWitnessedWeightCompanionSubgroup P b O hc hm R ⊓
      weightCompanionExtendedWeylSubgroup P b O hc hm R = ⊥ := by
  apply bot_unique
  rintro g ⟨hu, hn⟩
  exact Subgroup.mem_bot.mpr
    (positiveWitnessedWeightCompanion_eq_one_of_mem_extendedWeyl P b O hc hm R hdiamond g hu hn)

end Atlas.Chevalley
