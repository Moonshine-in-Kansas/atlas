import Atlas.LinearGroups.Chevalley.PositiveWitnessedRankOneCell
import Atlas.LinearGroups.Chevalley.WeightCompanionWeylSameRoot
import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionLength

/-! Root-sign tests for actual inverse-normalizer conjugates. Retained lifts
provide membership in U directly; canonical root-family coherence is unused. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R]

theorem weightCompanionN_conjugate_X_mem_positiveWitnessed
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm R)
    (i : b.support)
    (hpos : b.IsPos (weightCompanionNRootPermHom P b O hc hm R n i.val))
    (t : R) :
    n.val * weightCompanionX P b O hc hm R i t * n.val⁻¹ ∈
      positiveWitnessedWeightCompanionSubgroup P b O hc hm R := by
  let L : WeightCompanionRootLift P b O hc hm R
      (weightCompanionNRootPermHom P b O hc hm R n i.val) := ⟨i,n,rfl⟩
  exact rootLiftHom_mem_positiveWitnessedWeightCompanionSubgroup
    P b O hc hm R hpos L (Multiplicative.ofAdd t)

/-- The sign of n*s_i(alpha_i) is the opposite of that of n(alpha_i).
Only membership of the actual root permutation in the Weyl image is used. -/
theorem weightCompanionN_simple_root_sign_flip
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm R) (i : b.support) :
    b.IsPos (weightCompanionNRootPermHom P b O hc hm R
        (n * weightCompanionSimpleWeylInN P b O hc hm R i) i.val) ↔
      ¬ b.IsPos (weightCompanionNRootPermHom P b O hc hm R n i.val) := by
  let w : P.weylGroupToPerm.range :=
    ⟨weightCompanionNRootPermHom P b O hc hm R n,
      simpleRootPermutationSubgroup_le_weylImage P b
        (weightCompanionNRootPerm_spec P b O hc hm R n).1⟩
  rw [map_mul,weightCompanionNRootPermHom_simple]
  exact simpleWeylReflection_sign_flip P b w i

/-- A negative simple-root family becomes positive when the actual image of
the original simple root is negative. No parameter-choice comparison occurs. -/
theorem weightCompanionN_conjugate_Y_mem_positiveWitnessed_of_negative
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm R)
    (i : b.support)
    (hneg : ¬ b.IsPos (weightCompanionNRootPermHom P b O hc hm R n i.val))
    (t : R) :
    n.val * weightCompanionY P b O hc hm R i t * n.val⁻¹ ∈
      positiveWitnessedWeightCompanionSubgroup P b O hc hm R := by
  have hp := (weightCompanionN_simple_root_sign_flip P b O hc hm R n i).mpr hneg
  have h := weightCompanionN_conjugate_X_mem_positiveWitnessed P b O hc hm R
    (n * weightCompanionSimpleWeylInN P b O hc hm R i) i hp (-t)
  change (n.val * weightCompanionWeyl P b O hc hm R i 1) *
      weightCompanionX P b O hc hm R i (-t) *
        (n.val * weightCompanionWeyl P b O hc hm R i 1)⁻¹ ∈ _ at h
  have he : (n.val * weightCompanionWeyl P b O hc hm R i 1) *
      weightCompanionX P b O hc hm R i (-t) *
        (n.val * weightCompanionWeyl P b O hc hm R i 1)⁻¹ =
      n.val * weightCompanionY P b O hc hm R i t * n.val⁻¹ := by
    calc
      _ = n.val * (weightCompanionWeyl P b O hc hm R i 1 *
          weightCompanionX P b O hc hm R i (-t) *
            (weightCompanionWeyl P b O hc hm R i 1)⁻¹) * n.val⁻¹ := by group
      _ = _ := by rw [weightCompanionWeyl_one_conjugate_X_same,neg_neg]
  rwa [he] at h

end Atlas.Chevalley
