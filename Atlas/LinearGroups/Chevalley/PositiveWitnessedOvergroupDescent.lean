import Atlas.LinearGroups.Chevalley.PositiveWitnessedNormalizerSigns

/-! A negative inverse Weyl image forces the corresponding negative simple
root group into any subgroup containing the actual B. This is an elementary
conjugation statement for the existing full companion; no field, finiteness,
diamond, normality, group-order or simplicity premise is used. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData

private theorem subgroup_mem_of_inverse_conjugate_mem
    {G : Type*} [Group G] (H : Subgroup G) (n y : G)
    (hn : n ∈ H) (hy : n⁻¹ * y * n ∈ H) : y ∈ H := by
  have h := H.mul_mem (H.mul_mem hn hy) (H.inv_mem hn)
  have he : n * (n⁻¹ * y * n) * n⁻¹ = y := by group
  rwa [he] at h

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R]

/-- If H contains B and n, and n inverse takes the simple root i to a negative
root, then H contains every parameter of the literal negative simple family. -/
theorem weightCompanionY_mem_of_inverse_root_negative
    (H : Subgroup (WeightCompanion P b O hc hm R))
    (hB : positiveWitnessedTorusJoin P b O hc hm R ≤ H)
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm R)
    (hn : n.val ∈ H) (i : b.support)
    (hneg : ¬ b.IsPos
      (weightCompanionNRootPermHom P b O hc hm R n⁻¹ i.val))
    (t : R) : weightCompanionY P b O hc hm R i t ∈ H := by
  have hy := weightCompanionN_conjugate_Y_mem_positiveWitnessed_of_negative
    P b O hc hm R n⁻¹ i hneg t
  change n.val⁻¹ * weightCompanionY P b O hc hm R i t * n.val ∈
    positiveWitnessedWeightCompanionSubgroup P b O hc hm R at hy
  exact subgroup_mem_of_inverse_conjugate_mem H n.val
    (weightCompanionY P b O hc hm R i t) hn
    (hB ((show positiveWitnessedWeightCompanionSubgroup P b O hc hm R ≤
      positiveWitnessedTorusJoin P b O hc hm R from le_sup_left) hy))

/-- The same root-sign test puts the original simple Tits representative in H.
Its two positive factors already belong to B; its negative factor follows from
the preceding all-parameter conclusion. -/
theorem weightCompanionWeyl_mem_of_inverse_root_negative
    (H : Subgroup (WeightCompanion P b O hc hm R))
    (hB : positiveWitnessedTorusJoin P b O hc hm R ≤ H)
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm R)
    (hn : n.val ∈ H) (i : b.support)
    (hneg : ¬ b.IsPos
      (weightCompanionNRootPermHom P b O hc hm R n⁻¹ i.val)) :
    weightCompanionWeyl P b O hc hm R i 1 ∈ H := by
  have hx := hB (weightCompanionX_mem_positiveWitnessedTorusJoin
    P b O hc hm R i 1)
  have hy := weightCompanionY_mem_of_inverse_root_negative
    P b O hc hm R H hB n hn i hneg (-1)
  change weightCompanionX P b O hc hm R i 1 *
    weightCompanionY P b O hc hm R i (-1) *
      weightCompanionX P b O hc hm R i 1 ∈ H
  exact H.mul_mem (H.mul_mem hx hy) hx

end Atlas.Chevalley
