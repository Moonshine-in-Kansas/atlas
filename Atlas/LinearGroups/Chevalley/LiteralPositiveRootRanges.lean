import Atlas.LinearGroups.Chevalley.PositiveRootCanonicalFamily
import Atlas.LinearGroups.Chevalley.PositiveRootMinusculeHeight

/-! Literal normalizer/Weyl-word families have the already proved canonical
positive-root subgroup as their range. Only ranges, not parameter maps, are
identified. All positivity and actual root-label equations are explicit. -/
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
  (hdiamond : SimpleDiamondProducts P b)

include hdiamond

/-- An actual normalizer conjugate with a specified positive label has
exactly the chosen positive-root subgroup as its range. -/
theorem weightCompanion_conjugateXHom_range_eq_positiveRoot
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm R)
    (i : b.support) (β : ι) (hβ : b.IsPos β)
    (hn : weightCompanionNRootPermHom P b O hc hm R n i.val = β) :
    ((MulAut.conj n.val).toMonoidHom.comp
      (weightCompanionXHom P b O hc hm R i)).range =
      positiveWeightCompanionRootSubgroup P b O hc hm R ⟨β, hβ⟩ := by
  let L : WeightCompanionRootLift P b O hc hm R β := ⟨i, n, hn⟩
  exact rootLiftSubgroup_eq_positiveWeightCompanionRootSubgroup
    P b O hc hm R hdiamond ⟨β, hβ⟩ L

/-- Every element of the chosen subgroup has a parameter in any specified
literal normalizer family of the same positive label. This does not identify
the parameter with the chosen family's parameter. -/
theorem weightCompanion_conjugateX_mem_positiveRoot_iff
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm R)
    (i : b.support) (β : ι) (hβ : b.IsPos β)
    (hn : weightCompanionNRootPermHom P b O hc hm R n i.val = β)
    (g : WeightCompanion P b O hc hm R) :
    g ∈ positiveWeightCompanionRootSubgroup P b O hc hm R ⟨β, hβ⟩ ↔
      ∃ t : R, n.val * weightCompanionX P b O hc hm R i t * n.val⁻¹ = g := by
  rw [← weightCompanion_conjugateXHom_range_eq_positiveRoot
    P b O hc hm R hdiamond n i β hβ hn]
  change (∃ t : Multiplicative R,
    n.val * weightCompanionX P b O hc hm R i t.toAdd * n.val⁻¹ = g) ↔ _
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t.toAdd, ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨Multiplicative.ofAdd t, ht⟩

/-- The literal simple-root homomorphism has the canonical simple-positive
root subgroup as its range. -/
theorem weightCompanionXHom_range_eq_positiveRoot (i : b.support) :
    (weightCompanionXHom P b O hc hm R i).range =
      positiveWeightCompanionRootSubgroup P b O hc hm R
        ⟨i.val, b.isPos_of_mem_support i.property⟩ := by
  ext g
  have h := weightCompanion_conjugateX_mem_positiveRoot_iff
    P b O hc hm R hdiamond 1 i i.val (b.isPos_of_mem_support i.property) (by simp) g
  simp only [Subgroup.coe_one, one_mul, inv_one, mul_one] at h
  change (∃ t : Multiplicative R, weightCompanionX P b O hc hm R i t.toAdd = g) ↔ _
  rw [h]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t.toAdd, ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨Multiplicative.ofAdd t, ht⟩

/-- The actual word in N, rather than an abstract Weyl representative, supplies
the same root-subgroup range. No reduced-word hypothesis is required. -/
theorem weightCompanionWeylWord_XHom_range_eq_positiveRoot
    (l : List b.support) (i : b.support) (β : ι) (hβ : b.IsPos β)
    (hl : simpleReflectionWord P b l i.val = β) :
    ((MulAut.conj (weightCompanionWeylWordInN P b O hc hm R l).val).toMonoidHom.comp
      (weightCompanionXHom P b O hc hm R i)).range =
      positiveWeightCompanionRootSubgroup P b O hc hm R ⟨β, hβ⟩ := by
  apply weightCompanion_conjugateXHom_range_eq_positiveRoot P b O hc hm R hdiamond
  rw [weightCompanionWeylWordInN_rootPermutation]
  exact hl

/-- Membership is existence of a parameter in the literal word family.
This is the interface needed to insert local symbolic commutator formulas. -/
theorem weightCompanionWeylWord_X_mem_positiveRoot_iff
    (l : List b.support) (i : b.support) (β : ι) (hβ : b.IsPos β)
    (hl : simpleReflectionWord P b l i.val = β)
    (g : WeightCompanion P b O hc hm R) :
    g ∈ positiveWeightCompanionRootSubgroup P b O hc hm R ⟨β, hβ⟩ ↔
      ∃ t : R, (weightCompanionWeylWordInN P b O hc hm R l).val *
        weightCompanionX P b O hc hm R i t *
          (weightCompanionWeylWordInN P b O hc hm R l).val⁻¹ = g := by
  apply weightCompanion_conjugateX_mem_positiveRoot_iff P b O hc hm R hdiamond
  rw [weightCompanionWeylWordInN_rootPermutation]
  exact hl

end Atlas.Chevalley
