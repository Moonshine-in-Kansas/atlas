import Atlas.LinearGroups.Chevalley.WeightCompanionRootPermutation

/-! Source-only candidate. The torus quotient acts surjectively on the finite
simple-reflection root image. Faithfulness is deliberately not asserted. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hclosed : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hmin : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R]

local instance torusInExtendedWeyl_normal :
    ((weightCompanionTorusSubgroup P b O hclosed hmin R).subgroupOf
      (weightCompanionExtendedWeylSubgroup P b O hclosed hmin R)).Normal :=
  weightCompanionTorusSubgroup_normal_extendedWeyl P b O hclosed hmin R

theorem weightCompanionTorus_le_simpleRootPermKer :
    ((weightCompanionTorusSubgroup P b O hclosed hmin R).subgroupOf
      (weightCompanionExtendedWeylSubgroup P b O hclosed hmin R)) ≤
        (weightCompanionNToSimpleRootPerm P b O hclosed hmin R).ker := by
  intro g hg
  change weightCompanionNToSimpleRootPerm P b O hclosed hmin R g = 1
  apply Subtype.ext
  exact weightCompanionTorus_le_rootPermKer P b O hclosed hmin R hg

/-- Concrete quotient action. The unproved converse kernel inclusion is not a
hypothesis: this map is constructed using the proved T ≤ ker inclusion only. -/
def weightCompanionWeylQuotientAction :
    (weightCompanionExtendedWeylSubgroup P b O hclosed hmin R ⧸
      (weightCompanionTorusSubgroup P b O hclosed hmin R).subgroupOf
        (weightCompanionExtendedWeylSubgroup P b O hclosed hmin R)) →*
      simpleRootPermutationSubgroup P b :=
  QuotientGroup.lift
    ((weightCompanionTorusSubgroup P b O hclosed hmin R).subgroupOf
      (weightCompanionExtendedWeylSubgroup P b O hclosed hmin R))
    (weightCompanionNToSimpleRootPerm P b O hclosed hmin R)
    (weightCompanionTorus_le_simpleRootPermKer P b O hclosed hmin R)

theorem weightCompanionWeylQuotientAction_surjective :
    Function.Surjective (weightCompanionWeylQuotientAction P b O hclosed hmin R) :=
  QuotientGroup.lift_surjective_of_surjective
    ((weightCompanionTorusSubgroup P b O hclosed hmin R).subgroupOf
      (weightCompanionExtendedWeylSubgroup P b O hclosed hmin R))
    (weightCompanionNToSimpleRootPerm P b O hclosed hmin R)
    (weightCompanionNToSimpleRootPerm_surjective P b O hclosed hmin R)
    (weightCompanionTorus_le_simpleRootPermKer P b O hclosed hmin R)

end Atlas.Chevalley
