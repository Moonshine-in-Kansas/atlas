import Atlas.LinearGroups.Chevalley.WeightCompanionWeylRootLift
import Atlas.LinearGroups.Chevalley.WeightCompanionWeylKernelOfLift

/-! Identification of the actual torus quotient with the actual
root-permutation Weyl image. The constructive reduced-word lift supplies the
previously conditional algebraic argument. This does not identify the kernel
of the full companion-to-adjoint projection or the full companion center. -/

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




local instance quotientIdentificationTorusNormal : Subgroup.Normal ((Subgroup.subgroupOf (weightCompanionTorusSubgroup P b O hc hm R) (weightCompanionExtendedWeylSubgroup P b O hc hm R))) :=
  weightCompanionTorusSubgroup_normal_extendedWeyl P b O hc hm R

/-- Faithfulness of the actual quotient action, with its codomain expressed
as the full root-permutation Weyl image. -/
theorem weightCompanionWeylQuotientFullAction_injective
    (hdiamond : SimpleDiamondProducts P b) :
    Function.Injective (weightCompanionWeylQuotientFullAction P b O hc hm R) :=
  weightCompanionWeylQuotientFullAction_injective_of_lift P b O hc hm R
    (weightCompanionWeylRootLift P b O hc hm R hdiamond)
    (weightCompanionWeylRootLift_simple P b O hc hm R hdiamond)

/-- Faithfulness of the original existing quotient action itself. -/
theorem weightCompanionWeylQuotientAction_injective
    (hdiamond : SimpleDiamondProducts P b) :
    Function.Injective (weightCompanionWeylQuotientAction P b O hc hm R) :=
  weightCompanionWeylQuotientAction_injective_of_lift P b O hc hm R
    (weightCompanionWeylRootLift P b O hc hm R hdiamond)
    (weightCompanionWeylRootLift_simple P b O hc hm R hdiamond)

/-- The kernel of the actual N action on root labels is precisely its torus.
This concerns N and its root action, not the full adjoint projection. -/
theorem weightCompanionNRootPermHom_ker_eq_torus
    (hdiamond : SimpleDiamondProducts P b) :
    (weightCompanionNRootPermHom P b O hc hm R).ker = ((Subgroup.subgroupOf (weightCompanionTorusSubgroup P b O hc hm R) (weightCompanionExtendedWeylSubgroup P b O hc hm R))) :=
  weightCompanionNRootPermHom_ker_eq_torus_of_lift P b O hc hm R
    (weightCompanionWeylRootLift P b O hc hm R hdiamond)
    (weightCompanionWeylRootLift_simple P b O hc hm R hdiamond)

/-- The literal quotient N/T is isomorphic to the actual root-permutation
Weyl image, through its previously defined action. -/
def weightCompanionWeylQuotientEquiv (hdiamond : SimpleDiamondProducts P b) :
    ((weightCompanionExtendedWeylSubgroup P b O hc hm R) ⧸ ((Subgroup.subgroupOf (weightCompanionTorusSubgroup P b O hc hm R) (weightCompanionExtendedWeylSubgroup P b O hc hm R)))) ≃* P.weylGroupToPerm.range :=
  weightCompanionWeylQuotientEquiv_of_lift P b O hc hm R
    (weightCompanionWeylRootLift P b O hc hm R hdiamond)
    (weightCompanionWeylRootLift_simple P b O hc hm R hdiamond)

theorem weightCompanionWeylQuotientEquiv_apply
    (hdiamond : SimpleDiamondProducts P b) (q : (weightCompanionExtendedWeylSubgroup P b O hc hm R) ⧸ ((Subgroup.subgroupOf (weightCompanionTorusSubgroup P b O hc hm R) (weightCompanionExtendedWeylSubgroup P b O hc hm R)))) :
    weightCompanionWeylQuotientEquiv P b O hc hm R hdiamond q =
      weightCompanionWeylQuotientFullAction P b O hc hm R q := rfl

end Atlas.Chevalley
