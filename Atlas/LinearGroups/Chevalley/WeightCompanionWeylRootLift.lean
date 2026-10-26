import Atlas.GroupTheory.ReducedWordFactorization
import Atlas.LinearGroups.Chevalley.WeightCompanionWeylQuotientAlternatingBraid

/-! Constructive evaluation of the actual root-permutation Weyl image into the
actual torus quotient. The actual length and common-suffix lemmas discharge the
generic factorization premises. No faithfulness assumption is used. -/

noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData
open Atlas.GroupTheory.ReducedWords
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

local instance rootLiftTorusNormal :
    ((weightCompanionTorusSubgroup P b O hc hm R).subgroupOf
      (weightCompanionExtendedWeylSubgroup P b O hc hm R)).Normal :=
  weightCompanionTorusSubgroup_normal_extendedWeyl P b O hc hm R

/-- The actual common-suffix and quotient-braid theorems supply precisely the
local compatibility premise of the generic reduced-evaluation induction. -/
theorem weightCompanionSimpleWeylCoset_compatibleDescentSuffix
    (hdiamond : SimpleDiamondProducts P b) :
    HasCompatibleDescentSuffix (simpleWeylReflection P b) (rootWeylLength P b)
      (weightCompanionSimpleWeylCoset P b O hc hm R) :=
  compatibleDescentSuffix_of_alternating
    (weightCompanionSimpleWeylCoset P b O hc hm R) (simpleBraidLength P b)
    (fun i j _ => simpleBraidLength_pos P b i j)
    (root_reduced_representatives P b)
    (actualRoot_hasCommonAlternatingSuffix P b)
    (weightCompanionSimpleWeylCoset_alternating_braid P b O hc hm R hdiamond)

/-- Actual reduced-word evaluation defines a group homomorphism from the
root-permutation Weyl image into the literal quotient N/T. All commutative
coefficient rings, including characteristics 2 and 3, are allowed. -/
def weightCompanionWeylRootLift (hdiamond : SimpleDiamondProducts P b) :
    P.weylGroupToPerm.range →*
      (weightCompanionExtendedWeylSubgroup P b O hc hm R ⧸
        (weightCompanionTorusSubgroup P b O hc hm R).subgroupOf
          (weightCompanionExtendedWeylSubgroup P b O hc hm R)) :=
  evaluationHom (actualRootLengthData P b)
    (weightCompanionSimpleWeylCoset P b O hc hm R)
    (root_reduced_representatives P b)
    (weightCompanionSimpleWeylCoset_compatibleDescentSuffix P b O hc hm R hdiamond)
    (fun i => by
      simpa only [pow_two] using weightCompanionSimpleWeylCoset_sq P b O hc hm R i)
    (root_length_step_cases P b)

/-- The homomorphism sends an actual simple root reflection to its literal
simple Weyl coset. This equation does not assume any projection is injective. -/
theorem weightCompanionWeylRootLift_simple
    (hdiamond : SimpleDiamondProducts P b) (i : b.support) :
    weightCompanionWeylRootLift P b O hc hm R hdiamond (simpleWeylReflection P b i) =
      weightCompanionSimpleWeylCoset P b O hc hm R i := by
  exact evaluationHom_simple (actualRootLengthData P b)
    (weightCompanionSimpleWeylCoset P b O hc hm R)
    (root_reduced_representatives P b)
    (weightCompanionSimpleWeylCoset_compatibleDescentSuffix P b O hc hm R hdiamond)
    (fun k => by
      simpa only [pow_two] using weightCompanionSimpleWeylCoset_sq P b O hc hm R k)
    (root_length_step_cases P b) i

end Atlas.Chevalley
