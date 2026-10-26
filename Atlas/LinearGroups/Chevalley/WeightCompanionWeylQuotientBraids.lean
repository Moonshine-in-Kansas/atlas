import Atlas.LinearGroups.Chevalley.WeightCompanionWeylQuotientInvolutions
import Atlas.LinearGroups.Chevalley.WeightCompanionNonAdjacentWeyl
import Atlas.LinearGroups.Chevalley.WeightCompanionWeylBraidA2
import Atlas.LinearGroups.Chevalley.WeightCompanionWeylBraidDihedral

/-! The literal simple Weyl cosets satisfy the length-two, three, four and six
braid identities, by applying the quotient homomorphism to the actual full
companion identities. This does not identify the quotient with a Coxeter group
or assume faithfulness of its root-label action. -/

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
  (R : Type*) [CommRing R]

local instance quotientBraidTorusNormal :
    ((weightCompanionTorusSubgroup P b O hc hm R).subgroupOf
      (weightCompanionExtendedWeylSubgroup P b O hc hm R)).Normal :=
  weightCompanionTorusSubgroup_normal_extendedWeyl P b O hc hm R

/-- The length-two relation retains the actual diamond premise of the generic
nonadjacent full-companion theorem. All actual root-data providers may discharge
that premise separately. -/
theorem weightCompanionSimpleWeylCoset_commute_of_zero_cartan
    (hdiamond : SimpleDiamondProducts P b)
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = 0) :
    Commute (weightCompanionSimpleWeylCoset P b O hc hm R i)
      (weightCompanionSimpleWeylCoset P b O hc hm R j) := by
  change _ * _ = _ * _
  unfold weightCompanionSimpleWeylCoset
  simp only [← map_mul]
  apply congrArg (QuotientGroup.mk' _)
  apply Subtype.ext
  exact (weightCompanionWeyl_commute_of_zero_cartan P b hdiamond O hc hm R
    i j hne hji 1 1).eq

/-- The actual length-three braid descends to the literal torus quotient. -/
theorem weightCompanionSimpleWeylCoset_a2_braid (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) :
    weightCompanionSimpleWeylCoset P b O hc hm R i *
      weightCompanionSimpleWeylCoset P b O hc hm R j *
      weightCompanionSimpleWeylCoset P b O hc hm R i =
      weightCompanionSimpleWeylCoset P b O hc hm R j *
      weightCompanionSimpleWeylCoset P b O hc hm R i *
      weightCompanionSimpleWeylCoset P b O hc hm R j := by
  unfold weightCompanionSimpleWeylCoset
  simp only [← map_mul]
  apply congrArg (QuotientGroup.mk' _)
  apply Subtype.ext
  exact weightCompanionWeyl_a2_braid P b O hc hm R i j hij hji

/-- For the double edge, i is short: Cartan(i,j)=-1 and Cartan(j,i)=-2. -/
theorem weightCompanionSimpleWeylCoset_b2_braid (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) :
    weightCompanionSimpleWeylCoset P b O hc hm R i *
      weightCompanionSimpleWeylCoset P b O hc hm R j *
      weightCompanionSimpleWeylCoset P b O hc hm R i *
      weightCompanionSimpleWeylCoset P b O hc hm R j =
      weightCompanionSimpleWeylCoset P b O hc hm R j *
      weightCompanionSimpleWeylCoset P b O hc hm R i *
      weightCompanionSimpleWeylCoset P b O hc hm R j *
      weightCompanionSimpleWeylCoset P b O hc hm R i := by
  unfold weightCompanionSimpleWeylCoset
  simp only [← map_mul]
  apply congrArg (QuotientGroup.mk' _)
  apply Subtype.ext
  exact weightCompanionWeyl_b2_braid P b O hc hm R i j hij hji

/-- For the triple edge, i is short: Cartan(i,j)=-1 and Cartan(j,i)=-3.
The argument does not divide by 2 or 3 and includes these characteristics. -/
theorem weightCompanionSimpleWeylCoset_g2_braid (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) :
    weightCompanionSimpleWeylCoset P b O hc hm R i *
      weightCompanionSimpleWeylCoset P b O hc hm R j *
      weightCompanionSimpleWeylCoset P b O hc hm R i *
      weightCompanionSimpleWeylCoset P b O hc hm R j *
      weightCompanionSimpleWeylCoset P b O hc hm R i *
      weightCompanionSimpleWeylCoset P b O hc hm R j =
      weightCompanionSimpleWeylCoset P b O hc hm R j *
      weightCompanionSimpleWeylCoset P b O hc hm R i *
      weightCompanionSimpleWeylCoset P b O hc hm R j *
      weightCompanionSimpleWeylCoset P b O hc hm R i *
      weightCompanionSimpleWeylCoset P b O hc hm R j *
      weightCompanionSimpleWeylCoset P b O hc hm R i := by
  unfold weightCompanionSimpleWeylCoset
  simp only [← map_mul]
  apply congrArg (QuotientGroup.mk' _)
  apply Subtype.ext
  exact weightCompanionWeyl_g2_braid P b O hc hm R i j hij hji

end Atlas.Chevalley
