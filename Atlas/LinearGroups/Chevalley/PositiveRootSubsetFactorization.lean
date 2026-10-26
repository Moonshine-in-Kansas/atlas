import Atlas.LinearGroups.Chevalley.PositiveRootSubsetDisjoint
import Atlas.LinearGroups.Chevalley.PositiveRootSubsetParameters
import Mathlib.Logic.Equiv.Set
import Mathlib.SetTheory.Cardinal.Finite

/-! A partition of the positive roots into two cone-closed subsets gives a
unique ordered factorization of the actual U over a finite coefficient ring.
This is a bijection of sets; no normalization or direct-product group structure
is claimed. The only cardinalities used are the root-subset and U counts. -/

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

/-- Literal ordered multiplication of two restricted actual positive subgroups,
with codomain the original all-witness subgroup U. -/
def positiveRootSubsetMul (S T : Set {β : ι // b.IsPos β}) :
    positiveRootSubsetSubgroup P b O hc hm R S ×
      positiveRootSubsetSubgroup P b O hc hm R T →
        positiveWitnessedWeightCompanionSubgroup P b O hc hm R := fun p =>
  ⟨p.1.val * p.2.val,
    (positiveWitnessedWeightCompanionSubgroup P b O hc hm R).mul_mem
      (positiveRootSubsetSubgroup_le_witnessed P b O hc hm R S p.1.property)
      (positiveRootSubsetSubgroup_le_witnessed P b O hc hm R T p.2.property)⟩

theorem positiveRootSubsetMul_injective
    (hdiamond : SimpleDiamondProducts P b)
    (S T : Set {β : ι // b.IsPos β})
    (hS : PositiveRootConeClosed P b S) (hT : PositiveRootConeClosed P b T)
    (hd : Disjoint S T) :
    Function.Injective (positiveRootSubsetMul P b O hc hm R S T) := by
  intro x y hxy
  exact Subgroup.mul_injective_of_disjoint
    (positiveRootSubsetSubgroup_disjoint P b O hc hm R hdiamond S T hS hT hd)
    (congrArg Subtype.val hxy)

theorem positiveRootSubsetMul_bijective_of_partition [Finite R]
    (hdiamond : SimpleDiamondProducts P b)
    (S T : Set {β : ι // b.IsPos β})
    (hS : PositiveRootConeClosed P b S) (hT : PositiveRootConeClosed P b T)
    (hd : Disjoint S T) (hcover : S ∪ T = Set.univ) :
    Function.Bijective (positiveRootSubsetMul P b O hc hm R S T) := by
  letI : Finite (positiveWitnessedWeightCompanionSubgroup P b O hc hm R) :=
    positiveWitnessedWeightCompanionSubgroup_finite P b O hc hm R hdiamond
  have hroots : Nat.card S + Nat.card T = Nat.card {β : ι // b.IsPos β} := by
    calc
      Nat.card S + Nat.card T = Nat.card (S ⊕ T) := Nat.card_sum.symm
      _ = Nat.card ↥(S ∪ T) := (Nat.card_congr (Equiv.Set.union hd)).symm
      _ = Nat.card ↥(Set.univ : Set {β : ι // b.IsPos β}) := by rw [hcover]
      _ = Nat.card {β : ι // b.IsPos β} :=
        Nat.card_congr (Equiv.Set.univ {β : ι // b.IsPos β})
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨positiveRootSubsetMul_injective P b O hc hm R hdiamond S T hS hT hd, ?_⟩
  rw [Nat.card_prod, positiveRootSubsetSubgroup_card P b O hc hm R hdiamond S hS,
    positiveRootSubsetSubgroup_card P b O hc hm R hdiamond T hT,
    positiveWitnessedWeightCompanionSubgroup_card P b O hc hm R hdiamond,
    ← pow_add, hroots]

/-- Unique ordered factorization as a set equivalence. Neither factor is
asserted to be normal in U, and this equivalence is not a group isomorphism. -/
def positiveRootSubsetMulEquiv_of_partition [Finite R]
    (hdiamond : SimpleDiamondProducts P b)
    (S T : Set {β : ι // b.IsPos β})
    (hS : PositiveRootConeClosed P b S) (hT : PositiveRootConeClosed P b T)
    (hd : Disjoint S T) (hcover : S ∪ T = Set.univ) :
    positiveRootSubsetSubgroup P b O hc hm R S ×
      positiveRootSubsetSubgroup P b O hc hm R T ≃
        positiveWitnessedWeightCompanionSubgroup P b O hc hm R :=
  Equiv.ofBijective (positiveRootSubsetMul P b O hc hm R S T)
    (positiveRootSubsetMul_bijective_of_partition P b O hc hm R hdiamond S T hS hT hd hcover)

end Atlas.Chevalley
