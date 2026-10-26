import Atlas.LinearGroups.Chevalley.PositiveRootCanonicalProduct
import Atlas.GroupTheory.HeightOrderedSubgroupCollection
import Atlas.GroupTheory.OrderedSubgroupParameters
import Mathlib.SetTheory.Cardinal.Finite

/-! Conditional collection and counting for the actual all-witness positive
subgroup. The full strict-height subgroup-commutator containment remains an
explicit hypothesis; none of the statements below supplies that hypothesis. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData
open scoped commutatorElement

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
  (hcomm : ∀ α β : {β : ι // b.IsPos β}, α ≠ β →
    ⁅positiveWeightCompanionRootSubgroup P b O hc hm R α,
      positiveWeightCompanionRootSubgroup P b O hc hm R β⁆ ≤
      ⨆ γ : {γ : {β : ι // b.IsPos β} // b.height β.val < b.height γ.val},
        positiveWeightCompanionRootSubgroup P b O hc hm R γ.val)

include hdiamond hcomm

/-- The fixed chosen parameter product covers the existing all-witness U,
provided the actual positive-root subgroup commutators strictly raise height. -/
theorem positiveRootChosenProduct_surjective_of_height_commutators :
    Function.Surjective (positiveRootChosenProduct P b O hc hm R) := by
  intro g
  have hg : g.val ∈
      (⨆ β : {β : ι // b.IsPos β},
        positiveWeightCompanionRootSubgroup P b O hc hm R β :
          Subgroup (WeightCompanion P b O hc hm R)) := by
    rw [← positiveWitnessedWeightCompanion_eq_iSup_positiveRoots
      P b O hc hm R hdiamond]
    exact g.property
  have hcollection := Atlas.GroupTheory.orderedSubgroupProduct_map_eq_iSup_of_height
    (positiveWeightCompanionRootSubgroup P b O hc hm R)
    (fun β : {β : ι // b.IsPos β} => b.height β.val) hcomm
    (positiveRootHeightList P b) (positiveRootHeightList_nodup P b)
    (positiveRootHeightList_pairwise P b) (mem_positiveRootHeightList P b)
  have hgprod : g.val ∈ Atlas.GroupTheory.orderedSubgroupProduct
      ((positiveRootHeightList P b).map
        (positiveWeightCompanionRootSubgroup P b O hc hm R)) := by
    rw [hcollection]
    exact hg
  let f : {β : ι // b.IsPos β} → Multiplicative R →*
      WeightCompanion P b O hc hm R := fun β =>
    weightCompanionRootLiftHom P b O hc hm R (positiveRootChosenLift P b O hc hm R β)
  have hgprod' : g.val ∈ Atlas.GroupTheory.orderedSubgroupProduct
      ((positiveRootHeightList P b).map fun β => (f β).range) := hgprod
  obtain ⟨s, hs⟩ := (Atlas.GroupTheory.mem_orderedSubgroupProduct_map_range_iff
    f (positiveRootHeightList P b) (positiveRootHeightList_nodup P b) g.val).mp hgprod'
  refine ⟨fun β => (s β).toAdd, Subtype.ext ?_⟩
  exact hs

/-- Collection plus the independently proved adjoint parameter recovery gives
bijectivity for this exact chosen product, without a global projection kernel. -/
theorem positiveRootChosenProduct_bijective_of_height_commutators :
    Function.Bijective (positiveRootChosenProduct P b O hc hm R) :=
  ⟨positiveRootChosenProduct_injective P b O hc hm R,
    positiveRootChosenProduct_surjective_of_height_commutators P b O hc hm R hdiamond hcomm⟩

/-- A set equivalence with U, conditional on the actual strict-height
commutator containment. It is not a group isomorphism from the additive product. -/
def positiveRootChosenProductEquiv_of_height_commutators :
    ({β : ι // b.IsPos β} → R) ≃
      positiveWitnessedWeightCompanionSubgroup P b O hc hm R :=
  Equiv.ofBijective (positiveRootChosenProduct P b O hc hm R)
    (positiveRootChosenProduct_bijective_of_height_commutators P b O hc hm R hdiamond hcomm)

/-- A finite coefficient ring yields a finite actual U once the explicit
strict-height commutator premise is supplied. -/
theorem positiveWitnessedWeightCompanionSubgroup_finite_of_height_commutators [Finite R] :
    Finite (positiveWitnessedWeightCompanionSubgroup P b O hc hm R) :=
  Finite.of_equiv ({β : ι // b.IsPos β} → R)
    (positiveRootChosenProductEquiv_of_height_commutators P b O hc hm R hdiamond hcomm)

/-- Conditional order of the existing all-witness positive subgroup.
No unconditional collection, Bruhat decomposition or whole-group order is claimed. -/
theorem positiveWitnessedWeightCompanionSubgroup_card_of_height_commutators [Finite R] :
    Nat.card (positiveWitnessedWeightCompanionSubgroup P b O hc hm R) =
      Nat.card R ^ Nat.card {β : ι // b.IsPos β} := by
  calc
    Nat.card (positiveWitnessedWeightCompanionSubgroup P b O hc hm R) =
        Nat.card ({β : ι // b.IsPos β} → R) :=
      (Nat.card_congr
        (positiveRootChosenProductEquiv_of_height_commutators P b O hc hm R hdiamond hcomm)).symm
    _ = _ := Nat.card_fun

end Atlas.Chevalley
