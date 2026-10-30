import Atlas.LinearGroups.Chevalley.PositiveRootCollection

/-! A positive normal form for any explicit root-lift family and any complete
height-ordered distinct root list. The maps retain their actual parameter
markings; only their subgroup ranges are compared with the existing canonical
root groups. This is a set equivalence with the inherited positive subgroup. -/
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
  (L : ∀ β : {β : ι // b.IsPos β}, WeightCompanionRootLift P b O hc hm R β.val)
  (l : List {β : ι // b.IsPos β})

def positiveRootWitnessedProduct (s : {β : ι // b.IsPos β} → R) :
    positiveWitnessedWeightCompanionSubgroup P b O hc hm R :=
  ⟨positiveRootLiftProduct P b R O hc hm L l s,
    positiveRootLiftProduct_mem_witnessed P b O hc hm R L l s⟩

theorem positiveRootWitnessedProduct_val (s : {β : ι // b.IsPos β} → R) :
    (positiveRootWitnessedProduct P b O hc hm R L l s).val =
      positiveRootLiftProduct P b R O hc hm L l s := rfl

variable (hnodup : l.Nodup)
  (hsorted : l.Pairwise (fun β γ => b.height β.val ≤ b.height γ.val))
  (hcover : ∀ β : {β : ι // b.IsPos β}, β ∈ l)

include hnodup hsorted hcover

theorem positiveRootWitnessedProduct_injective :
    Function.Injective (positiveRootWitnessedProduct P b O hc hm R L l) := by
  intro s t h
  apply positiveRootLiftProduct_injective P b R O hc hm L l hnodup hsorted hcover
  exact congrArg (fun g : positiveWitnessedWeightCompanionSubgroup P b O hc hm R =>
    g.val) h

theorem positiveRootWitnessedProduct_surjective (hdiamond : SimpleDiamondProducts P b) :
    Function.Surjective (positiveRootWitnessedProduct P b O hc hm R L l) := by
  intro g
  have hg : g.val ∈
      (⨆ β : {β : ι // b.IsPos β},
        positiveWeightCompanionRootSubgroup P b O hc hm R β :
          Subgroup (WeightCompanion P b O hc hm R)) := by
    rw [← positiveWitnessedWeightCompanion_eq_iSup_positiveRoots P b O hc hm R hdiamond]
    exact g.property
  have hcollection := Atlas.GroupTheory.orderedSubgroupProduct_map_eq_iSup_of_height
    (positiveWeightCompanionRootSubgroup P b O hc hm R)
    (fun β : {β : ι // b.IsPos β} => b.height β.val)
    (positiveRootSubgroup_height_commutators P b O hc hm R hdiamond)
    l hnodup hsorted hcover
  have hgprod : g.val ∈ Atlas.GroupTheory.orderedSubgroupProduct
      (l.map (positiveWeightCompanionRootSubgroup P b O hc hm R)) := by
    rw [hcollection]
    exact hg
  let f : {β : ι // b.IsPos β} → Multiplicative R →*
      WeightCompanion P b O hc hm R := fun β =>
    weightCompanionRootLiftHom P b O hc hm R (L β)
  have hr (β : {β : ι // b.IsPos β}) :
      (f β).range = positiveWeightCompanionRootSubgroup P b O hc hm R β :=
    rootLiftSubgroup_eq_positiveWeightCompanionRootSubgroup P b O hc hm R hdiamond β (L β)
  have hgprod' : g.val ∈ Atlas.GroupTheory.orderedSubgroupProduct
      (l.map fun β => (f β).range) := by
    simpa only [hr] using hgprod
  obtain ⟨s, hs⟩ := (Atlas.GroupTheory.mem_orderedSubgroupProduct_map_range_iff
    f l hnodup g.val).mp hgprod'
  refine ⟨fun β => (s β).toAdd, Subtype.ext ?_⟩
  exact hs

def positiveRootWitnessedProductEquiv (hdiamond : SimpleDiamondProducts P b) :
    ({β : ι // b.IsPos β} → R) ≃ positiveWitnessedWeightCompanionSubgroup P b O hc hm R :=
  Equiv.ofBijective (positiveRootWitnessedProduct P b O hc hm R L l)
    ⟨positiveRootWitnessedProduct_injective P b O hc hm R L l hnodup hsorted hcover,
      positiveRootWitnessedProduct_surjective P b O hc hm R L l hnodup hsorted hcover hdiamond⟩

end Atlas.Chevalley
