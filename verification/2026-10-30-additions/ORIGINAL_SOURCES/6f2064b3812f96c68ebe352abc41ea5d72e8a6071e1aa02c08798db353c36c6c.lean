import FamilyWork.WitnessedPositiveProduct
import Atlas.LinearGroups.Chevalley.PositiveRootSubsetCollection

/-! Supported coordinates for the actual subgroup of a cone-closed positive-root
subset, using any explicitly chosen root lifts and any complete height-ordered
list. Range coherence and restricted collection give exhaustion; the existing
full-product parameter recovery gives the converse. No counting argument is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
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
  (L : ∀ β : {β : ι // b.IsPos β}, WeightCompanionRootLift P b O hc hm R β.val)

private theorem supported_list_prod_filter {A G : Type*} [Monoid G]
    (S : Set A) (f : A → G) (l : List A) (hone : ∀ a, a ∉ S → f a = 1) :
    (l.map f).prod = ((l.filter (fun a => decide (a ∈ S))).map f).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : a ∈ S
    · simp [ha, ih]
    · simp [ha, hone a ha, ih]

/-- Restricted collection retains the scalar markings of the displayed lifts. -/
theorem positiveRootWitnessedSubset_exists_parameters
    (hdiamond : SimpleDiamondProducts P b)
    (S : Set {β : ι // b.IsPos β}) (hS : PositiveRootConeClosed P b S)
    (l : List S) (hnodup : l.Nodup)
    (hsorted : l.Pairwise (fun β γ => b.height β.val.val ≤ b.height γ.val.val))
    (hcover : ∀ β : S, β ∈ l)
    (g : WeightCompanion P b O hc hm R)
    (hg : g ∈ positiveRootSubsetSubgroup P b O hc hm R S) :
    ∃ s : S → R, (l.map fun β => weightCompanionRootLiftHom P b O hc hm R
      (L β.val) (Multiplicative.ofAdd (s β))).prod = g := by
  let f : S → Multiplicative R →* WeightCompanion P b O hc hm R := fun β =>
    weightCompanionRootLiftHom P b O hc hm R (L β.val)
  have hr (β : S) : (f β).range =
      positiveWeightCompanionRootSubgroup P b O hc hm R β.val :=
    rootLiftSubgroup_eq_positiveWeightCompanionRootSubgroup
      P b O hc hm R hdiamond β.val (L β.val)
  have hp : g ∈ Atlas.GroupTheory.orderedSubgroupProduct
      (l.map fun β => positiveWeightCompanionRootSubgroup P b O hc hm R β.val) := by
    rw [positiveRootSubset_orderedProduct_eq_subgroup P b O hc hm R hdiamond
      S hS l hnodup hsorted hcover]
    exact hg
  have hp' : g ∈ Atlas.GroupTheory.orderedSubgroupProduct
      (l.map fun β => (f β).range) := by
    simpa only [hr] using hp
  obtain ⟨s, hs⟩ := (Atlas.GroupTheory.mem_orderedSubgroupProduct_map_range_iff
    f l hnodup g).mp hp'
  exact ⟨fun β => (s β).toAdd, hs⟩

/-- Extend restricted coordinates by zero in the same complete ordered product. -/
theorem positiveRootWitnessedSubset_exists_supported_parameters
    (hdiamond : SimpleDiamondProducts P b)
    (S : Set {β : ι // b.IsPos β}) (hS : PositiveRootConeClosed P b S)
    (l₀ : List {β : ι // b.IsPos β}) (hnodup : l₀.Nodup)
    (hsorted : l₀.Pairwise (fun β γ => b.height β.val ≤ b.height γ.val))
    (hcover : ∀ β : {β : ι // b.IsPos β}, β ∈ l₀)
    (g : WeightCompanion P b O hc hm R)
    (hg : g ∈ positiveRootSubsetSubgroup P b O hc hm R S) :
    ∃ s : {β : ι // b.IsPos β} → R, (∀ β, β ∉ S → s β = 0) ∧
      positiveRootLiftProduct P b R O hc hm L l₀ s = g := by
  let l := l₀.filter (fun β => decide (β ∈ S))
  have hlS : ∀ β ∈ l, β ∈ S := by
    intro β hβ
    exact of_decide_eq_true (List.mem_filter.mp hβ).2
  let ls : List S := l.attachWith (fun β => β ∈ S) hlS
  have hval : ls.map Subtype.val = l := List.attachWith_map_subtype_val hlS
  have hn : ls.Nodup := by
    apply List.Nodup.of_map Subtype.val
    rw [hval]
    exact hnodup.filter _
  have hs : ls.Pairwise (fun β γ => b.height β.val.val ≤ b.height γ.val.val) := by
    have h : (ls.map Subtype.val).Pairwise
        (fun β γ => b.height β.val ≤ b.height γ.val) := by
      rw [hval]
      exact hsorted.filter _
    simpa only [List.pairwise_map] using h
  have hcov (β : S) : β ∈ ls := by
    apply (List.mem_attachWith hlS β).mpr
    exact List.mem_filter.mpr ⟨hcover β.val, decide_eq_true β.property⟩
  obtain ⟨s, hprod⟩ := positiveRootWitnessedSubset_exists_parameters
    P b O hc hm R L hdiamond S hS ls hn hs hcov g hg
  let z : {β : ι // b.IsPos β} → R := fun β =>
    if h : β ∈ S then s ⟨β, h⟩ else 0
  have hz (β : {β : ι // b.IsPos β}) (hβ : β ∉ S) : z β = 0 := by
    simp only [z, dif_neg hβ]
  let f : {β : ι // b.IsPos β} → WeightCompanion P b O hc hm R := fun β =>
    weightCompanionRootLiftHom P b O hc hm R (L β) (Multiplicative.ofAdd (z β))
  have hf (β : {β : ι // b.IsPos β}) (hβ : β ∉ S) : f β = 1 := by
    dsimp only [f]
    rw [hz β hβ]
    exact map_one (weightCompanionRootLiftHom P b O hc hm R (L β))
  refine ⟨z, hz, ?_⟩
  change (l₀.map f).prod = g
  rw [supported_list_prod_filter S f l₀ hf]
  change (l.map f).prod = g
  rw [← hval, List.map_map]
  calc
    (ls.map (f ∘ Subtype.val)).prod =
        (ls.map fun β => weightCompanionRootLiftHom P b O hc hm R
          (L β.val) (Multiplicative.ofAdd (s β))).prod := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro β _
      simp only [Function.comp_apply, f, z, dif_pos β.property]
    _ = g := hprod

/-- Supported coordinates always give an element of the actual root-subset group. -/
theorem positiveRootWitnessedProduct_mem_subset_of_supported
    (hdiamond : SimpleDiamondProducts P b)
    (S : Set {β : ι // b.IsPos β}) (l : List {β : ι // b.IsPos β})
    (s : {β : ι // b.IsPos β} → R) (hs : ∀ β, β ∉ S → s β = 0) :
    positiveRootLiftProduct P b R O hc hm L l s ∈
      positiveRootSubsetSubgroup P b O hc hm R S := by
  apply (positiveRootSubsetSubgroup P b O hc hm R S).list_prod_mem
  intro g hg
  obtain ⟨β, _, rfl⟩ := List.mem_map.mp hg
  by_cases hβ : β ∈ S
  · apply positiveRootSubgroup_le_subset P b O hc hm R S ⟨β, hβ⟩
    rw [← rootLiftSubgroup_eq_positiveWeightCompanionRootSubgroup
      P b O hc hm R hdiamond β (L β)]
    exact ⟨Multiplicative.ofAdd (s β), rfl⟩
  · rw [hs β hβ]
    change weightCompanionRootLiftHom P b O hc hm R (L β) (1 : Multiplicative R) ∈ _
    rw [map_one]
    exact (positiveRootSubsetSubgroup P b O hc hm R S).one_mem

/-- Exact membership criterion for the entire actual restricted subgroup. -/
theorem positiveRootWitnessedProduct_mem_subset_iff
    (hdiamond : SimpleDiamondProducts P b)
    (S : Set {β : ι // b.IsPos β}) (hS : PositiveRootConeClosed P b S)
    (l : List {β : ι // b.IsPos β}) (hnodup : l.Nodup)
    (hsorted : l.Pairwise (fun β γ => b.height β.val ≤ b.height γ.val))
    (hcover : ∀ β : {β : ι // b.IsPos β}, β ∈ l)
    (s : {β : ι // b.IsPos β} → R) :
    positiveRootLiftProduct P b R O hc hm L l s ∈
        positiveRootSubsetSubgroup P b O hc hm R S ↔
      ∀ β, β ∉ S → s β = 0 := by
  constructor
  · intro hg
    obtain ⟨z, hz, he⟩ := positiveRootWitnessedSubset_exists_supported_parameters
      P b O hc hm R L hdiamond S hS l hnodup hsorted hcover _ hg
    have hzs : z = s := positiveRootLiftProduct_injective P b R O hc hm L
      l hnodup hsorted hcover he
    rw [← hzs]
    exact hz
  · exact positiveRootWitnessedProduct_mem_subset_of_supported P b O hc hm R L
      hdiamond S l s

end Atlas.Chevalley
