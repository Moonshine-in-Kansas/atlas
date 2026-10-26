import Atlas.LinearGroups.Chevalley.PositiveRootSubsetCollection

/-! Disjoint cone-closed positive-root subsets give disjoint actual subgroups.
Restricted parameters are extended by zero to the same full height-ordered
root list, so the existing adjoint parameter-recovery theorem applies directly.
No injectivity of the global companion projection is assumed. -/

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

private theorem list_prod_filter_of_one_off {A G : Type*} [Monoid G]
    (S : Set A) (f : A → G) (l : List A) (hone : ∀ a, a ∉ S → f a = 1) :
    (l.map f).prod = ((l.filter (fun a => decide (a ∈ S))).map f).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : a ∈ S
    · simp [ha, ih]
    · simp [ha, hone a ha, ih]

theorem positiveRootChosenProduct_zero :
    (positiveRootChosenProduct P b O hc hm R (fun _ => 0)).val = 1 := by
  change ((positiveRootHeightList P b).map fun β =>
    weightCompanionRootLiftHom P b O hc hm R
      (positiveRootChosenLift P b O hc hm R β) (1 : Multiplicative R)).prod = 1
  simp only [map_one]
  apply List.prod_eq_one
  intro x hx
  obtain ⟨β, hβ, rfl⟩ := List.mem_map.mp hx
  rfl

/-- A cone-closed restricted subgroup has full-list coordinates supported
inside that subset. The witnesses and full height list are fixed globally. -/
theorem positiveRootSubset_exists_supported_parameters
    (hdiamond : SimpleDiamondProducts P b)
    (S : Set {β : ι // b.IsPos β}) (hS : PositiveRootConeClosed P b S)
    (g : WeightCompanion P b O hc hm R)
    (hg : g ∈ positiveRootSubsetSubgroup P b O hc hm R S) :
    ∃ s : {β : ι // b.IsPos β} → R,
      (∀ β, β ∉ S → s β = 0) ∧
        (positiveRootChosenProduct P b O hc hm R s).val = g := by
  let l₀ := positiveRootHeightList P b
  let l := l₀.filter (fun β => decide (β ∈ S))
  have hlS : ∀ β ∈ l, β ∈ S := by
    intro β hβ
    exact of_decide_eq_true (List.mem_filter.mp hβ).2
  let ls : List S := l.attachWith (fun β => β ∈ S) hlS
  have hval : ls.map Subtype.val = l := List.attachWith_map_subtype_val hlS
  have hnodup : ls.Nodup := by
    apply List.Nodup.of_map Subtype.val
    rw [hval]
    exact (positiveRootHeightList_nodup P b).filter _
  have hsorted : ls.Pairwise (fun β γ => b.height β.val.val ≤ b.height γ.val.val) := by
    have hsorted' : (ls.map Subtype.val).Pairwise
        (fun β γ => b.height β.val ≤ b.height γ.val) := by
      rw [hval]
      exact (positiveRootHeightList_pairwise P b).filter _
    simpa only [List.pairwise_map] using hsorted'
  have hcover (β : S) : β ∈ ls := by
    apply (List.mem_attachWith hlS β).mpr
    exact List.mem_filter.mpr ⟨mem_positiveRootHeightList P b β.val,
      decide_eq_true β.property⟩
  obtain ⟨s, hs⟩ := positiveRootSubset_exists_parameters P b O hc hm R hdiamond
    S hS ls hnodup hsorted hcover g hg
  let z : {β : ι // b.IsPos β} → R := fun β =>
    if h : β ∈ S then s ⟨β, h⟩ else 0
  have hz (β : {β : ι // b.IsPos β}) (hβ : β ∉ S) : z β = 0 := by
    simp only [z, dif_neg hβ]
  let f : {β : ι // b.IsPos β} → WeightCompanion P b O hc hm R := fun β =>
    weightCompanionRootLiftHom P b O hc hm R
      (positiveRootChosenLift P b O hc hm R β) (Multiplicative.ofAdd (z β))
  have hf (β : {β : ι // b.IsPos β}) (hβ : β ∉ S) : f β = 1 := by
    dsimp only [f]
    rw [hz β hβ]
    exact map_one (weightCompanionRootLiftHom P b O hc hm R
      (positiveRootChosenLift P b O hc hm R β))
  refine ⟨z, hz, ?_⟩
  change (l₀.map f).prod = g
  rw [list_prod_filter_of_one_off S f l₀ hf]
  change (l.map f).prod = g
  rw [← hval, List.map_map]
  calc
    (ls.map (f ∘ Subtype.val)).prod =
        (ls.map fun β => weightCompanionRootLiftHom P b O hc hm R
          (positiveRootChosenLift P b O hc hm R β.val) (Multiplicative.ofAdd (s β))).prod := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro β hβ
      simp only [Function.comp_apply, f, z, dif_pos β.property]
    _ = g := hs

theorem positiveRootSubset_eq_one_of_mem_disjoint
    (hdiamond : SimpleDiamondProducts P b)
    (S T : Set {β : ι // b.IsPos β})
    (hS : PositiveRootConeClosed P b S) (hT : PositiveRootConeClosed P b T)
    (hd : Disjoint S T) (g : WeightCompanion P b O hc hm R)
    (hs : g ∈ positiveRootSubsetSubgroup P b O hc hm R S)
    (ht : g ∈ positiveRootSubsetSubgroup P b O hc hm R T) : g = 1 := by
  obtain ⟨s, hs0, hs⟩ := positiveRootSubset_exists_supported_parameters
    P b O hc hm R hdiamond S hS g hs
  obtain ⟨t, ht0, ht⟩ := positiveRootSubset_exists_supported_parameters
    P b O hc hm R hdiamond T hT g ht
  have hst : s = t := positiveRootChosenProduct_adjoint_injective P b O hc hm R
    (by
      change weightCompanionRho P b O hc hm R (positiveRootChosenProduct P b O hc hm R s).val =
        weightCompanionRho P b O hc hm R (positiveRootChosenProduct P b O hc hm R t).val
      rw [hs, ht])
  have hz : s = fun _ => 0 := by
    funext β
    by_cases hβ : β ∈ S
    · have hn : β ∉ T := fun hβT => Set.disjoint_left.mp hd hβ hβT
      rw [hst]
      exact ht0 β hn
    · exact hs0 β hβ
  rw [← hs, hz]
  exact positiveRootChosenProduct_zero P b O hc hm R

theorem positiveRootSubsetSubgroup_disjoint
    (hdiamond : SimpleDiamondProducts P b)
    (S T : Set {β : ι // b.IsPos β})
    (hS : PositiveRootConeClosed P b S) (hT : PositiveRootConeClosed P b T)
    (hd : Disjoint S T) :
    Disjoint (positiveRootSubsetSubgroup P b O hc hm R S)
      (positiveRootSubsetSubgroup P b O hc hm R T) := by
  apply disjoint_iff_inf_le.mpr
  rintro g ⟨hs, ht⟩
  exact Subgroup.mem_bot.mpr
    (positiveRootSubset_eq_one_of_mem_disjoint P b O hc hm R hdiamond S T hS hT hd g hs ht)

end Atlas.Chevalley
