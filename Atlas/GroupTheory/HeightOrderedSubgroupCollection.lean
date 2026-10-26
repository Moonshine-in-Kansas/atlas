import Atlas.GroupTheory.OrderedSubgroupCommutators

/-! Strictly increasing commutator height implies collection of a finite
height-ordered generating family. Root-specific containment remains an explicit
hypothesis; no root system, matrix group, or cardinality is assumed here. -/
namespace Atlas.GroupTheory
open scoped commutatorElement

variable {G ι : Type*} [Group G] [DecidableEq ι]

/-- In a height-upward-closed list, every head/tail commutator stays in the
tail join if distinct subgroup commutators increase the second input height. -/
theorem hasTailCommutators_map_of_height
    (H : ι → Subgroup G) (height : ι → ℤ)
    (hcomm : ∀ i j, i ≠ j →
      ⁅H i, H j⁆ ≤ ⨆ k : {k : ι // height j < height k}, H k.val)
    (l : List ι) (hnodup : l.Nodup)
    (hsorted : l.Pairwise (fun i j => height i ≤ height j))
    (hup : ∀ i ∈ l, ∀ j, height i < height j → j ∈ l) :
    HasTailCommutators (l.map H) := by
  induction l with
  | nil => trivial
  | cons i l ih =>
    obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hnodup
    obtain ⟨hhead, hsorted⟩ := List.pairwise_cons.mp hsorted
    have htail : ∀ j ∈ l, ∀ k, height j < height k → k ∈ l := by
      intro j hj k hk
      rcases List.mem_cons.mp (hup j (List.mem_cons_of_mem i hj) k hk) with hki | hkl
      · subst k
        exact False.elim ((not_lt_of_ge (hhead j hj)) hk)
      · exact hkl
    refine ⟨?_, ih hnodup hsorted htail⟩
    intro J hJ
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hJ
    have hne : i ≠ j := by
      intro he
      exact hnot (he.symm ▸ hj)
    refine (hcomm i j hne).trans (iSup_le fun k => ?_)
    exact ((subgroupListJoin_le_iff (l.map H) (subgroupListJoin (l.map H))).mp
      le_rfl (H k.val) (List.mem_map.mpr ⟨k.val, htail j hj k.val k.property, rfl⟩))

/-- An exhaustive distinct height-ordered list is collected under the actual
strict-height subgroup commutator hypothesis. -/
theorem hasOrderedCollection_map_of_height
    (H : ι → Subgroup G) (height : ι → ℤ)
    (hcomm : ∀ i j, i ≠ j →
      ⁅H i, H j⁆ ≤ ⨆ k : {k : ι // height j < height k}, H k.val)
    (l : List ι) (hnodup : l.Nodup)
    (hsorted : l.Pairwise (fun i j => height i ≤ height j))
    (hcover : ∀ i, i ∈ l) : HasOrderedCollection (l.map H) :=
  (hasOrderedCollection_iff_tail_commutators (l.map H)).mpr
    (hasTailCommutators_map_of_height H height hcomm l hnodup hsorted
      (fun _ _ j _ => hcover j))

/-- The literal ordered product is the full generated subgroup, conditional on
proved strict-height commutator containment for the given subgroup family. -/
theorem orderedSubgroupProduct_map_eq_iSup_of_height
    (H : ι → Subgroup G) (height : ι → ℤ)
    (hcomm : ∀ i j, i ≠ j →
      ⁅H i, H j⁆ ≤ ⨆ k : {k : ι // height j < height k}, H k.val)
    (l : List ι) (hnodup : l.Nodup)
    (hsorted : l.Pairwise (fun i j => height i ≤ height j))
    (hcover : ∀ i, i ∈ l) :
    orderedSubgroupProduct (l.map H) = ((⨆ i, H i : Subgroup G) : Set G) := by
  rw [orderedSubgroupProduct_eq_join (l.map H)
    (hasOrderedCollection_map_of_height H height hcomm l hnodup hsorted hcover)]
  congr 1
  apply le_antisymm
  · apply (subgroupListJoin_le_iff _ _).mpr
    intro J hJ
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hJ
    exact le_iSup H i
  · apply iSup_le
    intro i
    exact ((subgroupListJoin_le_iff (l.map H) (subgroupListJoin (l.map H))).mp
      le_rfl (H i) (List.mem_map.mpr ⟨i, hcover i, rfl⟩))

end Atlas.GroupTheory
