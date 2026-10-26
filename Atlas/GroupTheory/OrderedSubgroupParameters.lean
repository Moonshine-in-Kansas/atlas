import Atlas.GroupTheory.OrderedSubgroupCollection

/-! Parameters for a product of distinct indexed subgroup ranges. This lemma
identifies the image of a literal product; it assumes neither collection nor
injectivity of any parameter homomorphism. -/
namespace Atlas.GroupTheory
open scoped Pointwise

variable {G A ι : Type*} [Group G] [Group A] [DecidableEq ι]

/-- A distinct indexed product of homomorphism ranges has one parameter per
index. Parameters outside the list are unconstrained. -/
theorem mem_orderedSubgroupProduct_map_range_iff
    (f : ι → A →* G) (l : List ι) (hnodup : l.Nodup) (g : G) :
    g ∈ orderedSubgroupProduct (l.map fun i => (f i).range) ↔
      ∃ s : ι → A, (l.map fun i => f i (s i)).prod = g := by
  induction l generalizing g with
  | nil =>
    constructor
    · intro hg
      have he : g = 1 := hg
      exact ⟨fun _ => 1, by simpa using he.symm⟩
    · rintro ⟨s, hs⟩
      simpa only [List.map_nil, List.prod_nil, orderedSubgroupProduct, Set.mem_singleton_iff] using hs.symm
  | cons i l ih =>
    obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hnodup
    change g ∈ ((f i).range : Set G) *
      orderedSubgroupProduct (l.map fun j => (f j).range) ↔ _
    constructor
    · rintro ⟨x, ⟨a, rfl⟩, y, hy, rfl⟩
      obtain ⟨s, hs⟩ := (ih hnodup y).mp hy
      refine ⟨Function.update s i a, ?_⟩
      simp only [List.map_cons, List.prod_cons, Function.update_self]
      rw [← hs]
      congr 1
      apply congrArg List.prod
      apply List.map_congr_left
      intro j hj
      have hji : j ≠ i := fun he => hnot (he ▸ hj)
      rw [Function.update_of_ne hji]
    · rintro ⟨s, hs⟩
      refine ⟨f i (s i), ⟨s i, rfl⟩,
        (l.map fun j => f j (s j)).prod, (ih hnodup _).mpr ⟨s, rfl⟩, ?_⟩
      simpa only [List.map_cons, List.prod_cons] using hs

/-- The range of the literal parameter product is exactly the ordered product
of subgroup ranges. No assertion that this set is a subgroup is made. -/
theorem range_orderedParameters_eq_orderedSubgroupProduct
    (f : ι → A →* G) (l : List ι) (hnodup : l.Nodup) :
    Set.range (fun s : ι → A => (l.map fun i => f i (s i)).prod) =
      orderedSubgroupProduct (l.map fun i => (f i).range) := by
  ext g
  exact (mem_orderedSubgroupProduct_map_range_iff f l hnodup g).symm

end Atlas.GroupTheory
