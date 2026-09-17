import Atlas.GroupTheory.ThreeTranspositionFrames
import Mathlib.Order.Preorder.Finite

noncomputable section
namespace Atlas.GroupTheory

/-- Every commuting subset of a distinguished set in a finite group extends
to a maximal commuting frame. -/
theorem exists_commutingFrame_containing {G : Type*} [Group G] [Finite G]
    (D S : Set G) (hS : S ⊆ D) (hc : ∀ x ∈ S, ∀ y ∈ S, Commute x y) :
    ∃ F : Set G, IsCommutingFrame D F ∧ S ⊆ F := by
  let C : Set (Set G) := {F | F ⊆ D ∧ (∀ x ∈ F, ∀ y ∈ F, Commute x y) ∧ S ⊆ F}
  obtain ⟨F,hF,hmax⟩ := (Set.toFinite C).exists_maximal (show C.Nonempty from
    ⟨S,hS,hc,Set.Subset.refl S⟩)
  refine ⟨F,⟨hF.1,hF.2.1,?_⟩,hF.2.2⟩
  intro E hE hcE hFE
  apply Set.Subset.antisymm _ hFE
  exact hmax ⟨hE,hcE,hF.2.2.trans hFE⟩ hFE

end Atlas.GroupTheory
