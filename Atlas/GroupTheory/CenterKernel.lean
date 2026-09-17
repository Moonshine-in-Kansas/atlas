import Mathlib.GroupTheory.Subgroup.Center

namespace Atlas.GroupTheory

/-- A central extension of a centerless group has precisely its kernel as center. -/
theorem center_eq_kernel_of_surjective {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (hQ : Subgroup.center Q=⊥)
    (hk : f.ker ≤ Subgroup.center G) : Subgroup.center G=f.ker := by
  apply le_antisymm ?_ hk
  intro z hz
  have hm := Subgroup.map_center_le_center hf
    (show f z ∈ (Subgroup.center G).map f from ⟨z,hz,rfl⟩)
  rw [hQ] at hm
  exact hm

end Atlas.GroupTheory
