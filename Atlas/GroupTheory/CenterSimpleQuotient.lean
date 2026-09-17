import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace Atlas.GroupTheory

/-- A nonabelian simple group has trivial center. -/
theorem center_eq_bot_of_simple_nonabelian (G : Type*) [Group G] [IsSimpleGroup G]
    (hn : ¬IsMulCommutative G) : Subgroup.center G=⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with h|h
  · exact h
  · exact (hn (Subgroup.center_eq_top_iff.mp h)).elim

/-- If a central quotient is nonabelian simple, the divided-out subgroup was
already the entire center. No finiteness hypothesis is needed. -/
theorem center_eq_of_simple_quotient (G : Type*) [Group G]
    (Z : Subgroup G) [Z.Normal] (hz : Z ≤ Subgroup.center G)
    [IsSimpleGroup (G ⧸ Z)] (hn : ¬IsMulCommutative (G ⧸ Z)) :
    Subgroup.center G=Z := by
  apply le_antisymm ?_ hz
  intro x hx
  have hm : QuotientGroup.mk' Z x ∈ Subgroup.center (G ⧸ Z) :=
    Subgroup.map_center_le_center (QuotientGroup.mk'_surjective Z)
      (Subgroup.mem_map.mpr ⟨x,hx,rfl⟩)
  rw [center_eq_bot_of_simple_nonabelian (G ⧸ Z) hn,Subgroup.mem_bot] at hm
  exact (QuotientGroup.eq_one_iff x).mp hm

end Atlas.GroupTheory
