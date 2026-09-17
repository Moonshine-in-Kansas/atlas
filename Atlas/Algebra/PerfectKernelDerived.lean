import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Index
import Mathlib.Data.ZMod.Basic

namespace Atlas.Algebra

/-- A perfect kernel with abelian quotient is precisely the derived subgroup. -/
theorem commutator_eq_perfect_kernel {G A : Type*} [Group G] [CommGroup A]
    (f : G →* A) [Group.IsPerfect f.ker] : commutator G=f.ker := by
  apply le_antisymm (Abelianization.commutator_subset_ker f)
  rw [← f.ker.commutator_eq_self]
  exact Subgroup.commutator_mono le_top le_top

/-- Surjective actual binary parity has kernel index two, without knowing the
ambient group order. -/
theorem binary_parity_kernel_index {G : Type*} [Group G]
    (f : G →* Multiplicative (ZMod 2)) (hf : Function.Surjective f) : f.ker.index=2 := by
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr hf,Subgroup.card_top,Nat.card_eq_fintype_card]
  rfl

end Atlas.Algebra
