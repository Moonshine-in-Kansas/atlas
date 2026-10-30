import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Abelianization.Defs

namespace Atlas.GroupTheory
variable {N Q : Type*} [Group N] [CommGroup Q]

/-- A semidirect product of a perfect group by an abelian group has exactly
 the first factor as its literal derived subgroup, for any specified action. -/
theorem semidirect_commutator_eq_left [Group.IsPerfect N] (a : Q →* MulAut N) :
    commutator (N ⋊[a] Q) = (SemidirectProduct.inl : N →* N ⋊[a] Q).range := by
  apply le_antisymm
  · rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact Abelianization.commutator_subset_ker SemidirectProduct.rightHom
  · letI := Group.IsPerfect.range (SemidirectProduct.inl : N →* N ⋊[a] Q)
    rw [← Subgroup.commutator_eq_self (H := (SemidirectProduct.inl : N →* N ⋊[a] Q).range)]
    exact Subgroup.commutator_mono le_top le_top

end Atlas.GroupTheory
