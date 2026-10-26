import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Solvable

namespace Atlas.GroupTheory

theorem semidirectProduct_isSolvable {N H : Type*} [Group N] [Group H]
    (φ : H →* MulAut N) [Group.IsSolvable N] [Group.IsSolvable H] :
    Group.IsSolvable (N ⋊[φ] H) :=
  Group.isSolvable_of_ker_le_range SemidirectProduct.inl SemidirectProduct.rightHom
    (SemidirectProduct.range_inl_eq_ker_rightHom.symm.le)

end Atlas.GroupTheory
