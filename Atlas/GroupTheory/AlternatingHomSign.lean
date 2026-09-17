import Mathlib.GroupTheory.SpecificGroups.Alternating

namespace Atlas.GroupTheory
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem alternating_hom_sign (f : alternatingGroup α →* Equiv.Perm β)
    (g : alternatingGroup α) : Equiv.Perm.sign (f g) = 1 := by
  let h := Equiv.Perm.sign.comp f
  have htop : h.ker = ⊤ := by
    apply top_unique
    rw [← alternatingGroup.closure_isThreeCycles_eq_top, Subgroup.closure_le]
    intro x hx
    have hx3 : x ^ 3 = 1 := by
      apply Subtype.ext
      exact hx.orderOf ▸ pow_orderOf_eq_one x.val
    have hh : h x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
    have hs := Int.units_sq (h x)
    change h x = 1
    calc
      h x = h x ^ 2 * h x := by rw [hs,one_mul]
      _ = 1 := by simpa only [pow_succ] using hh
  have hg : g ∈ h.ker := by rw [htop]; trivial
  exact hg

end Atlas.GroupTheory
