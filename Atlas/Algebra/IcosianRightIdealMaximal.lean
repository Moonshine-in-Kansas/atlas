import Atlas.Algebra.IcosianRightIdeals
import Mathlib.Order.Atoms

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped Matrix

theorem icosianRowRightIdeal_ne_top (r : Fin 2) : icosianRowRightIdeal r≠⊤ := by
  intro h
  have hm : (1 : icosianOrder) ∈ icosianRowRightIdeal r := h ▸ Submodule.mem_top
  have he := hm r
  simpa using he

/-- A nonzero row vector generates the full two-dimensional row module. -/
theorem icosianRowRightIdeal_extension (r : Fin 2)
    (S : Submodule icosianOrderᵐᵒᵖ icosianOrder) (hS : icosianRowRightIdeal r≤S)
    (y : icosianOrder) (hy : y ∈ S) (hne : y ∉ icosianRowRightIdeal r) : S=⊤ := by
  have hn : ¬ ∀ j,icosianModuloTwo y r j=0 := hne
  push_neg at hn
  obtain ⟨k,hk⟩ := hn
  apply top_unique
  intro x _
  let m : IcosianMatrix := fun i j =>
    if i=k then (icosianModuloTwo y r k)⁻¹*icosianModuloTwo x r j else 0
  obtain ⟨a,ha⟩ := icosianModuloTwo_surjective m
  have hrow : ∀ j,icosianModuloTwo (y*a) r j=icosianModuloTwo x r j := by
    intro j
    rw [map_mul,ha]
    simp [Matrix.mul_apply,m,hk]
  have hd : x-y*a ∈ icosianRowRightIdeal r := by
    intro j
    rw [map_sub]
    change icosianModuloTwo x r j-icosianModuloTwo (y*a) r j=0
    rw [hrow,sub_self]
  have hmul : y*a ∈ S := S.smul_mem (MulOpposite.op a) hy
  have hadd := S.add_mem (hS hd) hmul
  simpa using hadd

theorem icosianRowRightIdeal_maximal (r : Fin 2) : IsCoatom (icosianRowRightIdeal r) := by
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨icosianRowRightIdeal_ne_top r,?_⟩
  intro S htop hS y hy
  by_contra hn
  exact htop (icosianRowRightIdeal_extension r S hS y hy hn)

theorem icosianP_maximal : IsCoatom icosianP := icosianRowRightIdeal_maximal 1

theorem icosianPZero_maximal : IsCoatom icosianPZero := icosianRowRightIdeal_maximal 0

end Atlas.Algebra
