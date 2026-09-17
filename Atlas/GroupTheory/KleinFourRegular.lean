import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

namespace Atlas.GroupTheory
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem kleinFour_fixed_eq_one (hc : Nat.card α = 4)
    (g : alternatingGroup.kleinFour α) (x : α) (hx : g.val.val x = x) : g = 1 := by
  have hg := g.prop
  rw [← SetLike.mem_coe,alternatingGroup.coe_kleinFour_of_card_eq_four hc] at hg
  rcases hg with hg | hg
  · exact Subtype.ext hg
  have hs : g.val.val.support.card = Fintype.card α := by
    rw [← Equiv.Perm.sum_cycleType,hg,← Nat.card_eq_fintype_card,hc]
    rfl
  have ht : g.val.val.support = Finset.univ := Finset.eq_univ_of_card _ hs
  have hn := Equiv.Perm.notMem_support.mpr hx
  rw [ht] at hn
  exact False.elim (hn (Finset.mem_univ x))

theorem kleinFour_regular (hc : Nat.card α = 4) (x y : α) :
    ∃! g : alternatingGroup.kleinFour α, g.val.val x = y := by
  classical
  letI := Fintype.ofFinite (alternatingGroup.kleinFour α)
  have hinj : Function.Injective (fun g : alternatingGroup.kleinFour α => g.val.val x) := by
    intro g h he
    change g.val.val x = h.val.val x at he
    have hh : (h⁻¹ * g).val.val x = x := by
      change h.val.val.symm (g.val.val x) = x
      rw [he,Equiv.symm_apply_apply]
    exact (inv_mul_eq_one.mp (kleinFour_fixed_eq_one hc _ x hh)).symm
  have hcard : Fintype.card (alternatingGroup.kleinFour α) = Fintype.card α := by
    rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,
      alternatingGroup.kleinFour_card_of_card_eq_four hc,hc]
  have hs := (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj,hcard⟩
  obtain ⟨g,hg⟩ := hs.2 y
  exact ⟨g,hg,fun h hh => hinj (hh.trans hg.symm)⟩

end Atlas.GroupTheory
