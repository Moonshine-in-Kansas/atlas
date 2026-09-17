import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.SetTheory.Cardinal.Finite

namespace Atlas.GroupTheory

theorem unique_smul_of_free_card {G X : Type*} [Group G] [MulAction G X] [Finite G] [Finite X]
    (hc : Nat.card G = Nat.card X) (hf : ∀ x : X, ∀ g : G, g • x = x → g = 1)
    (x y : X) : ∃! g : G, g • x = y := by
  have hi : Function.Injective (fun g : G => g • x) := by
    intro g h he
    change g • x = h • x at he
    have hh : (h⁻¹*g) • x = x := by rw [mul_smul,he,inv_smul_smul]
    exact (inv_mul_eq_one.mp (hf x (h⁻¹*g) hh)).symm
  have hb : Function.Bijective (fun g : G => g • x) :=
    (Nat.bijective_iff_injective_and_card _).mpr ⟨hi,hc⟩
  obtain ⟨g,hg⟩ := hb.2 y
  exact ⟨g,hg,fun h hh => hi (hh.trans hg.symm)⟩

end Atlas.GroupTheory
