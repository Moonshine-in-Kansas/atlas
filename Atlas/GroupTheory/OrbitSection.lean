import Mathlib.GroupTheory.GroupAction.Basic

noncomputable section
namespace Atlas.GroupTheory

/-- A stabilizer containment induces an equivariant map from a transitive set. -/
theorem exists_equivariant_map_of_stabilizer {G X Y : Type*} [Group G]
    [MulAction G X] [MulAction G Y] [MulAction.IsPretransitive G X]
    (x : X) (y : Y) (h : ∀ g : G, g • x = x → g • y = y) :
    ∃ f : X → Y, f x = y ∧ (∀ (g : G) (z : X), f (g • z) = g • f z) ∧
      ∀ z, ∃ g : G, g • x = z ∧ f z = g • y := by
  choose s hs using (fun z : X => MulAction.exists_smul_eq G x z)
  let f : X → Y := fun z => s z • y
  have he (g : G) (z : X) : f (g • z) = g • f z := by
    have ht : ((s (g • z))⁻¹ * g * s z) • x = x := by
      simp only [mul_smul,hs]
      exact inv_smul_eq_iff.mpr (hs (g • z)).symm
    have hh := h _ ht
    simp only [mul_smul] at hh
    exact (inv_smul_eq_iff.mp hh).symm
  refine ⟨f,h (s x) (hs x),he,?_⟩
  intro z
  exact ⟨s z,hs z,rfl⟩

end Atlas.GroupTheory
