import Mathlib.GroupTheory.GroupAction.Basic

namespace Atlas

/-- Orbits of a point stabilizer may be obtained by interchanging the two
coordinates of an invariant relation. Only the stabilizer of one reference
point needs to be analyzed. -/
theorem stabilizer_transitive_of_reference_invariant
    {G X Y Z : Type*} [Group G] [MulAction G X] [MulAction G Y]
    (f : X → Y → Z) (hf : ∀ (g : G) (x : X) (y : Y), f (g • x) (g • y)=f x y)
    (x₀ : X) (y₀ : Y)
    (href : ∀ y z, f x₀ y=f x₀ z →
      ∃ g : G, g • x₀=x₀ ∧ g • y=z)
    (x₁ x₂ : X) (h₁ : x₁∈MulAction.orbit G x₀)
    (h₂ : x₂∈MulAction.orbit G x₀) (he : f x₁ y₀=f x₂ y₀) :
    ∃ g : G, g • y₀=y₀ ∧ g • x₁=x₂ := by
  obtain ⟨a,rfl⟩ := h₁
  obtain ⟨b,rfl⟩ := h₂
  have ht : f x₀ (a⁻¹ • y₀)=f x₀ (b⁻¹ • y₀) := by
    have ha := hf a x₀ (a⁻¹ • y₀)
    have hb := hf b x₀ (b⁻¹ • y₀)
    simp only [smul_inv_smul] at ha hb
    exact ha.symm.trans (he.trans hb)
  obtain ⟨c,hc,hcy⟩ := href _ _ ht
  refine ⟨b*c*a⁻¹,?_,?_⟩
  · simp only [mul_smul]
    rw [hcy,smul_inv_smul]
  · simp only [mul_smul,inv_smul_smul,hc]

end Atlas
