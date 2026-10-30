import Atlas.GroupTheory.GraphFieldFixedPoints

/-! Fixed-point lifting across a surjection with kernel of exponent dividing
three. The explicit correction is valid even without a centrality hypothesis;
ambient surjectivity alone would not suffice. -/
namespace Atlas.GroupTheory
variable {G H : Type*} [Group G] [Group H]

theorem involution_cubic_correction (a : G ≃* G) (ha : Function.Involutive a)
    (g : G) (hc : (a g * g⁻¹) ^ 3 = 1) :
    a ((a g * g⁻¹)⁻¹ * g) = (a g * g⁻¹)⁻¹ * g := by
  let c := a g * g⁻¹
  have hac : a c = c⁻¹ := by
    dsimp [c]
    rw [map_mul, map_inv, ha g, mul_inv_rev, inv_inv]
  have hag : a g = c * g := by simp only [c, mul_assoc, inv_mul_cancel, mul_one]
  have hc3 : c * c * c = 1 := by simpa only [pow_succ, pow_zero, one_mul] using hc
  have hc2 : c * c = c⁻¹ := by
    calc
      c * c = (c * c * c) * c⁻¹ := by simp only [mul_assoc, mul_inv_cancel, mul_one]
      _ = c⁻¹ := by rw [hc3, one_mul]
  change a (c⁻¹ * g) = c⁻¹ * g
  rw [map_mul, map_inv, hac, inv_inv, hag, ← mul_assoc, hc2]

/-- Equivariance, ambient surjectivity and an actual exponent-three kernel
give surjectivity on the fixed subgroups. All three premises are explicit. -/
theorem fixedSubgroupMap_surjective_of_cubic_kernel
    (a : G ≃* G) (b : H ≃* H) (f : G →* H)
    (ha : Function.Involutive a) (hf : ∀ g, f (a g) = b (f g))
    (hsurj : Function.Surjective f) (hker : ∀ c ∈ f.ker, c ^ 3 = 1) :
    Function.Surjective (fixedSubgroupMap a b f hf) := by
  intro h
  obtain ⟨g, hg⟩ := hsurj h.val
  have hfix : b h.val = h.val := h.property
  have hc : f (a g * g⁻¹) = 1 := by
    rw [map_mul, map_inv, hf g, hg, hfix, mul_inv_cancel]
  refine ⟨⟨(a g * g⁻¹)⁻¹ * g,
    involution_cubic_correction a ha g (hker _ hc)⟩, ?_⟩
  apply Subtype.ext
  change f ((a g * g⁻¹)⁻¹ * g) = h.val
  rw [map_mul, map_inv, hc, inv_one, one_mul, hg]

end Atlas.GroupTheory
