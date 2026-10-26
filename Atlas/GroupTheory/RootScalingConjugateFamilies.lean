import Atlas.GroupTheory.RootScalingKernel

/-! Conjugate parameter families for group elements differing by an actual
unit-scaling element. These elementary lemmas use no root datum. -/

namespace Atlas.GroupTheory
variable {R G : Type*} [Monoid R] [Group G]

theorem rootScaling_conjugates_of_inv_mul (x : R → G) (g h : G)
    (hscale : g⁻¹ * h ∈ rootScalingSubgroup x) :
    ∃ a : Rˣ, ∀ t : R,
      h * x t * h⁻¹ = g * x (a.val * t) * g⁻¹ := by
  obtain ⟨a, ha⟩ := hscale
  refine ⟨a, ?_⟩
  intro t
  have he := congrArg (fun z : G => g * z * h⁻¹) (ha t)
  simpa [mul_assoc] using he

/-- Rescaling by a unit preserves the whole parameter-family image. -/
theorem rootScaling_conjugate_ranges_of_inv_mul (x : R → G) (g h : G)
    (hscale : g⁻¹ * h ∈ rootScalingSubgroup x) :
    Set.range (fun t : R => h * x t * h⁻¹) =
      Set.range (fun t : R => g * x t * g⁻¹) := by
  obtain ⟨a, ha⟩ := rootScaling_conjugates_of_inv_mul x g h hscale
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨a.val * t, (ha t).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨(a⁻¹).val * t, ?_⟩
    dsimp only
    rw [ha]
    simp [← mul_assoc]

end Atlas.GroupTheory
