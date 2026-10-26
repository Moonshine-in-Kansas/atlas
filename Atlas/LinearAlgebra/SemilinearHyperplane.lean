import Mathlib.Algebra.Module.LinearMap.Basic

/-! Extending equality of semilinear maps from a kernel and one normalized vector. -/
namespace Atlas
variable {F R V M : Type*} [CommRing F] [CommRing R]
  [AddCommGroup V] [Module F V] [AddCommGroup M] [Module R M]

theorem semilinear_ext_on_kernel_and_unit (σ : F →+* R) (δ : V →ₗ[F] F)
    (f g : V →ₛₗ[σ] M) (x : V) (hx : δ x = 1)
    (hk : ∀ z, δ z = 0 → f z = g z) (he : f x = g x) : f = g := by
  apply LinearMap.ext
  intro y
  have hz : δ (y - δ y • x) = 0 := by simp [hx]
  have h := hk _ hz
  simp only [map_sub, LinearMap.map_smulₛₗ, he] at h
  simp only [sub_eq_add_neg] at h
  exact add_right_cancel h

end Atlas
