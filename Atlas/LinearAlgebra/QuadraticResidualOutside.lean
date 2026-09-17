import Atlas.LinearAlgebra.QuadraticResidualReflection
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-! # Reflections outside an isometry's residual space -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (g : Q.IsometryEquiv Q)

theorem fixed_iff_mem_residual_orthogonal (hQ : Q.polarBilin.Nondegenerate) (x : V) :
    g x = x ↔ x ∈ LinearMap.BilinForm.orthogonal Q.polarBilin (residual Q g) := by
  rw [fixed_iff_perpendicular_residual Q g hQ]
  constructor
  · intro h y hy
    exact (polar_swap Q y x).trans (h ⟨y, hy⟩)
  · intro h y
    exact (polar_swap Q x y.val).trans (h y.val y.prop)

/-- An outside vector has a nonzero polar pairing with some fixed vector. -/
theorem outside_residual_fixed_witness (hQ : Q.polarBilin.Nondegenerate)
    (a : V) (ha : a ∉ residual Q g) : ∃ x, g x = x ∧ Q.polarBilin x a ≠ 0 := by
  classical
  by_contra! h
  apply ha
  have hr : Q.polarBilin.IsRefl := fun x y h => (polar_swap Q y x).trans h
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hQ hr (residual Q g)]
  intro x hx
  exact h x ((fixed_iff_mem_residual_orthogonal Q g hQ x).mpr hx)

/-- An anisotropic reflecting vector outside the old residual belongs to the new one. -/
theorem outside_mem_reflected_residual (hQ : Q.polarBilin.Nondegenerate)
    (a : V) (ha : Q a ≠ 0) (hout : a ∉ residual Q g) :
    a ∈ residual Q (reflectedIsometry Q g a ha) := by
  obtain ⟨x, hx, hp⟩ := outside_residual_fixed_witness Q g hQ a hout
  let c := (Q a)⁻¹ * Q.polarBilin x a
  have hc : c ≠ 0 := mul_ne_zero (inv_ne_zero ha) hp
  have he : residualMap Q (reflectedIsometry Q g a ha) x = c • a := by
    rw [reflected_residual, residualMap_apply, hx, sub_self, zero_add]
  refine ⟨c⁻¹ • x, ?_⟩
  rw [map_smul, he, smul_smul, inv_mul_cancel₀ hc, one_smul]

end Atlas.Quadratic
