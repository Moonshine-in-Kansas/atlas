import Atlas.LinearAlgebra.QuadraticSiegel

/-! # Equal-value transport by a single Siegel transformation -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (u v w : V)
  (hw : Q w = 0) (hval : Q u = Q v)
  (hp : Q.polarBilin u w = Q.polarBilin v w) (hne : Q.polarBilin u w ≠ 0)

def transportParameter : V := (Q.polarBilin u w)⁻¹ • (u-v)

include hp in
theorem transportParameter_perp : Q.polarBilin w (transportParameter Q u v w) = 0 := by
  have h : Q.polarBilin w u = Q.polarBilin w v := by
    rw [polar_swap Q w u, polar_swap Q w v]
    exact hp
  rw [transportParameter, map_smul, map_sub, h, sub_self, smul_zero]

include hval in
theorem difference_polar_value : Q.polarBilin u (u-v) = Q (u-v) := by
  rw [map_sub, polar_self, sub_eq_add_neg u v, ← neg_one_smul F v, add_smul]
  rw [hval]
  ring

include hval hne in
/-- Equal quadratic values and equal nonzero pairing with a singular direction suffice. -/
theorem siegel_equal_value_transport : siegel Q w (transportParameter Q u v w) u = v := by
  have hdiff := difference_polar_value Q u v hval
  simp only [siegel, transportParameter, map_smul, smul_eq_mul, Q.map_smul, smul_smul]
  rw [hdiff]
  match_scalars <;> field_simp <;> ring

end Atlas.Quadratic
