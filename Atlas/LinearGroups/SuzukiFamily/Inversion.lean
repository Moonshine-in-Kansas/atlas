import Atlas.LinearGroups.SuzukiFamily.Anisotropy

/-! Explicit inversion of the affine Suzuki ovoid chart. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def inverseFirst (m : ℕ) (a b : F) := (a*theta F m a+b)/norm m a b
def inverseSecond (m : ℕ) (a b : F) :=
  a/norm m a b + inverseFirst m a b*theta F m (inverseFirst m a b)

set_option maxHeartbeats 800000 in
theorem norm_inverse (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a b : F)
    (hn : norm m a b ≠ 0) :
    norm m (inverseFirst m a b) (inverseSecond m a b) = (norm m a b)⁻¹ := by
  have ht : theta F m (norm m a b) ≠ 0 := (map_ne_zero (theta F m)).mpr hn
  simp only [inverseFirst,inverseSecond]
  rw [norm]
  simp only [map_add,map_mul,map_div₀,map_pow,theta_square hcard]
  field_simp [hn,ht]
  simp only [norm,map_add,map_mul,map_pow,theta_square hcard]
  apply sub_eq_zero.mp
  ring_nf
  reduce_mod_char!
end Atlas.SuzukiFamily
