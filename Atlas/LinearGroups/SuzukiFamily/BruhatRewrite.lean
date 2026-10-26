import Atlas.LinearGroups.SuzukiFamily.Inversion
import Atlas.LinearGroups.SuzukiFamily.Torus

/-! The explicit nontrivial Weyl/root rewrite underlying the two-cell decomposition. -/
noncomputable section
namespace Atlas.SuzukiFamily
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem norm_reciprocal (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a b : F)
    (hn : norm m a b ≠ 0) :
    norm m (b/norm m a b) (a/norm m a b) = (norm m a b)⁻¹ := by
  have ht : theta F m (norm m a b) ≠ 0 := (map_ne_zero (theta F m)).mpr hn
  rw [norm]
  simp only [map_div₀]
  field_simp [hn,ht]
  simp only [norm,map_add,map_mul,map_pow,theta_square hcard]
  apply sub_eq_zero.mp
  ring_nf
  reduce_mod_char!

def bruhatTorus (m : ℕ) (a b : F) (hn : norm m a b ≠ 0) : Fˣ :=
  Units.mk0 (norm m a b / theta F m (norm m a b))
    (div_ne_zero hn ((map_ne_zero (theta F m)).mpr hn))

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 8192 in
theorem weyl_root_weyl (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a b : F)
    (hn : norm m a b ≠ 0) :
    w * u m a b * w =
      u m (inverseFirst m a b) (inverseSecond m a b) * w *
        h m (bruhatTorus m a b hn) * u m (b/norm m a b) (a/norm m a b) := by
  have ht : theta F m (norm m a b) ≠ 0 := (map_ne_zero (theta F m)).mpr hn
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u,w,h,bruhatTorus,Matrix.mul_apply,Matrix.vecMul,dotProduct,
      Fin.sum_univ_succ,Matrix.diagonal_apply,-theta_apply,
      norm_inverse m hcard a b hn,norm_reciprocal m hcard a b hn,
      map_div₀,theta_square hcard] <;>
    (try simp only [inverseFirst,inverseSecond,map_add,map_mul,map_div₀,map_pow,
      theta_square hcard]) <;>
    field_simp [hn,ht] <;>
    (try simp only [norm,map_add,map_mul,map_pow,theta_square hcard]) <;>
    apply sub_eq_zero.mp <;> ring_nf <;> reduce_mod_char!
end Atlas.SuzukiFamily
