import Atlas.LinearGroups.SuzukiFamily.Matrices

/-! Diagonal torus and Weyl identities in the actual four-coordinate model. -/
noncomputable section
namespace Atlas.SuzukiFamily
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

@[simp] theorem h_one (m : ℕ) : h m (1 : Fˣ)=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h,Matrix.diagonal_apply]

theorem h_mul (m : ℕ) (s t : Fˣ) : h m s * h m t = h m (s*t) := by
  simp only [h,Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp [-theta_apply,map_mul] <;> ring

theorem h_injective (m : ℕ) : Function.Injective (h (F := F) m) := by
  intro s t he
  apply Units.ext
  exact congrArg (fun A => A 1 1) he

theorem w_h_w (m : ℕ) (t : Fˣ) :
    w * h m t * w = h m t⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [w,h,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.diagonal_apply,Matrix.vecMul, dotProduct,Fin.sum_univ_succ,-theta_apply]

theorem h_conjugate_u (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (t : Fˣ) (a b : F) :
    h m t⁻¹ * u m a b * h m t =
      u m (theta F m (t:F)*a) ((t:F)^2*theta F m (t:F)*b) := by
  have ht : (t:F) ≠ 0 := Units.ne_zero t
  have hθ : theta F m (t:F) ≠ 0 := (map_ne_zero (theta F m)).mpr ht
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h,u,norm,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.diagonal_apply,
      -theta_apply,theta_square hcard, map_mul,map_pow,Units.val_inv_eq_inv_val] <;>
    field_simp <;> ring
end Atlas.SuzukiFamily
