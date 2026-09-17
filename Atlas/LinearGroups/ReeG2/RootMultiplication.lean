import Atlas.LinearGroups.ReeG2.RootMatrices

noncomputable section
namespace Atlas.ReeG2
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 3]
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The root multiplication law in the inverse-Tits convention. -/
theorem rootMatrix_mul (m : ℕ) (hcard : Nat.card F = 3 ^ (2*m+1))
    (a b c d e f : F) :
    rootMatrix m a b c * rootMatrix m d e f =
      rootMatrix m (a+d) (b+e-a*(theta F m d)^3)
        (c+f-d*b+a*(theta F m d)^3*d-a^2*(theta F m d)^3) := by
  have hc : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have ht := theta_square_cube hcard d
  simp only [rootMatrix_expanded]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootExpanded, Matrix.mul_apply,
      Fin.sum_univ_succ, -theta_apply, theta_square_cube hcard] <;>
    apply sub_eq_zero.mp <;> ring_nf <;> reduce_mod_char!
end Atlas.ReeG2
