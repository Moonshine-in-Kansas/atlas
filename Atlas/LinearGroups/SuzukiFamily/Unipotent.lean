import Atlas.LinearGroups.SuzukiFamily.Matrices

/-! The exact root-group laws in the retained column convention. -/
noncomputable section
namespace Atlas.SuzukiFamily
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem u_mul (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a b c d : F) :
    u m a b * u m c d = u m (a+c) (b+d+a*theta F m c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u,norm,Matrix.mul_apply,Fin.sum_univ_succ,-theta_apply,theta_square hcard] <;>
    apply sub_eq_zero.mp <;> ring_nf <;> reduce_mod_char!

theorem u_square (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a b : F) :
    u m a b * u m a b = u m 0 (a*theta F m a) := by
  rw [u_mul m hcard]
  simp [CharTwo.add_self_eq_zero]

theorem u_mul_inverse (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a b : F) :
    u m a b * u m a (b+a*theta F m a) = 1 := by
  rw [u_mul m hcard]
  have hb : b+(b+a*theta F m a)+a*theta F m a=0 := by
    ring_nf
    reduce_mod_char!
  simp only [CharTwo.add_self_eq_zero,hb,u_zero]

theorem u_central_parameter (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a b c : F) :
    u m 0 c * u m a b = u m a b * u m 0 c := by
  simp [u_mul m hcard,add_comm,-theta_apply]
end Atlas.SuzukiFamily
