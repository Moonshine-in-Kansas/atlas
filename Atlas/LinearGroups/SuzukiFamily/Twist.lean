import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-! The characteristic-two Tits automorphism, including the binary parameter. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

def theta (m : ℕ) : F ≃+* F := iterateFrobeniusEquiv F 2 (m+1)
@[simp] theorem theta_apply (m : ℕ) (x : F) :
    theta F m x = x ^ (2^(m+1)) := rfl

variable {F} {m : ℕ}
theorem frobenius_period (hcard : Nat.card F = 2^(2*m+1)) (x : F) :
    iterateFrobeniusEquiv F 2 (2*m+1) x = x := by
  letI := Fintype.ofFinite F
  rw [iterateFrobeniusEquiv_def, ← hcard, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

theorem theta_square (hcard : Nat.card F = 2^(2*m+1)) (x : F) :
    theta F m (theta F m x) = x^2 := by
  change iterateFrobeniusEquiv F 2 (m+1) (iterateFrobeniusEquiv F 2 (m+1) x) = x^2
  rw [← iterateFrobeniusEquiv_add_apply]
  rw [show m+1+(m+1) = 1+(2*m+1) by omega, iterateFrobeniusEquiv_add_apply,
    frobenius_period hcard]
  rfl

variable {K : Type*} [Field K] [Finite K] [CharP K 2]
theorem map_theta (e : F ≃+* K) (m : ℕ) (x : F) :
    e (theta F m x) = theta K m (e x) := by simp only [theta_apply, map_pow]

theorem theta_binary (hcard : Nat.card F = 2) (x : F) : theta F 0 x = x := by
  simpa [theta, iterateFrobeniusEquiv_def] using
    frobenius_period (m := 0) (by simpa using hcard) x

theorem card_ge_eight (hcard : Nat.card F = 2^(2*m+1)) (hm : 1 ≤ m) :
    8 ≤ Nat.card F := by
  rw [hcard]
  calc
    8 = 2^3 := by norm_num
    _ ≤ 2^(2*m+1) := Nat.pow_le_pow_right (by omega) (by omega)
end Atlas.SuzukiFamily
