import Atlas.OrderArithmetic.PolynomialCoefficient

namespace Atlas.OrderArithmetic
open Polynomial

/-- Sparse binomial multiplication avoids expanding a whole residual product. -/
theorem coeff_mul_pow_sub_one (P : ℤ[X]) (e k : ℕ) :
    (P * (X ^ e - 1)).coeff k =
      (if e ≤ k then P.coeff (k - e) else 0) - P.coeff k := by
  simp only [mul_sub, coeff_sub, coeff_mul_X_pow', mul_one]

theorem coeff_mul_pow_add_one (P : ℤ[X]) (e k : ℕ) :
    (P * (X ^ e + 1)).coeff k =
      (if e ≤ k then P.coeff (k - e) else 0) + P.coeff k := by
  simp only [mul_add, coeff_add, coeff_mul_X_pow', mul_one]

theorem coeff_pow_sub_one_mul (P : ℤ[X]) (e k : ℕ) :
    ((X ^ e - 1) * P).coeff k =
      (if e ≤ k then P.coeff (k - e) else 0) - P.coeff k := by
  rw [mul_comm]
  exact coeff_mul_pow_sub_one P e k

theorem coeff_pow_add_one_mul (P : ℤ[X]) (e k : ℕ) :
    ((X ^ e + 1) * P).coeff k =
      (if e ≤ k then P.coeff (k - e) else 0) + P.coeff k := by
  rw [mul_comm]
  exact coeff_mul_pow_add_one P e k

end Atlas.OrderArithmetic
