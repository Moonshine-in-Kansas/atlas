import Atlas.OrderArithmetic.ResidualPolynomial
import Atlas.OrderArithmetic.IntegerRootCoefficient
import Mathlib.Algebra.Polynomial.Expand

namespace Atlas.OrderArithmetic
open Polynomial

theorem comparisonPolynomial_coeff (x y : RawEntry) (b a dx dy k : ℕ)
    (hb : 0 < b) (ha : 0 < a) :
    (comparisonPolynomial x y b a dx dy).coeff k =
      (dy : ℤ) * (if b ∣ k then (residualPolynomial x).coeff (k / b) else 0) -
      (dx : ℤ) * (if a ∣ k then (residualPolynomial y).coeff (k / a) else 0) := by
  simp only [comparisonPolynomial, coeff_sub, coeff_C_mul, ← expand_eq_comp_X_pow,
    coeff_expand hb, coeff_expand ha]

end Atlas.OrderArithmetic
