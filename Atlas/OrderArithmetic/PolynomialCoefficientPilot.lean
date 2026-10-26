import Atlas.OrderArithmetic.PolynomialCoefficient
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Parity

namespace Atlas.OrderArithmetic
open Polynomial

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000 in
-- This checks only the first 31 coefficients, despite polynomial degree 2280.
theorem unitary17_E8_first_coefficients :
    ∀ i ∈ Finset.range 31,
      (comparisonPolynomial (.unitary 17 0) (.E8 0) 15 17 1 1).coeff i =
        if i = 30 then -1 else 0 := by
  intro i hi
  have hi31 : i < 31 := Finset.mem_range.mp hi
  rw [comparisonPolynomial_coeff _ _ 15 17 _ _ i (by decide) (by decide)]
  interval_cases i <;> norm_num
  all_goals
    norm_num [
      residualPolynomial, Finset.prod_Icc_succ_top, coeff_mul, coeff_one,
      Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero]

end Atlas.OrderArithmetic
