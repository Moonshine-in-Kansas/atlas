import Atlas.OrderArithmetic.PolynomialCoefficient
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Parity

namespace Atlas.OrderArithmetic
open Polynomial

/-! Generated coefficient-prefix proofs for unitary(5,0) versus G2(0).
Generator: verification/order-arithmetic/generate-polynomial-certificates.rb.
The generator is not trusted: every theorem below must be checked by Lean.
These statements do not assert the exclusion of integer roots. -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000 in
theorem exceptional_pair15_d1_d1_first_coefficients :
    ∀ i ∈ Finset.range 7,
      (comparisonPolynomial (.unitary 5 0) (.G2 0) 3 5 1 1).coeff i =
        if i = 6 then (-1 : ℤ) else 0 := by
  intro i hi
  have hi_bound : i < 7 := Finset.mem_range.mp hi
  rw [comparisonPolynomial_coeff _ _ 3 5 _ _ i (by decide) (by decide)]
  interval_cases i <;> norm_num
  all_goals
    norm_num [
      residualPolynomial, Finset.prod_Icc_succ_top, coeff_mul, coeff_one,
      Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000 in
theorem exceptional_pair15_d5_d1_first_coefficients :
    ∀ i ∈ Finset.range 1,
      (comparisonPolynomial (.unitary 5 0) (.G2 0) 3 5 5 1).coeff i =
        if i = 0 then (-4 : ℤ) else 0 := by
  intro i hi
  have hi_bound : i < 1 := Finset.mem_range.mp hi
  rw [comparisonPolynomial_coeff _ _ 3 5 _ _ i (by decide) (by decide)]
  interval_cases i <;> norm_num
  all_goals
    norm_num [
      residualPolynomial, Finset.prod_Icc_succ_top, coeff_mul, coeff_one,
      Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero]

end Atlas.OrderArithmetic
