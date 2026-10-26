import Atlas.OrderArithmetic.PolynomialCoefficient
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Parity

namespace Atlas.OrderArithmetic
open Polynomial

/-! Generated coefficient-prefix proofs for linear(3,0) versus trialityD4(0).
Generator: verification/order-arithmetic/generate-polynomial-certificates.rb.
The generator is not trusted: every theorem below must be checked by Lean.
These statements do not assert the exclusion of integer roots. -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000 in
theorem exceptional_pair03_d1_d1_first_coefficients :
    ∀ i ∈ Finset.range 3,
      (comparisonPolynomial (.linear 3 0) (.trialityD4 0) 4 1 1 1).coeff i =
        if i = 2 then (1 : ℤ) else 0 := by
  intro i hi
  have hi_bound : i < 3 := Finset.mem_range.mp hi
  rw [comparisonPolynomial_coeff _ _ 4 1 _ _ i (by decide) (by decide)]
  interval_cases i <;> norm_num
  all_goals
    norm_num [
      residualPolynomial, Finset.prod_Icc_succ_top, coeff_mul, coeff_one,
      Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000 in
theorem exceptional_pair03_d3_d1_first_coefficients :
    ∀ i ∈ Finset.range 1,
      (comparisonPolynomial (.linear 3 0) (.trialityD4 0) 4 1 3 1).coeff i =
        if i = 0 then (-2 : ℤ) else 0 := by
  intro i hi
  have hi_bound : i < 1 := Finset.mem_range.mp hi
  rw [comparisonPolynomial_coeff _ _ 4 1 _ _ i (by decide) (by decide)]
  interval_cases i <;> norm_num
  all_goals
    norm_num [
      residualPolynomial, Finset.prod_Icc_succ_top, coeff_mul, coeff_one,
      Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero]

end Atlas.OrderArithmetic
