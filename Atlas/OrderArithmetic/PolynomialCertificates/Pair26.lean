import Atlas.OrderArithmetic.PolynomialSparseCoefficient
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Parity

namespace Atlas.OrderArithmetic
open Polynomial

/-! Generated coefficient-prefix proofs for unitary(16,0) versus E8(0).
Generator: verification/order-arithmetic/generate-polynomial-certificates.rb.
The generator is not trusted: every theorem below must be checked by Lean.
These statements do not assert the exclusion of integer roots. -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000 in
theorem exceptional_pair26_d1_d1_first_coefficients :
    ∀ i ∈ Finset.range 4,
      (comparisonPolynomial (.unitary 16 0) (.E8 0) 1 1 1 1).coeff i =
        if i = 3 then (1 : ℤ) else 0 := by
  intro i hi
  have hi_bound : i < 4 := Finset.mem_range.mp hi
  rw [comparisonPolynomial_coeff _ _ 1 1 _ _ i (by decide) (by decide)]
  interval_cases i <;> norm_num
  all_goals
    norm_num [
      residualPolynomial, Finset.prod_Icc_succ_top, coeff_one,
      coeff_mul_pow_sub_one, coeff_mul_pow_add_one,
      coeff_pow_sub_one_mul, coeff_pow_add_one_mul, coeff_sub, coeff_add, coeff_X_pow]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000 in
theorem exceptional_pair26_d2_d1_first_coefficients :
    ∀ i ∈ Finset.range 1,
      (comparisonPolynomial (.unitary 16 0) (.E8 0) 1 1 2 1).coeff i =
        if i = 0 then (-1 : ℤ) else 0 := by
  intro i hi
  have hi_bound : i < 1 := Finset.mem_range.mp hi
  rw [comparisonPolynomial_coeff _ _ 1 1 _ _ i (by decide) (by decide)]
  interval_cases i <;> norm_num
  all_goals
    norm_num [
      residualPolynomial, Finset.prod_Icc_succ_top, coeff_one,
      coeff_mul_pow_sub_one, coeff_mul_pow_add_one,
      coeff_pow_sub_one_mul, coeff_pow_add_one_mul, coeff_sub, coeff_add, coeff_X_pow]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000 in
theorem exceptional_pair26_d4_d1_first_coefficients :
    ∀ i ∈ Finset.range 1,
      (comparisonPolynomial (.unitary 16 0) (.E8 0) 1 1 4 1).coeff i =
        if i = 0 then (-3 : ℤ) else 0 := by
  intro i hi
  have hi_bound : i < 1 := Finset.mem_range.mp hi
  rw [comparisonPolynomial_coeff _ _ 1 1 _ _ i (by decide) (by decide)]
  interval_cases i <;> norm_num
  all_goals
    norm_num [
      residualPolynomial, Finset.prod_Icc_succ_top, coeff_one,
      coeff_mul_pow_sub_one, coeff_mul_pow_add_one,
      coeff_pow_sub_one_mul, coeff_pow_add_one_mul, coeff_sub, coeff_add, coeff_X_pow]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000 in
theorem exceptional_pair26_d8_d1_first_coefficients :
    ∀ i ∈ Finset.range 1,
      (comparisonPolynomial (.unitary 16 0) (.E8 0) 1 1 8 1).coeff i =
        if i = 0 then (-7 : ℤ) else 0 := by
  intro i hi
  have hi_bound : i < 1 := Finset.mem_range.mp hi
  rw [comparisonPolynomial_coeff _ _ 1 1 _ _ i (by decide) (by decide)]
  interval_cases i <;> norm_num
  all_goals
    norm_num [
      residualPolynomial, Finset.prod_Icc_succ_top, coeff_one,
      coeff_mul_pow_sub_one, coeff_mul_pow_add_one,
      coeff_pow_sub_one_mul, coeff_pow_add_one_mul, coeff_sub, coeff_add, coeff_X_pow]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000 in
theorem exceptional_pair26_d16_d1_first_coefficients :
    ∀ i ∈ Finset.range 1,
      (comparisonPolynomial (.unitary 16 0) (.E8 0) 1 1 16 1).coeff i =
        if i = 0 then (-15 : ℤ) else 0 := by
  intro i hi
  have hi_bound : i < 1 := Finset.mem_range.mp hi
  rw [comparisonPolynomial_coeff _ _ 1 1 _ _ i (by decide) (by decide)]
  interval_cases i <;> norm_num
  all_goals
    norm_num [
      residualPolynomial, Finset.prod_Icc_succ_top, coeff_one,
      coeff_mul_pow_sub_one, coeff_mul_pow_add_one,
      coeff_pow_sub_one_mul, coeff_pow_add_one_mul, coeff_sub, coeff_add, coeff_X_pow]

end Atlas.OrderArithmetic
