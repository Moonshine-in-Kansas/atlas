import Atlas.OrderArithmetic.PolynomialCoefficient
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Parity

namespace Atlas.OrderArithmetic
open Polynomial

/-! Generated coefficient-prefix proofs for unitary(12,0) versus E6(0).
Generator: verification/order-arithmetic/generate-polynomial-certificates.rb.
The generator is not trusted: every theorem below must be checked by Lean.
These statements do not assert the exclusion of integer roots. -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000 in
theorem exceptional_pair22_d1_d1_first_coefficients :
    ∀ i ∈ Finset.range 13,
      (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 1 1).coeff i =
        if i = 12 then (-1 : ℤ) else 0 := by
  intro i hi
  have hi_bound : i < 13 := Finset.mem_range.mp hi
  rw [comparisonPolynomial_coeff _ _ 6 11 _ _ i (by decide) (by decide)]
  interval_cases i <;> norm_num
  all_goals
    norm_num [
      residualPolynomial, Finset.prod_Icc_succ_top, coeff_mul, coeff_one,
      Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000 in
theorem exceptional_pair22_d1_d3_first_coefficients :
    ∀ i ∈ Finset.range 1,
      (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 1 3).coeff i =
        if i = 0 then (2 : ℤ) else 0 := by
  intro i hi
  have hi_bound : i < 1 := Finset.mem_range.mp hi
  rw [comparisonPolynomial_coeff _ _ 6 11 _ _ i (by decide) (by decide)]
  interval_cases i <;> norm_num
  all_goals
    norm_num [
      residualPolynomial, Finset.prod_Icc_succ_top, coeff_mul, coeff_one,
      Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000 in
theorem exceptional_pair22_d2_d1_first_coefficients :
    ∀ i ∈ Finset.range 1,
      (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 2 1).coeff i =
        if i = 0 then (-1 : ℤ) else 0 := by
  intro i hi
  have hi_bound : i < 1 := Finset.mem_range.mp hi
  rw [comparisonPolynomial_coeff _ _ 6 11 _ _ i (by decide) (by decide)]
  interval_cases i <;> norm_num
  all_goals
    norm_num [
      residualPolynomial, Finset.prod_Icc_succ_top, coeff_mul, coeff_one,
      Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000 in
theorem exceptional_pair22_d2_d3_first_coefficients :
    ∀ i ∈ Finset.range 1,
      (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 2 3).coeff i =
        if i = 0 then (1 : ℤ) else 0 := by
  intro i hi
  have hi_bound : i < 1 := Finset.mem_range.mp hi
  rw [comparisonPolynomial_coeff _ _ 6 11 _ _ i (by decide) (by decide)]
  interval_cases i <;> norm_num
  all_goals
    norm_num [
      residualPolynomial, Finset.prod_Icc_succ_top, coeff_mul, coeff_one,
      Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000 in
theorem exceptional_pair22_d3_d1_first_coefficients :
    ∀ i ∈ Finset.range 1,
      (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 3 1).coeff i =
        if i = 0 then (-2 : ℤ) else 0 := by
  intro i hi
  have hi_bound : i < 1 := Finset.mem_range.mp hi
  rw [comparisonPolynomial_coeff _ _ 6 11 _ _ i (by decide) (by decide)]
  interval_cases i <;> norm_num
  all_goals
    norm_num [
      residualPolynomial, Finset.prod_Icc_succ_top, coeff_mul, coeff_one,
      Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000 in
theorem exceptional_pair22_d3_d3_first_coefficients :
    ∀ i ∈ Finset.range 13,
      (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 3 3).coeff i =
        if i = 12 then (-3 : ℤ) else 0 := by
  intro i hi
  have hi_bound : i < 13 := Finset.mem_range.mp hi
  rw [comparisonPolynomial_coeff _ _ 6 11 _ _ i (by decide) (by decide)]
  interval_cases i <;> norm_num
  all_goals
    norm_num [
      residualPolynomial, Finset.prod_Icc_succ_top, coeff_mul, coeff_one,
      Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000 in
theorem exceptional_pair22_d4_d1_first_coefficients :
    ∀ i ∈ Finset.range 1,
      (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 4 1).coeff i =
        if i = 0 then (-3 : ℤ) else 0 := by
  intro i hi
  have hi_bound : i < 1 := Finset.mem_range.mp hi
  rw [comparisonPolynomial_coeff _ _ 6 11 _ _ i (by decide) (by decide)]
  interval_cases i <;> norm_num
  all_goals
    norm_num [
      residualPolynomial, Finset.prod_Icc_succ_top, coeff_mul, coeff_one,
      Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000 in
theorem exceptional_pair22_d4_d3_first_coefficients :
    ∀ i ∈ Finset.range 1,
      (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 4 3).coeff i =
        if i = 0 then (-1 : ℤ) else 0 := by
  intro i hi
  have hi_bound : i < 1 := Finset.mem_range.mp hi
  rw [comparisonPolynomial_coeff _ _ 6 11 _ _ i (by decide) (by decide)]
  interval_cases i <;> norm_num
  all_goals
    norm_num [
      residualPolynomial, Finset.prod_Icc_succ_top, coeff_mul, coeff_one,
      Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000 in
theorem exceptional_pair22_d6_d1_first_coefficients :
    ∀ i ∈ Finset.range 1,
      (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 6 1).coeff i =
        if i = 0 then (-5 : ℤ) else 0 := by
  intro i hi
  have hi_bound : i < 1 := Finset.mem_range.mp hi
  rw [comparisonPolynomial_coeff _ _ 6 11 _ _ i (by decide) (by decide)]
  interval_cases i <;> norm_num
  all_goals
    norm_num [
      residualPolynomial, Finset.prod_Icc_succ_top, coeff_mul, coeff_one,
      Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000 in
theorem exceptional_pair22_d6_d3_first_coefficients :
    ∀ i ∈ Finset.range 1,
      (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 6 3).coeff i =
        if i = 0 then (-3 : ℤ) else 0 := by
  intro i hi
  have hi_bound : i < 1 := Finset.mem_range.mp hi
  rw [comparisonPolynomial_coeff _ _ 6 11 _ _ i (by decide) (by decide)]
  interval_cases i <;> norm_num
  all_goals
    norm_num [
      residualPolynomial, Finset.prod_Icc_succ_top, coeff_mul, coeff_one,
      Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000 in
theorem exceptional_pair22_d12_d1_first_coefficients :
    ∀ i ∈ Finset.range 1,
      (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 12 1).coeff i =
        if i = 0 then (-11 : ℤ) else 0 := by
  intro i hi
  have hi_bound : i < 1 := Finset.mem_range.mp hi
  rw [comparisonPolynomial_coeff _ _ 6 11 _ _ i (by decide) (by decide)]
  interval_cases i <;> norm_num
  all_goals
    norm_num [
      residualPolynomial, Finset.prod_Icc_succ_top, coeff_mul, coeff_one,
      Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000 in
theorem exceptional_pair22_d12_d3_first_coefficients :
    ∀ i ∈ Finset.range 1,
      (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 12 3).coeff i =
        if i = 0 then (-9 : ℤ) else 0 := by
  intro i hi
  have hi_bound : i < 1 := Finset.mem_range.mp hi
  rw [comparisonPolynomial_coeff _ _ 6 11 _ _ i (by decide) (by decide)]
  interval_cases i <;> norm_num
  all_goals
    norm_num [
      residualPolynomial, Finset.prod_Icc_succ_top, coeff_mul, coeff_one,
      Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero]

end Atlas.OrderArithmetic
