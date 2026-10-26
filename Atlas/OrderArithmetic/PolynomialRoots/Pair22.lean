import Atlas.OrderArithmetic.PolynomialCertificates.Pair22
import Atlas.OrderArithmetic.PolynomialPrefix
import Atlas.OrderArithmetic.PolynomialRowReversal
import Mathlib.Tactic.FinCases

namespace Atlas.OrderArithmetic
open Polynomial

/-! Generated finite integer-root exclusions for unitary(12,0) and E6(0).
All arithmetic is proved in Lean; the Ruby generator is not trusted. -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair22_d1_d1_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 12 0), (.E6 0), 1, 1⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 12 0), (.E6 0), 1, 1⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 1 1).eval (z : ℤ) = 0 at hroot
  exact (integer_eval_ne_zero_of_unit_prefix hz (by decide)
    exceptional_pair22_d1_d1_first_coefficients hroot).elim

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair22_d1_d3_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 12 0), (.E6 0), 1, 3⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 12 0), (.E6 0), 1, 3⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 1 3).eval (z : ℤ) = 0 at hroot
  have hd := integer_root_mem_prefix_divisors hz (by decide : (2 : ℤ) ≠ 0)
    exceptional_pair22_d1_d3_first_coefficients hroot
  have htable : (2 : ℤ).natAbs.divisors = ({1, 2} : Finset ℕ) := by decide +kernel
  rw [htable] at hd
  have hchoices : z ∈ ({2} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd ⊢
    omega
  fin_cases hchoices
  all_goals
    norm_num [comparisonPolynomial, residualPolynomial,
      eval_sub, eval_add, eval_mul, eval_C, eval_comp, eval_pow, eval_X,
      eval_one, eval_prod, Finset.prod_Icc_succ_top] at hroot

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair22_d2_d1_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 12 0), (.E6 0), 2, 1⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 12 0), (.E6 0), 2, 1⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 2 1).eval (z : ℤ) = 0 at hroot
  exact (integer_eval_ne_zero_of_unit_prefix hz (by decide)
    exceptional_pair22_d2_d1_first_coefficients hroot).elim

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair22_d2_d3_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 12 0), (.E6 0), 2, 3⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 12 0), (.E6 0), 2, 3⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 2 3).eval (z : ℤ) = 0 at hroot
  exact (integer_eval_ne_zero_of_unit_prefix hz (by decide)
    exceptional_pair22_d2_d3_first_coefficients hroot).elim

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair22_d3_d1_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 12 0), (.E6 0), 3, 1⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 12 0), (.E6 0), 3, 1⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 3 1).eval (z : ℤ) = 0 at hroot
  have hd := integer_root_mem_prefix_divisors hz (by decide : (-2 : ℤ) ≠ 0)
    exceptional_pair22_d3_d1_first_coefficients hroot
  have htable : (-2 : ℤ).natAbs.divisors = ({1, 2} : Finset ℕ) := by decide +kernel
  rw [htable] at hd
  have hchoices : z ∈ ({2} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd ⊢
    omega
  fin_cases hchoices
  all_goals
    norm_num [comparisonPolynomial, residualPolynomial,
      eval_sub, eval_add, eval_mul, eval_C, eval_comp, eval_pow, eval_X,
      eval_one, eval_prod, Finset.prod_Icc_succ_top] at hroot

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair22_d3_d3_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 12 0), (.E6 0), 3, 3⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 12 0), (.E6 0), 3, 3⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 3 3).eval (z : ℤ) = 0 at hroot
  have hd := integer_root_mem_prefix_divisors hz (by decide : (-3 : ℤ) ≠ 0)
    exceptional_pair22_d3_d3_first_coefficients hroot
  have htable : (-3 : ℤ).natAbs.divisors = ({1, 3} : Finset ℕ) := by decide +kernel
  rw [htable] at hd
  have hchoices : z ∈ ({3} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd ⊢
    omega
  fin_cases hchoices
  all_goals
    norm_num [comparisonPolynomial, residualPolynomial,
      eval_sub, eval_add, eval_mul, eval_C, eval_comp, eval_pow, eval_X,
      eval_one, eval_prod, Finset.prod_Icc_succ_top] at hroot

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair22_d4_d1_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 12 0), (.E6 0), 4, 1⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 12 0), (.E6 0), 4, 1⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 4 1).eval (z : ℤ) = 0 at hroot
  have hd := integer_root_mem_prefix_divisors hz (by decide : (-3 : ℤ) ≠ 0)
    exceptional_pair22_d4_d1_first_coefficients hroot
  have htable : (-3 : ℤ).natAbs.divisors = ({1, 3} : Finset ℕ) := by decide +kernel
  rw [htable] at hd
  have hchoices : z ∈ ({3} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd ⊢
    omega
  fin_cases hchoices
  all_goals
    norm_num [comparisonPolynomial, residualPolynomial,
      eval_sub, eval_add, eval_mul, eval_C, eval_comp, eval_pow, eval_X,
      eval_one, eval_prod, Finset.prod_Icc_succ_top] at hroot

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair22_d4_d3_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 12 0), (.E6 0), 4, 3⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 12 0), (.E6 0), 4, 3⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 4 3).eval (z : ℤ) = 0 at hroot
  exact (integer_eval_ne_zero_of_unit_prefix hz (by decide)
    exceptional_pair22_d4_d3_first_coefficients hroot).elim

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair22_d6_d1_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 12 0), (.E6 0), 6, 1⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 12 0), (.E6 0), 6, 1⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 6 1).eval (z : ℤ) = 0 at hroot
  have hd := integer_root_mem_prefix_divisors hz (by decide : (-5 : ℤ) ≠ 0)
    exceptional_pair22_d6_d1_first_coefficients hroot
  have htable : (-5 : ℤ).natAbs.divisors = ({1, 5} : Finset ℕ) := by decide +kernel
  rw [htable] at hd
  have hchoices : z ∈ ({5} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd ⊢
    omega
  fin_cases hchoices
  all_goals
    norm_num [comparisonPolynomial, residualPolynomial,
      eval_sub, eval_add, eval_mul, eval_C, eval_comp, eval_pow, eval_X,
      eval_one, eval_prod, Finset.prod_Icc_succ_top] at hroot

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair22_d6_d3_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 12 0), (.E6 0), 6, 3⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 12 0), (.E6 0), 6, 3⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 6 3).eval (z : ℤ) = 0 at hroot
  have hd := integer_root_mem_prefix_divisors hz (by decide : (-3 : ℤ) ≠ 0)
    exceptional_pair22_d6_d3_first_coefficients hroot
  have htable : (-3 : ℤ).natAbs.divisors = ({1, 3} : Finset ℕ) := by decide +kernel
  rw [htable] at hd
  have hchoices : z ∈ ({3} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd ⊢
    omega
  fin_cases hchoices
  all_goals
    norm_num [comparisonPolynomial, residualPolynomial,
      eval_sub, eval_add, eval_mul, eval_C, eval_comp, eval_pow, eval_X,
      eval_one, eval_prod, Finset.prod_Icc_succ_top] at hroot

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair22_d12_d1_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 12 0), (.E6 0), 12, 1⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 12 0), (.E6 0), 12, 1⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 12 1).eval (z : ℤ) = 0 at hroot
  have hd := integer_root_mem_prefix_divisors hz (by decide : (-11 : ℤ) ≠ 0)
    exceptional_pair22_d12_d1_first_coefficients hroot
  have htable : (-11 : ℤ).natAbs.divisors = ({1, 11} : Finset ℕ) := by decide +kernel
  rw [htable] at hd
  have hchoices : z ∈ ({11} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd ⊢
    omega
  fin_cases hchoices
  all_goals
    norm_num [comparisonPolynomial, residualPolynomial,
      eval_sub, eval_add, eval_mul, eval_C, eval_comp, eval_pow, eval_X,
      eval_one, eval_prod, Finset.prod_Icc_succ_top] at hroot

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair22_d12_d3_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 12 0), (.E6 0), 12, 3⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 12 0), (.E6 0), 12, 3⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 12 0) (.E6 0) 6 11 12 3).eval (z : ℤ) = 0 at hroot
  have hd := integer_root_mem_prefix_divisors hz (by decide : (-9 : ℤ) ≠ 0)
    exceptional_pair22_d12_d3_first_coefficients hroot
  have htable : (-9 : ℤ).natAbs.divisors = ({1, 3, 9} : Finset ℕ) := by decide +kernel
  rw [htable] at hd
  have hchoices : z ∈ ({3, 9} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd ⊢
    omega
  fin_cases hchoices
  all_goals
    norm_num [comparisonPolynomial, residualPolynomial,
      eval_sub, eval_add, eval_mul, eval_C, eval_comp, eval_pow, eval_X,
      eval_one, eval_prod, Finset.prod_Icc_succ_top] at hroot

end Atlas.OrderArithmetic
