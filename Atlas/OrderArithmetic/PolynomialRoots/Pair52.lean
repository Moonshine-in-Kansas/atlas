import Atlas.OrderArithmetic.PolynomialCertificates.Pair52
import Atlas.OrderArithmetic.PolynomialPrefix
import Atlas.OrderArithmetic.PolynomialRowReversal
import Mathlib.Tactic.FinCases

namespace Atlas.OrderArithmetic
open Polynomial

/-! Generated finite integer-root exclusions for Dminus(8,0) and E7(0).
All arithmetic is proved in Lean; the Ruby generator is not trusted. -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair52_d1_d1_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.Dminus 8 0), (.E7 0), 1, 1⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.Dminus 8 0), (.E7 0), 1, 1⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.Dminus 8 0) (.E7 0) 9 8 1 1).eval (z : ℤ) = 0 at hroot
  exact (integer_eval_ne_zero_of_unit_prefix hz (by decide)
    exceptional_pair52_d1_d1_first_coefficients hroot).elim

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair52_d1_d2_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.Dminus 8 0), (.E7 0), 1, 2⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.Dminus 8 0), (.E7 0), 1, 2⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.Dminus 8 0) (.E7 0) 9 8 1 2).eval (z : ℤ) = 0 at hroot
  exact (integer_eval_ne_zero_of_unit_prefix hz (by decide)
    exceptional_pair52_d1_d2_first_coefficients hroot).elim

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair52_d2_d1_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.Dminus 8 0), (.E7 0), 2, 1⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.Dminus 8 0), (.E7 0), 2, 1⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.Dminus 8 0) (.E7 0) 9 8 2 1).eval (z : ℤ) = 0 at hroot
  exact (integer_eval_ne_zero_of_unit_prefix hz (by decide)
    exceptional_pair52_d2_d1_first_coefficients hroot).elim

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair52_d2_d2_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.Dminus 8 0), (.E7 0), 2, 2⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.Dminus 8 0), (.E7 0), 2, 2⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.Dminus 8 0) (.E7 0) 9 8 2 2).eval (z : ℤ) = 0 at hroot
  have hd := integer_root_mem_prefix_divisors hz (by decide : (-2 : ℤ) ≠ 0)
    exceptional_pair52_d2_d2_first_coefficients hroot
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
theorem exceptional_pair52_d4_d1_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.Dminus 8 0), (.E7 0), 4, 1⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.Dminus 8 0), (.E7 0), 4, 1⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.Dminus 8 0) (.E7 0) 9 8 4 1).eval (z : ℤ) = 0 at hroot
  have hd := integer_root_mem_prefix_divisors hz (by decide : (3 : ℤ) ≠ 0)
    exceptional_pair52_d4_d1_first_coefficients hroot
  have htable : (3 : ℤ).natAbs.divisors = ({1, 3} : Finset ℕ) := by decide +kernel
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
theorem exceptional_pair52_d4_d2_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.Dminus 8 0), (.E7 0), 4, 2⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.Dminus 8 0), (.E7 0), 4, 2⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.Dminus 8 0) (.E7 0) 9 8 4 2).eval (z : ℤ) = 0 at hroot
  have hd := integer_root_mem_prefix_divisors hz (by decide : (2 : ℤ) ≠ 0)
    exceptional_pair52_d4_d2_first_coefficients hroot
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

end Atlas.OrderArithmetic
