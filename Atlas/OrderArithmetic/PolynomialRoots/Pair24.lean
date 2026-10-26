import Atlas.OrderArithmetic.PolynomialCertificates.Pair24
import Atlas.OrderArithmetic.PolynomialPrefix
import Atlas.OrderArithmetic.PolynomialRowReversal
import Mathlib.Tactic.FinCases

namespace Atlas.OrderArithmetic
open Polynomial

/-! Generated finite integer-root exclusions for unitary(14,0) and E7(0).
All arithmetic is proved in Lean; the Ruby generator is not trusted. -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair24_d1_d1_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 14 0), (.E7 0), 1, 1⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 14 0), (.E7 0), 1, 1⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 14 0) (.E7 0) 9 13 1 1).eval (z : ℤ) = 0 at hroot
  exact (integer_eval_ne_zero_of_unit_prefix hz (by decide)
    exceptional_pair24_d1_d1_first_coefficients hroot).elim

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair24_d1_d2_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 14 0), (.E7 0), 1, 2⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 14 0), (.E7 0), 1, 2⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 14 0) (.E7 0) 9 13 1 2).eval (z : ℤ) = 0 at hroot
  exact (integer_eval_ne_zero_of_unit_prefix hz (by decide)
    exceptional_pair24_d1_d2_first_coefficients hroot).elim

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair24_d2_d1_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 14 0), (.E7 0), 2, 1⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 14 0), (.E7 0), 2, 1⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 14 0) (.E7 0) 9 13 2 1).eval (z : ℤ) = 0 at hroot
  exact (integer_eval_ne_zero_of_unit_prefix hz (by decide)
    exceptional_pair24_d2_d1_first_coefficients hroot).elim

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair24_d2_d2_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 14 0), (.E7 0), 2, 2⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 14 0), (.E7 0), 2, 2⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 14 0) (.E7 0) 9 13 2 2).eval (z : ℤ) = 0 at hroot
  have hd := integer_root_mem_prefix_divisors hz (by decide : (2 : ℤ) ≠ 0)
    exceptional_pair24_d2_d2_first_coefficients hroot
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
theorem exceptional_pair24_d7_d1_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 14 0), (.E7 0), 7, 1⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 14 0), (.E7 0), 7, 1⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 14 0) (.E7 0) 9 13 7 1).eval (z : ℤ) = 0 at hroot
  have hd := integer_root_mem_prefix_divisors hz (by decide : (6 : ℤ) ≠ 0)
    exceptional_pair24_d7_d1_first_coefficients hroot
  have htable : (6 : ℤ).natAbs.divisors = ({1, 2, 3, 6} : Finset ℕ) := by decide +kernel
  rw [htable] at hd
  have hchoices : z ∈ ({2, 3, 6} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd ⊢
    omega
  fin_cases hchoices
  all_goals
    norm_num [comparisonPolynomial, residualPolynomial,
      eval_sub, eval_add, eval_mul, eval_C, eval_comp, eval_pow, eval_X,
      eval_one, eval_prod, Finset.prod_Icc_succ_top] at hroot

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair24_d7_d2_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 14 0), (.E7 0), 7, 2⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 14 0), (.E7 0), 7, 2⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 14 0) (.E7 0) 9 13 7 2).eval (z : ℤ) = 0 at hroot
  have hd := integer_root_mem_prefix_divisors hz (by decide : (5 : ℤ) ≠ 0)
    exceptional_pair24_d7_d2_first_coefficients hroot
  have htable : (5 : ℤ).natAbs.divisors = ({1, 5} : Finset ℕ) := by decide +kernel
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
theorem exceptional_pair24_d14_d1_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 14 0), (.E7 0), 14, 1⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 14 0), (.E7 0), 14, 1⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 14 0) (.E7 0) 9 13 14 1).eval (z : ℤ) = 0 at hroot
  have hd := integer_root_mem_prefix_divisors hz (by decide : (13 : ℤ) ≠ 0)
    exceptional_pair24_d14_d1_first_coefficients hroot
  have htable : (13 : ℤ).natAbs.divisors = ({1, 13} : Finset ℕ) := by decide +kernel
  rw [htable] at hd
  have hchoices : z ∈ ({13} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd ⊢
    omega
  fin_cases hchoices
  all_goals
    norm_num [comparisonPolynomial, residualPolynomial,
      eval_sub, eval_add, eval_mul, eval_C, eval_comp, eval_pow, eval_X,
      eval_one, eval_prod, Finset.prod_Icc_succ_top] at hroot

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair24_d14_d2_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 14 0), (.E7 0), 14, 2⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 14 0), (.E7 0), 14, 2⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 14 0) (.E7 0) 9 13 14 2).eval (z : ℤ) = 0 at hroot
  have hd := integer_root_mem_prefix_divisors hz (by decide : (12 : ℤ) ≠ 0)
    exceptional_pair24_d14_d2_first_coefficients hroot
  have htable : (12 : ℤ).natAbs.divisors = ({1, 2, 3, 4, 6, 12} : Finset ℕ) := by decide +kernel
  rw [htable] at hd
  have hchoices : z ∈ ({2, 3, 4, 6, 12} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd ⊢
    omega
  fin_cases hchoices
  all_goals
    norm_num [comparisonPolynomial, residualPolynomial,
      eval_sub, eval_add, eval_mul, eval_C, eval_comp, eval_pow, eval_X,
      eval_one, eval_prod, Finset.prod_Icc_succ_top] at hroot

end Atlas.OrderArithmetic
