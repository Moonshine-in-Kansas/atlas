import Atlas.OrderArithmetic.PolynomialCertificates.Pair25
import Atlas.OrderArithmetic.PolynomialPrefix
import Atlas.OrderArithmetic.PolynomialRowReversal
import Mathlib.Tactic.FinCases

namespace Atlas.OrderArithmetic
open Polynomial

/-! Generated finite integer-root exclusions for unitary(15,0) and E7(0).
All arithmetic is proved in Lean; the Ruby generator is not trusted. -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair25_d1_d1_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 15 0), (.E7 0), 1, 1⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 15 0), (.E7 0), 1, 1⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 15 0) (.E7 0) 3 5 1 1).eval (z : ℤ) = 0 at hroot
  exact (integer_eval_ne_zero_of_unit_prefix hz (by decide)
    exceptional_pair25_d1_d1_first_coefficients hroot).elim

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair25_d1_d2_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 15 0), (.E7 0), 1, 2⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 15 0), (.E7 0), 1, 2⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 15 0) (.E7 0) 3 5 1 2).eval (z : ℤ) = 0 at hroot
  exact (integer_eval_ne_zero_of_unit_prefix hz (by decide)
    exceptional_pair25_d1_d2_first_coefficients hroot).elim

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair25_d3_d1_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 15 0), (.E7 0), 3, 1⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 15 0), (.E7 0), 3, 1⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 15 0) (.E7 0) 3 5 3 1).eval (z : ℤ) = 0 at hroot
  have hd := integer_root_mem_prefix_divisors hz (by decide : (2 : ℤ) ≠ 0)
    exceptional_pair25_d3_d1_first_coefficients hroot
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
theorem exceptional_pair25_d3_d2_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 15 0), (.E7 0), 3, 2⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 15 0), (.E7 0), 3, 2⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 15 0) (.E7 0) 3 5 3 2).eval (z : ℤ) = 0 at hroot
  exact (integer_eval_ne_zero_of_unit_prefix hz (by decide)
    exceptional_pair25_d3_d2_first_coefficients hroot).elim

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair25_d5_d1_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 15 0), (.E7 0), 5, 1⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 15 0), (.E7 0), 5, 1⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 15 0) (.E7 0) 3 5 5 1).eval (z : ℤ) = 0 at hroot
  have hd := integer_root_mem_prefix_divisors hz (by decide : (4 : ℤ) ≠ 0)
    exceptional_pair25_d5_d1_first_coefficients hroot
  have htable : (4 : ℤ).natAbs.divisors = ({1, 2, 4} : Finset ℕ) := by decide +kernel
  rw [htable] at hd
  have hchoices : z ∈ ({2, 4} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd ⊢
    omega
  fin_cases hchoices
  all_goals
    norm_num [comparisonPolynomial, residualPolynomial,
      eval_sub, eval_add, eval_mul, eval_C, eval_comp, eval_pow, eval_X,
      eval_one, eval_prod, Finset.prod_Icc_succ_top] at hroot

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair25_d5_d2_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 15 0), (.E7 0), 5, 2⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 15 0), (.E7 0), 5, 2⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 15 0) (.E7 0) 3 5 5 2).eval (z : ℤ) = 0 at hroot
  have hd := integer_root_mem_prefix_divisors hz (by decide : (3 : ℤ) ≠ 0)
    exceptional_pair25_d5_d2_first_coefficients hroot
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
theorem exceptional_pair25_d15_d1_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 15 0), (.E7 0), 15, 1⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 15 0), (.E7 0), 15, 1⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 15 0) (.E7 0) 3 5 15 1).eval (z : ℤ) = 0 at hroot
  have hd := integer_root_mem_prefix_divisors hz (by decide : (14 : ℤ) ≠ 0)
    exceptional_pair25_d15_d1_first_coefficients hroot
  have htable : (14 : ℤ).natAbs.divisors = ({1, 2, 7, 14} : Finset ℕ) := by decide +kernel
  rw [htable] at hd
  have hchoices : z ∈ ({2, 7, 14} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd ⊢
    omega
  fin_cases hchoices
  all_goals
    norm_num [comparisonPolynomial, residualPolynomial,
      eval_sub, eval_add, eval_mul, eval_C, eval_comp, eval_pow, eval_X,
      eval_one, eval_prod, Finset.prod_Icc_succ_top] at hroot

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair25_d15_d2_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 15 0), (.E7 0), 15, 2⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 15 0), (.E7 0), 15, 2⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 15 0) (.E7 0) 3 5 15 2).eval (z : ℤ) = 0 at hroot
  have hd := integer_root_mem_prefix_divisors hz (by decide : (13 : ℤ) ≠ 0)
    exceptional_pair25_d15_d2_first_coefficients hroot
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

end Atlas.OrderArithmetic
