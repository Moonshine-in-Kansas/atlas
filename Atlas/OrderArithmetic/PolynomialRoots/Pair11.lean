import Atlas.OrderArithmetic.PolynomialCertificates.Pair11
import Atlas.OrderArithmetic.PolynomialPrefix
import Atlas.OrderArithmetic.PolynomialRowReversal
import Mathlib.Tactic.FinCases

namespace Atlas.OrderArithmetic
open Polynomial

/-! Generated finite integer-root exclusions for unitary(3,0) and smallRee(0).
All arithmetic is proved in Lean; the Ruby generator is not trusted. -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair11_d1_d1_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 3 0), (.smallRee 0), 1, 1⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 3 0), (.smallRee 0), 1, 1⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 3 0) (.smallRee 0) 1 1 1 1).eval (z : ℤ) = 0 at hroot
  exact (integer_eval_ne_zero_of_unit_prefix hz (by decide)
    exceptional_pair11_d1_d1_first_coefficients hroot).elim

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair11_d3_d1_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 3 0), (.smallRee 0), 3, 1⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 3 0), (.smallRee 0), 3, 1⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.unitary 3 0) (.smallRee 0) 1 1 3 1).eval (z : ℤ) = 0 at hroot
  have hd := integer_root_mem_prefix_divisors hz (by decide : (2 : ℤ) ≠ 0)
    exceptional_pair11_d3_d1_first_coefficients hroot
  have htable : (2 : ℤ).natAbs.divisors = ({1, 2} : Finset ℕ) := by decide +kernel
  rw [htable] at hd
  have hchoices : z ∈ ({2} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd ⊢
    omega
  have hz2 : z = 2 := by simpa only [Finset.mem_singleton] using hchoices
  exact ⟨rfl, hz2⟩

end Atlas.OrderArithmetic
