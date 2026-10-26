import Atlas.OrderArithmetic.PolynomialCertificates.Pair39
import Atlas.OrderArithmetic.PolynomialPrefix
import Atlas.OrderArithmetic.PolynomialRowReversal
import Mathlib.Tactic.FinCases

namespace Atlas.OrderArithmetic
open Polynomial

/-! Generated finite integer-root exclusions for C(4,0) and F4(0).
All arithmetic is proved in Lean; the Ruby generator is not trusted. -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair39_d1_d1_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.C 4 0), (.F4 0), 1, 1⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.C 4 0), (.F4 0), 1, 1⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.C 4 0) (.F4 0) 3 2 1 1).eval (z : ℤ) = 0 at hroot
  exact (integer_eval_ne_zero_of_unit_prefix hz (by decide)
    exceptional_pair39_d1_d1_first_coefficients hroot).elim

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair39_d2_d1_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.C 4 0), (.F4 0), 2, 1⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.C 4 0), (.F4 0), 2, 1⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.C 4 0) (.F4 0) 3 2 2 1).eval (z : ℤ) = 0 at hroot
  exact (integer_eval_ne_zero_of_unit_prefix hz (by decide)
    exceptional_pair39_d2_d1_first_coefficients hroot).elim

end Atlas.OrderArithmetic
