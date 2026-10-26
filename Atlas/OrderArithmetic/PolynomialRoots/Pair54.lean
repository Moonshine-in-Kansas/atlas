import Atlas.OrderArithmetic.PolynomialCertificates.Pair54
import Atlas.OrderArithmetic.PolynomialPrefix
import Atlas.OrderArithmetic.PolynomialRowReversal
import Mathlib.Tactic.FinCases

namespace Atlas.OrderArithmetic
open Polynomial

/-! Generated finite integer-root exclusions for G2(0) and trialityD4(0).
All arithmetic is proved in Lean; the Ruby generator is not trusted. -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem exceptional_pair54_d1_d1_root {z : ℕ} (hz : 2 ≤ z)
    (hroot : (⟨(.G2 0), (.trialityD4 0), 1, 1⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.G2 0), (.trialityD4 0), 1, 1⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  change (comparisonPolynomial (.G2 0) (.trialityD4 0) 2 1 1 1).eval (z : ℤ) = 0 at hroot
  exact (integer_eval_ne_zero_of_unit_prefix hz (by decide)
    exceptional_pair54_d1_d1_first_coefficients hroot).elim

end Atlas.OrderArithmetic
