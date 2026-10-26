import Atlas.LinearGroups.ReeF4.LongRootCoordinates
import Atlas.Algebra.Albert.TraceZeroFormIsometry

namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

private theorem four_zero : (4 : F) = 0 := by
  linear_combination 2 * (CharTwo.two_eq_zero (R := F))

private theorem eight_zero : (8 : F) = 0 := by
  linear_combination 4 * (CharTwo.two_eq_zero (R := F))

set_option maxHeartbeats 2000000 in
-- Expand the fixed Albert cubic and normalize its characteristic-two coefficients.
theorem longRootFormula_norm (w : Carrier F) : norm (longRootFormula w) = norm w := by
  simp [longRootFormula, Albert.norm, SplitOctonion.norm, SplitOctonion.trace,
    SplitOctonion.mul, sub_eq_add_neg, CharTwo.neg_eq]
  ring_nf <;> simp [CharTwo.two_eq_zero, four_zero, eight_zero]

set_option maxHeartbeats 800000 in
-- The quadratic trace is a fixed 27-coordinate polynomial.
theorem longRootFormula_quadratic (w : Carrier F) :
    quadraticTrace (longRootFormula w) = quadraticTrace w := by
  simp [longRootFormula, quadraticTrace, SplitOctonion.norm,
    sub_eq_add_neg, CharTwo.neg_eq]
  ring_nf <;> simp [CharTwo.two_eq_zero, four_zero, eight_zero]


end Atlas.ReeF4
