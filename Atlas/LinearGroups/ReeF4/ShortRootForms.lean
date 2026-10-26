import Atlas.LinearGroups.ReeF4.ShortRootCoordinates
import Atlas.Algebra.Albert.TraceZeroFormIsometry

namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

private theorem four_zero : (4 : F) = 0 := by
  linear_combination 2 * (CharTwo.two_eq_zero (R := F))

private theorem six_zero : (6 : F) = 0 := by
  linear_combination 3 * (CharTwo.two_eq_zero (R := F))

private theorem eight_zero : (8 : F) = 0 := by
  linear_combination 4 * (CharTwo.two_eq_zero (R := F))

set_option maxHeartbeats 2000000 in
-- Expand the fixed Albert cubic and normalize its characteristic-two coefficients.
theorem shortRootFormula_norm (w : Carrier F) : norm (shortRootFormula w) = norm w := by
  simp [shortRootFormula, Albert.norm, SplitOctonion.norm, SplitOctonion.trace,
    SplitOctonion.mul, sub_eq_add_neg, CharTwo.neg_eq]
  ring_nf <;> simp [CharTwo.two_eq_zero, four_zero, six_zero, eight_zero]

set_option maxHeartbeats 800000 in
-- The quadratic trace is a fixed 27-coordinate polynomial.
theorem shortRootFormula_quadratic (w : Carrier F) :
    quadraticTrace (shortRootFormula w) = quadraticTrace w := by
  simp [shortRootFormula, quadraticTrace, SplitOctonion.norm,
    sub_eq_add_neg, CharTwo.neg_eq]
  ring_nf <;> simp [CharTwo.two_eq_zero, four_zero, six_zero, eight_zero]


end Atlas.ReeF4
