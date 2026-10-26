import Atlas.LinearGroups.ReeF4.LongRootStarData

/-! One basis row of the local equivariance identity; separated to bound compiler memory. -/
namespace Atlas.ReeF4
open Atlas.Albert
set_option maxRecDepth 8192 in
set_option maxHeartbeats 600000 in
-- Twenty-six local coefficient equalities, checked by the kernel.
theorem longRootStarCheckRow26 : ∀ j : TraceZeroCoordinate,
    longRootStarCoefficient (F := ZMod 2) (.inr (2,6)) j =
      longRootCoordinateLinear (extensionCoefficient (.inr (2,6)) j) +
        longRootStarCorrection (traceZeroCross (starMarkedVector (.inr (2,6))) (starMarkedVector j)) := by
  intro j
  fin_cases j <;> decide
end Atlas.ReeF4
