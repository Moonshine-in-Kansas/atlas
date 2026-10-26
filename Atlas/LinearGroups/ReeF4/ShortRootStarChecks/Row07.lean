import Atlas.LinearGroups.ReeF4.ShortRootStarData

/-! One basis row of the local equivariance identity; separated to bound compiler memory. -/
namespace Atlas.ReeF4
open Atlas.Albert
set_option maxRecDepth 8192 in
set_option maxHeartbeats 600000 in
-- Twenty-six local coefficient equalities, checked by the kernel.
theorem shortRootStarCheckRow07 : ∀ j : TraceZeroCoordinate,
    shortRootStarCoefficient (F := ZMod 2) (.inr (0,7)) j =
      shortRootCoordinateLinear (extensionCoefficient (.inr (0,7)) j) +
        shortRootStarCorrection (traceZeroCross (starMarkedVector (.inr (0,7))) (starMarkedVector j)) +
        shortRootStarPolarCorrection (traceZeroPolar (starMarkedVector (.inr (0,7))) (starMarkedVector j)) := by
  intro j
  fin_cases j <;> decide
end Atlas.ReeF4
