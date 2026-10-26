import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row10
import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row11
import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row12
import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row13
import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row14
import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row15
import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row16
import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row17

/-! One bounded part of the local coefficient check, using ordinary kernel reduction. -/
namespace Atlas.ReeF4
open Atlas.Albert
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- A small block of the 26-by-26 coefficient identity, not group enumeration.
theorem shortRootStarCheckBlock1 : ∀ i : Fin 8, ∀ j : TraceZeroCoordinate,
    shortRootStarCoefficient (F := ZMod 2) (.inr (1,i)) j =
      shortRootCoordinateLinear (extensionCoefficient (.inr (1,i)) j) +
        shortRootStarCorrection (traceZeroCross (starMarkedVector (.inr (1,i))) (starMarkedVector j)) +
        shortRootStarPolarCorrection (traceZeroPolar (starMarkedVector (.inr (1,i))) (starMarkedVector j)) := by
  intro i j
  fin_cases i
  · exact shortRootStarCheckRow10 j
  · exact shortRootStarCheckRow11 j
  · exact shortRootStarCheckRow12 j
  · exact shortRootStarCheckRow13 j
  · exact shortRootStarCheckRow14 j
  · exact shortRootStarCheckRow15 j
  · exact shortRootStarCheckRow16 j
  · exact shortRootStarCheckRow17 j
end Atlas.ReeF4
