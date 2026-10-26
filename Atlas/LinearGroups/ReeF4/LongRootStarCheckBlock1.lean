import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row10
import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row11
import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row12
import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row13
import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row14
import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row15
import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row16
import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row17

/-! One bounded part of the local coefficient check, using ordinary kernel reduction. -/
namespace Atlas.ReeF4
open Atlas.Albert
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- A small block of the 26-by-26 coefficient identity, not group enumeration.
theorem longRootStarCheckBlock1 : ∀ i : Fin 8, ∀ j : TraceZeroCoordinate,
    longRootStarCoefficient (F := ZMod 2) (.inr (1,i)) j =
      longRootCoordinateLinear (extensionCoefficient (.inr (1,i)) j) +
        longRootStarCorrection (traceZeroCross (starMarkedVector (.inr (1,i))) (starMarkedVector j)) := by
  intro i j
  fin_cases i
  · exact longRootStarCheckRow10 j
  · exact longRootStarCheckRow11 j
  · exact longRootStarCheckRow12 j
  · exact longRootStarCheckRow13 j
  · exact longRootStarCheckRow14 j
  · exact longRootStarCheckRow15 j
  · exact longRootStarCheckRow16 j
  · exact longRootStarCheckRow17 j
end Atlas.ReeF4
