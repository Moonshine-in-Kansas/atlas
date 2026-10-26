import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row00
import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row01
import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row02
import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row03
import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row04
import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row05
import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row06
import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row07

/-! One bounded part of the local coefficient check, using ordinary kernel reduction. -/
namespace Atlas.ReeF4
open Atlas.Albert
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- A small block of the 26-by-26 coefficient identity, not group enumeration.
theorem longRootStarCheckBlock0 : ∀ i : Fin 8, ∀ j : TraceZeroCoordinate,
    longRootStarCoefficient (F := ZMod 2) (.inr (0,i)) j =
      longRootCoordinateLinear (extensionCoefficient (.inr (0,i)) j) +
        longRootStarCorrection (traceZeroCross (starMarkedVector (.inr (0,i))) (starMarkedVector j)) := by
  intro i j
  fin_cases i
  · exact longRootStarCheckRow00 j
  · exact longRootStarCheckRow01 j
  · exact longRootStarCheckRow02 j
  · exact longRootStarCheckRow03 j
  · exact longRootStarCheckRow04 j
  · exact longRootStarCheckRow05 j
  · exact longRootStarCheckRow06 j
  · exact longRootStarCheckRow07 j
end Atlas.ReeF4
