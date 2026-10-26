import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row20
import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row21
import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row22
import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row23
import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row24
import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row25
import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row26
import Atlas.LinearGroups.ReeF4.LongRootStarChecks.Row27

/-! One bounded part of the local coefficient check, using ordinary kernel reduction. -/
namespace Atlas.ReeF4
open Atlas.Albert
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- A small block of the 26-by-26 coefficient identity, not group enumeration.
theorem longRootStarCheckBlock2 : ∀ i : Fin 8, ∀ j : TraceZeroCoordinate,
    longRootStarCoefficient (F := ZMod 2) (.inr (2,i)) j =
      longRootCoordinateLinear (extensionCoefficient (.inr (2,i)) j) +
        longRootStarCorrection (traceZeroCross (starMarkedVector (.inr (2,i))) (starMarkedVector j)) := by
  intro i j
  fin_cases i
  · exact longRootStarCheckRow20 j
  · exact longRootStarCheckRow21 j
  · exact longRootStarCheckRow22 j
  · exact longRootStarCheckRow23 j
  · exact longRootStarCheckRow24 j
  · exact longRootStarCheckRow25 j
  · exact longRootStarCheckRow26 j
  · exact longRootStarCheckRow27 j
end Atlas.ReeF4
