import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row00
import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row01
import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row02
import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row03
import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row04
import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row05
import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row06
import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row07

/-! One bounded part of the local coefficient check, using ordinary kernel reduction. -/
namespace Atlas.ReeF4
open Atlas.Albert
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- A small block of the 26-by-26 coefficient identity, not group enumeration.
theorem shortRootStarCheckBlock0 : ∀ i : Fin 8, ∀ j : TraceZeroCoordinate,
    shortRootStarCoefficient (F := ZMod 2) (.inr (0,i)) j =
      shortRootCoordinateLinear (extensionCoefficient (.inr (0,i)) j) +
        shortRootStarCorrection (traceZeroCross (starMarkedVector (.inr (0,i))) (starMarkedVector j)) +
        shortRootStarPolarCorrection (traceZeroPolar (starMarkedVector (.inr (0,i))) (starMarkedVector j)) := by
  intro i j
  fin_cases i
  · exact shortRootStarCheckRow00 j
  · exact shortRootStarCheckRow01 j
  · exact shortRootStarCheckRow02 j
  · exact shortRootStarCheckRow03 j
  · exact shortRootStarCheckRow04 j
  · exact shortRootStarCheckRow05 j
  · exact shortRootStarCheckRow06 j
  · exact shortRootStarCheckRow07 j
end Atlas.ReeF4
