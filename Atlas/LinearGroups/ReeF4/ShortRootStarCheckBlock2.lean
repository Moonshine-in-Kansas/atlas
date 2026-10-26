import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row20
import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row21
import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row22
import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row23
import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row24
import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row25
import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row26
import Atlas.LinearGroups.ReeF4.ShortRootStarChecks.Row27

/-! One bounded part of the local coefficient check, using ordinary kernel reduction. -/
namespace Atlas.ReeF4
open Atlas.Albert
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- A small block of the 26-by-26 coefficient identity, not group enumeration.
theorem shortRootStarCheckBlock2 : ∀ i : Fin 8, ∀ j : TraceZeroCoordinate,
    shortRootStarCoefficient (F := ZMod 2) (.inr (2,i)) j =
      shortRootCoordinateLinear (extensionCoefficient (.inr (2,i)) j) +
        shortRootStarCorrection (traceZeroCross (starMarkedVector (.inr (2,i))) (starMarkedVector j)) +
        shortRootStarPolarCorrection (traceZeroPolar (starMarkedVector (.inr (2,i))) (starMarkedVector j)) := by
  intro i j
  fin_cases i
  · exact shortRootStarCheckRow20 j
  · exact shortRootStarCheckRow21 j
  · exact shortRootStarCheckRow22 j
  · exact shortRootStarCheckRow23 j
  · exact shortRootStarCheckRow24 j
  · exact shortRootStarCheckRow25 j
  · exact shortRootStarCheckRow26 j
  · exact shortRootStarCheckRow27 j
end Atlas.ReeF4
