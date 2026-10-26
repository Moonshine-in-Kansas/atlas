import Atlas.LinearGroups.ReeF4.ShortRootStarData

/-! One bounded part of the local coefficient check, using ordinary kernel reduction. -/
namespace Atlas.ReeF4
open Atlas.Albert
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- A small block of the 26-by-26 coefficient identity, not group enumeration.
theorem shortRootStarCheckDiagonal : ∀ i : Fin 2, ∀ j : TraceZeroCoordinate,
    shortRootStarCoefficient (F := ZMod 2) (.inl i) j =
      shortRootCoordinateLinear (extensionCoefficient (.inl i) j) +
        shortRootStarCorrection (traceZeroCross (starMarkedVector (.inl i)) (starMarkedVector j)) +
        shortRootStarPolarCorrection (traceZeroPolar (starMarkedVector (.inl i)) (starMarkedVector j)) := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide
end Atlas.ReeF4
