import Atlas.LinearGroups.ReeF4.WeylStarData

/-! One bounded row of the concrete Weyl/star coefficient identity. -/
namespace Atlas.ReeF4
open Atlas.Albert
set_option maxRecDepth 8192 in
set_option maxHeartbeats 600000 in
theorem weylStarCheckRow026 : ∀ j : TraceZeroCoordinate,
    weylStarCoefficient (F := ZMod 2) 0 (.inr (2,6)) j =
      weylOperator 0 (extensionCoefficient (.inr (2,6)) j) +
        weylStarCorrection 0 (traceZeroCross (starMarkedVector (.inr (2,6))) (starMarkedVector j)) := by
  intro j
  fin_cases j <;> decide
end Atlas.ReeF4
