import Atlas.LinearGroups.ReeF4.WeylStarData

/-! One bounded row of the concrete Weyl/star coefficient identity. -/
namespace Atlas.ReeF4
open Atlas.Albert
set_option maxRecDepth 8192 in
set_option maxHeartbeats 600000 in
theorem weylStarCheckRow102 : ∀ j : TraceZeroCoordinate,
    weylStarCoefficient (F := ZMod 2) 1 (.inr (0,2)) j =
      weylOperator 1 (extensionCoefficient (.inr (0,2)) j) +
        weylStarCorrection 1 (traceZeroCross (starMarkedVector (.inr (0,2))) (starMarkedVector j)) := by
  intro j
  fin_cases j <;> decide
end Atlas.ReeF4
