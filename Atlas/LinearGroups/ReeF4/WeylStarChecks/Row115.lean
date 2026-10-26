import Atlas.LinearGroups.ReeF4.WeylStarData

/-! One bounded row of the concrete Weyl/star coefficient identity. -/
namespace Atlas.ReeF4
open Atlas.Albert
set_option maxRecDepth 8192 in
set_option maxHeartbeats 600000 in
theorem weylStarCheckRow115 : ∀ j : TraceZeroCoordinate,
    weylStarCoefficient (F := ZMod 2) 1 (.inr (1,5)) j =
      weylOperator 1 (extensionCoefficient (.inr (1,5)) j) +
        weylStarCorrection 1 (traceZeroCross (starMarkedVector (.inr (1,5))) (starMarkedVector j)) := by
  intro j
  fin_cases j <;> decide
end Atlas.ReeF4
