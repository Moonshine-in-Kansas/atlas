import Atlas.LinearGroups.ReeF4.WeylStarData

/-! One bounded row of the concrete Weyl/star coefficient identity. -/
namespace Atlas.ReeF4
open Atlas.Albert
set_option maxRecDepth 8192 in
set_option maxHeartbeats 600000 in
theorem weylStarCheckRow0D0 : ∀ j : TraceZeroCoordinate,
    weylStarCoefficient (F := ZMod 2) 0 (.inl 0) j =
      weylOperator 0 (extensionCoefficient (.inl 0) j) +
        weylStarCorrection 0 (traceZeroCross (starMarkedVector (.inl 0)) (starMarkedVector j)) := by
  intro j
  fin_cases j <;> decide
end Atlas.ReeF4
