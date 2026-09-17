import Atlas.Codes.TernaryBinaryComparisonData

namespace Atlas.Codes

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- A bounded check of the 729 code parameters against the proved binary linear lift.
-- It checks octad weight and every marked trace coordinate; no group enumeration occurs.
theorem ternaryBinaryOctadLift_check : ∀ p : TernaryParameters,
    ternaryWeight (ternaryEncoder p) = 6 →
      hammingNorm (ternaryBinaryOctadWord (ternaryEncoder p)) = 8 ∧
      ∀ i : Fin 12, ternaryBinaryOctadWord (ternaryEncoder p) (ternaryBinaryPosition i) =
        if ternaryEncoder p i ≠ 0 then 1 else 0 := by
  decide +kernel

theorem ternaryBinaryOctadLift_spec (u : TernaryWord) (hu : u ∈ ternaryGolay)
    (hw : ternaryWeight u = 6) :
    hammingNorm (ternaryBinaryOctadWord u) = 8 ∧
      ∀ i : Fin 12, ternaryBinaryOctadWord u (ternaryBinaryPosition i) =
        if u i ≠ 0 then 1 else 0 := by
  obtain ⟨p,rfl⟩ := hu
  exact ternaryBinaryOctadLift_check p hw

end Atlas.Codes
