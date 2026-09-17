import Atlas.Fischer.CountingShapeCounts

namespace Atlas.Fischer

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6000000 in
/-- Every admissible source profile has its Type A target subtotal, including
the exceptional placement D union F in the trio case. Component subtotals
need not be constant on a coarse total-histogram row. -/
theorem countingAllProfiles_histogramA :
    ∀ (trio : Bool) (s : CountingSourceShape), countingShapeAdmissible s →
      (countingShapeData trio s).histogramA =
        (if trio && decide (s=Sum.inr (Sum.inl ⟨{0,1,4,5},by decide⟩)) then
          ![0,0,0,6,0,0] else countingTypeAExpectedHistogram (countingShapeRow trio s)) := by
  decide

end Atlas.Fischer
