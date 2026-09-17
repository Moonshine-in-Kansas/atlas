import Atlas.Fischer.CountingAllProfileTotals
import Atlas.Fischer.CountingSignedMoments

namespace Atlas.Fischer

set_option maxRecDepth 4096 in
/-- The small aggregate arithmetic uses the actual source-fiber sizes and
the already verified full-profile histograms, not assumed table symmetry. -/
theorem countingShape_expected_signed_total :
    ∀ trio : Bool,
      (∑ s : CountingSourceShape, if countingShapeAdmissible s then
        (countingShapeMultiplicity s : ℤ) *
          countingHistogramMoment (countingExpectedTotalHistogram (countingShapeRow trio s))
        else 0) = if trio then (13738 : ℤ) else 13634 := by
  decide

theorem countingShape_actual_signed_total (trio : Bool) :
    (∑ s : CountingSourceShape, if countingShapeAdmissible s then
      (countingShapeMultiplicity s : ℤ) *
        countingHistogramMoment (countingShapeData trio s).histogram else 0) =
      if trio then (13738 : ℤ) else 13634 := by
  calc
    _ = ∑ s : CountingSourceShape, if countingShapeAdmissible s then
        (countingShapeMultiplicity s : ℤ) *
          countingHistogramMoment (countingExpectedTotalHistogram (countingShapeRow trio s))
        else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases h : countingShapeAdmissible s
      · rw [if_pos h, if_pos h, countingAllProfiles_totalHistogram trio s h]
      · rw [if_neg h, if_neg h]
    _ = _ := countingShape_expected_signed_total trio

end Atlas.Fischer
