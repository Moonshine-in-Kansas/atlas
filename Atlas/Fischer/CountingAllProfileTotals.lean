import Atlas.Fischer.CountingShapeCounts

namespace Atlas.Fischer

def CountingProfileData.histogram (p : CountingProfileData) : CountingSignedHistogram :=
  fun k => p.histogramA k + p.histogramB k + p.histogramC k

def countingExpectedTotalHistogram (r : Fin 14) : CountingSignedHistogram :=
  fun k => countingTypeAExpectedHistogram r k + countingTypeBExpectedHistogram r k +
    countingTypeCExpectedHistogram r k

set_option maxRecDepth 8192 in
set_option maxHeartbeats 40000000 in
/-- Exhaustive coverage of all23 admissible geometric source profiles in
both settings. The combined signed histogram is checked directly, so no
unstated permutation symmetry of the separate target subtotals is needed. -/
theorem countingAllProfiles_totalHistogram :
    ∀ (trio : Bool) (s : CountingSourceShape), countingShapeAdmissible s →
      (countingShapeData trio s).histogram =
        countingExpectedTotalHistogram (countingShapeRow trio s) := by
  intro trio
  cases trio <;> decide

end Atlas.Fischer
