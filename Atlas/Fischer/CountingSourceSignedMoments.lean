import Atlas.Fischer.CountingActualProfileHistograms
import Atlas.Fischer.CountingShapeSignedTotals
import Atlas.Fischer.CountingShapeSums

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Failure of the fixed-source intersection test kills the optional weight,
regardless of the target octad or the other three tests. -/
theorem countingColumnWeight_invalid (epsilon : ℕ) (D E F : Finset (Fin 6))
    (g b h : CountingColumnVector)
    (hg : (∑ i ∈ D, g i) ≠ 0 ∧ (∑ i ∈ D, g i) ≠ 4) :
    countingColumnWeight epsilon D E F g b h=none := by
  have hd : countingColumnDelta (∑ i ∈ D, g i)=none := by
    simp [countingColumnDelta,hg.1,hg.2]
  unfold countingColumnWeight
  cases countingColumnDelta (∑ i, h i) <;> simp [hd]

theorem countingSourceWeight_invalid (trio : Bool) (t u : CountingSourceParameters)
    (ht : ¬countingShapeAdmissible (countingSourceShape t)) :
    let p := countingShapeData trio (countingSourceShape t)
    countingSourceWeight p.epsilon p.D p.E p.F t u=none := by
  have hs := (countingShape_admissible_profile (countingSourceShape t)).not.mp ht
  simp only [not_or] at hs
  apply countingColumnWeight_invalid
  simpa only [countingSourceShape_profile,countingShapeData] using hs

/-- The signed first moment of the actual759-target histogram equals the
literal sum of the optional column weights, with invalid terms set to zero. -/
theorem countingSourceSignedMoment (trio : Bool) (t : CountingSourceParameters) :
    let p := countingShapeData trio (countingSourceShape t)
    (∑ u : CountingSourceParameters, (countingSourceWeight p.epsilon p.D p.E p.F t u).getD 0)=
      countingHistogramMoment p.histogram := by
  have hh := congrArg countingHistogramMoment (countingActualProfile_histogram trio t)
  rw [countingHistogramMoment_sum] at hh
  simpa only [countingSourceWeight,countingColumnWeight_moment] using hh

/-- Exact signed double sum, grouped by actual source fibers of sizes1,24,64.
Every target histogram is the verified full profile, not an assumed table row. -/
theorem countingSourceSignedSum (trio : Bool) :
    (∑ t : CountingSourceParameters, ∑ u : CountingSourceParameters,
      (countingSourceWeight (if trio then 1 else 0) countingTableD
        (if trio then {2,3} else {0,2}) (if trio then {4,5} else {1,2}) t u).getD 0)=
      if trio then (13738 : ℤ) else 13634 := by
  calc
    _ = ∑ t : CountingSourceParameters,
        if countingShapeAdmissible (countingSourceShape t) then
          countingHistogramMoment (countingShapeData trio (countingSourceShape t)).histogram else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : countingShapeAdmissible (countingSourceShape t)
      · rw [if_pos ht]
        exact countingSourceSignedMoment trio t
      · rw [if_neg ht]
        apply Finset.sum_eq_zero
        intro u _
        have h := countingSourceWeight_invalid trio t u ht
        dsimp only [countingShapeData] at h
        rw [h]
        rfl
    _ = ∑ s : CountingSourceShape,
        if countingShapeAdmissible s then (countingShapeMultiplicity s : ℤ)*
          countingHistogramMoment (countingShapeData trio s).histogram else 0 := by
      rw [countingSourceShape_sum (fun s => if countingShapeAdmissible s then
        countingHistogramMoment (countingShapeData trio s).histogram else (0 : ℤ))]
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : countingShapeAdmissible s <;> simp [hs,nsmul_eq_mul]
    _ = _ := countingShape_actual_signed_total trio

end Atlas.Fischer
