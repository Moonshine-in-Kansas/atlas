import Atlas.Fischer.CountingAllProfileTotals
import Atlas.Fischer.CountingTypeBInterpretation
import Atlas.Fischer.CountingTypeCCrossInterpretation
import Atlas.Fischer.CountingTypeABInterpretation
import Atlas.Fischer.CountingTypeCBInterpretation

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Every actual source, before normalization, has the Type A target histogram
of its full column profile. -/
theorem countingActualProfile_histogramA (trio : Bool) (t : CountingSourceParameters) :
    let p := countingShapeData trio (countingSourceShape t)
    countingSourceATargetHistogram p.epsilon p.D p.E p.F t=p.histogramA := by
  apply countingProfile_actual_A
  exact countingSourceShape_profile t

/-- Every actual source has its full-profile Type B target histogram. Actual row
translations normalize the source while permuting all target parameters. -/
theorem countingActualProfile_histogramB (trio : Bool) (t : CountingSourceParameters) :
    let p := countingShapeData trio (countingSourceShape t)
    countingSourceBTargetHistogram p.epsilon p.D p.E p.F t=p.histogramB := by
  let p := countingShapeData trio (countingSourceShape t)
  change countingSourceBTargetHistogram p.epsilon p.D p.E p.F t=p.histogramB
  rcases t with a | (b | c)
  · exact countingProfile_actual_AB p a rfl (fun i => rfl)
  · have hn := countingSourceB_histograms_normalize p.epsilon p.D p.E p.F b
    rw [hn.2.1]
    apply countingProfile_actual_BB p b.1 rfl
    intro i
    exact (countingSourceShape_profile (.inr (.inl b)) i).symm.trans
      (countingSourceColumn_card_B b i)
  · have hn := countingSourceC_histograms_normalize p.epsilon p.D p.E p.F c.1 c.2
    rw [hn.2.1]
    exact countingProfile_actual_CB p c.2 rfl (fun i => rfl)

/-- Every actual source has its full-profile Type C target histogram. -/
theorem countingActualProfile_histogramC (trio : Bool) (t : CountingSourceParameters) :
    let p := countingShapeData trio (countingSourceShape t)
    countingSourceCTargetHistogram p.epsilon p.D p.E p.F t=p.histogramC := by
  let p := countingShapeData trio (countingSourceShape t)
  change countingSourceCTargetHistogram p.epsilon p.D p.E p.F t=p.histogramC
  rcases t with a | (b | c)
  · exact countingProfile_actual_AC p a rfl (fun i => rfl)
  · have hn := countingSourceB_histograms_normalize p.epsilon p.D p.E p.F b
    rw [hn.2.2]
    apply countingProfile_actual_BC p b.1 rfl
    intro i
    exact (countingSourceShape_profile (.inr (.inl b)) i).symm.trans
      (countingSourceColumn_card_B b i)
  · have hn := countingSourceC_histograms_normalize p.epsilon p.D p.E p.F c.1 c.2
    rw [hn.2.2]
    exact countingProfile_actual_CC p c.2 rfl (fun i => rfl)

/-- All759 actual target octads, partitioned by their verified source parameters,
give exactly the complete histogram of the source's full column profile. -/
theorem countingActualProfile_histogram (trio : Bool) (t : CountingSourceParameters) :
    let p := countingShapeData trio (countingSourceShape t)
    (fun j => ∑ u : CountingSourceParameters, countingWeightHistogram
      (countingSourceWeight p.epsilon p.D p.E p.F t u) j)=p.histogram := by
  let p := countingShapeData trio (countingSourceShape t)
  funext j
  simp only [Fintype.sum_sum_type,CountingProfileData.histogram]
  change countingSourceATargetHistogram p.epsilon p.D p.E p.F t j+
    (countingSourceBTargetHistogram p.epsilon p.D p.E p.F t j+
      countingSourceCTargetHistogram p.epsilon p.D p.E p.F t j)=_
  rw [countingActualProfile_histogramA trio t,countingActualProfile_histogramB trio t,
    countingActualProfile_histogramC trio t]
  exact (Nat.add_assoc _ _ _).symm

end Atlas.Fischer

