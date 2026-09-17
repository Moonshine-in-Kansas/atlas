import Atlas.Fischer.CountingTypeABInterpretation
import Atlas.Fischer.CountingPairIntersections

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The intersection of a normalized singleton/triple with a pair depends only
 on the parity mask, not on which nonzero field letter defines the pair. -/
theorem countingColumnSingleton_pair_zero_intersection (h : CountingFour)
    (e : Bit) (d : Bool) :
    (countingColumnSingleton 0 d ∩ countingColumnPair h e).card=
      if h=0 then 0 else if d then 1+e.val else 1-e.val := by
  revert h e d
  decide

/-- Exact Type B target subtotal for a normalized actual Type C source. -/
theorem countingProfile_actual_CB (p : CountingProfileData) (l : Fin 6)
    (ht : p.sourceType=2) (hg : ∀ i, p.g i=if i=l then 3 else 1) :
    countingSourceBTargetHistogram p.epsilon p.D p.E p.F (.inr (.inr (0,l)))=p.histogramB := by
  have hw (T : CountingFourSupport) (e : CountingMaskOn T.val) (h : CountingWordOn T.val) :
      countingSourceWeight p.epsilon p.D p.E p.F (.inr (.inr (0,l)))
        (.inr (.inl (countingSourceBGrouped T e h)))=
      p.weight (countingTypeBColumnProfile T.val)
        (fun i => if i ∈ T.val then
          (if p.g i=3 then 1+(e.val.val i).val else 1-(e.val.val i).val) else 0) := by
    simp only [countingSourceWeight,CountingProfileData.weight,countingSourceColumn_card_C,
      countingGroupedB_column_card]
    rw [show (fun i => if i=l then 3 else 1)=p.g from funext (fun i => (hg i).symm)]
    apply congrArg (countingColumnWeight p.epsilon p.D p.E p.F p.g
      (countingTypeBColumnProfile T.val))
    funext i
    change (countingColumnSingleton 0 (decide (i=l)) ∩
      countingColumnPair (h.val.val i) (e.val.val i)).card=_
    rw [countingColumnSingleton_pair_zero_intersection]
    have hs : i ∈ T.val ↔ h.val.val i ≠ 0 := by
      simpa only [h.property] using (show i ∈ countingHexSupport h.val ↔ h.val.val i ≠ 0 by simp [countingHexSupport])
    by_cases hi : i=l
    · subst i
      by_cases hz : h.val.val l=0 <;> simp [hs,hz,hg]
    · by_cases hz : h.val.val i=0 <;> simp [hs,hz,hg,hi]
  funext j
  unfold countingSourceBTargetHistogram
  rw [countingGroupedB_histogram_sum _
    (fun T e => countingWeightHistogram (p.weight (countingTypeBColumnProfile T)
      (fun i => if i ∈ T then
        (if p.g i=3 then 1+(e.val i).val else 1-(e.val i).val) else 0)) j)
    (by intro T e h; rw [hw])]
  simp only [CountingProfileData.histogramB,CountingProfileData.wordHistogramB,ht,
    show (2 : Fin 3)≠0 by decide,ite_false,ite_true,countingTableMask]
  rfl

end Atlas.Fischer
