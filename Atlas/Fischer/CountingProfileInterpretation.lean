import Atlas.Fischer.CountingProfileEvaluation
import Atlas.Fischer.CountingHistogramNormalization

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Arbitrary source-profile interpretation of the complete Type A target sum. -/
theorem countingProfile_actual_A (p : CountingProfileData) (t : CountingSourceParameters)
    (ht : ∀ i, (countingSourceColumn t i).card=p.g i) :
    countingSourceATargetHistogram p.epsilon p.D p.E p.F t=p.histogramA := by
  have hw (a : CountingSourceTypeA) : countingSourceWeight p.epsilon p.D p.E p.F t (.inl a)=
      p.weight (countingTypeAColumnProfile a.val) (fun i => if i ∈ a.val then p.g i else 0) := by
    have hj (i : Fin 6) : (countingSourceColumn t i ∩ countingSourceColumn (.inl a) i).card=
        if i ∈ a.val then p.g i else 0 := by
      change (countingSourceColumn t i ∩ (if i ∈ a.val then Finset.univ else ∅)).card=_
      by_cases hi : i ∈ a.val <;> simp [hi,ht]
    simp only [countingSourceWeight,CountingProfileData.weight,countingTypeAColumnProfile,
      ht,countingSourceColumn_card_A,hj]
    rfl
  funext j
  simp only [countingSourceATargetHistogram,hw,CountingProfileData.histogramA]
  let e : CountingSourceTypeA ≃ ↥((Finset.univ : Finset (Fin 6)).powersetCard 2) :=
    Equiv.subtypeEquivRight (by intro T; simp)
  let f (T : Finset (Fin 6)) := countingWeightHistogram
    (p.weight (countingTypeAColumnProfile T) (fun i => if i ∈ T then p.g i else 0)) j
  change (∑ a : CountingSourceTypeA, f a.val)=∑ T ∈ Finset.univ.powersetCard 2, f T
  calc
    _ = ∑ a : ↥((Finset.univ : Finset (Fin 6)).powersetCard 2), f a.val :=
      Equiv.sum_comp e (fun a => f a.val)
    _ = _ := by
      rw [Finset.sum_coe_sort_eq_attach]
      exact Finset.sum_attach _ f

end Atlas.Fischer
