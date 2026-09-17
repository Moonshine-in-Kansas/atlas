import Atlas.Fischer.CountingTypeACrossInterpretation
import Atlas.Fischer.CountingTraceFiberSums

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The Type C target sum for a zero-mask Type B source is exactly the eight
trace-pattern fibers, each containing eight actual hexacode words. -/
theorem countingProfile_actual_BC (p : CountingProfileData)
    (g : {g : countingHexacode // hammingNorm g.val=4})
    (ht : p.sourceType=1) (hg : ∀ i, p.g i=if g.val.val i=0 then 0 else 2) :
    countingSourceCTargetHistogram p.epsilon p.D p.E p.F
      (.inr (.inl ⟨g,⟨0,by intros; rfl⟩⟩))=p.histogramC := by
  have hs : p.support=countingHexSupport g.val := by
    ext i
    simp only [CountingProfileData.support,countingHexSupport,Finset.mem_filter,
      Finset.mem_univ,true_and]
    by_cases hi : g.val.val i=0 <;> simp [hg,hi]
  let f (j k : Fin 6) (v : P6) := countingWeightHistogram
    (p.weight (countingTypeCColumnProfile j) (fun i => if g.val.val i=0 then 0 else
      (if i=j then 1+(v.val i).val else 1-(v.val i).val))) k
  have hw (c : CountingSourceTypeC) (k : Fin 6) :
      countingWeightHistogram (countingSourceWeight p.epsilon p.D p.E p.F
        (.inr (.inl ⟨g,⟨0,by intros; rfl⟩⟩)) (.inr (.inr c))) k=
        f c.2 k (countingRatioMask c.1 g.val) := by
    congr 1
    simp only [countingSourceWeight,CountingProfileData.weight,
      countingSourceColumn_card_B,countingSourceColumn_card_C]
    rw [show (fun i => if g.val.val i=0 then 0 else 2)=p.g from funext (fun i => (hg i).symm)]
    congr 1
    funext i
    change ((countingColumnPair (g.val.val i) 0) ∩
      countingColumnSingleton (c.1.val i) (decide (i=c.2))).card=_
    simpa [countingRatioMask] using countingColumnPair_singleton_intersection
      (g.val.val i) (c.1.val i) (decide (i=c.2))
  funext k
  simp only [countingSourceCTargetHistogram,hw,CountingProfileData.histogramC]
  change (∑ c : countingHexacode × Fin 6, f c.2 k (countingRatioMask c.1 g.val))=_
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ x : countingHexacode, f j k (countingRatioMask x g.val))=_
  rw [countingRatioMask_sum g.val g.property (f j k),
    countingSupportedMask_sum g.val (fun v => 8*f j k v)]
  simp only [CountingProfileData.wordHistogramC,ht,show (1 : Fin 3)≠0 by decide,
    if_false,if_true,hs]
  apply Finset.sum_congr rfl
  intro m _
  split_ifs
  · dsimp only [f]
    apply congrArg (fun n : ℕ => 8*n)
    apply congrArg (fun w => countingWeightHistogram w k)
    apply congrArg (p.weight (countingTypeCColumnProfile j))
    funext i
    simp only [countingHexSupport,Finset.mem_filter,Finset.mem_univ,true_and]
    by_cases hi : g.val.val i=0 <;> simp [f,CountingProfileData.weight,countingTableMask,hi]
    all_goals rfl
  · rfl

end Atlas.Fischer
