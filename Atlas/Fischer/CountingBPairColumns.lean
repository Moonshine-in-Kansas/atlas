import Atlas.Fischer.CountingHistogramNormalization
import Atlas.Fischer.CountingGroupedBParameters
import Atlas.Fischer.CountingProfileEvaluation
import Atlas.Fischer.CountingRatioTable

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Pair-intersection columns with an actual supported even mask. -/
def countingBPairColumns (I Z : Finset (Fin 6)) (e : P6) : CountingColumnVector :=
  fun i => if i ∈ I then (if i ∈ Z then 2*(1-(e.val i).val) else 1) else 0

theorem countingBPairColumns_parity (I Z : Finset (Fin 6)) (m : Fin 5 → Bit) :
    countingBPairColumns I Z (parityEquiv 5 m)=countingPairJointColumns I Z m := rfl

/-- The ratio-one condition is exactly the local equal-pair case. -/
theorem countingColumnPair_ratio_intersection (g h : CountingFour) (e : Bit) :
    (countingColumnPair g 0 ∩ countingColumnPair h e).card=
      if g≠0 ∧ h≠0 then (if h/g=1 then 2*(1-e.val) else 1) else 0 := by
  simp only [countingFour_div]
  revert g h e
  decide

/-- Literal joint columns for a normalized actual Type B source and a grouped
actual Type B target. -/
theorem countingSourceBB_joint (g : {g : countingHexacode // hammingNorm g.val=4})
    (T : CountingFourSupport) (e : CountingMaskOn T.val) (h : CountingWordOn T.val) :
    (fun i => (countingSourceColumn (.inr (.inl ⟨g,⟨0,by intros; rfl⟩⟩)) i ∩
      countingSourceColumn (.inr (.inl (countingSourceBGrouped T e h))) i).card)=
      countingBPairColumns (countingHexSupport g.val ∩ T.val) (countingRatioOnes g.val h.val) e.val := by
  funext i
  change (countingColumnPair (g.val.val i) 0 ∩ countingColumnPair (h.val.val i) (e.val.val i)).card=_
  rw [countingColumnPair_ratio_intersection]
  simp only [countingBPairColumns,← h.property,countingRatioOnes,Finset.mem_inter,
    Finset.mem_filter,countingHexSupport,Finset.mem_univ,true_and]
  by_cases hg : g.val.val i=0 <;> by_cases hh : h.val.val i=0 <;> simp [hg,hh]

/-- Exact source weight with both source and target Type B, retaining the actual
hexacode ratio set and actual target parity mask. -/
theorem countingSourceBB_weight (p : CountingProfileData)
    (g : {g : countingHexacode // hammingNorm g.val=4})
    (hg : ∀ i, p.g i=if g.val.val i=0 then 0 else 2)
    (T : CountingFourSupport) (e : CountingMaskOn T.val) (h : CountingWordOn T.val) :
    countingSourceWeight p.epsilon p.D p.E p.F
      (.inr (.inl ⟨g,⟨0,by intros; rfl⟩⟩)) (.inr (.inl (countingSourceBGrouped T e h)))=
      p.weight (countingTypeBColumnProfile T.val)
        (countingBPairColumns (countingHexSupport g.val ∩ T.val) (countingRatioOnes g.val h.val) e.val) := by
  simp only [countingSourceWeight,CountingProfileData.weight,countingSourceColumn_card_B,
    countingSourceBB_joint]
  rw [show (fun i => if g.val.val i=0 then 0 else 2)=p.g from funext (fun i => (hg i).symm)]
  have hb : (fun i => if h.val.val i=0 then 0 else 2)=countingTypeBColumnProfile T.val := by
    funext i
    simp only [countingTypeBColumnProfile,← h.property,countingHexSupport,Finset.mem_filter,
      Finset.mem_univ,true_and]
    by_cases hi : h.val.val i=0 <;> simp [hi]
  rw [show (fun i => if (countingSourceBGrouped T e h).1.val.val i=0 then 0 else 2)=
    countingTypeBColumnProfile T.val from hb]


end Atlas.Fischer
