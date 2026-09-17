import Atlas.Fischer.CountingTypeBCrossInterpretation
import Atlas.Fischer.CountingZeroSetFibres

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Two singleton/triple columns are determined by equality of their letters. -/
theorem countingColumnSingleton_zero_intersection (h : CountingFour) (a b : Bool) :
    (countingColumnSingleton 0 a ∩ countingColumnSingleton h b).card=
      if a then (if b then (if h=0 then 3 else 2) else (if h=0 then 0 else 1))
      else (if b then (if h=0 then 0 else 1) else (if h=0 then 1 else 0)) := by
  revert h a b
  decide

/-- Exact Type C target subtotal for a zero-word Type C source. The three zero-set
multiplicities are derived from actual hexacode fibers, with no orbit assumption. -/
theorem countingProfile_actual_CC (p : CountingProfileData) (l : Fin 6)
    (ht : p.sourceType=2) (hg : ∀ i, p.g i=if i=l then 3 else 1) :
    countingSourceCTargetHistogram p.epsilon p.D p.E p.F (.inr (.inr (0,l)))=p.histogramC := by
  have hw (c : CountingSourceTypeC) :
      countingSourceWeight p.epsilon p.D p.E p.F (.inr (.inr (0,l))) (.inr (.inr c))=
        p.weight (countingTypeCColumnProfile c.2) (p.singletonJoint c.2 (countingHexZeroSet c.1)) := by
    simp only [countingSourceWeight,CountingProfileData.weight,countingSourceColumn_card_C]
    rw [show (fun i => if i=l then 3 else 1)=p.g from funext (fun i => (hg i).symm)]
    apply congrArg (countingColumnWeight p.epsilon p.D p.E p.F p.g
      (countingTypeCColumnProfile c.2))
    funext i
    change (countingColumnSingleton 0 (decide (i=l)) ∩
      countingColumnSingleton (c.1.val i) (decide (i=c.2))).card=_
    rw [countingColumnSingleton_zero_intersection]
    simp only [CountingProfileData.singletonJoint,countingHexZeroSet_mem,hg]
    by_cases hi : i=l <;> simp [hi]
  funext k
  simp only [countingSourceCTargetHistogram,hw,CountingProfileData.histogramC]
  change (∑ c : countingHexacode × Fin 6, _)=_
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ h : countingHexacode, countingWeightHistogram
    (p.weight (countingTypeCColumnProfile j) (p.singletonJoint j (countingHexZeroSet h))) k)=_
  rw [countingHexZeroSet_sum (fun Z => countingWeightHistogram
    (p.weight (countingTypeCColumnProfile j) (p.singletonJoint j Z)) k)]
  simp only [CountingProfileData.wordHistogramC,ht,show (2 : Fin 3)≠0 by decide,
    show (2 : Fin 3)≠1 by decide,if_false]

end Atlas.Fischer
