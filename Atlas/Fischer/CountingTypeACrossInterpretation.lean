import Atlas.Fischer.CountingProfileInterpretation
import Atlas.Fischer.CountingHexacodeWeights

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- For a Type A source, every target column is either kept in full or discarded. -/
theorem countingSourceA_joint_card (a : CountingSourceTypeA)
    (t : CountingSourceParameters) (i : Fin 6) :
    (countingSourceColumn (.inl a) i ∩ countingSourceColumn t i).card=
      if i ∈ a.val then (countingSourceColumn t i).card else 0 := by
  change ((if i ∈ a.val then Finset.univ else ∅) ∩ countingSourceColumn t i).card=_
  by_cases hi : i ∈ a.val <;> simp [hi]

/-- Exact Type C target subtotal for every actual Type A source and arbitrary
external column configuration. The factor64 is the actual hexacode cardinality. -/
theorem countingProfile_actual_AC (p : CountingProfileData) (a : CountingSourceTypeA)
    (ht : p.sourceType=0) (hg : ∀ i, p.g i=if i ∈ a.val then 4 else 0) :
    countingSourceCTargetHistogram p.epsilon p.D p.E p.F (.inl a)=p.histogramC := by
  have hw (c : CountingSourceTypeC) :
      countingSourceWeight p.epsilon p.D p.E p.F (.inl a) (.inr (.inr c))=
        p.weight (countingTypeCColumnProfile c.2)
          (fun i => if p.g i=4 then countingTypeCColumnProfile c.2 i else 0) := by
    simp only [countingSourceWeight,CountingProfileData.weight,countingSourceColumn_card_A,
      countingSourceColumn_card_C,countingSourceA_joint_card,countingTypeCColumnProfile]
    congr 1
    · funext i; exact (hg i).symm
    · funext i
      by_cases hi : i ∈ a.val <;> simp [hg,hi]
  have hc : Fintype.card countingHexacode=64 := by
    simpa only [Nat.card_eq_fintype_card] using countingHexacode_card
  funext k
  simp only [countingSourceCTargetHistogram,hw,CountingProfileData.histogramC,
    CountingProfileData.wordHistogramC,ht,ite_true]
  change (∑ c : countingHexacode × Fin 6, _)=_
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [hc]

end Atlas.Fischer
