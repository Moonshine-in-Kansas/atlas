import Atlas.Fischer.CountingColumnTranslation
import Atlas.Fischer.CountingTypeATable

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The Type A target subtotal for the column evaluator on actual source octads. -/
def countingSourceATargetHistogram (epsilon : ℕ) (D E F : Finset (Fin 6))
    (t : CountingSourceParameters) : CountingSignedHistogram :=
  fun j => ∑ a : CountingSourceTypeA,
    countingWeightHistogram (countingSourceWeight epsilon D E F t (.inl a)) j

theorem countingSourceA_target_weight (r : Fin 14) (t : CountingSourceParameters)
    (ht : ∀ i, (countingSourceColumn t i).card=countingTableProfile r i)
    (a : CountingSourceTypeA) :
    countingSourceWeight (countingTableEpsilon r) countingTableD (countingTableE r)
      (countingTableF r) t (.inl a)=countingTypeATargetWeight r a.val := by
  have hj (i : Fin 6) : (countingSourceColumn t i ∩ countingSourceColumn (.inl a) i).card=
      if i ∈ a.val then countingTableProfile r i else 0 := by
    change (countingSourceColumn t i ∩ (if i ∈ a.val then Finset.univ else ∅)).card=_
    by_cases hi : i ∈ a.val <;> simp [hi,ht]
  simp only [countingSourceWeight,countingTypeATargetWeight,ht,countingSourceColumn_card_A,hj]
  rfl

/-- Exact reindexing of the actual two-column parameter space into the fifteen finite choices. -/
theorem countingSourceATargetHistogram_eq (r : Fin 14) (t : CountingSourceParameters)
    (ht : ∀ i, (countingSourceColumn t i).card=countingTableProfile r i) :
    countingSourceATargetHistogram (countingTableEpsilon r) countingTableD
      (countingTableE r) (countingTableF r) t=countingTypeATargetHistogram r := by
  funext j
  simp only [countingSourceATargetHistogram,countingSourceA_target_weight r t ht,
    countingTypeATargetHistogram]
  let f : CountingSourceTypeA ≃ ↥((Finset.univ : Finset (Fin 6)).powersetCard 2) :=
    Equiv.subtypeEquivRight (by intro T; simp)
  calc
    (∑ a : CountingSourceTypeA, countingWeightHistogram (countingTypeATargetWeight r a.val) j)=
        ∑ a : ↥((Finset.univ : Finset (Fin 6)).powersetCard 2),
          countingWeightHistogram (countingTypeATargetWeight r a.val) j :=
      (Equiv.sum_comp f (fun a => countingWeightHistogram (countingTypeATargetWeight r a.val) j))
    _ = _ := by
      rw [Finset.sum_coe_sort_eq_attach]
      exact Finset.sum_attach _ (fun T => countingWeightHistogram (countingTypeATargetWeight r T) j)

/-- The entire displayed Type A column of subtotals holds for actual source parameters. -/
theorem countingSourceATargetHistogram_expected (r : Fin 14) (t : CountingSourceParameters)
    (ht : ∀ i, (countingSourceColumn t i).card=countingTableProfile r i) :
    countingSourceATargetHistogram (countingTableEpsilon r) countingTableD
      (countingTableE r) (countingTableF r) t=countingTypeAExpectedHistogram r := by
  rw [countingSourceATargetHistogram_eq r t ht,countingTypeATargetHistogram_all]

end Atlas.Fischer
