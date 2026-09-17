import Atlas.Fischer.CountingTypeAInterpretation
import Atlas.Fischer.CountingMaskNormalization

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Signed Type B target subtotal over the actual source parameter space. -/
def countingSourceBTargetHistogram (epsilon : ℕ) (D E F : Finset (Fin 6))
    (t : CountingSourceParameters) : CountingSignedHistogram :=
  fun j => ∑ b : CountingSourceTypeB,
    countingWeightHistogram (countingSourceWeight epsilon D E F t (.inr (.inl b))) j

/-- Signed Type C target subtotal over the actual source parameter space. -/
def countingSourceCTargetHistogram (epsilon : ℕ) (D E F : Finset (Fin 6))
    (t : CountingSourceParameters) : CountingSignedHistogram :=
  fun j => ∑ c : CountingSourceTypeC,
    countingWeightHistogram (countingSourceWeight epsilon D E F t (.inr (.inr c))) j

theorem countingSourceATargetHistogram_translation (epsilon : ℕ) (D E F : Finset (Fin 6))
    (b : countingHexacode) (t : CountingSourceParameters) :
    countingSourceATargetHistogram epsilon D E F (countingSourceTranslation b t)=
      countingSourceATargetHistogram epsilon D E F t := by
  funext j
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  exact countingSourceWeight_translation epsilon D E F b t (.inl a)

theorem countingSourceBTargetHistogram_translation (epsilon : ℕ) (D E F : Finset (Fin 6))
    (b : countingHexacode) (t : CountingSourceParameters) :
    countingSourceBTargetHistogram epsilon D E F (countingSourceTranslation b t)=
      countingSourceBTargetHistogram epsilon D E F t := by
  funext j
  change (∑ u : CountingSourceTypeB, countingWeightHistogram
    (countingSourceWeight epsilon D E F (countingSourceTranslation b t) (.inr (.inl u))) j)=_
  rw [← Equiv.sum_comp (countingSourceBTranslation b)]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  exact countingSourceWeight_translation epsilon D E F b t (.inr (.inl u))

theorem countingSourceCTargetHistogram_translation (epsilon : ℕ) (D E F : Finset (Fin 6))
    (b : countingHexacode) (t : CountingSourceParameters) :
    countingSourceCTargetHistogram epsilon D E F (countingSourceTranslation b t)=
      countingSourceCTargetHistogram epsilon D E F t := by
  funext j
  change (∑ u : CountingSourceTypeC, countingWeightHistogram
    (countingSourceWeight epsilon D E F (countingSourceTranslation b t) (.inr (.inr u))) j)=_
  rw [← Equiv.sum_comp (countingSourceCTranslation b)]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  exact countingSourceWeight_translation epsilon D E F b t (.inr (.inr u))

/-- An actual Type B source admits zero-mask normalization simultaneously for all
three signed target subtotals. No orbit transitivity is assumed. -/
theorem countingSourceB_histograms_normalize (epsilon : ℕ) (D E F : Finset (Fin 6))
    (t : CountingSourceTypeB) :
    let t0 : CountingSourceParameters := .inr (.inl ⟨t.1,⟨0,by intros; rfl⟩⟩)
    countingSourceATargetHistogram epsilon D E F (.inr (.inl t))=
      countingSourceATargetHistogram epsilon D E F t0 ∧
    countingSourceBTargetHistogram epsilon D E F (.inr (.inl t))=
      countingSourceBTargetHistogram epsilon D E F t0 ∧
    countingSourceCTargetHistogram epsilon D E F (.inr (.inl t))=
      countingSourceCTargetHistogram epsilon D E F t0 := by
  obtain ⟨b,hb⟩ := countingSourceB_normalizes t
  have he : countingSourceTranslation b (.inr (.inl t))=
      .inr (.inl ⟨t.1,⟨0,by intros; rfl⟩⟩) := congrArg (fun u => Sum.inr (Sum.inl u)) hb
  exact ⟨by rw [← he,countingSourceATargetHistogram_translation],
    by rw [← he,countingSourceBTargetHistogram_translation],
    by rw [← he,countingSourceCTargetHistogram_translation]⟩

/-- Actual Type C normalization preserves all signed target subtotals. -/
theorem countingSourceC_histograms_normalize (epsilon : ℕ) (D E F : Finset (Fin 6))
    (b : countingHexacode) (k : Fin 6) :
    let t : CountingSourceParameters := .inr (.inr (b,k))
    let t0 : CountingSourceParameters := .inr (.inr (0,k))
    countingSourceATargetHistogram epsilon D E F t=countingSourceATargetHistogram epsilon D E F t0 ∧
    countingSourceBTargetHistogram epsilon D E F t=countingSourceBTargetHistogram epsilon D E F t0 ∧
    countingSourceCTargetHistogram epsilon D E F t=countingSourceCTargetHistogram epsilon D E F t0 := by
  have he : countingSourceTranslation (-b) (.inr (.inr (b,k)))=.inr (.inr (0,k)) :=
    congrArg (fun u => Sum.inr (Sum.inr u)) (countingSourceCTranslation_normalizes b k)
  exact ⟨by rw [← he,countingSourceATargetHistogram_translation],
    by rw [← he,countingSourceBTargetHistogram_translation],
    by rw [← he,countingSourceCTargetHistogram_translation]⟩

end Atlas.Fischer
