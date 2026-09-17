import Atlas.Fischer.CubicOctadC0SignedGram

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def cubicC0CommonIndicator (E F : Octad) (u : ℕ) (H : Octad) : Prop :=
  (H.val ∩ E.val).card = 4 ∧ (H.val ∩ F.val).card = 4 ∧
    (H.val ∩ E.val ∩ F.val).card = u

def cubicC0PairIndicator (E F : Octad) (a b : ℕ) (H : Octad) : Prop :=
  (H.val ∩ E.val).card = a ∧ (H.val ∩ F.val).card = b

/-- The signed Gram function is exhausted by seven actual sextet-side fibers. -/
theorem cubicOctadC0SignedGram_four_indicators (E F H : Octad)
    (hEF : (E.val ∩ F.val).card = 4) :
    cubicOctadC0SignedGram E F (Or.inl hEF) H =
      (11 / 4 : Scalar) * (if cubicC0CommonIndicator E F 0 H then 1 else 0) +
      (3 / 4 : Scalar) * (if cubicC0CommonIndicator E F 2 H then 1 else 0) +
      (1 / 4 : Scalar) * (if cubicC0CommonIndicator E F 3 H then 1 else 0) -
      (5 / 4 : Scalar) * (if cubicC0CommonIndicator E F 4 H then 1 else 0) +
      (9 / 4 : Scalar) * (if cubicC0PairIndicator E F 0 4 H then 1 else 0) +
      (9 / 4 : Scalar) * (if cubicC0PairIndicator E F 4 0 H then 1 else 0) +
      (15 / 4 : Scalar) * (if cubicC0PairIndicator E F 0 0 H then 1 else 0) := by
  by_cases he : OctadPairAdmissible H E
  · by_cases hf : OctadPairAdmissible H F
    · rcases he with he | he <;> rcases hf with hf | hf
      · rw [cubicOctadC0SignedGram_four E F H hEF he hf]
        rcases cubicCommonNeighbor_actual_levels H E F he hf hEF with hu | hu | hu | hu <;>
          norm_num [← Finset.inter_assoc, cubicC0CommonIndicator, cubicC0PairIndicator, he, hf, hu]
      · rw [cubicOctadC0SignedGram_one_empty E F H (Or.inl hEF) (Or.inr ⟨he,hf⟩)]
        norm_num [← Finset.inter_assoc, cubicC0CommonIndicator, cubicC0PairIndicator, he, hf]
      · rw [cubicOctadC0SignedGram_one_empty E F H (Or.inl hEF) (Or.inl ⟨he,hf⟩)]
        norm_num [← Finset.inter_assoc, cubicC0CommonIndicator, cubicC0PairIndicator, he, hf]
      · rw [cubicOctadC0SignedGram_both_zero_four E F H hEF he hf]
        norm_num [← Finset.inter_assoc, cubicC0CommonIndicator, cubicC0PairIndicator, he, hf]
    · rw [cubicOctadC0SignedGram_zero E F (Or.inl hEF) H (Or.inr hf)]
      have hn4 : (H.val ∩ F.val).card ≠ 4 := fun h => hf (Or.inl h)
      have hn0 : (H.val ∩ F.val).card ≠ 0 := fun h => hf (Or.inr h)
      simp [cubicC0CommonIndicator, cubicC0PairIndicator, hn4, hn0]
  · rw [cubicOctadC0SignedGram_zero E F (Or.inl hEF) H (Or.inl he)]
    have hn4 : (H.val ∩ E.val).card ≠ 4 := fun h => he (Or.inl h)
    have hn0 : (H.val ∩ E.val).card ≠ 0 := fun h => he (Or.inr h)
    simp [cubicC0CommonIndicator, cubicC0PairIndicator, hn4, hn0]

/-- Four actual trio-side fibers exhaust the signed Gram function. -/
theorem cubicOctadC0SignedGram_zero_indicators (E F H : Octad)
    (hEF : (E.val ∩ F.val).card = 0) :
    cubicOctadC0SignedGram E F (Or.inr hEF) H =
      (15 / 4 : Scalar) * (if cubicC0PairIndicator E F 4 4 H then 1 else 0) +
      (9 / 4 : Scalar) * (if cubicC0PairIndicator E F 0 4 H then 1 else 0) +
      (9 / 4 : Scalar) * (if cubicC0PairIndicator E F 4 0 H then 1 else 0) +
      (99 / 4 : Scalar) * (if cubicC0PairIndicator E F 0 0 H then 1 else 0) := by
  by_cases he : OctadPairAdmissible H E
  · by_cases hf : OctadPairAdmissible H F
    · rcases he with he | he <;> rcases hf with hf | hf
      · rw [cubicOctadC0SignedGram_both_four_zero E F H hEF he hf]
        norm_num [← Finset.inter_assoc, cubicC0PairIndicator, he, hf]
      · rw [cubicOctadC0SignedGram_one_empty E F H (Or.inr hEF) (Or.inr ⟨he,hf⟩)]
        norm_num [← Finset.inter_assoc, cubicC0PairIndicator, he, hf]
      · rw [cubicOctadC0SignedGram_one_empty E F H (Or.inr hEF) (Or.inl ⟨he,hf⟩)]
        norm_num [← Finset.inter_assoc, cubicC0PairIndicator, he, hf]
      · rw [cubicOctadC0SignedGram_both_zero_zero E F H hEF he hf]
        norm_num [← Finset.inter_assoc, cubicC0PairIndicator, he, hf]
    · rw [cubicOctadC0SignedGram_zero E F (Or.inr hEF) H (Or.inr hf)]
      have hn4 : (H.val ∩ F.val).card ≠ 4 := fun h => hf (Or.inl h)
      have hn0 : (H.val ∩ F.val).card ≠ 0 := fun h => hf (Or.inr h)
      simp [cubicC0PairIndicator, hn4, hn0]
  · rw [cubicOctadC0SignedGram_zero E F (Or.inr hEF) H (Or.inl he)]
    have hn4 : (H.val ∩ E.val).card ≠ 4 := fun h => he (Or.inl h)
    have hn0 : (H.val ∩ E.val).card ≠ 0 := fun h => he (Or.inr h)
    simp [cubicC0PairIndicator, hn4, hn0]

end Atlas.Fischer
