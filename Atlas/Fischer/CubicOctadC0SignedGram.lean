import Atlas.Fischer.QuinticOctadC0Weights
import Atlas.Fischer.CubicQuadrilateralWeights
import Atlas.Fischer.CubicCompletionIntersections

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The actual signed Gram summand; the factor16 clears the four cubic halves. -/
def cubicOctadC0SignedGram (E F : Octad) (hEF : OctadPairAdmissible E F) (H : Octad) : Scalar :=
  cubicOctadPointGram (octadDiamond E F hEF) H *
    (if hHE : OctadPairAdmissible H E then
      if hHF : OctadPairAdmissible H F then
        16 * cubicOctadQuadrilateralWeight H E F hHE hHF hEF else 0 else 0)

theorem cubicOctadC0Gram_value (E F : Octad) (hEF : OctadPairAdmissible E F) (H : Octad) :
    cubicOctadPointGram (octadDiamond E F hEF) H =
      ((if (E.val ∩ F.val).card = 4 then
        (H.val ∩ E.val).card + (H.val ∩ F.val).card - 2 * (H.val ∩ E.val ∩ F.val).card
        else 8 - ((H.val ∩ E.val).card + (H.val ∩ F.val).card) : ℕ) : Scalar) / 2 - 5 / 4 := by
  rw [cubicOctadPointGram_eq, Finset.inter_comm, cubicOctadDiamond_intersection]

theorem cubicOctadC0SignedGram_zero (E F : Octad) (hEF : OctadPairAdmissible E F) (H : Octad)
    (h : ¬ OctadPairAdmissible H E ∨ ¬ OctadPairAdmissible H F) :
    cubicOctadC0SignedGram E F hEF H = 0 := by
  rcases h with he | hf
  · simp [cubicOctadC0SignedGram, he]
  · by_cases he : OctadPairAdmissible H E <;> simp [cubicOctadC0SignedGram, he, hf]

/-- Four refined all-sextet values, uniformly on actual common neighbors. -/
theorem cubicOctadC0SignedGram_four (E F H : Octad)
    (hEF : (E.val ∩ F.val).card = 4) (hHE : (H.val ∩ E.val).card = 4)
    (hHF : (H.val ∩ F.val).card = 4) :
    cubicOctadC0SignedGram E F (Or.inl hEF) H =
      if (H.val ∩ E.val ∩ F.val).card = 0 then (11 / 4 : Scalar)
      else if (H.val ∩ E.val ∩ F.val).card = 2 then 3 / 4
      else if (H.val ∩ E.val ∩ F.val).card = 3 then 1 / 4 else -5 / 4 := by
  unfold cubicOctadC0SignedGram
  rw [dif_pos (show OctadPairAdmissible H E from Or.inl hHE), dif_pos (show OctadPairAdmissible H F from Or.inl hHF), cubicQuadrilateral_weight_four H E F hHE hHF hEF,
    cubicOctadC0Gram_value]
  rcases cubicCommonNeighbor_actual_levels H E F hHE hHF hEF with hu | hu | hu | hu <;>
    norm_num [← Finset.inter_assoc, hEF, hHE, hHF, hu, parkerScalarSign]
  all_goals decide

/-- Exactly one empty pair: the Gram coefficient is3/4 in both external phases. -/
theorem cubicOctadC0SignedGram_one_empty (E F H : Octad)
    (hEF : OctadPairAdmissible E F)
    (h : ((H.val ∩ E.val).card = 0 ∧ (H.val ∩ F.val).card = 4) ∨
      ((H.val ∩ E.val).card = 4 ∧ (H.val ∩ F.val).card = 0)) :
    cubicOctadC0SignedGram E F hEF H = 9 / 4 := by
  have he : OctadPairAdmissible H E := by
    rcases h with ⟨a,b⟩ | ⟨a,b⟩
    · exact Or.inr a
    · exact Or.inl a
  have hf : OctadPairAdmissible H F := by
    rcases h with ⟨a,b⟩ | ⟨a,b⟩
    · exact Or.inl b
    · exact Or.inr b
  unfold cubicOctadC0SignedGram
  rw [dif_pos he, dif_pos hf, cubicQuadrilateral_weight_one_empty H E F he hf hEF h,
    cubicOctadC0Gram_value]
  have hu : (H.val ∩ E.val ∩ F.val).card = 0 :=
    cubicTripleIntersection_zero_of_pair H E F (by rcases h with ⟨a,b⟩ | ⟨a,b⟩ <;> omega)
  rcases h with ⟨he0,hf4⟩ | ⟨he4,hf0⟩ <;> rcases hEF with h4 | h0 <;>
    norm_num [← Finset.inter_assoc, *, show (0 : ℕ) ≠ 4 by decide]

theorem cubicOctadC0SignedGram_both_zero_four (E F H : Octad)
    (hEF : (E.val ∩ F.val).card = 4) (hHE : (H.val ∩ E.val).card = 0)
    (hHF : (H.val ∩ F.val).card = 0) :
    cubicOctadC0SignedGram E F (Or.inl hEF) H = 15 / 4 := by
  unfold cubicOctadC0SignedGram
  rw [dif_pos (show OctadPairAdmissible H E from Or.inr hHE), dif_pos (show OctadPairAdmissible H F from Or.inr hHF), cubicQuadrilateral_weight_zero_zero_four H E F hHE hHF hEF,
    cubicOctadC0Gram_value]
  norm_num [← Finset.inter_assoc, hEF, hHE, hHF]

theorem cubicOctadC0SignedGram_both_four_zero (E F H : Octad)
    (hEF : (E.val ∩ F.val).card = 0) (hHE : (H.val ∩ E.val).card = 4)
    (hHF : (H.val ∩ F.val).card = 4) :
    cubicOctadC0SignedGram E F (Or.inr hEF) H = 15 / 4 := by
  unfold cubicOctadC0SignedGram
  rw [dif_pos (show OctadPairAdmissible H E from Or.inl hHE), dif_pos (show OctadPairAdmissible H F from Or.inl hHF), cubicQuadrilateral_weight_four_four_zero H E F hHE hHF hEF,
    cubicOctadC0Gram_value]
  norm_num [← Finset.inter_assoc, hEF, hHE, hHF]

theorem cubicOctadC0SignedGram_both_zero_zero (E F H : Octad)
    (hEF : (E.val ∩ F.val).card = 0) (hHE : (H.val ∩ E.val).card = 0)
    (hHF : (H.val ∩ F.val).card = 0) :
    cubicOctadC0SignedGram E F (Or.inr hEF) H = 99 / 4 := by
  unfold cubicOctadC0SignedGram
  rw [dif_pos (show OctadPairAdmissible H E from Or.inr hHE), dif_pos (show OctadPairAdmissible H F from Or.inr hHF), cubicQuadrilateral_weight_zero_zero_zero H E F hHE hHF hEF,
    cubicOctadC0Gram_value]
  norm_num [← Finset.inter_assoc, hEF, hHE, hHF]

end Atlas.Fischer
