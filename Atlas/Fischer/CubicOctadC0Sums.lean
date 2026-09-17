import Atlas.Fischer.CubicOctadC0Indicators

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

private theorem indicator_card {A : Type} [Fintype A] (P : A → Prop) :
    (∑ a : A, if P a then (1 : Scalar) else 0) = (Nat.card (Subtype P) : Scalar) := by
  rw [← Finset.sum_filter, Finset.sum_const]
  simp only [nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem cubicC0CommonIndicator_sum (E F : Octad) (u : ℕ) :
    (∑ H : Octad, if cubicC0CommonIndicator E F u H then (1 : Scalar) else 0) =
      (cubicCommonNeighborCount E F u : Scalar) := by
  rw [indicator_card]
  congr 1
  unfold cubicCommonNeighborCount
  apply Nat.card_congr
  exact Equiv.subtypeEquiv (Equiv.refl Octad) (by
    intro H
    simp only [cubicC0CommonIndicator, Equiv.refl_apply, Finset.inter_comm,
      Finset.inter_left_comm, Finset.inter_assoc])

theorem cubicC0PairIndicator_sum (E F : Octad) (a b : ℕ) :
    (∑ H : Octad, if cubicC0PairIndicator E F a b H then (1 : Scalar) else 0) =
      (Nat.card (CubicPairIntersectionFibre E F a b) : Scalar) := by
  rw [indicator_card]
  congr 1
  apply Nat.card_congr
  exact Equiv.subtypeEquiv (Equiv.refl Octad) (by
    intro H
    simp only [cubicC0PairIndicator, Equiv.refl_apply, Finset.inter_comm])

/-- Actual fixed-sextet signed Gram total; all seven fiber counts are proved upstream. -/
theorem cubicOctadC0SignedGram_sum_four (E F : Octad) (hEF : (E.val ∩ F.val).card = 4) :
    (∑ H : Octad, cubicOctadC0SignedGram E F (Or.inl hEF) H) = 375 / 4 := by
  simp_rw [cubicOctadC0SignedGram_four_indicators E F _ hEF]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    cubicC0CommonIndicator_sum, cubicC0PairIndicator_sum]
  obtain ⟨h0,h2,h3,h4⟩ := cubicCommonNeighbor_distribution E F hEF
  have hm := cubicPairIntersection_four_mixed E F hEF
  have hr : Nat.card (CubicPairIntersectionFibre E F 4 0) = 3 := by
    rw [Nat.card_congr (cubicPairIntersectionSwap E F 4 0)]
    exact (cubicPairIntersection_four_mixed F E (by simpa [Finset.inter_comm] using hEF)).1
  rw [h0,h2,h3,h4,hm.1,hm.2,hr]
  norm_num

/-- Actual fixed-trio signed Gram total; no new enumeration is used. -/
theorem cubicOctadC0SignedGram_sum_zero (E F : Octad) (hEF : (E.val ∩ F.val).card = 0) :
    (∑ H : Octad, cubicOctadC0SignedGram E F (Or.inr hEF) H) = 1023 / 4 := by
  simp_rw [cubicOctadC0SignedGram_zero_indicators E F _ hEF]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, cubicC0PairIndicator_sum]
  have hr : Nat.card (CubicPairIntersectionFibre E F 4 0) = 28 := by
    rw [Nat.card_congr (cubicPairIntersectionSwap E F 4 0)]
    exact cubicCommonNeighbor_disjoint_pair_twentyEight F E (by simpa [Finset.inter_comm] using hEF)
  rw [cubicPairIntersection_disjoint_bothFour E F hEF,
    cubicCommonNeighbor_disjoint_pair_twentyEight E F hEF, hr,
    cubicPairIntersection_disjoint_bothZero E F hEF]
  norm_num

end Atlas.Fischer
