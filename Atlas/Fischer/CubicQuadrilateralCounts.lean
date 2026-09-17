import Atlas.Fischer.CubicTrioNeighborCounts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Actual ordered octad pairs, with all three prescribed intersections. -/
abbrev CubicQuadrilateralFibre (D : Octad) (a b c : ℕ) :=
  Σ F : CubicOctadIntersectionRow D a, CubicPairIntersectionFibre D F.val b c

/-- The all-four intersection configuration, refined by the actual triple overlap. -/
abbrev CubicQuadrilateralRefinedFibre (D : Octad) (u : ℕ) :=
  Σ F : CubicOctadIntersectionRow D 4, CubicCommonNeighbors D F.val u

abbrev CubicQuadrilateralOneEmptyFibre (D : Octad) :=
  (CubicQuadrilateralFibre D 0 4 4 ⊕ CubicQuadrilateralFibre D 0 4 0) ⊕
  (CubicQuadrilateralFibre D 4 0 4 ⊕ CubicQuadrilateralFibre D 4 0 0)

theorem cubicOctadIntersectionRow_four_card (D : Octad) :
    Nat.card (CubicOctadIntersectionRow D 4) = 280 := by
  rw [cubicOctadIntersectionRow_card]
  exact (octad_intersection_distribution D.val D.property).2.2.1

theorem cubicOctadIntersectionRow_zero_card (D : Octad) :
    Nat.card (CubicOctadIntersectionRow D 0) = 30 := by
  rw [cubicOctadIntersectionRow_card]
  exact (octad_intersection_distribution D.val D.property).1

theorem cubicQuadrilateral_fibre_card (D : Octad) (a b c n : ℕ)
    (h : ∀ F : CubicOctadIntersectionRow D a, Nat.card (CubicPairIntersectionFibre D F.val b c) = n) :
    Nat.card (CubicQuadrilateralFibre D a b c) = Nat.card (CubicOctadIntersectionRow D a) * n := by
  rw [Nat.card_sigma]
  simp_rw [h]
  simp [Nat.card_eq_fintype_card]

theorem cubicQuadrilateral_refined_card (D : Octad) (u n : ℕ)
    (h : ∀ F : CubicOctadIntersectionRow D 4, cubicCommonNeighborCount D F.val u = n) :
    Nat.card (CubicQuadrilateralRefinedFibre D u) = 280 * n := by
  rw [Nat.card_sigma]
  change (∑ F : CubicOctadIntersectionRow D 4, cubicCommonNeighborCount D F.val u) = _
  simp_rw [h]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [← Nat.card_eq_fintype_card,cubicOctadIntersectionRow_four_card]

theorem cubicQuadrilateral_refined_distribution (D : Octad) :
    Nat.card (CubicQuadrilateralRefinedFibre D 0) = 280 ∧
    Nat.card (CubicQuadrilateralRefinedFibre D 2) = 280 * 72 ∧
    Nat.card (CubicQuadrilateralRefinedFibre D 3) = 280 * 64 ∧
    Nat.card (CubicQuadrilateralRefinedFibre D 4) = 280 * 3 := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa using cubicQuadrilateral_refined_card D 0 1 (fun F =>
      (cubicCommonNeighbor_distribution D F.val F.property).1)
  · exact cubicQuadrilateral_refined_card D 2 72 (fun F =>
      (cubicCommonNeighbor_distribution D F.val F.property).2.1)
  · exact cubicQuadrilateral_refined_card D 3 64 (fun F =>
      (cubicCommonNeighbor_distribution D F.val F.property).2.2.1)
  · exact cubicQuadrilateral_refined_card D 4 3 (fun F =>
      (cubicCommonNeighbor_distribution D F.val F.property).2.2.2)

theorem cubicQuadrilateral_remaining_distribution (D : Octad) :
    Nat.card (CubicQuadrilateralFibre D 4 4 0) = 840 ∧
    Nat.card (CubicQuadrilateralOneEmptyFibre D) = 3360 ∧
    Nat.card (CubicQuadrilateralFibre D 0 0 4) = 840 ∧
    Nat.card (CubicQuadrilateralFibre D 0 0 0) = 30 := by
  have h440 : Nat.card (CubicQuadrilateralFibre D 4 4 0) = 280 * 3 := by
    rw [cubicQuadrilateral_fibre_card D 4 4 0 3, cubicOctadIntersectionRow_four_card]
    intro F
    rw [Nat.card_congr (cubicPairIntersectionSwap D F.val 4 0)]
    exact (cubicPairIntersection_four_mixed F.val D (by simpa [Finset.inter_comm] using F.property)).1
  have h044 : Nat.card (CubicQuadrilateralFibre D 0 4 4) = 30 * 28 := by
    rw [cubicQuadrilateral_fibre_card D 0 4 4 28, cubicOctadIntersectionRow_zero_card]
    intro F
    exact cubicPairIntersection_disjoint_bothFour D F.val F.property
  have h040 : Nat.card (CubicQuadrilateralFibre D 0 4 0) = 30 * 28 := by
    rw [cubicQuadrilateral_fibre_card D 0 4 0 28, cubicOctadIntersectionRow_zero_card]
    intro F
    rw [Nat.card_congr (cubicPairIntersectionSwap D F.val 4 0)]
    exact cubicCommonNeighbor_disjoint_pair_twentyEight F.val D (by simpa [Finset.inter_comm] using F.property)
  have h404 : Nat.card (CubicQuadrilateralFibre D 4 0 4) = 280 * 3 := by
    rw [cubicQuadrilateral_fibre_card D 4 0 4 3,cubicOctadIntersectionRow_four_card]
    intro F
    exact (cubicPairIntersection_four_mixed D F.val F.property).1
  have h400 : Nat.card (CubicQuadrilateralFibre D 4 0 0) = 280 * 3 := by
    rw [cubicQuadrilateral_fibre_card D 4 0 0 3,cubicOctadIntersectionRow_four_card]
    intro F
    exact (cubicPairIntersection_four_mixed D F.val F.property).2
  have h004 : Nat.card (CubicQuadrilateralFibre D 0 0 4) = 30 * 28 := by
    rw [cubicQuadrilateral_fibre_card D 0 0 4 28,cubicOctadIntersectionRow_zero_card]
    intro F
    exact cubicCommonNeighbor_disjoint_pair_twentyEight D F.val F.property
  have h000 : Nat.card (CubicQuadrilateralFibre D 0 0 0) = 30 * 1 := by
    rw [cubicQuadrilateral_fibre_card D 0 0 0 1,cubicOctadIntersectionRow_zero_card]
    intro F
    exact cubicPairIntersection_disjoint_bothZero D F.val F.property
  refine ⟨h440,?_,h004,h000⟩
  change Nat.card ((_ ⊕ _) ⊕ (_ ⊕ _)) = _
  rw [Nat.card_sum,Nat.card_sum,Nat.card_sum,h044,h040,h404,h400]

end Atlas.Fischer
