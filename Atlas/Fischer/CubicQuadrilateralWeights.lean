import Atlas.Fischer.CubicQuadrilateralDelta

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem cubicTripleIntersection_zero_of_pair (D F G : Octad)
    (h : (D.val ∩ F.val).card = 0 ∨ (D.val ∩ G.val).card = 0 ∨ (F.val ∩ G.val).card = 0) :
    (D.val ∩ F.val ∩ G.val).card = 0 := by
  have h1 := Finset.card_le_card (Finset.inter_subset_left : D.val ∩ F.val ∩ G.val ⊆ D.val ∩ F.val)
  have h2 : D.val ∩ F.val ∩ G.val ⊆ D.val ∩ G.val := by intro i hi; simp_all
  have h3 : D.val ∩ F.val ∩ G.val ⊆ F.val ∩ G.val := by intro i hi; simp_all
  have h2' := Finset.card_le_card h2
  have h3' := Finset.card_le_card h3
  omega

theorem cubicQuadrilateral_weight_four (D F G : Octad)
    (hDF : (D.val ∩ F.val).card = 4) (hDG : (D.val ∩ G.val).card = 4)
    (hFG : (F.val ∩ G.val).card = 4) :
    16 * cubicOctadQuadrilateralWeight D F G (Or.inl hDF) (Or.inl hDG) (Or.inl hFG) =
      parkerScalarSign ((D.val ∩ F.val ∩ G.val).card : ParkerBit) := by
  rw [cubicOctadQuadrilateralWeight_formula,cubicQuadrilateral_delta D F G _ _ (Or.inl hFG)]
  simp [octadDelta,hDF,hDG,hFG]

 theorem cubicQuadrilateral_weight_four_four_zero (D F G : Octad)
    (hDF : (D.val ∩ F.val).card = 4) (hDG : (D.val ∩ G.val).card = 4)
    (hFG : (F.val ∩ G.val).card = 0) :
    16 * cubicOctadQuadrilateralWeight D F G (Or.inl hDF) (Or.inl hDG) (Or.inr hFG) = -3 := by
  rw [cubicOctadQuadrilateralWeight_formula,cubicQuadrilateral_delta D F G _ _ (Or.inr hFG),
    cubicTripleIntersection_zero_of_pair D F G (Or.inr (Or.inr hFG))]
  norm_num [octadDelta,hDF,hDG,hFG,parkerScalarSign,← pow_two,theta_sq]

 theorem cubicQuadrilateral_weight_one_empty (D F G : Octad)
    (hDF : OctadPairAdmissible D F) (hDG : OctadPairAdmissible D G)
    (hFG : OctadPairAdmissible F G)
    (h : ((D.val ∩ F.val).card = 0 ∧ (D.val ∩ G.val).card = 4) ∨
      ((D.val ∩ F.val).card = 4 ∧ (D.val ∩ G.val).card = 0)) :
    16 * cubicOctadQuadrilateralWeight D F G hDF hDG hFG = 3 := by
  rw [cubicOctadQuadrilateralWeight_formula,cubicQuadrilateral_delta D F G hDF hDG hFG]
  have hz := cubicTripleIntersection_zero_of_pair D F G (by omega)
  rw [hz]
  rcases h with ⟨hf,hg⟩ | ⟨hf,hg⟩ <;> rcases hFG with hk | hk <;>
    norm_num [octadDelta,hf,hg,hk,parkerScalarSign,theta_conjugate,← pow_two,theta_sq]

 theorem cubicQuadrilateral_weight_zero_zero_four (D F G : Octad)
    (hDF : (D.val ∩ F.val).card = 0) (hDG : (D.val ∩ G.val).card = 0)
    (hFG : (F.val ∩ G.val).card = 4) :
    16 * cubicOctadQuadrilateralWeight D F G (Or.inr hDF) (Or.inr hDG) (Or.inl hFG) = -3 := by
  rw [cubicOctadQuadrilateralWeight_formula,cubicQuadrilateral_delta D F G _ _ (Or.inl hFG),
    cubicTripleIntersection_zero_of_pair D F G (Or.inl hDF)]
  norm_num [octadDelta,hDF,hDG,hFG,parkerScalarSign,theta_conjugate,← pow_two,theta_sq]

 theorem cubicQuadrilateral_weight_zero_zero_zero (D F G : Octad)
    (hDF : (D.val ∩ F.val).card = 0) (hDG : (D.val ∩ G.val).card = 0)
    (hFG : (F.val ∩ G.val).card = 0) :
    16 * cubicOctadQuadrilateralWeight D F G (Or.inr hDF) (Or.inr hDG) (Or.inr hFG) = 9 := by
  rw [cubicOctadQuadrilateralWeight_formula,cubicQuadrilateral_delta D F G _ _ (Or.inr hFG),
    cubicTripleIntersection_zero_of_pair D F G (Or.inl hDF)]
  norm_num [octadDelta,hDF,hDG,hFG,parkerScalarSign,theta_conjugate]
  linear_combination (theta ^ 2 - 3) * theta_sq

end Atlas.Fischer
