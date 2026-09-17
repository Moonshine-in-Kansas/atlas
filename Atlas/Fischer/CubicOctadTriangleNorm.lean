import Atlas.Fischer.CubicOctadDiamondSupport

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

theorem coordinateCubic_triangle_norm (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E ∨
      octadWord F = octadWord D + octadWord E + golayOne) :
    coordinateCubic (.inr D) (.inr E) (.inr F) *
      star (coordinateCubic (.inr D) (.inr E) (.inr F)) =
      if (D.val ∩ E.val).card = 4 then (1 / 4 : Scalar) else 3 / 4 := by
  classical
  have ha := octadPairAdmissible_of_triangle D E F hF
  have hf := octadDiamond_eq_of_triangle D E F ha hF
  have hs : (∑ X : Octad, coordinateCubic (.inr D) (.inr E) (.inr X) *
      star (coordinateCubic (.inr D) (.inr E) (.inr X))) =
      coordinateCubic (.inr D) (.inr E) (.inr F) *
        star (coordinateCubic (.inr D) (.inr E) (.inr F)) := by
    apply Finset.sum_eq_single F
    · intro X hX hXF
      have hx : X ≠ octadDiamond D E ha := by simpa only [← hf] using hXF
      rw [coordinateCubic_octad_delta D E X ha, if_neg hx, zero_mul]
    · simp
  rw [← hs, coordinateCubic_octad_row_norm]
  rcases ha with h4 | h0
  · simp [h4]
  · have h4 : (D.val ∩ E.val).card ≠ 4 := by omega
    simp [h4, h0]

theorem coordinateCubic_sextet_norm (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E) :
    coordinateCubic (.inr D) (.inr E) (.inr F) *
      star (coordinateCubic (.inr D) (.inr E) (.inr F)) = 1 / 4 := by
  have h4 : (D.val ∩ E.val).card = 4 := by
    simpa only [signedOctadIntersection, signedOctadSupport_canonical] using
      octadWord_sum_weight F D E hF
  rw [coordinateCubic_triangle_norm D E F (Or.inl hF), if_pos h4]

theorem coordinateCubic_trio_norm (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E + golayOne) :
    coordinateCubic (.inr D) (.inr E) (.inr F) *
      star (coordinateCubic (.inr D) (.inr E) (.inr F)) = 3 / 4 := by
  have h0 : (D.val ∩ E.val).card = 0 := by
    simpa only [signedOctadIntersection, signedOctadSupport_canonical] using
      octadWord_complementary_sum_weight F D E hF
  have h4 : (D.val ∩ E.val).card ≠ 4 := by omega
  rw [coordinateCubic_triangle_norm D E F (Or.inr hF), if_neg h4]

end Atlas.Fischer
