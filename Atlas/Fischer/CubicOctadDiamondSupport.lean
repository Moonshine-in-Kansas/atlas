import Atlas.Fischer.OctadDiamond
import Atlas.Fischer.CubicSliceOctadRows

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem octadDiamond_eq_of_triangle (D E F : Octad) (h : OctadPairAdmissible D E)
    (hF : octadWord F = octadWord D + octadWord E ∨
      octadWord F = octadWord D + octadWord E + golayOne) :
    F = octadDiamond D E h := by
  rcases hF with hF | hF
  · have h4 : (D.val ∩ E.val).card = 4 := by
      simpa only [signedOctadIntersection, signedOctadSupport_canonical] using
        octadWord_sum_weight F D E hF
    rw [octadDiamond, dif_pos h4]
    apply octadWord_injective
    rw [cubicSextetCompletion_word]
    exact hF
  · have h0 : (D.val ∩ E.val).card = 0 := by
      simpa only [signedOctadIntersection, signedOctadSupport_canonical] using
        octadWord_complementary_sum_weight F D E hF
    have h4 : (D.val ∩ E.val).card ≠ 4 := by omega
    rw [octadDiamond, dif_neg h4]
    apply octadWord_injective
    rw [cubicTrioCompletion_word]
    exact hF

theorem coordinateCubic_octad_nonzero_triangle (D E F : Octad)
    (h : coordinateCubic (.inr D) (.inr E) (.inr F) ≠ 0) :
    octadWord F = octadWord D + octadWord E ∨
      octadWord F = octadWord D + octadWord E + golayOne := by
  rw [coordinateCubic_octad_product, octadBasisProduct_octad_apply] at h
  by_cases h0 : octadWord F = octadWord D + octadWord E
  · exact Or.inl h0
  · by_cases h1 : octadWord F = octadWord D + octadWord E + golayOne
    · exact Or.inr h1
    · simp only [if_neg h0, if_neg h1, star_zero, ne_eq, not_true_eq_false] at h

theorem coordinateCubic_octad_zero_of_not_admissible (D E F : Octad)
    (h : ¬ OctadPairAdmissible D E) :
    coordinateCubic (.inr D) (.inr E) (.inr F) = 0 := by
  by_contra hn
  exact h (octadPairAdmissible_of_triangle D E F
    (coordinateCubic_octad_nonzero_triangle D E F hn))

theorem coordinateCubic_octad_delta (D E F : Octad) (h : OctadPairAdmissible D E) :
    coordinateCubic (.inr D) (.inr E) (.inr F) =
      if F = octadDiamond D E h then
        coordinateCubic (.inr D) (.inr E) (.inr (octadDiamond D E h)) else 0 := by
  by_cases he : F = octadDiamond D E h
  · subst F
    simp only [ite_true]
  · rw [if_neg he]
    by_contra hn
    exact he (octadDiamond_eq_of_triangle D E F h
      (coordinateCubic_octad_nonzero_triangle D E F hn))

end Atlas.Fischer
