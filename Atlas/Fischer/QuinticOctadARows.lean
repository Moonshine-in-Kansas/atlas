import Atlas.Fischer.QuinticOctadUUU

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem coordinateCubic_sextet_star (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E) :
    star (coordinateCubic (.inr D) (.inr E) (.inr F)) =
      coordinateCubic (.inr D) (.inr E) (.inr F) := by
  classical
  rw [coordinateCubic_octad_product, octadBasisProduct_octad_apply, if_pos hF]
  simp only [star_star, star_mul, star_div₀, star_one, star_ofNat, parkerScalarSign_star]
  ring

theorem coordinateCubic_trio_star (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E + golayOne) :
    star (coordinateCubic (.inr D) (.inr E) (.inr F)) =
      -coordinateCubic (.inr D) (.inr E) (.inr F) := by
  classical
  have hn : octadWord F ≠ octadWord D + octadWord E := by
    intro he
    have h4 := octadWord_sum_weight F D E he
    have h0 := octadWord_complementary_sum_weight F D E hF
    omega
  rw [coordinateCubic_octad_product, octadBasisProduct_octad_apply, if_neg hn, if_pos hF]
  simp only [star_star, star_mul, star_div₀, star_ofNat, parkerScalarSign_star, theta_conjugate, star_neg, neg_neg]
  ring

theorem quinticOctad_A_sextet (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E) :
    quinticOctadBlockUUU_WWW D E F =
      (47 / 16 : Scalar) * coordinateCubic (.inr D) (.inr E) (.inr F) := by
  rw [quinticOctadBlockUUU_WWW_collapse, coordinateCubic_incidence_triple_sextet D E F hF,
    coordinateCubic_sextet_star D E F hF]
  ring

theorem quinticOctad_A_trio (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E + golayOne) :
    quinticOctadBlockUUU_WWW D E F =
      (49 / 16 : Scalar) * coordinateCubic (.inr D) (.inr E) (.inr F) := by
  rw [quinticOctadBlockUUU_WWW_collapse, coordinateCubic_incidence_triple_trio D E F hF,
    coordinateCubic_trio_star D E F hF]
  ring

end Atlas.Fischer
