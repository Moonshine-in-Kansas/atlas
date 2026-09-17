import Atlas.Fischer.QuinticOctadBlockSymmetry
import Atlas.Fischer.QuinticOctadGramBlock
import Atlas.Fischer.QuinticOctadUUU

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Every Gram-square occurrence in the actual six-block B contribution. -/
theorem quinticOctadB_gram (D E F : Octad) :
    quinticOctadB D E F =
      2 * (cubicOctadPointGram D E ^ 2 + cubicOctadPointGram D F ^ 2 +
        cubicOctadPointGram E F ^ 2) * coordinateCubic (.inr D) (.inr E) (.inr F) := by
  unfold quinticOctadB
  rw [quinticOctadBlockWUW_UWW_transpose, quinticOctadBlockWWU_UWW_transpose,
    quinticOctadBlockWWU_WUW_transpose, quinticOctadBlockUWW_WWU_permute,
    quinticOctadBlockWUW_WWU_permute]
  rw [quinticOctadBlockUWW_WUW_gram, quinticOctadBlockUWW_WUW_gram,
    quinticOctadBlockUWW_WUW_gram]
  rw [coordinateCubic_swap_last (.inr D) (.inr F) (.inr E),
    coordinateCubic_swap_last (.inr E) (.inr F) (.inr D),
    coordinateCubic_swap_first (.inr E) (.inr D) (.inr F)]
  ring

theorem cubicOctadPointGram_sextet (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E) :
    cubicOctadPointGram D E = 3 / 4 := by
  apply cubicOctadPointGram_four
  simpa only [signedOctadIntersection, signedOctadSupport_canonical] using
    octadWord_sum_weight F D E hF

theorem cubicOctadPointGram_trio (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E + golayOne) :
    cubicOctadPointGram D E = -5 / 4 := by
  apply cubicOctadPointGram_zero
  simpa only [signedOctadIntersection, signedOctadSupport_canonical] using
    octadWord_complementary_sum_weight F D E hF

theorem quinticOctad_B_sextet (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E) :
    quinticOctadB D E F =
      (54 / 16 : Scalar) * coordinateCubic (.inr D) (.inr E) (.inr F) := by
  have hr := octadTriangle_rotations D E F 0 (by simpa only [add_zero] using hF)
  have hD : octadWord D = octadWord E + octadWord F := by simpa only [add_zero] using hr.1
  have hE : octadWord E = octadWord D + octadWord F := by simpa only [add_zero] using hr.2
  rw [quinticOctadB_gram, cubicOctadPointGram_sextet D E F hF,
    cubicOctadPointGram_sextet D F E hE, cubicOctadPointGram_sextet E F D hD]
  ring

theorem quinticOctad_B_trio (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E + golayOne) :
    quinticOctadB D E F =
      (150 / 16 : Scalar) * coordinateCubic (.inr D) (.inr E) (.inr F) := by
  have hr := octadTriangle_rotations D E F golayOne hF
  rw [quinticOctadB_gram, cubicOctadPointGram_trio D E F hF,
    cubicOctadPointGram_trio D F E hr.2, cubicOctadPointGram_trio E F D hr.1]
  ring

end Atlas.Fischer
