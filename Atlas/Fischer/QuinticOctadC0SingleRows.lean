import Atlas.Fischer.CubicOctadC0Sums
import Atlas.Fischer.CubicOctadTriangleNorm
import Atlas.Fischer.QuinticOctadUUU

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The exact factor16 relating the actual C0 block to its signed Gram sum. -/
theorem quinticOctadBlockUWW_WWW_signedGram (D E F : Octad)
    (hEF : OctadPairAdmissible E F) (hD : D = octadDiamond E F hEF) :
    16 * (star (coordinateCubic (.inr D) (.inr E) (.inr F)) *
      quinticOctadBlockUWW_WWW D E F) =
      ∑ H : Octad, cubicOctadC0SignedGram E F hEF H := by
  rw [quinticOctadBlockUWW_WWW_weights D E F hEF hD, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H hH
  unfold cubicOctadC0SignedGram
  rw [hD]
  by_cases he : OctadPairAdmissible H E <;> by_cases hf : OctadPairAdmissible H F <;>
    simp [he, hf] <;> ring

theorem quinticOctad_C0_single_sextet (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E) :
    quinticOctadBlockUWW_WWW D E F =
      (375 / 16 : Scalar) * coordinateCubic (.inr D) (.inr E) (.inr F) := by
  have hr := octadTriangle_rotations D E F 0 (by simpa only [add_zero] using hF)
  have hDword : octadWord D = octadWord E + octadWord F := by simpa only [add_zero] using hr.1
  have hEF : (E.val ∩ F.val).card = 4 := by
    simpa only [signedOctadIntersection, signedOctadSupport_canonical] using
      octadWord_sum_weight D E F hDword
  have hD := octadDiamond_eq_of_triangle E F D (Or.inl hEF) (Or.inl hDword)
  have hw := quinticOctadBlockUWW_WWW_signedGram D E F (Or.inl hEF) hD
  rw [cubicOctadC0SignedGram_sum_four E F hEF] at hw
  have hn := coordinateCubic_sextet_norm D E F hF
  have hs : star (coordinateCubic (.inr D) (.inr E) (.inr F)) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hn
    norm_num at hn
  apply mul_left_cancel₀ hs
  linear_combination hw / 16 - (375 / 16 : Scalar) * hn

theorem quinticOctad_C0_single_trio (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E + golayOne) :
    quinticOctadBlockUWW_WWW D E F =
      (341 / 16 : Scalar) * coordinateCubic (.inr D) (.inr E) (.inr F) := by
  have hr := octadTriangle_rotations D E F golayOne hF
  have hEF : (E.val ∩ F.val).card = 0 := by
    simpa only [signedOctadIntersection, signedOctadSupport_canonical] using
      octadWord_complementary_sum_weight D E F hr.1
  have hD := octadDiamond_eq_of_triangle E F D (Or.inr hEF) (Or.inr hr.1)
  have hw := quinticOctadBlockUWW_WWW_signedGram D E F (Or.inr hEF) hD
  rw [cubicOctadC0SignedGram_sum_zero E F hEF] at hw
  have hn := coordinateCubic_trio_norm D E F hF
  have hs : star (coordinateCubic (.inr D) (.inr E) (.inr F)) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hn
    norm_num at hn
  apply mul_left_cancel₀ hs
  linear_combination hw / 16 - (341 / 16 : Scalar) * hn

end Atlas.Fischer
