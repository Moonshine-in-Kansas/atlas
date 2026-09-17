import Atlas.Fischer.QuinticOctadContractionSupport

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem octadContractionCoefficient_sum_first (D E F G H : Octad)
    (hGH : OctadPairAdmissible G H) :
    (∑ J : Octad, ∑ GP : Octad, ∑ HP : Octad, ∑ JP : Octad,
      octadContractionCoefficient D E F G H J GP HP JP) =
      ∑ GP : Octad, ∑ HP : Octad, ∑ JP : Octad,
        octadContractionCoefficient D E F G H (octadDiamond G H hGH) GP HP JP := by
  apply Finset.sum_eq_single (octadDiamond G H hGH)
  · intro J hJ hn
    have hz := coordinateCubic_octad_off_diamond G H J hGH hn
    simp only [octadContractionCoefficient, hz, star_zero, zero_mul, Finset.sum_const_zero]
  · simp

/-- Every valid pair contributes the exact derived integer weight; every invalid
pair vanishes by actual cubic support. -/
theorem octadContractionCoefficient_sum_weight (D E F G H : Octad)
    (hDE : octadWord D + octadWord E + octadWord F ∈ allOneCodeLine) :
    16 * (∑ J : Octad, ∑ GP : Octad, ∑ HP : Octad, ∑ JP : Octad,
      octadContractionCoefficient D E F G H J GP HP JP) =
      coordinateCubic (.inr D) (.inr E) (.inr F) *
        (octadContractionPairWeight D E F G H : Scalar) := by
  by_cases hGH : OctadPairAdmissible G H
  · by_cases hDG : OctadPairAdmissible D G
    · by_cases hEH : OctadPairAdmissible E H
      · by_cases hFJ : OctadPairAdmissible F (octadDiamond G H hGH)
        · rw [octadContractionCoefficient_sum D E F G H hGH hDG hEH hFJ]
          simp only [octadContractionPairWeight, dif_pos hGH, dif_pos hDG, dif_pos hEH, dif_pos hFJ]
          have hw := coordinateQuinticCubicProduct_octad_weight D E F G H (octadDiamond G H hGH)
            (octadDiamond D G hDG) (octadDiamond E H hEH)
            (octadDiamond F (octadDiamond G H hGH) hFJ) hDE
            (octadDiamond_triangle_line G H hGH) (octadDiamond_triangle_line D G hDG)
            (octadDiamond_triangle_line E H hEH)
            (octadDiamond_triangle_line F (octadDiamond G H hGH) hFJ)
          rw [coordinateQuinticCubicProduct_octad_coefficient] at hw
          exact hw
        · rw [octadContractionCoefficient_sum_first D E F G H hGH]
          simp only [octadContractionCoefficient,
            coordinateCubic_octad_zero_of_not_admissible F (octadDiamond G H hGH) _ hFJ,
            mul_zero, Finset.sum_const_zero, octadContractionPairWeight,
            dif_pos hGH, dif_pos hDG, dif_pos hEH, dif_neg hFJ, Int.cast_zero]
      · simp only [octadContractionCoefficient,
          coordinateCubic_octad_zero_of_not_admissible E H _ hEH,
          mul_zero, zero_mul, Finset.sum_const_zero, octadContractionPairWeight,
          dif_pos hGH, dif_pos hDG, dif_neg hEH, Int.cast_zero]
    · simp only [octadContractionCoefficient,
        coordinateCubic_octad_zero_of_not_admissible D G _ hDG,
        mul_zero, zero_mul, Finset.sum_const_zero, octadContractionPairWeight,
        dif_pos hGH, dif_neg hDG, Int.cast_zero]
  · simp only [octadContractionCoefficient,
      coordinateCubic_octad_zero_of_not_admissible G H _ hGH,
      star_zero, mul_zero, zero_mul, Finset.sum_const_zero, octadContractionPairWeight,
      dif_neg hGH, Int.cast_zero]

end Atlas.Fischer
