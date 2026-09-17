import Atlas.Fischer.QuinticOctadPairContraction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

/-- The actual source signed sum over the two free Golay octads. -/
def octadContractionSignedSum (D E F : Octad) : ℤ :=
  ∑ G : Octad, ∑ H : Octad, octadContractionPairWeight D E F G H

/-- Exact six-index to two-free-octad contraction, including all invalid configurations. -/
theorem quinticOctadBlockWWW_WWW_signed_sum (D E F : Octad)
    (hDE : octadWord D + octadWord E + octadWord F ∈ allOneCodeLine) :
    16 * quinticOctadBlockWWW_WWW D E F =
      coordinateCubic (.inr D) (.inr E) (.inr F) *
        (octadContractionSignedSum D E F : Scalar) := by
  unfold quinticOctadBlockWWW_WWW coordinateQuinticTerm octadContractionSignedSum
  simp only [inverseCoordinateMetric, coordinateWeight, Rat.cast_one, inv_one, one_mul,
    coordinateQuinticCubicProduct_octad_coefficient, Int.cast_sum]
  calc
    _ = ∑ G : Octad, ∑ H : Octad,
        16 * (∑ J : Octad, ∑ GP : Octad, ∑ HP : Octad, ∑ JP : Octad,
          octadContractionCoefficient D E F G H J GP HP JP) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro G hG
      rw [Finset.mul_sum]
    _ = ∑ G : Octad, ∑ H : Octad,
        coordinateCubic (.inr D) (.inr E) (.inr F) *
          (octadContractionPairWeight D E F G H : Scalar) := by
      apply Finset.sum_congr rfl
      intro G hG
      apply Finset.sum_congr rfl
      intro H hH
      exact octadContractionCoefficient_sum_weight D E F G H hDE
    _ = _ := by simp only [Finset.mul_sum]

/-- The pure-octad block is the actual cubic coefficient times its derived signed sum/16. -/
theorem quinticOctadBlockWWW_WWW_eq_signed_sum (D E F : Octad)
    (hDE : octadWord D + octadWord E + octadWord F ∈ allOneCodeLine) :
    quinticOctadBlockWWW_WWW D E F =
      coordinateCubic (.inr D) (.inr E) (.inr F) *
        (octadContractionSignedSum D E F : Scalar) / 16 := by
  linear_combination quinticOctadBlockWWW_WWW_signed_sum D E F hDE / 16

end Atlas.Fischer
