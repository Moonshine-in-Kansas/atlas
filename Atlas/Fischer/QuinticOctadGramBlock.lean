import Atlas.Fischer.QuinticOctadBlocks
import Atlas.Fischer.CubicOctadPointGram

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- An actual mixed point/octet block is the square of a retained Gram pairing. -/
theorem quinticOctadBlockUWW_WUW_gram (D E F : Octad) :
    quinticOctadBlockUWW_WUW D E F =
      cubicOctadPointGram D E ^ 2 * coordinateCubic (.inr D) (.inr E) (.inr F) := by
  have hm (B : Octad) (i : Omega) (A : Octad) :
      coordinateCubic (.inr B) (.inl i) (.inr A) =
        if B = A then cubicPointOctadIncidence i B / 16 else 0 := by
    rw [coordinateCubic_swap_first, coordinateCubic_point_octads]
  unfold quinticOctadBlockUWW_WUW coordinateQuinticTerm coordinateQuinticCubicProduct
    cubicOctadPointGram
  rw [pow_two]
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp only [coordinateCubic_point_octads, hm, inverseCoordinateMetric, coordinateWeight]
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, inv_div, inv_one, mul_one]
  simp only [apply_ite star, star_div₀, star_ofNat, star_zero, cubicPointOctadIncidence_star,
    mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro b hb
  ring

end Atlas.Fischer
