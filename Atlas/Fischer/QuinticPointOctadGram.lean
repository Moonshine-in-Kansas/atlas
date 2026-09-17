import Atlas.Fischer.QuinticPointOctadBlocks
import Atlas.Fischer.CubicOctadPointGram

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The two point slots in this actual contraction are precisely the square
of the retained point-coordinate Gram pairing. -/
theorem quinticPointOctadWUW_WWU_gram (p : Omega) (D : Octad) :
    quinticPointOctadWUW_WWU p D =
      coordinateCubic (.inl p) (.inr D) (.inr D) * cubicOctadPointGram D D ^ 2 := by
  have hm (b : Octad) (j : Omega) (E : Octad) :
      coordinateCubic (.inr b) (.inl j) (.inr E) =
        if b = E then cubicPointOctadIncidence j b / 16 else 0 := by
    rw [coordinateCubic_swap_first, coordinateCubic_point_octads]
  unfold quinticPointOctadWUW_WWU coordinateQuinticTerm coordinateQuinticCubicProduct
    cubicOctadPointGram
  rw [pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum]
  simp only [coordinateCubic_point_octads, coordinateCubic_octads_point, hm,
    inverseCoordinateMetric, coordinateWeight]
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, inv_div, inv_one, mul_one]
  simp (maxSteps := 100000) only [apply_ite star, star_div₀, star_ofNat, star_zero,
    cubicPointOctadIncidence_star, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem quinticPointOctadWUW_WWU_ratio (p : Omega) (D : Octad) :
    quinticPointOctadWUW_WWU p D =
      (121 / 16 : Scalar) * coordinateCubic (.inl p) (.inr D) (.inr D) := by
  rw [quinticPointOctadWUW_WWU_gram, cubicOctadPointGram_self]
  ring

end Atlas.Fischer
