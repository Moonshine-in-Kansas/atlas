import Atlas.Fischer.QuinticPointOctadBlocks
import Atlas.Fischer.CubicOctadUnsignedNeighbors

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The WUW/WWW block is the actual unsigned neighboring-octad contraction. -/
theorem quinticPointOctadWUW_WWW_neighbors (p : Omega) (D : Octad) :
    quinticPointOctadWUW_WWW p D =
      cubicOctadUnsignedNeighborContribution p D / 32 := by
  have hm (b : Octad) (j : Omega) (E : Octad) :
      coordinateCubic (.inr b) (.inl j) (.inr E) =
        if b = E then cubicPointOctadIncidence j b / 16 else 0 := by
    rw [coordinateCubic_swap_first, coordinateCubic_point_octads]
  unfold quinticPointOctadWUW_WWW coordinateQuinticTerm coordinateQuinticCubicProduct
  simp only [coordinateCubic_octads_point, hm, inverseCoordinateMetric, coordinateWeight]
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, inv_div, inv_one, mul_one]
  simp (maxSteps := 100000) only [apply_ite star, star_div₀, star_ofNat, star_zero,
    cubicPointOctadIncidence_star, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  unfold cubicOctadUnsignedNeighborContribution cubicOctadPointGram
  simp only [coordinateCubic_point_octads, ite_true,
    inverseCoordinateMetric, coordinateWeight]
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, inv_div, inv_one, mul_one]
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro E hE
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro F hF
  rw [coordinateCubic_swap_first (.inr E) (.inr D) (.inr F),
    coordinateCubic_swap_first (.inr F) (.inr E) (.inr D),
    coordinateCubic_swap_last (.inr E) (.inr F) (.inr D),
    coordinateCubic_swap_first (.inr E) (.inr D) (.inr F)]
  ring

/-- Exact unsigned-neighbor ratio in one ordered internal block. -/
theorem quinticPointOctadWUW_WWW_ratio (p : Omega) (D : Octad) :
    quinticPointOctadWUW_WWW p D =
      (if p ∈ D.val then (215 / 8 : Scalar) else 225 / 8) *
        coordinateCubic (.inl p) (.inr D) (.inr D) := by
  rw [quinticPointOctadWUW_WWW_neighbors, cubicOctadUnsignedNeighborContribution_eq,
    coordinateCubic_point_octads]
  by_cases hp : p ∈ D.val <;> simp only [hp, ite_true, ite_false] <;> ring

end Atlas.Fischer
