import Atlas.Fischer.QuinticPointOctadBlocks

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The actual four-triangle network, with both conjugated internal vertices retained. -/
def cubicOctadQuadrilateralNetwork (D I : Octad) : Scalar :=
  ∑ J : Octad, ∑ K : Octad, ∑ B : Octad, ∑ C : Octad,
    star (coordinateCubic (.inr I) (.inr J) (.inr K)) *
    star (coordinateCubic (.inr I) (.inr B) (.inr C)) *
    coordinateCubic (.inr D) (.inr B) (.inr J) *
    coordinateCubic (.inr D) (.inr C) (.inr K)

/-- Collapsing the external point edge gives the exact signed network on actual octads. -/
theorem quinticPointOctadWWW_WWW_network (p : Omega) (D : Octad) :
    quinticPointOctadWWW_WWW p D =
      (1 / 16 : Scalar) * ∑ I : Octad,
        cubicPointOctadIncidence p I * cubicOctadQuadrilateralNetwork D I := by
  unfold quinticPointOctadWWW_WWW coordinateQuinticTerm coordinateQuinticCubicProduct
    cubicOctadQuadrilateralNetwork
  simp only [coordinateCubic_octads_point, inverseCoordinateMetric, coordinateWeight]
  norm_num only [Rat.cast_one, inv_one, one_mul, mul_one]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro K hK
  apply Finset.sum_congr rfl
  intro B hB
  apply Finset.sum_congr rfl
  intro C hC
  rw [coordinateCubic_swap_last (.inr B) (.inr J) (.inr D),
    coordinateCubic_swap_first (.inr B) (.inr D) (.inr J),
    coordinateCubic_swap_last (.inr C) (.inr K) (.inr D),
    coordinateCubic_swap_first (.inr C) (.inr D) (.inr K)]
  ring

end Atlas.Fischer
