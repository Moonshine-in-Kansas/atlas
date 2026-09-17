import Atlas.Fischer.QuinticOctadBlockSymmetry
import Atlas.Fischer.CubicOctadPointGram

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Literal three-cubic neighbor contraction with one fixed external octad. -/
def cubicOctadTriangleNeighbor (D E F H : Octad) : Scalar :=
  ∑ B : Octad, ∑ C : Octad,
    star (coordinateCubic (.inr D) (.inr B) (.inr C)) *
      coordinateCubic (.inr H) (.inr B) (.inr E) *
      coordinateCubic (.inr H) (.inr C) (.inr F)

/-- One actual C0 block becomes a Gram-weighted triangle-neighbor sum. -/
theorem quinticOctadBlockUWW_WWW_neighbors (D E F : Octad) :
    quinticOctadBlockUWW_WWW D E F =
      ∑ H : Octad, cubicOctadPointGram D H * cubicOctadTriangleNeighbor D E F H := by
  have hm (B : Octad) (i : Omega) (A : Octad) :
      coordinateCubic (.inr B) (.inl i) (.inr A) =
        if B = A then cubicPointOctadIncidence i B / 16 else 0 := by
    rw [coordinateCubic_swap_first, coordinateCubic_point_octads]
  unfold quinticOctadBlockUWW_WWW coordinateQuinticTerm coordinateQuinticCubicProduct
    cubicOctadPointGram cubicOctadTriangleNeighbor
  simp only [coordinateCubic_point_octads, hm, inverseCoordinateMetric, coordinateWeight]
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, inv_div, inv_one, mul_one]
  simp only [apply_ite star, star_div₀, star_ofNat, star_zero, cubicPointOctadIncidence_star,
    mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro H hH
  rw [sum_three_left_rotate]
  apply Finset.sum_congr rfl
  intro B hB
  apply Finset.sum_congr rfl
  intro C hC
  apply Finset.sum_congr rfl
  intro i hi
  rw [coordinateCubic_swap_first (.inr B) (.inr H) (.inr E),
    coordinateCubic_swap_first (.inr C) (.inr H) (.inr F)]
  ring

end Atlas.Fischer
