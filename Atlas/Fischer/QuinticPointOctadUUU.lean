import Atlas.Fischer.QuinticPointOctadBlocks
import Atlas.Fischer.CubicPointRows

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem coordinateCubic_point_octad_linear (p : Omega) (D : Octad) :
    (∑ i : Omega, ∑ a : Omega, coordinateCubic (.inl a) (.inl i) (.inl p) *
      cubicPointOctadIncidence a D) = (1 + 4 * cubicPointOctadIncidence p D) / 16 := by
  rw [Finset.sum_comm]
  have hs (a : Omega) : (∑ i : Omega, coordinateCubic (.inl a) (.inl i) (.inl p)) =
      cubicPointRowSum a p / 1024 := by
    simp_rw [coordinateCubic_points, ← Finset.sum_div]
    rw [cubicPointPattern_row_sum]
  simp only [← Finset.sum_mul, hs, cubicPointRowSum, add_div, add_mul,
    Finset.sum_add_distrib, mul_ite, ite_mul, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum, cubicPointOctadIncidence_sum]
  ring_nf
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- The UUU/UWW block loses its two octad sums by the actual diagonal incidence table. -/
theorem quinticPointOctadUUU_UWW_collapse (p : Omega) (D : Octad) :
    quinticPointOctadUUU_UWW p D =
      ∑ i : Omega, ∑ j : Omega, ∑ k : Omega, ∑ a : Omega,
        coordinateCubic (.inl i) (.inl j) (.inl k) * coordinateCubic (.inl a) (.inl i) (.inl p) *
          cubicPointOctadIncidence a D * cubicPointOctadIncidence j D * cubicPointOctadIncidence k D := by
  have hp (i j k : Omega) : star (coordinateCubic (.inl i) (.inl j) (.inl k)) =
      coordinateCubic (.inl i) (.inl j) (.inl k) := by
    rw [coordinateCubic_points]
    simp only [star_div₀, star_ofNat, cubicPointPattern_star]
  have hm (b : Octad) (j : Omega) (E : Octad) : coordinateCubic (.inr b) (.inl j) (.inr E) =
      if b = E then cubicPointOctadIncidence j b / 16 else 0 := by
    rw [coordinateCubic_swap_first, coordinateCubic_point_octads]
  unfold quinticPointOctadUUU_UWW coordinateQuinticTerm coordinateQuinticCubicProduct
  simp only [coordinateCubic_point_octads, hm, hp, inverseCoordinateMetric, coordinateWeight]
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, inv_div, inv_one, mul_one]
  simp only [apply_ite star, star_div₀, star_ofNat, star_zero, cubicPointOctadIncidence_star,
    mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem quinticPointOctadUUU_UWW_eq (p : Omega) (D : Octad) :
    quinticPointOctadUUU_UWW p D = (15 : Scalar) * (1 + 4 * cubicPointOctadIncidence p D) / 256 := by
  rw [quinticPointOctadUUU_UWW_collapse]
  have hs (i : Omega) :
      (∑ j : Omega, ∑ k : Omega, ∑ a : Omega,
        coordinateCubic (.inl i) (.inl j) (.inl k) * coordinateCubic (.inl a) (.inl i) (.inl p) *
          cubicPointOctadIncidence a D * cubicPointOctadIncidence j D * cubicPointOctadIncidence k D) =
      (15 / 16 : Scalar) * ∑ a : Omega,
        coordinateCubic (.inl a) (.inl i) (.inl p) * cubicPointOctadIncidence a D := by
    calc
      _ = ∑ j : Omega, ∑ a : Omega, ∑ k : Omega,
          coordinateCubic (.inl i) (.inl j) (.inl k) * coordinateCubic (.inl a) (.inl i) (.inl p) *
            cubicPointOctadIncidence a D * cubicPointOctadIncidence j D * cubicPointOctadIncidence k D := by
        apply Finset.sum_congr rfl
        intro j hj
        exact Finset.sum_comm
      _ = ∑ a : Omega, ∑ j : Omega, ∑ k : Omega,
          coordinateCubic (.inl i) (.inl j) (.inl k) * coordinateCubic (.inl a) (.inl i) (.inl p) *
            cubicPointOctadIncidence a D * cubicPointOctadIncidence j D * cubicPointOctadIncidence k D := Finset.sum_comm
      _ = ∑ a : Omega, (∑ j : Omega, ∑ k : Omega,
          coordinateCubic (.inl i) (.inl j) (.inl k) * cubicPointOctadIncidence j D * cubicPointOctadIncidence k D) *
            (coordinateCubic (.inl a) (.inl i) (.inl p) * cubicPointOctadIncidence a D) := by
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = _ := by simp only [coordinateCubic_point_octad_quadratic, Finset.mul_sum]
  simp only [hs, ← Finset.mul_sum]
  rw [coordinateCubic_point_octad_linear]
  ring

/-- Exact source first column, relative to the actual unnormalized cubic coefficient. -/
theorem quinticPointOctadUUU_UWW_ratio (p : Omega) (D : Octad) :
    quinticPointOctadUUU_UWW p D =
      (if p ∈ D.val then (65 / 16 : Scalar) else 45 / 16) *
        coordinateCubic (.inl p) (.inr D) (.inr D) := by
  rw [quinticPointOctadUUU_UWW_eq, coordinateCubic_point_octads]
  by_cases hp : p ∈ D.val <;> norm_num [cubicPointOctadIncidence, hp]

end Atlas.Fischer
