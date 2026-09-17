import Atlas.Fischer.QuinticBlocks
import Atlas.Fischer.CubicPointBlockQuadratic

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

theorem coordinateCubic_octads_point (D E : Octad) (i : Omega) :
    coordinateCubic (.inr D) (.inr E) (.inl i) =
      if D = E then cubicPointOctadIncidence i D / 16 else 0 := by
  rw [coordinateCubic_swap_last, coordinateCubic_swap_first, coordinateCubic_point_octads]

/-- Collapse the four octad indices using the actual diagonal point--octad blocks. -/
theorem quinticPointUWW_collapse (p q r : Omega) :
    quinticPointUWW p q r =
      ∑ i : Omega, ∑ D : Octad, ∑ a : Omega,
        coordinateCubic (.inl a) (.inl i) (.inl p) *
          cubicPointOctadIncidence i D * cubicPointOctadIncidence a D *
          cubicPointOctadIncidence q D * cubicPointOctadIncidence r D / 1024 := by
  classical
  have hite (P : Prop) (x : Scalar) :
      (if P then (if P then x else 0) else 0) = if P then x else 0 := by
    by_cases h : P <;> simp [h]
  unfold quinticPointUWW coordinateQuinticTerm coordinateQuinticCubicProduct
  simp only [coordinateCubic_point_octads, coordinateCubic_octads_point,
    inverseCoordinateMetric, coordinateWeight]
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, inv_div, inv_one, mul_one]
  simp only [apply_ite star, star_div₀, star_mul, star_ofNat, star_zero, cubicPointOctadIncidence_star,
    mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Finset.sum_ite_irrel, Finset.sum_const_zero, hite]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro D _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem quinticPointUWW_incidence (p q r : Omega) :
    quinticPointUWW p q r =
      (15 / 16384 : Scalar) * ∑ D : Octad,
        cubicPointOctadIncidence q D * cubicPointOctadIncidence r D := by
  classical
  rw [quinticPointUWW_collapse, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  have hc (a i : Omega) : coordinateCubic (.inl a) (.inl i) (.inl p) =
      coordinateCubic (.inl p) (.inl i) (.inl a) := by
    rw [coordinateCubic_swap_first, coordinateCubic_swap_last, coordinateCubic_swap_first]
  simp_rw [hc]
  calc
    _ = (∑ i : Omega, ∑ a : Omega, coordinateCubic (.inl p) (.inl i) (.inl a) *
        cubicPointOctadIncidence i D * cubicPointOctadIncidence a D) *
          cubicPointOctadIncidence q D * cubicPointOctadIncidence r D / 1024 := by
      simp only [Finset.sum_mul, Finset.sum_div]
    _ = _ := by rw [coordinateCubic_point_octad_quadratic]; ring

theorem quinticPointUWW_eq (p q r : Omega) :
    quinticPointUWW p q r =
      (15 / 16384 : Scalar) * (if q = r then 2783 else -33) := by
  rw [quinticPointUWW_incidence, cubicPointOctadIncidence_pair_sum]

/-- The three ordered UWW patterns give the source's entire mixed contribution. -/
theorem quinticPointUWW_three (p q r : Omega) :
    1024 * (quinticPointUWW p q r + quinticPointUWW q p r + quinticPointUWW r p q) =
      -1485 / 16 + 2640 * ((if p = q then (1 : Scalar) else 0) +
        (if q = r then 1 else 0) + (if p = r then 1 else 0)) := by
  classical
  rw [quinticPointUWW_eq, quinticPointUWW_eq, quinticPointUWW_eq]
  split_ifs <;> norm_num

end Atlas.Fischer
