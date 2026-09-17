import Atlas.Fischer.QuinticPointDecomposition
import Atlas.Fischer.QuinticPointUWW
import Atlas.Fischer.CubicOctadSquaredRows
import Atlas.Fischer.CubicTrianglePointRows
import Atlas.Algebra.FintypeSumDite

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

/-- The three point links are diagonal on octads, so all three second-triangle
indices collapse. The two conjugations give a square, not an absolute square. -/
theorem quinticPointWWW_collapse (p q r : Omega) :
    quinticPointWWW p q r = ∑ D : Octad, ∑ E : Octad, ∑ F : Octad,
      (star (coordinateCubic (.inr D) (.inr E) (.inr F)))^2 *
        cubicPointOctadIncidence p D * cubicPointOctadIncidence q E *
        cubicPointOctadIncidence r F / 4096 := by
  classical
  unfold quinticPointWWW coordinateQuinticTerm coordinateQuinticCubicProduct
  simp only [coordinateCubic_octads_point, inverseCoordinateMetric, coordinateWeight,
    Rat.cast_one, inv_one, one_mul, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro D _
  apply Finset.sum_congr rfl
  intro E _
  apply Finset.sum_congr rfl
  intro F _
  ring

theorem cubicSextetIncidenceSum_pairs (p q r : Omega) :
    cubicSextetIncidenceSum p q r = ∑ D : Octad, ∑ E : Octad,
      if h : (D.val ∩ E.val).card = 4 then
        cubicPointOctadIncidence p D * cubicPointOctadIncidence q E *
          cubicPointOctadIncidence r (cubicSextetCompletion D E h) else 0 := by
  classical
  unfold cubicSextetIncidenceSum
  rw [← Equiv.sum_comp cubicSextetTrianglePairEquiv.symm, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro D _
  rw [Atlas.Algebra.fintype_sum_dite]
  simp only [Finset.sum_const_zero, add_zero]
  rfl

theorem cubicTrioIncidenceSum_pairs (p q r : Omega) :
    cubicTrioIncidenceSum p q r = ∑ D : Octad, ∑ E : Octad,
      if h : (D.val ∩ E.val).card = 0 then
        cubicPointOctadIncidence p D * cubicPointOctadIncidence q E *
          cubicPointOctadIncidence r (cubicTrioCompletion D E h) else 0 := by
  classical
  unfold cubicTrioIncidenceSum
  rw [← Equiv.sum_comp cubicTrioPairEquiv.symm, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro D _
  rw [Atlas.Algebra.fintype_sum_dite]
  simp only [Finset.sum_const_zero, add_zero]
  rfl

theorem quinticPointWWW_incidence (p q r : Omega) :
    quinticPointWWW p q r =
      (1 / 16384 : Scalar) * cubicSextetIncidenceSum p q r -
        (3 / 16384 : Scalar) * cubicTrioIncidenceSum p q r := by
  classical
  rw [quinticPointWWW_collapse, cubicSextetIncidenceSum_pairs, cubicTrioIncidenceSum_pairs]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro D _
  apply Finset.sum_congr rfl
  intro E _
  calc
    _ = (cubicPointOctadIncidence p D * cubicPointOctadIncidence q E / 4096) *
        ∑ F : Octad, (star (coordinateCubic (.inr D) (.inr E) (.inr F)))^2 *
          cubicPointOctadIncidence r F := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro F _
      ring
    _ = _ := by
      rw [coordinateCubic_octad_star_square_row]
      by_cases h4 : (D.val ∩ E.val).card = 4 <;>
        by_cases h0 : (D.val ∩ E.val).card = 0
      · omega
      all_goals simp [h4, h0] <;> ring

theorem quinticPointWWW_source_rows (p q r : Omega) :
    1024 * quinticPointWWW p q r =
      cubicSextetPointContributionOverGamma p q r + cubicTrioPointContributionOverGamma p q r := by
  rw [quinticPointWWW_incidence]
  unfold cubicSextetPointContributionOverGamma cubicTrioPointContributionOverGamma
  ring

end Atlas.Fischer
