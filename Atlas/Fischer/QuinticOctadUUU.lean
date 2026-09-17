import Atlas.Fischer.QuinticOctadBlocks
import Atlas.Fischer.CubicPointVectorContraction
import Atlas.Fischer.QuinticPointOctadCompletionValues

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The first distinct-octad block, with its actual conjugation retained. -/
theorem quinticOctadBlockUUU_WWW_collapse (D E F : Octad) :
    quinticOctadBlockUUU_WWW D E F =
      star (coordinateCubic (.inr D) (.inr E) (.inr F)) / 8 *
        (∑ i : Omega, ∑ j : Omega, ∑ k : Omega,
          coordinateCubic (.inl i) (.inl j) (.inl k) *
            cubicPointOctadIncidence i D * cubicPointOctadIncidence j E *
            cubicPointOctadIncidence k F) := by
  have hp (i j k : Omega) : star (coordinateCubic (.inl i) (.inl j) (.inl k)) =
      coordinateCubic (.inl i) (.inl j) (.inl k) := by
    rw [coordinateCubic_points]
    simp only [star_div₀, star_ofNat, cubicPointPattern_star]
  have hm (B : Octad) (i : Omega) (A : Octad) :
      coordinateCubic (.inr B) (.inl i) (.inr A) =
        if B = A then cubicPointOctadIncidence i B / 16 else 0 := by
    rw [coordinateCubic_swap_first, coordinateCubic_point_octads]
  unfold quinticOctadBlockUUU_WWW coordinateQuinticTerm coordinateQuinticCubicProduct
  simp only [hm, hp, inverseCoordinateMetric, coordinateWeight]
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, inv_div, inv_one, mul_one]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The needed cyclic Golay word identities, for either sextet or trio phase. -/
theorem octadTriangle_rotations (D E F : Octad) (z : golay)
    (hF : octadWord F = octadWord D + octadWord E + z) :
    octadWord D = octadWord E + octadWord F + z ∧
      octadWord E = octadWord D + octadWord F + z := by
  constructor
  · rw [hF]
    symm
    calc
      _ = octadWord D + (octadWord E + octadWord E) + (z + z) := by abel
      _ = _ := by simp only [parkerGolay_add_self, add_zero]
  · rw [hF]
    symm
    calc
      _ = octadWord E + (octadWord D + octadWord D) + (z + z) := by abel
      _ = _ := by simp only [parkerGolay_add_self, add_zero]

theorem coordinateCubic_incidence_triple_sextet (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E) :
    (∑ i : Omega, ∑ j : Omega, ∑ k : Omega,
      coordinateCubic (.inl i) (.inl j) (.inl k) *
        cubicPointOctadIncidence i D * cubicPointOctadIncidence j E *
        cubicPointOctadIncidence k F) = 47 / 2 := by
  let t : OrderedCubicSextetTriangle := ⟨(D,E,F),hF⟩
  have hr := octadTriangle_rotations D E F 0 (by simpa only [add_zero] using hF)
  have hD : octadWord D = octadWord E + octadWord F := by simpa only [add_zero] using hr.1
  have hE : octadWord E = octadWord D + octadWord F := by simpa only [add_zero] using hr.2
  have hDE := cubicSextetTriangle_pair_sum t
  have hDF := cubicSextetTriangle_pair_sum ⟨(D,F,E),hE⟩
  have hEF := cubicSextetTriangle_pair_sum ⟨(E,F,D),hD⟩
  have ht := cubicSextetTriangle_triple_sum t
  simp only [t] at hDE ht
  simp_rw [coordinateCubic_points, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [cubicPointPattern_vector_contraction, cubicPointOctadIncidence_sum,
    cubicPointOctadIncidence_sum, cubicPointOctadIncidence_sum, hDE, hDF, hEF, ht]
  norm_num

theorem coordinateCubic_incidence_triple_trio (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E + golayOne) :
    (∑ i : Omega, ∑ j : Omega, ∑ k : Omega,
      coordinateCubic (.inl i) (.inl j) (.inl k) *
        cubicPointOctadIncidence i D * cubicPointOctadIncidence j E *
        cubicPointOctadIncidence k F) = -49 / 2 := by
  let t : OrderedCubicTrio := ⟨(D,E,F),hF⟩
  have hr := octadTriangle_rotations D E F golayOne hF
  have hDE := cubicTrio_pair_sum t
  have hDF := cubicTrio_pair_sum ⟨(D,F,E),hr.2⟩
  have hEF := cubicTrio_pair_sum ⟨(E,F,D),hr.1⟩
  have ht := cubicTrio_triple_sum t
  simp only [t] at hDE ht
  simp_rw [coordinateCubic_points, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [cubicPointPattern_vector_contraction, cubicPointOctadIncidence_sum,
    cubicPointOctadIncidence_sum, cubicPointOctadIncidence_sum, hDE, hDF, hEF, ht]
  norm_num

end Atlas.Fischer
