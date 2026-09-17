import Atlas.Fischer.QuinticPointOctadBlocks
import Atlas.Fischer.QuinticPointOctadCompletionValues
import Atlas.Fischer.CubicOctadSquaredRows

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem coordinateCubic_octad_square_row (D E : Octad) (v : Octad → Scalar) :
    (∑ F : Octad, coordinateCubic (.inr D) (.inr E) (.inr F)^2 * v F) =
      (if h : (D.val ∩ E.val).card = 4 then v (cubicSextetCompletion D E h) / 4
       else if h : (D.val ∩ E.val).card = 0 then -3 * v (cubicTrioCompletion D E h) / 4
       else 0) := by
  have h := congrArg star (coordinateCubic_octad_star_square_row D E (fun F => star (v F)))
  simpa only [star_sum, star_mul, star_pow, star_star, apply_dite star,
    star_div₀, star_ofNat, star_neg, star_zero, mul_comm] using h

/-- Literal contraction collapse; the octad coefficient is squared, not norm-squared. -/
theorem quinticPointOctadUWW_UWW_collapse (p : Omega) (D : Octad) :
    quinticPointOctadUWW_UWW p D =
      (1 / 4 : Scalar) * ∑ E : Octad, ∑ F : Octad,
        coordinateCubic (.inr D) (.inr E) (.inr F)^2 *
          (∑ a : Omega, ∑ b : Omega, coordinateCubic (.inl p) (.inl a) (.inl b) *
            cubicPointOctadIncidence a E * cubicPointOctadIncidence b F) := by
  have hm (b : Octad) (j : Omega) (E : Octad) :
      coordinateCubic (.inr b) (.inl j) (.inr E) =
        if b = E then cubicPointOctadIncidence j b / 16 else 0 := by
    rw [coordinateCubic_swap_first, coordinateCubic_point_octads]
  unfold quinticPointOctadUWW_UWW coordinateQuinticTerm coordinateQuinticCubicProduct
  simp only [coordinateCubic_point_octads, inverseCoordinateMetric, coordinateWeight]
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, inv_div, inv_one, mul_one]
  simp (maxSteps := 100000) only [apply_ite star, star_div₀, star_ofNat, star_zero,
    cubicPointOctadIncidence_star, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E hE
  have hswap {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
      (f : A → B → C → Scalar) :
      (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
    have h : (∑ ab : A × B, ∑ c : C, f ab.1 ab.2 c) =
        ∑ c : C, ∑ ab : A × B, f ab.1 ab.2 c := Finset.sum_comm
    simpa only [Fintype.sum_prod_type] using h
  rw [hswap (A := Omega) (B := Omega) (C := Octad)]
  apply Finset.sum_congr rfl
  intro F hF
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [coordinateCubic_swap_last (.inr F) (.inr E) (.inr D),
    coordinateCubic_swap_first (.inr F) (.inr D) (.inr E),
    coordinateCubic_swap_last (.inr D) (.inr F) (.inr E),
    coordinateCubic_swap_last (.inl b) (.inl a) (.inl p),
    coordinateCubic_swap_first (.inl b) (.inl p) (.inl a),
    coordinateCubic_swap_last (.inl p) (.inl b) (.inl a)]
  ring

theorem quinticPointOctadUWW_UWW_eq (p : Omega) (D : Octad) :
    quinticPointOctadUWW_UWW p D =
      (740 * cubicPointOctadIncidence p D + 645) / 128 := by
  rw [quinticPointOctadUWW_UWW_collapse]
  have hr (E : Octad) :
      (∑ F : Octad, coordinateCubic (.inr D) (.inr E) (.inr F)^2 *
        (∑ a : Omega, ∑ b : Omega, coordinateCubic (.inl p) (.inl a) (.inl b) *
          cubicPointOctadIncidence a E * cubicPointOctadIncidence b F)) =
      (if (D.val ∩ E.val).card = 4 then
        (if p ∈ D.val then (15 / 16 : Scalar) else -1 / 16) / 4 else 0) +
      (if (D.val ∩ E.val).card = 0 then
        -3 * (if p ∈ D.val then (-17 / 16 : Scalar) else -1 / 16) / 4 else 0) := by
    rw [coordinateCubic_octad_square_row]
    by_cases h4 : (D.val ∩ E.val).card = 4
    · have h0 : (D.val ∩ E.val).card ≠ 0 := by omega
      simp only [dif_pos h4, if_pos h4, if_neg h0, add_zero]
      rw [coordinateCubic_point_sextet_completion p D E _ (cubicSextetCompletion_word D E h4)]
    · by_cases h0 : (D.val ∩ E.val).card = 0
      · simp only [dif_neg h4, dif_pos h0, if_neg h4, if_pos h0, zero_add]
        rw [coordinateCubic_point_trio_completion p D E _ (cubicTrioCompletion_word D E h0)]
      · simp only [dif_neg h4, dif_neg h0, if_neg h4, if_neg h0, zero_add]
  simp_rw [hr]
  rw [Finset.sum_add_distrib]
  have hsum (k : ℕ) (v : Scalar) :
      (∑ E : Octad, if (D.val ∩ E.val).card = k then v else 0) =
        (octadIntersectionCount D.val ∅ k : Scalar) * v := by
    have h := cubicSlice_octad_intersection_count D k
    rw [← h, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro E hE
    split_ifs <;> ring
  rw [hsum, hsum, (octad_intersection_distribution D.val D.property).2.2.1,
    (octad_intersection_distribution D.val D.property).1]
  by_cases hp : p ∈ D.val <;> norm_num [cubicPointOctadIncidence, hp]

end Atlas.Fischer
