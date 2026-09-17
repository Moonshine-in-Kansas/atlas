import Atlas.Fischer.CubicOctadDiamondSupport

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The literal four cubic factors for one actual admissible quadrilateral. -/
def cubicOctadQuadrilateralWeight (D J K : Octad)
    (hDJ : OctadPairAdmissible D J) (hDK : OctadPairAdmissible D K)
    (hJK : OctadPairAdmissible J K) : Scalar :=
  let I := octadDiamond J K hJK
  let B := octadDiamond D J hDJ
  let C := octadDiamond D K hDK
  star (coordinateCubic (.inr I) (.inr J) (.inr K)) *
    star (coordinateCubic (.inr I) (.inr B) (.inr C)) *
    coordinateCubic (.inr D) (.inr B) (.inr J) *
    coordinateCubic (.inr D) (.inr C) (.inr K)

/-- Actual sparse support removes all three completion indices. -/
theorem cubicOctadQuadrilateral_edge_sum (D J K : Octad) (v : Octad → Scalar) :
    (∑ I : Octad, ∑ B : Octad, ∑ C : Octad,
      v I * star (coordinateCubic (.inr I) (.inr J) (.inr K)) *
        star (coordinateCubic (.inr I) (.inr B) (.inr C)) *
        coordinateCubic (.inr D) (.inr B) (.inr J) *
        coordinateCubic (.inr D) (.inr C) (.inr K)) =
    if hDJ : OctadPairAdmissible D J then
      if hDK : OctadPairAdmissible D K then
        if hJK : OctadPairAdmissible J K then
          v (octadDiamond J K hJK) * cubicOctadQuadrilateralWeight D J K hDJ hDK hJK
        else 0
      else 0
    else 0 := by
  have ht (I : Octad) : coordinateCubic (.inr I) (.inr J) (.inr K) =
      coordinateCubic (.inr J) (.inr K) (.inr I) := by
    rw [coordinateCubic_swap_first, coordinateCubic_swap_last]
  have hb (B : Octad) : coordinateCubic (.inr D) (.inr B) (.inr J) =
      coordinateCubic (.inr D) (.inr J) (.inr B) := coordinateCubic_swap_last _ _ _
  have hc (C : Octad) : coordinateCubic (.inr D) (.inr C) (.inr K) =
      coordinateCubic (.inr D) (.inr K) (.inr C) := coordinateCubic_swap_last _ _ _
  by_cases hDJ : OctadPairAdmissible D J
  · rw [dif_pos hDJ]
    by_cases hDK : OctadPairAdmissible D K
    · rw [dif_pos hDK]
      by_cases hJK : OctadPairAdmissible J K
      · rw [dif_pos hJK]
        conv_lhs =>
          arg 2
          ext I
          arg 2
          ext B
          arg 2
          ext C
          rw [ht I, hb B, hc C]
          rw [coordinateCubic_octad_delta D J B hDJ,
            coordinateCubic_octad_delta D K C hDK, coordinateCubic_octad_delta J K I hJK]
        simp only [apply_ite star, star_zero, mul_ite, ite_mul, mul_zero, zero_mul,
          Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
          Finset.sum_ite_irrel, Finset.sum_const_zero]
        unfold cubicOctadQuadrilateralWeight
        simp only [ht, hb, hc]
        ring
      · simp only [dif_neg hJK, ht, coordinateCubic_octad_zero_of_not_admissible J K _ hJK,
          star_zero, mul_zero, zero_mul, Finset.sum_const_zero]
    · simp only [dif_neg hDK, hc, coordinateCubic_octad_zero_of_not_admissible D K _ hDK,
        mul_zero, Finset.sum_const_zero]
  · simp only [dif_neg hDJ, hb, coordinateCubic_octad_zero_of_not_admissible D J _ hDJ,
      mul_zero, zero_mul, Finset.sum_const_zero]

end Atlas.Fischer
