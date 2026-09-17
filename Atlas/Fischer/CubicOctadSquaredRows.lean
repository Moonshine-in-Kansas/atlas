import Atlas.Fischer.CubicSliceOctadRows
import Atlas.Fischer.CubicTriangleCounts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

theorem signedOctadVector_square_weighted (a : Scalar) (d : SignedOctad)
    (v : Octad → Scalar) :
    (∑ F : Octad, ((a • signedOctadVector d) (.inr F))^2 * v F) =
      a^2 * v (signedOctadSupport d) := by
  classical
  simp only [Pi.smul_apply, smul_eq_mul, signedOctadVector, xOctad_octad_apply,
    mul_ite, mul_zero, mul_one, ite_pow, zero_pow (by decide : 2 ≠ 0),
    ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [mul_pow]
  have hs : parkerScalarSign d.val.2 ^ 2 = (1 : Scalar) := by
    unfold parkerScalarSign
    split_ifs <;> norm_num
  rw [hs, mul_one]

/-- Squared conjugated cubic coefficients retain the negative trio contribution.
This is deliberately a square, not an absolute square. -/
theorem coordinateCubic_octad_star_square_row (D E : Octad) (v : Octad → Scalar) :
    (∑ F : Octad, (star (coordinateCubic (.inr D) (.inr E) (.inr F)))^2 * v F) =
      (if h : (D.val ∩ E.val).card = 4 then v (cubicSextetCompletion D E h) / 4
       else if h : (D.val ∩ E.val).card = 0 then -3 * v (cubicTrioCompletion D E h) / 4
       else 0) := by
  classical
  simp only [coordinateCubic_octad_product, star_star]
  have hint : signedOctadIntersection (canonicalOctadLift D) (canonicalOctadLift E) =
      (D.val ∩ E.val).card := by
    simp only [signedOctadIntersection, signedOctadSupport_canonical]
  by_cases he : D = E
  · subst E
    simp [octadBasisProduct, Finset.sum_apply, octad_size D.val D.property]
  · unfold octadBasisProduct
    rw [if_neg he]
    by_cases h4 : signedOctadIntersection (canonicalOctadLift D) (canonicalOctadLift E) = 4
    · simp only [dif_pos h4]
      rw [signedOctadVector_square_weighted]
      have h4' : (D.val ∩ E.val).card = 4 := hint ▸ h4
      simp only [dif_pos h4', cubicSextetCompletion]
      ring
    · simp only [dif_neg h4]
      have h4' : (D.val ∩ E.val).card ≠ 4 := hint ▸ h4
      rw [dif_neg h4']
      by_cases h0 : signedOctadIntersection (canonicalOctadLift D) (canonicalOctadLift E) = 0
      · simp only [dif_pos h0]
        rw [signedOctadVector_square_weighted]
        have h0' : (D.val ∩ E.val).card = 0 := hint ▸ h0
        simp only [dif_pos h0', cubicTrioCompletion, div_pow, theta_sq]
        ring
      · have h0' : (D.val ∩ E.val).card ≠ 0 := hint ▸ h0
        simp [h0, h0']

end Atlas.Fischer
