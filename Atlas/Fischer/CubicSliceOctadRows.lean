import Atlas.Fischer.CubicSliceCoefficients

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem coordinateCubic_octad_product (D E F : Octad) :
    coordinateCubic (.inr D) (.inr E) (.inr F)=star (octadBasisProduct D E (.inr F)) := by
  rw [coordinateCubic_swap_last (.inr D) (.inr E) (.inr F),
    coordinateCubic_swap_first (.inr D) (.inr F) (.inr E)]
  simp only [coordinateCubic,cubic,product_coordinateVector,hermitian_coordinateVector_left,
    basisProduct,coordinateWeight,Rat.cast_one,one_mul]

theorem cubicSlice_signed_octad_norm (a : Scalar) (d : SignedOctad) :
    (∑ F : Octad,star ((a • signedOctadVector d) (.inr F)) *
      (a • signedOctadVector d) (.inr F))=star a*a := by
  have hstar : star (parkerScalarSign d.val.2)=parkerScalarSign d.val.2 := by
    unfold parkerScalarSign
    split_ifs <;> norm_num
  simp only [Pi.smul_apply,smul_eq_mul,signedOctadVector,xOctad_octad_apply,star_mul,
    hstar,star_one,star_zero,mul_ite,ite_mul,mul_zero,zero_mul,
    mul_one,one_mul,ite_self,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  calc
    _ = (star a*a)*(parkerScalarSign d.val.2*parkerScalarSign d.val.2) := by ring
    _ = _ := by unfold parkerScalarSign; split_ifs <;> ring

/-- A single actual octad product contributes 1/4 for intersection4, 3/4 for
intersection0, and zero otherwise; all Parker signs are squared internally. -/
theorem coordinateCubic_octad_row_norm (D E : Octad) :
    (∑ F : Octad,coordinateCubic (.inr D) (.inr E) (.inr F)*
      star (coordinateCubic (.inr D) (.inr E) (.inr F)))=
      if (D.val ∩ E.val).card=4 then (1/4 : Scalar)
      else if (D.val ∩ E.val).card=0 then 3/4 else 0 := by
  simp only [coordinateCubic_octad_product,star_star]
  have hint : signedOctadIntersection (canonicalOctadLift D) (canonicalOctadLift E)=
      (D.val ∩ E.val).card := by
    simp only [signedOctadIntersection,signedOctadSupport_canonical]
  by_cases he : D=E
  · subst E
    simp [octadBasisProduct,Finset.sum_apply,octad_size D.val D.property]
  · unfold octadBasisProduct
    rw [if_neg he]
    by_cases h4 : signedOctadIntersection (canonicalOctadLift D) (canonicalOctadLift E)=4
    · simp only [dif_pos h4]
      rw [cubicSlice_signed_octad_norm]
      rw [hint] at h4
      norm_num [h4]
    · simp only [dif_neg h4]
      by_cases h0 : signedOctadIntersection (canonicalOctadLift D) (canonicalOctadLift E)=0
      · simp only [dif_pos h0]
        rw [cubicSlice_signed_octad_norm]
        rw [hint] at h4 h0
        rw [if_neg h4,if_pos h0]
        rw [star_div₀,theta_conjugate,star_ofNat]
        have ht := theta_sq
        calc
          _ = -(theta^2)/4 := by ring
          _ = _ := by rw [ht]; norm_num
      · simp only [dif_neg h0,Pi.zero_apply,star_zero,mul_zero,Finset.sum_const_zero]
        rw [hint] at h4 h0
        simp [h4,h0]

end Atlas.Fischer
