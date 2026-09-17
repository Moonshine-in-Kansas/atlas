import Atlas.Fischer.OctadicMixedAxisProducts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Axis multiplication records the actual intersection cardinality. -/
theorem product_octadAxisSum_xOctad_intersection (O D : Octad) :
    product (octadAxisSum O) (xOctad D) =
      (((O.val ∩ D.val).card : Scalar) / 4 - 1 / 2) • xOctad D := by
  rw [octadAxisSum,product_sum_left]
  have ht (i : Omega) : product (u i) (xOctad D) =
      ((if i ∈ D.val then (1 / 4 : Scalar) else 0) - 1 / 16) • xOctad D := by
    rw [product_u_xOctad,axisOctadBasisProduct]
    split_ifs <;> congr 1 <;> norm_num
  simp_rw [ht]
  rw [← Finset.sum_smul,Finset.sum_sub_distrib,Finset.sum_const,
    octad_size O.val O.property]
  have hc : (∑ i ∈ O.val, if i ∈ D.val then (1 / 4 : Scalar) else 0) =
      ((O.val ∩ D.val).card : Scalar) / 4 := by
    rw [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.sum_const]
    simp [nsmul_eq_mul,div_eq_mul_inv]
  rw [hc]
  congr 1
  norm_num

/-- The first coefficient in source (5.14), before the outer root factor. -/
theorem product_octadicAxisPart_signedOctad (O : Octad) (d : SignedOctad) :
    product (octadicAxisPart O) (signedOctadVector d) =
      ((3 - ((O.val ∩ (signedOctadSupport d).val).card : Scalar)) / 2) •
        signedOctadVector d := by
  rw [signedOctadVector,product_smul_right,parkerScalarSign_star,
    octadicAxisPart_eq,product_sub_left,product_smul_left,
    product_comm axisSum (xOctad _),product_xOctad_axisSum,
    product_octadAxisSum_xOctad_intersection]
  norm_num only [star_ofNat]
  module

end Atlas.Fischer
