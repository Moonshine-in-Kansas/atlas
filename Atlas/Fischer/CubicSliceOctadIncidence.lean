import Atlas.Fischer.CubicSliceOctadRows

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem cubicPointOctadIncidence_square_sum (D : Octad) :
    (∑ i : Omega,cubicPointOctadIncidence i D*cubicPointOctadIncidence i D)=88 := by
  have he (i : Omega) : cubicPointOctadIncidence i D*cubicPointOctadIncidence i D=
      (8 : Scalar)*(if i ∈ D.val then 1 else 0)+1 := by
    unfold cubicPointOctadIncidence
    split_ifs <;> norm_num
  simp_rw [he]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_filter,Finset.sum_const]
  have hf : Finset.univ.filter (fun i : Omega => i ∈ D.val)=D.val := by ext i; simp
  rw [hf,octad_size D.val D.property,Finset.sum_const,Finset.card_univ]
  have hc : Fintype.card Omega=24 := by decide
  rw [hc]
  norm_num

theorem cubicSlice_octad_intersection_count (D : Octad) (k : ℕ) :
    (∑ E : Octad,if (D.val ∩ E.val).card=k then (1 : Scalar) else 0)=
      (octadIntersectionCount D.val ∅ k : Scalar) := by
  rw [Finset.sum_coe_sort octads (fun E => if (D.val ∩ E).card=k then (1 : Scalar) else 0),
    ← Finset.sum_filter,Finset.sum_const]
  simp only [nsmul_eq_mul,mul_one,octadIntersectionCount,Finset.empty_subset,true_and]
  congr 2
  ext E
  simp only [Finset.mem_filter,Finset.inter_comm]

theorem coordinateCubic_octads_squared_sum (D : Octad) :
    (∑ E : Octad,∑ F : Octad,coordinateCubic (.inr D) (.inr E) (.inr F)*
      star (coordinateCubic (.inr D) (.inr E) (.inr F)))=(185/2 : Scalar) := by
  simp_rw [coordinateCubic_octad_row_norm]
  have he (E : Octad) :
      (if (D.val ∩ E.val).card=4 then (1/4 : Scalar)
      else if (D.val ∩ E.val).card=0 then 3/4 else 0)=
      (1/4 : Scalar)*(if (D.val ∩ E.val).card=4 then 1 else 0)+
      (3/4 : Scalar)*(if (D.val ∩ E.val).card=0 then 1 else 0) := by
    by_cases h4 : (D.val ∩ E.val).card=4
    · have h0 : (D.val ∩ E.val).card ≠ 0 := by omega
      simp [h4,h0]
    · simp [h4]
  simp_rw [he]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
    cubicSlice_octad_intersection_count,cubicSlice_octad_intersection_count]
  have hc := octad_intersection_distribution D.val D.property
  rw [hc.2.2.1,hc.1]
  norm_num

end Atlas.Fischer
