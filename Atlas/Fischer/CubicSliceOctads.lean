import Atlas.Fischer.CubicSliceOctadIncidence

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Diagonal slice norm98 for every actual Golay octad, including its actual
sextet-triangle and trio product contributions. -/
theorem coordinateCubicSlice_octad_self (D : Octad) :
    coordinateCubicSlice (.inr D) (.inr D)=98 := by
  let T (a b : CoordinateIndex) := inverseCoordinateMetric a*inverseCoordinateMetric b*
    coordinateCubic (.inr D) a b*star (coordinateCubic (.inr D) a b)
  have hpp (i j : Omega) : T (.inl i) (.inl j)=0 := by
    simp only [T,coordinateCubic_swap_first (.inr D) (.inl i),
      coordinateCubic_swap_last (.inl i) (.inr D),coordinateCubic_two_points_octad,mul_zero,zero_mul]
  have hpw (i : Omega) (E : Octad) : T (.inl i) (.inr E)=
      if E=D then (1/32 : Scalar)*(cubicPointOctadIncidence i D*cubicPointOctadIncidence i D) else 0 := by
    simp only [T,coordinateCubic_swap_first (.inr D) (.inl i),coordinateCubic_point_octads]
    by_cases h : E=D
    · subst E
      simp only [ite_true,star_div₀,cubicPointOctadIncidence_star,star_ofNat]
      norm_num [inverseCoordinateMetric,coordinateWeight]
      ring
    · simp [h,Ne.symm h]
  have hwp (E : Octad) (i : Omega) : T (.inr E) (.inl i)=T (.inl i) (.inr E) := by
    dsimp only [T]
    rw [coordinateCubic_swap_last (.inr D) (.inr E) (.inl i)]
    ring
  have hww (E F : Octad) : T (.inr E) (.inr F)=
      coordinateCubic (.inr D) (.inr E) (.inr F)*star (coordinateCubic (.inr D) (.inr E) (.inr F)) := by
    simp [T,inverseCoordinateMetric,coordinateWeight]
  change (∑ a,∑ b,T a b)=_
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_sum_type]
  simp only [hpp,hwp,hpw,hww,Finset.sum_add_distrib,Finset.sum_const_zero,
    add_zero,zero_add,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,
    Finset.mem_univ,ite_true]
  simp_rw [← Finset.mul_sum]
  rw [cubicPointOctadIncidence_square_sum,coordinateCubic_octads_squared_sum]
  norm_num

end Atlas.Fischer
