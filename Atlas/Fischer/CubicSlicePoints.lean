import Atlas.Fischer.CubicSlicePointPattern

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The actual weighted slice identity for every pair of point coordinates. -/
theorem coordinateCubicSlice_points (i j : Omega) :
    coordinateCubicSlice (.inl i) (.inl j)=if i=j then (49/4 : Scalar) else 0 := by
  let T (a b : CoordinateIndex) := inverseCoordinateMetric a*inverseCoordinateMetric b*
    coordinateCubic (.inl i) a b*star (coordinateCubic (.inl j) a b)
  have hpp (a b : Omega) : T (.inl a) (.inl b)=
      (1/16384 : Scalar)*(cubicPointPattern i a b*cubicPointPattern j a b) := by
    simp only [T,coordinateCubic_points,star_div₀,cubicPointPattern_star,star_ofNat]
    norm_num [inverseCoordinateMetric,coordinateWeight]
    ring
  have hpw (a : Omega) (D : Octad) : T (.inl a) (.inr D)=0 := by
    simp [T,coordinateCubic_two_points_octad]
  have hwp (D : Octad) (a : Omega) : T (.inr D) (.inl a)=0 := by
    simp only [T,coordinateCubic_swap_last (.inl i) (.inr D),
      coordinateCubic_two_points_octad,mul_zero,zero_mul]
  have hww (D E : Octad) : T (.inr D) (.inr E)=
      if D=E then (1/256 : Scalar)*(cubicPointOctadIncidence i D*cubicPointOctadIncidence j D) else 0 := by
    by_cases h : D=E
    · subst E
      simp only [T,coordinateCubic_point_octads,ite_true,star_div₀,
        cubicPointOctadIncidence_star,star_ofNat]
      norm_num [inverseCoordinateMetric,coordinateWeight]
      ring
    · simp [T,coordinateCubic_point_octads,h]
  change (∑ a,∑ b,T a b)=_
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_sum_type]
  simp only [hpp,hpw,hwp,hww,Finset.sum_add_distrib,Finset.sum_const_zero,
    add_zero,zero_add,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  simp_rw [← Finset.mul_sum]
  rw [cubicPointPattern_pair_sum,cubicPointOctadIncidence_pair_sum]
  split_ifs <;> norm_num

end Atlas.Fischer
