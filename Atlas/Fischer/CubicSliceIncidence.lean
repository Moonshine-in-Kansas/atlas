import Atlas.Fischer.Scalars
import Atlas.Fischer.WittDuads

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The integer incidence coefficient in the point--octad cubic entry. -/
def cubicPointOctadIncidence (i : Omega) (O : Octad) : Scalar :=
  if i ∈ O.val then 3 else -1

theorem cubicSlice_point_incidence_sum (i : Omega) :
    (∑ O : Octad,if i ∈ O.val then (1 : Scalar) else 0)=253 := by
  rw [Finset.sum_coe_sort octads (fun D => if i ∈ D then (1 : Scalar) else 0),
    ← Finset.sum_filter,Finset.sum_const,octads_through_point_card]
  norm_num

theorem cubicSlice_pair_incidence_sum (i j : Omega) (h : i ≠ j) :
    (∑ O : Octad,if i ∈ O.val ∧ j ∈ O.val then (1 : Scalar) else 0)=77 := by
  rw [Finset.sum_coe_sort octads (fun D => if i ∈ D ∧ j ∈ D then (1 : Scalar) else 0),
    ← Finset.sum_filter,Finset.sum_const,octads_through_pair_card i j h]
  norm_num

/-- The two-incidence contraction is derived from the actual Witt parameters. -/
theorem cubicPointOctadIncidence_pair_sum (i j : Omega) :
    (∑ O : Octad,cubicPointOctadIncidence i O*cubicPointOctadIncidence j O)=
      if i=j then (2783 : Scalar) else -33 := by
  have hc : Fintype.card Octad=759 := by rw [Fintype.card_coe,octads_card]
  have he (O : Octad) : cubicPointOctadIncidence i O*cubicPointOctadIncidence j O=
      16*(if i ∈ O.val ∧ j ∈ O.val then (1 : Scalar) else 0)-
      4*(if i ∈ O.val then (1 : Scalar) else 0)-
      4*(if j ∈ O.val then (1 : Scalar) else 0)+1 := by
    unfold cubicPointOctadIncidence
    by_cases hi : i ∈ O.val <;> by_cases hj : j ∈ O.val <;> norm_num [hi,hj]
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib,
    ← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum,
    cubicSlice_point_incidence_sum,cubicSlice_point_incidence_sum,
    Finset.sum_const,Finset.card_univ,hc]
  by_cases h : i=j
  · subst j
    simp only [and_self,cubicSlice_point_incidence_sum,ite_true]
    norm_num
  · rw [cubicSlice_pair_incidence_sum i j h,if_neg h]
    norm_num

end Atlas.Fischer
