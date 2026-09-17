import Atlas.Fischer.CubicInsidePointCounts
import Atlas.Fischer.CubicSliceOctadIncidence

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem cubicOctad_neighbor_point_count (D : Octad) (i : Omega) (k : ℕ) :
    (∑ E : Octad,if i ∈ E.val ∧ (D.val ∩ E.val).card=k then (1 : Scalar) else 0)=
      (octadIntersectionCount D.val {i} k : Scalar) := by
  rw [Finset.sum_coe_sort octads (fun E => if i ∈ E ∧ (D.val ∩ E).card=k then (1 : Scalar) else 0),
    ← Finset.sum_filter,Finset.sum_const]
  simp only [nsmul_eq_mul,mul_one,octadIntersectionCount,Finset.singleton_subset_iff]
  congr 2
  ext E
  simp only [Finset.mem_filter,Finset.inter_comm]

theorem cubicOctad_neighbor_incidence (D : Octad) (i : Omega) (k : ℕ) :
    (∑ E : Octad,if (D.val ∩ E.val).card=k then cubicPointOctadIncidence i E else 0)=
      4*(octadIntersectionCount D.val {i} k : Scalar)-(octadIntersectionCount D.val ∅ k : Scalar) := by
  have he (E : Octad) :
      (if (D.val ∩ E.val).card=k then cubicPointOctadIncidence i E else 0)=
      4*(if i ∈ E.val ∧ (D.val ∩ E.val).card=k then (1 : Scalar) else 0)-
      (if (D.val ∩ E.val).card=k then 1 else 0) := by
    by_cases hi : i ∈ E.val <;> by_cases hk : (D.val ∩ E.val).card=k <;>
      simp [cubicPointOctadIncidence,hi,hk] <;> norm_num
  simp_rw [he]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,cubicOctad_neighbor_point_count,
    cubicSlice_octad_intersection_count]

theorem cubicOctad_neighbor_four_incidence (D : Octad) (i : Omega) :
    (∑ E : Octad,if (D.val ∩ E.val).card=4 then cubicPointOctadIncidence i E else 0)=
      if i ∈ D.val then 280 else 0 := by
  rw [cubicOctad_neighbor_incidence,(octad_intersection_distribution D.val D.property).2.2.1]
  by_cases hi : i ∈ D.val
  · rw [(octad_inside_point_distribution D.val D.property i hi).2.2.1]
    simp [hi]
    norm_num
  · have hd : Disjoint D.val {i} := by simpa using hi
    rw [(octad_outside_point_distribution D.val {i} D.property hd (by simp)).2.2]
    simp [hi]
    norm_num

theorem cubicOctad_neighbor_zero_incidence (D : Octad) (i : Omega) :
    (∑ E : Octad,if (D.val ∩ E.val).card=0 then cubicPointOctadIncidence i E else 0)=
      if i ∈ D.val then -30 else 30 := by
  rw [cubicOctad_neighbor_incidence,(octad_intersection_distribution D.val D.property).1]
  by_cases hi : i ∈ D.val
  · rw [(octad_inside_point_distribution D.val D.property i hi).1]
    simp [hi]
  · have hd : Disjoint D.val {i} := by simpa using hi
    rw [(octad_outside_point_distribution D.val {i} D.property hd (by simp)).1]
    simp [hi]
    norm_num

end Atlas.Fischer
