import Atlas.Fischer.CubicOctadCoordinateAveraging
import Atlas.Fischer.CubicTriangleAction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Reindexing an actual finite geometric family gives fixed-octad invariance. -/
theorem cubicWeightedIncidence_invariant {I : Type*} [Fintype I] (D : Octad)
    (L : I → Octad) (w : I → Scalar)
    (e : MathieuOctadStabilizer D → Equiv.Perm I)
    (hL : ∀ g a, L (e g a) = g.val • L a)
    (hw : ∀ g a, w (e g a) = w a) :
    CubicOctadCoordinateInvariant D (fun p => ∑ a,w a * cubicPointOctadIncidence p (L a)) := by
  intro g p
  change (∑ a,w a * cubicPointOctadIncidence (g.val.val p) (L a)) = _
  rw [← Equiv.sum_comp (e g)]
  apply Finset.sum_congr rfl
  intro a _
  rw [hw,hL,cubicTriangle_incidence_smul]

theorem cubicIncidence_inside_sum (D E : Octad) :
    (∑ i : OctadInterior D, cubicPointOctadIncidence i.val E) =
      4 * ((D.val ∩ E.val).card : Scalar) - 8 := by
  rw [Finset.sum_coe_sort D.val (fun i => cubicPointOctadIncidence i E)]
  have he (i : Omega) : cubicPointOctadIncidence i E =
      4 * (if i ∈ E.val then (1 : Scalar) else 0) - 1 := by
    unfold cubicPointOctadIncidence
    split_ifs <;> norm_num
  simp_rw [he]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_filter,Finset.sum_const,
    Finset.sum_const,octad_size D.val D.property]
  have hs : D.val.filter (fun i => i ∈ E.val) = D.val ∩ E.val := by ext i; simp
  simp [hs]

theorem cubicIncidence_outside_sum (D E : Octad) :
    (∑ i : OctadExterior D, cubicPointOctadIncidence i.val E) =
      16 - 4 * ((D.val ∩ E.val).card : Scalar) := by
  have h : (∑ i : OctadInterior D, cubicPointOctadIncidence i.val E) +
      (∑ i : OctadExterior D, cubicPointOctadIncidence i.val E) =
      ∑ i : Omega,cubicPointOctadIncidence i E := by
    convert Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ D.val)
      (fun i => cubicPointOctadIncidence i E) using 1
    congr 1 <;> apply Finset.sum_congr (by ext x; simp) <;> intros <;> rfl
  rw [cubicIncidence_inside_sum,cubicPointOctadIncidence_sum] at h
  linear_combination h

theorem cubicWeightedIncidence_inside {I : Type*} [Fintype I] (D : Octad)
    (L : I → Octad) (w : I → Scalar)
    (hf : CubicOctadCoordinateInvariant D (fun p => ∑ a,w a * cubicPointOctadIncidence p (L a)))
    (i : OctadInterior D) :
    (∑ a,w a * cubicPointOctadIncidence i.val (L a)) =
      (1 / 2 : Scalar) * (∑ a,w a * ((D.val ∩ (L a).val).card : Scalar)) - ∑ a,w a := by
  have h := cubicOctadInvariant_inside_average D _ hf i
  rw [Finset.sum_comm] at h
  simp only [← Finset.mul_sum,cubicIncidence_inside_sum,mul_sub] at h
  rw [Finset.sum_sub_distrib] at h
  have h1 : (∑ a,w a * (4 * ((D.val ∩ (L a).val).card : Scalar))) =
      4 * ∑ a,w a * ((D.val ∩ (L a).val).card : Scalar) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [h1,← Finset.sum_mul] at h
  linear_combination -(1 / 8 : Scalar) * h

theorem cubicWeightedIncidence_outside {I : Type*} [Fintype I] (D : Octad)
    (L : I → Octad) (w : I → Scalar)
    (hf : CubicOctadCoordinateInvariant D (fun p => ∑ a,w a * cubicPointOctadIncidence p (L a)))
    (i : OctadExterior D) :
    (∑ a,w a * cubicPointOctadIncidence i.val (L a)) =
      (∑ a,w a) - (1 / 4 : Scalar) * ∑ a,w a * ((D.val ∩ (L a).val).card : Scalar) := by
  have h := cubicOctadInvariant_outside_average D _ hf i
  rw [Finset.sum_comm] at h
  simp only [← Finset.mul_sum,cubicIncidence_outside_sum,mul_sub] at h
  rw [Finset.sum_sub_distrib] at h
  have h1 : (∑ a,w a * (4 * ((D.val ∩ (L a).val).card : Scalar))) =
      4 * ∑ a,w a * ((D.val ∩ (L a).val).card : Scalar) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [h1,← Finset.sum_mul] at h
  linear_combination -(1 / 16 : Scalar) * h

end Atlas.Fischer
