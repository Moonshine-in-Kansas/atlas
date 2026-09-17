import Atlas.Fischer.CubicOctadNeighborIncidence
import Atlas.Fischer.CubicOctadPointGram

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The actual unsigned neighboring-octad contribution, retaining the cubic
slice norm and its point-coordinate Gram pairing. -/
def cubicOctadUnsignedNeighborContribution (i : Omega) (D : Octad) : Scalar :=
  2*∑ E : Octad,(∑ F : Octad,coordinateCubic (.inr D) (.inr E) (.inr F)*
    star (coordinateCubic (.inr D) (.inr E) (.inr F)))*
    cubicOctadPointGram D E*cubicPointOctadIncidence i E

theorem cubicOctadUnsignedNeighborContribution_eq (i : Omega) (D : Octad) :
    cubicOctadUnsignedNeighborContribution i D=
      (if i ∈ D.val then 215/4 else 225/4)*cubicPointOctadIncidence i D := by
  have he (E : Octad) :
      2*((∑ F : Octad,coordinateCubic (.inr D) (.inr E) (.inr F)*
        star (coordinateCubic (.inr D) (.inr E) (.inr F)))*
        cubicOctadPointGram D E*cubicPointOctadIncidence i E)=
      (3/8 : Scalar)*(if (D.val ∩ E.val).card=4 then cubicPointOctadIncidence i E else 0)-
      (15/8 : Scalar)*(if (D.val ∩ E.val).card=0 then cubicPointOctadIncidence i E else 0) := by
    rw [coordinateCubic_octad_row_norm]
    by_cases h4 : (D.val ∩ E.val).card=4
    · have h0 : (D.val ∩ E.val).card ≠ 0 := by omega
      rw [cubicOctadPointGram_four D E h4]
      simp [h4,h0]
      ring
    · by_cases h0 : (D.val ∩ E.val).card=0
      · rw [cubicOctadPointGram_zero D E h0]
        simp [h4,h0]
        ring
      · simp [h4,h0]
  unfold cubicOctadUnsignedNeighborContribution
  rw [Finset.mul_sum]
  simp_rw [he]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,
    cubicOctad_neighbor_four_incidence,cubicOctad_neighbor_zero_incidence]
  by_cases hi : i ∈ D.val <;> simp [hi,cubicPointOctadIncidence] <;> norm_num

end Atlas.Fischer
