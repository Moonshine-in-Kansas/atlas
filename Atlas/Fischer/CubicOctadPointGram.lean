import Atlas.Fischer.CubicTriangleIncidence

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

/-- The Gram pairing of the actual point-coordinate parts of the octad
slices, using the retained inverse metric. It equals the normalized v_D·v_E. -/
def cubicOctadPointGram (D E : Octad) : Scalar :=
  ∑ i : Omega,inverseCoordinateMetric (.inl i)*
    coordinateCubic (.inl i) (.inr D) (.inr D)*
    coordinateCubic (.inl i) (.inr E) (.inr E)

theorem cubicOctadPointGram_eq (D E : Octad) :
    cubicOctadPointGram D E=((D.val ∩ E.val).card : Scalar)/2-5/4 := by
  have he (i : Omega) : inverseCoordinateMetric (.inl i)*
      coordinateCubic (.inl i) (.inr D) (.inr D)*
      coordinateCubic (.inl i) (.inr E) (.inr E)=
      (cubicPointOctadIncidence i D*cubicPointOctadIncidence i E)/32 := by
    rw [coordinateCubic_point_octads,coordinateCubic_point_octads]
    simp only [ite_true]
    norm_num [inverseCoordinateMetric,coordinateWeight]
    ring
  simp_rw [cubicOctadPointGram,he,← Finset.sum_div]
  rw [cubicPointOctadIncidence_overlap_sum]
  ring

theorem cubicOctadPointGram_self (D : Octad) : cubicOctadPointGram D D=11/4 := by
  rw [cubicOctadPointGram_eq,Finset.inter_self,octad_size D.val D.property]
  norm_num

theorem cubicOctadPointGram_four (D E : Octad) (h : (D.val ∩ E.val).card=4) :
    cubicOctadPointGram D E=3/4 := by
  rw [cubicOctadPointGram_eq,h]
  norm_num

theorem cubicOctadPointGram_zero (D E : Octad) (h : (D.val ∩ E.val).card=0) :
    cubicOctadPointGram D E= -5/4 := by
  rw [cubicOctadPointGram_eq,h]
  norm_num

/-- The two point-slice Gram-square occurrences in the repeated-octad row.
The value is derived from the actual cubic and metric, not supplied as data. -/
theorem cubicOctadPointGram_two_squares (D : Octad) :
    2*cubicOctadPointGram D D^2=121/8 := by
  rw [cubicOctadPointGram_self]
  norm_num

end Atlas.Fischer
