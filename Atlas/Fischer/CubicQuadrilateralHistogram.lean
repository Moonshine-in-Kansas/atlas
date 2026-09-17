import Atlas.Fischer.CubicQuadrilateralRowCounts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

 theorem cubicQuadrilateral_weight_total (D : Octad) :
    (∑ F : Octad,∑ G : Octad,cubicQuadrilateralNormalizedWeight D F G) = 8670 := by
  simp_rw [cubicQuadrilateralNormalizedWeight_rows]
  rw [cubicQuadrilateralRow_weighted_count]
  norm_num [Fin.sum_univ_succ,cubicQuadrilateralRowCard,cubicQuadrilateralRowWeight]

 theorem cubicQuadrilateral_weight_first_moment (D : Octad) :
    (∑ F : Octad,∑ G : Octad,cubicQuadrilateralNormalizedWeight D F G *
      ((D.val ∩ (cubicQuadrilateralLabel F G).val).card : Scalar)) = 89520 := by
  simp_rw [cubicQuadrilateralNormalizedWeight_moment_rows]
  rw [cubicQuadrilateralRow_weighted_count]
  norm_num [Fin.sum_univ_succ,cubicQuadrilateralRowCard,cubicQuadrilateralRowWeight,
    cubicQuadrilateralRowIntersection]

 theorem cubicQuadrilateral_histogram_pointwise (D F G : Octad) (k : ℕ) :
    cubicQuadrilateralNormalizedWeight D F G *
      (if (D.val ∩ (cubicQuadrilateralLabel F G).val).card = k then (1 : Scalar) else 0) =
    ∑ n,if CubicQuadrilateralRow D F G n then
      cubicQuadrilateralRowWeight n * (if cubicQuadrilateralRowIntersection n = k then 1 else 0) else 0 := by
  by_cases h : OctadPairAdmissible D F ∧ OctadPairAdmissible D G ∧ OctadPairAdmissible F G
  · obtain ⟨n,hn⟩ := cubicQuadrilateralRow_exhaustive D F G h.1 h.2.1 h.2.2
    rw [cubicQuadrilateralRow_sum D F G _ n hn,cubicQuadrilateralRow_weight D F G n hn,
      cubicQuadrilateralRow_intersection D F G n hn]
  · have hn (n : Fin 8) : ¬ CubicQuadrilateralRow D F G n :=
      fun hn => h (cubicQuadrilateralRow_admissible D F G n hn)
    rw [cubicQuadrilateralNormalizedWeight_rows]
    simp [hn]

def cubicQuadrilateralSignedHistogram (D : Octad) (k : ℕ) : Scalar :=
  ∑ F : Octad,∑ G : Octad,cubicQuadrilateralNormalizedWeight D F G *
    (if (D.val ∩ (cubicQuadrilateralLabel F G).val).card = k then 1 else 0)

 theorem cubicQuadrilateralSignedHistogram_eq (D : Octad) (k : ℕ) :
    cubicQuadrilateralSignedHistogram D k =
      ∑ n,(cubicQuadrilateralRowCard n : Scalar) * (cubicQuadrilateralRowWeight n *
        (if cubicQuadrilateralRowIntersection n = k then 1 else 0)) := by
  unfold cubicQuadrilateralSignedHistogram
  simp_rw [cubicQuadrilateral_histogram_pointwise]
  rw [cubicQuadrilateralRow_weighted_count]

/-- The source signed histogram, derived from actual octads and the actual
four cubic factors. -/
theorem cubicQuadrilateral_signed_histogram (D : Octad) :
    cubicQuadrilateralSignedHistogram D 8 = 550 ∧
    cubicQuadrilateralSignedHistogram D 4 = 30240 ∧
    cubicQuadrilateralSignedHistogram D 2 = -17920 ∧
    cubicQuadrilateralSignedHistogram D 0 = -4200 := by
  simp only [cubicQuadrilateralSignedHistogram_eq]
  norm_num [Fin.sum_univ_succ,cubicQuadrilateralRowCard,cubicQuadrilateralRowWeight,
    cubicQuadrilateralRowIntersection]

end Atlas.Fischer
