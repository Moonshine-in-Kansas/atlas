import Atlas.Fischer.CubicQuadrilateralRowConditions

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

 theorem cubicQuadrilateralRow_weight (D F G : Octad) (n : Fin 8)
    (h : CubicQuadrilateralRow D F G n) :
    cubicQuadrilateralNormalizedWeight D F G = cubicQuadrilateralRowWeight n := by
  have ha := cubicQuadrilateralRow_admissible D F G n h
  rw [cubicQuadrilateralNormalizedWeight,dif_pos ha.1,dif_pos ha.2.1,dif_pos ha.2.2]
  fin_cases n
  all_goals dsimp [CubicQuadrilateralRow] at h
  · rw [cubicQuadrilateral_weight_four D F G h.1 h.2.1 h.2.2.1,h.2.2.2]
    norm_num [cubicQuadrilateralRowWeight,parkerScalarSign] <;> decide
  · rw [cubicQuadrilateral_weight_four D F G h.1 h.2.1 h.2.2.1,h.2.2.2]
    norm_num [cubicQuadrilateralRowWeight,parkerScalarSign] <;> decide
  · rw [cubicQuadrilateral_weight_four D F G h.1 h.2.1 h.2.2.1,h.2.2.2]
    norm_num [cubicQuadrilateralRowWeight,parkerScalarSign] <;> decide
  · rw [cubicQuadrilateral_weight_four D F G h.1 h.2.1 h.2.2.1,h.2.2.2]
    norm_num [cubicQuadrilateralRowWeight,parkerScalarSign] <;> decide
  · exact cubicQuadrilateral_weight_four_four_zero D F G h.1 h.2.1 h.2.2
  · exact cubicQuadrilateral_weight_one_empty D F G ha.1 ha.2.1 ha.2.2 h.1
  · exact cubicQuadrilateral_weight_zero_zero_four D F G h.1 h.2.1 h.2.2
  · exact cubicQuadrilateral_weight_zero_zero_zero D F G h.1 h.2.1 h.2.2

 theorem cubicQuadrilateralRow_intersection (D F G : Octad) (n : Fin 8)
    (h : CubicQuadrilateralRow D F G n) :
    (D.val ∩ (cubicQuadrilateralLabel F G).val).card = cubicQuadrilateralRowIntersection n := by
  have ha := cubicQuadrilateralRow_admissible D F G n h
  rw [cubicQuadrilateralLabel,dif_pos ha.2.2,cubicOctadDiamond_intersection]
  fin_cases n
  all_goals dsimp [CubicQuadrilateralRow] at h
  · rw [h.1,h.2.1,h.2.2.1,h.2.2.2]
    norm_num [cubicQuadrilateralRowIntersection]
  · rw [h.1,h.2.1,h.2.2.1,h.2.2.2]
    norm_num [cubicQuadrilateralRowIntersection]
  · rw [h.1,h.2.1,h.2.2.1,h.2.2.2]
    norm_num [cubicQuadrilateralRowIntersection]
  · rw [h.1,h.2.1,h.2.2.1,h.2.2.2]
    norm_num [cubicQuadrilateralRowIntersection]
  · simp [h.1,h.2.1,h.2.2,cubicQuadrilateralRowIntersection]
  · have hz := cubicTripleIntersection_zero_of_pair D F G (by omega)
    rw [hz]
    rcases h.1 with ⟨hf,hg⟩ | ⟨hf,hg⟩ <;> rcases h.2 with hk | hk <;>
      simp [hf,hg,hk,hz,cubicQuadrilateralRowIntersection]
  · have hz := cubicTripleIntersection_zero_of_pair D F G (Or.inl h.1)
    rw [hz]
    simp [h.1,h.2.1,h.2.2,cubicQuadrilateralRowIntersection]
  · simp [h.1,h.2.1,h.2.2,cubicQuadrilateralRowIntersection]

 theorem cubicQuadrilateralRow_sum (D F G : Octad) (v : Fin 8 → Scalar)
    (n : Fin 8) (hn : CubicQuadrilateralRow D F G n) :
    (∑ m,if CubicQuadrilateralRow D F G m then v m else 0) = v n := by
  rw [Finset.sum_eq_single n]
  · simp [hn]
  · intro m _ hmn
    have hm : ¬ CubicQuadrilateralRow D F G m :=
      fun h => hmn (cubicQuadrilateralRow_unique D F G m n h hn)
    simp [hm]
  · simp

 theorem cubicQuadrilateralNormalizedWeight_rows (D F G : Octad) :
    cubicQuadrilateralNormalizedWeight D F G =
      ∑ n,if CubicQuadrilateralRow D F G n then cubicQuadrilateralRowWeight n else 0 := by
  by_cases h : OctadPairAdmissible D F ∧ OctadPairAdmissible D G ∧ OctadPairAdmissible F G
  · obtain ⟨n,hn⟩ := cubicQuadrilateralRow_exhaustive D F G h.1 h.2.1 h.2.2
    rw [cubicQuadrilateralRow_sum D F G _ n hn,cubicQuadrilateralRow_weight D F G n hn]
  · have hn (n : Fin 8) : ¬ CubicQuadrilateralRow D F G n :=
      fun hn => h (cubicQuadrilateralRow_admissible D F G n hn)
    simp only [hn,ite_false,Finset.sum_const_zero]
    unfold cubicQuadrilateralNormalizedWeight
    split_ifs <;> tauto

 theorem cubicQuadrilateralNormalizedWeight_moment_rows (D F G : Octad) :
    cubicQuadrilateralNormalizedWeight D F G *
      ((D.val ∩ (cubicQuadrilateralLabel F G).val).card : Scalar) =
      ∑ n,if CubicQuadrilateralRow D F G n then
        cubicQuadrilateralRowWeight n * (cubicQuadrilateralRowIntersection n : Scalar) else 0 := by
  by_cases h : OctadPairAdmissible D F ∧ OctadPairAdmissible D G ∧ OctadPairAdmissible F G
  · obtain ⟨n,hn⟩ := cubicQuadrilateralRow_exhaustive D F G h.1 h.2.1 h.2.2
    rw [cubicQuadrilateralRow_sum D F G _ n hn,cubicQuadrilateralRow_weight D F G n hn,
      cubicQuadrilateralRow_intersection D F G n hn]
  · have hn (n : Fin 8) : ¬ CubicQuadrilateralRow D F G n :=
      fun hn => h (cubicQuadrilateralRow_admissible D F G n hn)
    rw [cubicQuadrilateralNormalizedWeight_rows]
    simp [hn]

end Atlas.Fischer
