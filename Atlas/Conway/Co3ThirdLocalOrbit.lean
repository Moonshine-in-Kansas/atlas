import Atlas.Conway.Co3LocalAction

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem co3LocalType_two_iff (q : Co3PointHeptad co3MarkedCoordinate) :
    co3LocalType _ co3BasePoint q = 2 ↔
      ∃ C : Co3Heptads co3MarkedCoordinate, co3BasePoint ∈ C.val ∧ q = Sum.inr C := by
  cases q with
  | inl c => simp only [co3LocalType]; split_ifs <;> simp
  | inr C => simp [co3LocalType]

theorem co3Fusion_moves_through_vector (p : Mathieu24CodeModel)
    (hp : ∀ a ∈ co3FusionTriple, p.val a = a)
    (hO : permuteBlock p.val (distinguishedTrio 0) = co3FusionTarget) :
    ∃ F : Co3Heptads co3MarkedCoordinate, co3BasePoint ∈ F.val ∧
      (co3FusionIsometry p).val (co3HeptadEndpoint _ F) ∉
        co3ThroughHeptadVectors co3MarkedCoordinate co3BasePoint := by
  by_contra hn
  push_neg at hn
  apply co3Fusion_not_preserves_through p hp hO
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨F,hF,rfl⟩ := (co3ThroughHeptadVectors_mem _ _ _).mp hz
    exact hn F hF
  · rw [Finset.card_image_of_injective _ (co3FusionIsometry p).val.injective]

theorem co3_third_local_fusion : ∃ g : Co3PointStabilizer,
    ∃ F : Co3Heptads co3MarkedCoordinate, ∃ q : Co3PointHeptad co3MarkedCoordinate,
      co3BasePoint ∈ F.val ∧ co3LocalType _ co3BasePoint q ≠ 2 ∧
      g • co3PointHeptadDecompositionEquiv _ (Sum.inr F) = co3PointHeptadDecompositionEquiv _ q := by
  obtain ⟨p,hp,hO⟩ := co3Fusion_permutation_exists
  let g0 : Co3MarkedModel := ⟨co3FusionIsometry p,co3Fusion_fixes_normSix p hp⟩
  let g : Co3PointStabilizer := ⟨g0,co3Fusion_fixes_base_decomposition p hp⟩
  obtain ⟨F,hF,hout⟩ := co3Fusion_moves_through_vector p hp hO
  obtain ⟨q,hq⟩ := (co3PointHeptadDecompositionEquiv co3MarkedCoordinate).surjective
    (g • co3PointHeptadDecompositionEquiv _ (Sum.inr F))
  refine ⟨g,F,q,hF,?_,hq.symm⟩
  intro htype
  obtain ⟨C,hC,rfl⟩ := co3LocalType_two_iff q |>.mp htype
  have he := congrArg Subtype.val hq
  change ({co3HeptadEndpoint _ C,normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ C} : Finset leech) =
    ({co3HeptadEndpoint _ F,normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ F} : Finset leech).image
      (co3FusionIsometry p).val at he
  have hm : (co3FusionIsometry p).val (co3HeptadEndpoint _ F) ∈
      ({co3HeptadEndpoint _ C,normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ C} : Finset leech) := by
    rw [he]; exact Finset.mem_image.mpr ⟨_,Finset.mem_insert_self _ _,rfl⟩
  rcases Finset.mem_insert.mp hm with h | h
  · exact hout ((co3ThroughHeptadVectors_mem _ _ _).mpr ⟨C,hC,h.symm⟩)
  · have h := Finset.mem_singleton.mp h
    have hd := (co3FusionIsometry p).prop (minimumPairPlus co3MarkedCoordinate co3BasePoint.val)
      (co3HeptadEndpoint _ F)
    rw [co3Fusion_fixes_base_endpoint p hp,h,co3Point_heptad_complement_dot,
      co3Point_heptad_dot,if_pos hC,if_pos hF] at hd
    norm_num at hd

end Atlas.Conway
