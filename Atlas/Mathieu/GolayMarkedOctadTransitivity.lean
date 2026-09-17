import Atlas.Mathieu.GolaySmallSetFixing

noncomputable section
namespace Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem mathieu24_marked_octad_transitive (A O P : Finset Omega)
    (hA : A.card ≤ 5) (hO : O ∈ octads) (hP : P ∈ octads)
    (hAO : A ⊆ O) (hAP : A ⊆ P) :
    ∃ g : Mathieu24CodeModel, (∀ a ∈ A, g.val a = a) ∧ permuteBlock g.val O = P := by
  have hnO : 5 - A.card ≤ (O \ A).card := by
    rw [Finset.card_sdiff_of_subset hAO,octad_size O hO]
    omega
  have hnP : 5 - A.card ≤ (P \ A).card := by
    rw [Finset.card_sdiff_of_subset hAP,octad_size P hP]
    omega
  obtain ⟨S,hSO,hS⟩ := Finset.exists_subset_card_eq hnO
  obtain ⟨T,hTP,hT⟩ := Finset.exists_subset_card_eq hnP
  have hAS : Disjoint A S := Finset.disjoint_left.mpr (fun a ha hs =>
    (Finset.mem_sdiff.mp (hSO hs)).2 ha)
  have hAT : Disjoint A T := Finset.disjoint_left.mpr (fun a ha ht =>
    (Finset.mem_sdiff.mp (hTP ht)).2 ha)
  obtain ⟨g,hgA,hg⟩ := mathieu24_fixing_small_set_transitive A S T (5-A.card)
    hAS hAT hS hT (by omega)
  refine ⟨g,hgA,?_⟩
  apply octad_unique_on_five (A ∪ T) _ P
  · rw [Finset.card_union_of_disjoint hAT,hT]
    omega
  · exact (codePreserving_octadPreserving g.val g.prop O).mp hO
  · exact hP
  · apply Finset.union_subset
    · intro a ha
      exact Finset.mem_image.mpr ⟨a,hAO ha,hgA a ha⟩
    · rw [← hg]
      exact Finset.image_subset_image (hSO.trans Finset.sdiff_subset)
  · exact Finset.union_subset hAP (hTP.trans Finset.sdiff_subset)

end Atlas.Codes
