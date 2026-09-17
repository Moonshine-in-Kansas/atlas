import Atlas.Fischer.OctadQuadraticRestriction

namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra

 theorem octadExteriorWord_eq_zero_iff (O : Octad) (c : golay) :
    octadExteriorWord O c=0 ↔ ∀ i ∉ O.val, c.val i=0 := by
  constructor
  · intro h i hi
    have he := congrFun h (octadExteriorCoordinates O ⟨i,hi⟩)
    simpa [octadExteriorWord] using he
  · intro h
    funext v
    exact h _ ((octadExteriorCoordinates O).symm v).property

 theorem octadExteriorWord_kernel_cases (O : Octad) (c : golay)
    (hc : octadExteriorWord O c=0) : c=0 ∨ c=octadWord O := by
  classical
  by_cases hz : c=0
  · exact Or.inl hz
  right
  have hc0 : c.val ≠ 0 := fun h => hz (Subtype.ext h)
  have hs : support c.val ⊆ O.val := by
    intro i hi
    by_contra hn
    have hzi := (octadExteriorWord_eq_zero_iff O c).mp hc i hn
    simpa [support,hzi] using hi
  have hmin := golay_minimum c.val c.property hc0
  have he : support c.val=O.val := Finset.eq_of_subset_of_card_le hs (by
    rw [octad_size O.val O.property]
    exact hmin)
  apply Subtype.ext
  apply support_injective
  rw [he,octadWord_support]

 theorem octadExteriorWord_kernel (O : Octad) :
    (octadExteriorWord O).ker = Submodule.span Bit {octadWord O} := by
  apply le_antisymm
  · intro c hc
    rcases octadExteriorWord_kernel_cases O c hc with h | h
    · rw [h]; exact Submodule.zero_mem _
    · rw [h]; exact Submodule.subset_span (Set.mem_singleton _)
  · apply Submodule.span_le.mpr
    intro c hc
    have he : c=octadWord O := Set.mem_singleton_iff.mp hc
    rw [he]
    apply (octadExteriorWord_eq_zero_iff O (octadWord O)).mpr
    intro i hi
    simp [octadWord_apply,hi]

 theorem octadExteriorWord_finrank (O : Octad) :
    Module.finrank Bit (octadExteriorWord O).range=11 := by
  have hn : octadWord O ≠ 0 := by
    intro h
    have hw := octadWord_weight O
    rw [h] at hw
    simpa [hammingNorm] using hw
  have h := (octadExteriorWord O).finrank_range_add_finrank_ker
  rw [octadExteriorWord_kernel,finrank_span_singleton hn,golay_finrank] at h
  omega

/-- Actual puncturing of Golay is onto RM(2,4) in the retained affine coordinates;
no replacement code or weight-enumerator recognition is used. -/
theorem octadExteriorWord_range (O : Octad) :
    (octadExteriorWord O).range=binaryQuadraticCode := by
  apply Submodule.eq_of_le_of_finrank_le
  · rintro w ⟨c,rfl⟩
    exact octadExteriorWord_mem_quadratic O c
  · rw [binaryQuadraticCode_finrank,octadExteriorWord_finrank]

end Atlas.Fischer
