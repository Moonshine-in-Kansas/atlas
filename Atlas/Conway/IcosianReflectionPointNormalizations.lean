import Atlas.Conway.IcosianPointNormalizations
import Atlas.Conway.IcosianReflectionDiagonalImage

noncomputable section
namespace Atlas.Conway

/-- Every actual quaternionic root line is reached by actual root reflections.
This is separated from the independent incidence count. -/
theorem icosianReflectionGroup_point_normalizer (p : IcosianRootPoint) :
    ∃ g : icosianReflectionGroup,g.val • icosianRootAxisPoint 0=p := by
  obtain ⟨g,hg,he⟩ := icosianRootPoint_normalizers_in icosianReflectionGroup
    icosian_full_frame_generated_by_reflections icosianRootReflectionOf_mem p
  exact ⟨⟨g,hg⟩,he⟩

instance icosianReflectionGroup_rootPoint_pretransitive :
    MulAction.IsPretransitive icosianReflectionGroup IcosianRootPoint where
  exists_smul_eq p q := by
    obtain ⟨g,hg⟩ := icosianReflectionGroup_point_normalizer p
    obtain ⟨h,hh⟩ := icosianReflectionGroup_point_normalizer q
    refine ⟨h*g⁻¹,?_⟩
    change (h.val*g.val⁻¹) • p=q
    rw [mul_smul,← hg,inv_smul_smul,hh]

end Atlas.Conway
