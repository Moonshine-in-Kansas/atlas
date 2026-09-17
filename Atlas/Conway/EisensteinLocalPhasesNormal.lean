import Atlas.Conway.EisensteinProjectivePhases

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices MulAction

/-- The actual local phase subgroup is normal inside the full intrinsic-frame
stabilizer. This is independent of global transitivity. -/
theorem eisensteinProjectivePhases_normal :
    (eisensteinProjectivePhases.subgroupOf
      (stabilizer EisensteinProjectiveModel eisensteinStandardFrame)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff eisensteinProjectivePhases_le_stabilizer).mpr
  intro a g ha hg
  obtain ⟨h, rfl⟩ := eisensteinLocalProjectiveEmbedding_range.symm ▸ hg
  obtain ⟨e, he, rfl⟩ := ha
  have hnormal : ternaryLocalPhaseNormal.Normal := by
    unfold ternaryLocalPhaseNormal
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  refine ⟨h*e*h⁻¹, hnormal.conj_mem e he h, ?_⟩
  simp only [map_mul,map_inv]

/-- The full frame stabilizer of the actual scalar quotient is perfect. -/
theorem eisensteinProjectiveStabilizer_perfect :
    Group.IsPerfect (stabilizer EisensteinProjectiveModel eisensteinStandardFrame) := by
  rw [← eisensteinLocalProjectiveEmbedding_range]
  letI := ternaryLocalPhaseGroup_perfect
  exact Group.IsPerfect.range eisensteinLocalProjectiveEmbedding

end Atlas.Conway
