import Atlas.Conway.EisensteinSuborbitOrbits
import Atlas.Conway.EisensteinFullGeneration
import Atlas.Conway.EisensteinProjectiveGeometryTransport
import Atlas.GroupTheory.FiniteSuborbitFamilies

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Lattices MulAction
open scoped BigOperators
attribute [local irreducible] eisensteinNineHexadFamily

/-- The actual thirteen local suborbits and their subset-sum obstruction prove
primitivity of the full Hermitian frame action. -/
theorem eisensteinHermitian_frame_primitive :
    IsPreprimitive eisensteinHermitianGroup EisensteinFrame := by
  classical
  letI := eisensteinHermitian_frame_transitive
  apply Atlas.GroupTheory.primitive_of_suborbit_families eisensteinStandardFrame
    eisensteinSuborbitFinset (0 : Fin 13)
  · exact (eisensteinSuborbitFinset_mem 0 _).mpr rfl
  · intro F
    obtain ⟨i,hi⟩ := eisensteinSuborbitFrames_cover F
    exact ⟨i,(eisensteinSuborbitFinset_mem i F).mpr hi⟩
  · exact eisensteinSuborbitFinset_pairwise
  · intro i F H hF hH
    obtain ⟨g,hg⟩ := eisensteinSuborbitFrames_transitive i F H
      ((eisensteinSuborbitFinset_mem i F).mp hF) ((eisensteinSuborbitFinset_mem i H).mp hH)
    exact ⟨⟨g.val,(le_of_eq eisensteinStandardFrame_stabilizer.symm) g.property⟩,hg⟩
  · intro S h0 hd
    simp_rw [eisensteinSuborbitFinset_card] at hd ⊢
    rw [eisensteinFrame_card] at hd ⊢
    exact eisensteinSubdegree_block_arithmetic S h0 hd

theorem eisensteinProjective_frame_primitive :
    IsPreprimitive EisensteinProjectiveModel EisensteinFrame := by
  letI := eisensteinHermitian_frame_primitive
  exact eisensteinProjective_primitive_of_linear

end Atlas.Conway
