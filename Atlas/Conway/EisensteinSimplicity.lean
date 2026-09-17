import Atlas.Conway.EisensteinSuborbitPrimitivity
import Atlas.Conway.EisensteinPrimitiveSimplicity

noncomputable section
namespace Atlas.Conway

theorem eisensteinPhase_normalClosure :
    Subgroup.normalClosure (eisensteinProjectivePhases : Set EisensteinProjectiveModel)=⊤ := by
  letI := eisensteinProjective_frame_primitive
  exact eisensteinPhase_normalClosure_of_primitive

theorem eisensteinProjective_perfect : Group.IsPerfect EisensteinProjectiveModel := by
  letI := eisensteinProjective_frame_primitive
  exact eisensteinPerfect_of_primitive

/-- Simplicity of the actual centralizer modulo its six scalar isometries,
with every geometric and Iwasawa premise discharged for that same quotient. -/
theorem eisensteinProjective_simple : IsSimpleGroup EisensteinProjectiveModel := by
  letI := eisensteinProjective_frame_primitive
  exact eisensteinSimplicity_of_primitive

theorem eisensteinProjective_nonabelian : ¬ IsMulCommutative EisensteinProjectiveModel := by
  letI := eisensteinProjective_frame_primitive
  exact eisensteinNonabelian_of_primitive

end Atlas.Conway
