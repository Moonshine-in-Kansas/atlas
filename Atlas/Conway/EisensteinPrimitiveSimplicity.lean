import Atlas.Conway.EisensteinLocalPhasesNormal
import Atlas.GroupTheory.PrimitivePerfectStabilizer
import Atlas.GroupTheory.IwasawaStabilizer

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices MulAction

theorem eisensteinProjectivePhases_ne_bot : eisensteinProjectivePhases ≠ ⊥ := by
  intro h
  have hc := eisensteinProjectivePhases_card
  rw [h] at hc
  simp at hc

theorem eisensteinProjectiveStabilizer_ne_bot :
    stabilizer EisensteinProjectiveModel eisensteinStandardFrame ≠ ⊥ := by
  intro h
  exact eisensteinProjectivePhases_ne_bot (le_antisymm
    (h ▸ eisensteinProjectivePhases_le_stabilizer) bot_le)

theorem eisensteinProjective_nontrivial : Nontrivial EisensteinProjectiveModel := by
  obtain ⟨F,h,hm⟩ := eisensteinLocalProjective_moves
  apply nontrivial_of_ne (eisensteinLocalProjectiveEmbedding h) 1
  intro he
  exact hm (by rw [he,one_smul])

/-- This helper isolates the remaining geometric premise. It is not an
unconditional simplicity certificate: primitivity must be supplied by S4. -/
theorem eisensteinPhase_normalClosure_of_primitive
    [IsPreprimitive EisensteinProjectiveModel EisensteinFrame] :
    Subgroup.normalClosure (eisensteinProjectivePhases : Set EisensteinProjectiveModel) = ⊤ := by
  have hn : Subgroup.normalClosure
      (eisensteinProjectivePhases : Set EisensteinProjectiveModel) ≠ ⊥ := by
    intro h
    have he : eisensteinProjectivePhases ≤ Subgroup.normalClosure
        (eisensteinProjectivePhases : Set EisensteinProjectiveModel) := Subgroup.le_normalClosure
    rw [h] at he
    exact eisensteinProjectivePhases_ne_bot (le_antisymm he bot_le)
  have hs : stabilizer EisensteinProjectiveModel eisensteinStandardFrame ≤
      Subgroup.normalClosure (eisensteinProjectivePhases : Set EisensteinProjectiveModel) := by
    rw [← eisensteinLocalProjectiveEmbedding_range]
    exact eisensteinLocal_le_phase_normalClosure
  exact Atlas.GroupTheory.normal_eq_top_of_full_stabilizer _ hn eisensteinStandardFrame hs

theorem eisensteinPerfect_of_primitive
    [IsPreprimitive EisensteinProjectiveModel EisensteinFrame] :
    Group.IsPerfect EisensteinProjectiveModel := by
  letI := eisensteinProjectiveStabilizer_perfect
  exact Atlas.GroupTheory.perfect_of_perfect_stabilizer eisensteinStandardFrame
    eisensteinProjectiveStabilizer_ne_bot

theorem eisensteinSimplicity_of_primitive
    [IsPreprimitive EisensteinProjectiveModel EisensteinFrame] :
    IsSimpleGroup EisensteinProjectiveModel := by
  letI := eisensteinProjective_nontrivial
  letI := eisensteinPerfect_of_primitive
  exact Atlas.GroupTheory.iwasawa_stabilizer_simple eisensteinStandardFrame
    eisensteinProjectivePhases eisensteinProjectivePhases_le_stabilizer
    eisensteinProjectivePhases_normal eisensteinProjectivePhases_abelian
    eisensteinPhase_normalClosure_of_primitive

theorem eisensteinNonabelian_of_primitive
    [IsPreprimitive EisensteinProjectiveModel EisensteinFrame] :
    ¬ IsMulCommutative EisensteinProjectiveModel := by
  letI := eisensteinProjective_nontrivial
  letI := eisensteinPerfect_of_primitive
  exact Group.IsPerfect.not_isMulCommutative EisensteinProjectiveModel

end Atlas.Conway
