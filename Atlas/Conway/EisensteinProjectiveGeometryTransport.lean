import Atlas.Conway.EisensteinProjectiveFusion
import Mathlib.GroupTheory.GroupAction.Primitive

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Lattices MulAction

theorem eisensteinProjectiveProjection_surjective :
    Function.Surjective eisensteinProjectiveProjection :=
  (QuotientGroup.mk'_surjective eisensteinCentralizerScalars).comp
    eisensteinCentralizerEquiv.surjective

theorem eisensteinProjectiveProjection_smul (g : eisensteinHermitianGroup)
    (F : EisensteinFrame) : eisensteinProjectiveProjection g • F = g • F :=
  eisensteinProjectiveFrameAction_mk g F

/-- The quotient stabilizer has exactly the same suborbits as the full linear
stabilizer, for the actual quotient action on intrinsic frames. -/
theorem eisensteinProjectiveStabilizer_orbit (F : EisensteinFrame) :
    orbit (stabilizer EisensteinProjectiveModel eisensteinStandardFrame) F =
      orbit eisensteinCoordinateFrameStabilizer F := by
  ext X
  constructor
  · rintro ⟨g,rfl⟩
    obtain ⟨c,hc⟩ := eisensteinProjectiveProjection_surjective g.val
    have hn : c ∈ eisensteinCoordinateFrameStabilizer := by
      rw [← eisensteinStandardFrame_stabilizer]
      change c • eisensteinStandardFrame = eisensteinStandardFrame
      rw [← eisensteinProjectiveProjection_smul,hc]
      exact g.property
    refine ⟨⟨c,hn⟩,?_⟩
    change c • F = g.val • F
    rw [← eisensteinProjectiveProjection_smul,hc]
  · rintro ⟨g,rfl⟩
    have hn : eisensteinProjectiveProjection g.val ∈
        stabilizer EisensteinProjectiveModel eisensteinStandardFrame := by
      change eisensteinProjectiveProjection g.val • eisensteinStandardFrame = _
      rw [eisensteinProjectiveProjection_smul]
      have hg : g.val ∈ stabilizer eisensteinHermitianGroup eisensteinStandardFrame :=
        (le_of_eq eisensteinStandardFrame_stabilizer.symm) g.property
      exact hg
    refine ⟨⟨eisensteinProjectiveProjection g.val,hn⟩,?_⟩
    exact eisensteinProjectiveProjection_smul g.val F

theorem eisensteinProjective_transitive_of_linear
    [IsPretransitive eisensteinHermitianGroup EisensteinFrame] :
    IsPretransitive EisensteinProjectiveModel EisensteinFrame := by
  constructor
  intro F H
  obtain ⟨g,hg⟩ := exists_smul_eq eisensteinHermitianGroup F H
  exact ⟨eisensteinProjectiveProjection g,(eisensteinProjectiveProjection_smul g F).trans hg⟩

theorem eisensteinProjective_primitive_of_linear
    [IsPreprimitive eisensteinHermitianGroup EisensteinFrame] :
    IsPreprimitive EisensteinProjectiveModel EisensteinFrame := by
  let f : EisensteinFrame →ₑ[eisensteinProjectiveProjection] EisensteinFrame :=
    ⟨id,fun g F => (eisensteinProjectiveProjection_smul g F).symm⟩
  exact IsPreprimitive.of_surjective (f := f) Function.surjective_id

end Atlas.Conway
