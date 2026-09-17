import Atlas.LinearGroups.Orthogonal.SingularPointConnectors
import Atlas.LinearGroups.Orthogonal.NonperpendicularOrbit
import Atlas.LinearGroups.Orthogonal.SingularProjectiveAction
import Atlas.LinearGroups.Orthogonal.CenterStandard
import Atlas.GroupTheory.RankThreePrimitive

/-! # Faithfulness and primitivity for the actual odd B elementary action -/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F]

theorem singularPointsB_faithful (n : ℕ) (h2 : (2 : F) ≠ 0) :
    FaithfulSMul (elementarySubgroup (formB (n + 2) F))
      (SingularPoints (formB (n + 2) F)) := by
  apply faithfulSMul_iff.mpr
  intro g hg
  have hs := (fixes_singularPoints_iff_scalar _ (wittTwoFrameB n) g).mp hg
  have hc := elementaryScalarSubgroup_le_center _ hs
  rw [elementaryB_center_eq_bot n h2] at hc
  exact hc

theorem singularPointsB_primitive (n : ℕ) (h2 : (2 : F) ≠ 0) :
    MulAction.IsPreprimitive (elementarySubgroup (formB (n + 3) F))
      (SingularPoints (formB (n + 3) F)) := by
  letI := singularPointsB_pretransitive (n + 1) h2
  let Q := formB (n + 3) F
  let a := singularPointMk Q (wittTwoFrameB (n + 1)).e₁
    (Atlas.Quadratic.WittTwoFrame.first_ne_zero Q (wittTwoFrameB (n + 1))) (wittTwoFrameB (n + 1)).qe₁
  apply Atlas.GroupTheory.primitive_of_two_suborbits_and_connectors a
    (SingularPerp Q) (singularPerp_symmetric Q)
    (singular_stabilizerB_perpendicular_transitive n h2)
    (singular_stabilizer_nonperpendicular_transitive Q)
  · intro p r _ hpr
    exact singularPointsB_perpendicular_connector (n + 1) p r hpr
  · intro p r hpr _
    exact singularPointsB_nonperpendicular_connector (n + 1) h2 p r hpr
end Atlas.Orthogonal
