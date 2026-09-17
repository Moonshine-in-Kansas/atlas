import Atlas.LinearGroups.Orthogonal.SingularTriangleKernel
import Atlas.LinearGroups.Orthogonal.B1ConjugationComparison
import Atlas.LinearGroups.Orthogonal.SingularProjectiveAction

/-! # Actual rank-one B singular-line faithfulness over every field -/
noncomputable section
namespace Atlas.Orthogonal
open scoped LinearAlgebra.Projectivization
variable {F : Type*} [Field F]

theorem B1_projective_singular_faithful :
    FaithfulSMul (ProjectiveElementary (formB 1 F)) (SingularPoints (formB 1 F)) := by
  apply faithfulSMul_iff.mpr
  intro g hg
  obtain ⟨a,rfl⟩ := projectiveElementaryMap_surjective (formB 1 F) g
  have hx : ∀ x : VectorB 1 F, formB 1 F x = 0 → ∃ c : F, a.val.val x = c • x := by
    intro x hq
    by_cases hz : x = 0
    · subst x
      exact ⟨1,by simp⟩
    · have h := congrArg Subtype.val (hg (singularPointMk _ x hz hq))
      change a.val.val • Projectivization.mk F x hz = Projectivization.mk F x hz at h
      rw [Projectivization.smul_mk,Projectivization.mk_eq_mk_iff'] at h
      obtain ⟨c,hc⟩ := h
      refine ⟨c,?_⟩
      simpa only [LinearEquiv.smul_def] using hc.symm
  have he : formB 1 F (e 0,0) = 0 := by simp [formB_apply,formD_apply,e]
  have hf : formB 1 F (f 0,0) = 0 := by simp [formB_apply,formD_apply,f]
  have hs : formB 1 F (e 0-f 0,1) = 0 := by simp [formB_apply,formD_apply,e,f,Pi.single_apply]
  have hef : (formB 1 F).polarBilin (e 0,0) (f 0,0) = 1 := by
    simp [-QuadraticMap.polarBilin_apply_apply,polarB_apply,polarD_apply,e,f,Pi.single_apply]
  have hes : (formB 1 F).polarBilin (e 0,0) (e 0-f 0,1) ≠ 0 := by
    simp [-QuadraticMap.polarBilin_apply_apply,polarB_apply,polarD_apply,e,f,Pi.single_apply]
  have hfs : (formB 1 F).polarBilin (f 0,0) (e 0-f 0,1) ≠ 0 := by
    simp [-QuadraticMap.polarBilin_apply_apply,polarB_apply,polarD_apply,e,f,Pi.single_apply]
  obtain ⟨c,hc,hca⟩ := singular_line_kernel_scalar_of_triangle (formB 1 F)
    (e 0,0) (f 0,0) (e 0-f 0,1) he hf hs hef hes hfs a.val hx
  have ha : a ∈ elementaryScalarSubgroup (formB 1 F) := ⟨c,hc,hca⟩
  rw [B1Conjugation.elementaryScalar_eq_bot,Subgroup.mem_bot] at ha
  rw [ha,map_one]
end Atlas.Orthogonal
