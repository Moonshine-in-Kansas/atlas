import Atlas.LinearGroups.Orthogonal.Minus.RankTwoHermitian
import Atlas.LinearGroups.Orthogonal.SpecialStandard
import Atlas.LinearGroups.Elementary

/-! Elementary SL₂ matrices act by the actual four-dimensional Siegel transformations. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Atlas.FiniteQuadratic Atlas.Quadratic Matrix
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem hermitianHom_upper (hdeg : Module.finrank F K = 2) (a : K) :
    hermitianHom hdeg (SpecialLinearGroup.transvection (by decide : (0:Fin 2) ≠ 1) a) =
      siegelElement (form hdeg 1) (e 0,0) (0,a) (by simp only [form_apply,formD_e,←normForm_apply hdeg,map_zero,add_zero])
        (by simp only [polar_apply,map_zero,LinearMap.zero_apply,add_zero]) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change hermitianTransform (SpecialLinearGroup.transvection (by decide : (0:Fin 2) ≠ 1) a).val x =
    siegel (form hdeg 1) (e 0,0) (0,a) x
  simp only [siegel,polar_apply,form_apply,normForm_polar,polarD_e]
  apply Prod.ext
  · funext i
    cases i with
    | inl i =>
      fin_cases i
      apply (algebraMap F K).injective
      simp [hermitianTransform,SpecialLinearGroup.transvection_coe,                e,Algebra.smul_def,norm_formula hdeg,
        trace_formula hdeg,map_add,map_sub,map_mul,conjugation_conjugation hdeg]
      ring
    | inr i =>
      fin_cases i
      simp [hermitianTransform,SpecialLinearGroup.transvection_coe,                e]
  · simp [hermitianTransform,SpecialLinearGroup.transvection_coe,            e,Algebra.smul_def]
    ring

theorem hermitianHom_lower (hdeg : Module.finrank F K = 2) (a : K) :
    hermitianHom hdeg (SpecialLinearGroup.transvection (by decide : (1:Fin 2) ≠ 0) a) =
      siegelElement (form hdeg 1) (f 0,0) (0,-conjugation F K a)
        (by simp only [form_apply,formD_f,←normForm_apply hdeg,map_zero,add_zero]) (by simp only [polar_apply,map_zero,LinearMap.zero_apply,add_zero]) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change hermitianTransform (SpecialLinearGroup.transvection (by decide : (1:Fin 2) ≠ 0) a).val x =
    siegel (form hdeg 1) (f 0,0) (0,-conjugation F K a) x
  simp only [siegel,polar_apply,form_apply,normForm_polar,polarD_f]
  apply Prod.ext
  · funext i
    cases i with
    | inl i =>
      fin_cases i
      simp [hermitianTransform,SpecialLinearGroup.transvection_coe,                f]
    | inr i =>
      fin_cases i
      apply (algebraMap F K).injective
      simp [hermitianTransform,SpecialLinearGroup.transvection_coe,                f,Algebra.smul_def,norm_formula hdeg,
        trace_formula hdeg,map_add,map_sub,map_mul,conjugation_conjugation hdeg]
      ring
  · simp [hermitianTransform,SpecialLinearGroup.transvection_coe,            f,Algebra.smul_def]
    ring

theorem hermitianHom_mem_elementary (hdeg : Module.finrank F K = 2)
    (g : SpecialLinearGroup (Fin 2) K) : hermitianHom hdeg g ∈ E hdeg 1 := by
  apply Atlas.sl_elementary_induction (fun g => hermitianHom hdeg g ∈ E hdeg 1) _ _ g
  · intro i j hij a
    fin_cases i <;> fin_cases j <;> try contradiction
    · rw [hermitianHom_upper]
      exact siegelElement_mem _ _ _ _ _
    · rw [hermitianHom_lower]
      exact siegelElement_mem _ _ _ _ _
  · intro g h hg hh
    rw [map_mul]
    exact (E hdeg 1).mul_mem hg hh

theorem hermitianHom_range_le_elementary (hdeg : Module.finrank F K = 2) :
    (hermitianHom hdeg).range ≤ E hdeg 1 := by
  rintro g ⟨a,rfl⟩
  exact hermitianHom_mem_elementary hdeg a
end Atlas.Orthogonal.Minus
