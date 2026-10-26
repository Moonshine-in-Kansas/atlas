import Atlas.LinearGroups.Orthogonal.Minus.RankTwoRoots
import Atlas.LinearGroups.Orthogonal.Minus.RankTwoTransport
import Atlas.LinearGroups.Orthogonal.RootGenerationFromLineTransport

/-! Structural identification of the actual Hermitian SL₂ image and elementary minus group. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Atlas.Quadratic Matrix
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem first_root_le_hermitian_range (hdeg : Module.finrank F K = 2) :
    rootSubgroup (form hdeg 1) (e 0,0)
      (by simp only [form_apply,formD_e,←normForm_apply hdeg,map_zero,add_zero]) ≤
      (hermitianHom hdeg).range := by
  rintro g ⟨w,rfl⟩
  let v : Vector 1 F K := w.toAdd.val
  have hv : (form hdeg 1).polarBilin (e 0,0) v = 0 := w.toAdd.prop
  have hvy : v.1 (.inr 0) = 0 := by
    have hv' : (form hdeg 1).polarBilin v (e 0,0) = 0 :=
      (polar_swap _ _ _).trans hv
    simpa only [polar_apply,polarD_e,map_zero,add_zero] using hv'
  have he : v = (0,v.2) + v.1 (.inl 0) • (e 0,0) := by
    apply Prod.ext
    · funext i
      cases i with
      | inl i => fin_cases i; simp [e]
      | inr i => fin_cases i; simpa [e,Pi.single_apply] using hvy
    · simp
  refine ⟨SpecialLinearGroup.transvection (by decide : (0:Fin 2) ≠ 1) v.2, ?_⟩
  rw [hermitianHom_upper]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change siegel (form hdeg 1) (e 0,0) (0,v.2) x =
    siegel (form hdeg 1) (e 0,0) v x
  conv_rhs => rw [he]
  symm
  apply siegel_parameter_mod_line
  · simp only [form_apply,formD_e,←normForm_apply hdeg,map_zero,add_zero]
  · simp only [polar_apply,map_zero,LinearMap.zero_apply,add_zero]

theorem elementary_le_hermitian_range (hdeg : Module.finrank F K = 2) :
    E hdeg 1 ≤ (hermitianHom hdeg).range := by
  apply elementary_le_of_root_and_line_transport (form hdeg 1) (hermitianHom hdeg).range
    (e 0,0) (by simp only [form_apply,formD_e,←normForm_apply hdeg,map_zero,add_zero])
    (first_root_le_hermitian_range hdeg)
  intro u hun hu
  obtain ⟨g,c,hc,hgu⟩ := hermitian_singular_line_transport hdeg u hun hu
  exact ⟨hermitianHom hdeg g,⟨g,rfl⟩,c,hc,hgu⟩

theorem hermitianHom_range_eq_elementary (hdeg : Module.finrank F K = 2) :
    (hermitianHom hdeg).range = E hdeg 1 :=
  le_antisymm (hermitianHom_range_le_elementary hdeg) (elementary_le_hermitian_range hdeg)

end Atlas.Orthogonal.Minus
