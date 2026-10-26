import Atlas.LinearGroups.F4.LeviElementaryImage
import Atlas.LinearGroups.F4.LeviTorusImage
import Atlas.LinearGroups.Orthogonal.IntrinsicStandard
import Atlas.LinearGroups.Orthogonal.CompensatedTorus

/-! Structural lower inclusion of the full special orthogonal group in the
actual parabolic quotient image. No F₄ order theorem is used. -/
noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]

theorem levi_first_pair :
    (Atlas.Orthogonal.formB 3 F).polarBilin (leviSingularDirection 0) (leviSingularDirection 5)=1 := by
  simp [leviSingularDirection,leviShortDirection,QuadraticMap.polar,
    Atlas.Orthogonal.formD_apply,Fin.sum_univ_succ,Pi.single_apply]

def leviHyperbolicTorus (a : Fˣ) : Atlas.Orthogonal.O_B 3 F :=
  Atlas.Orthogonal.hyperbolicTorus (Atlas.Orthogonal.formB 3 F)
    (leviSingularDirection 0) (leviSingularDirection 5)
    (leviSingularDirection_singular 0) (leviSingularDirection_singular 5)
    levi_first_pair (a : F) a.ne_zero

theorem levi_hyperbolic_reflection_apply (c : F) (hc : c≠0)
    (x : Atlas.Orthogonal.VectorB 3 F) :
    (Atlas.Orthogonal.hyperbolicReflection (Atlas.Orthogonal.formB 3 F)
      (leviSingularDirection 0) (leviSingularDirection 5)
      (leviSingularDirection_singular 0) (leviSingularDirection_singular 5)
      levi_first_pair c hc).val x=
      x-(c⁻¹*(Atlas.Orthogonal.formB 3 F).polarBilin x
        (leviSingularDirection 0+c • leviSingularDirection 5)) •
          (leviSingularDirection 0+c • leviSingularDirection 5) := by
  change Atlas.Quadratic.reflectionLinear (Atlas.Orthogonal.formB 3 F)
    (leviSingularDirection 0+c • leviSingularDirection 5)
    (ne_of_eq_of_ne (Atlas.Orthogonal.hyperbolic_reflection_norm
      (Atlas.Orthogonal.formB 3 F) (leviSingularDirection 0) (leviSingularDirection 5)
      (leviSingularDirection_singular 0) (leviSingularDirection_singular 5)
      levi_first_pair c) hc) x=_
  rw [Atlas.Quadratic.reflectionLinear_apply,
    Atlas.Orthogonal.hyperbolic_reflection_norm _ _ _
      (leviSingularDirection_singular 0) (leviSingularDirection_singular 5) levi_first_pair]

set_option maxHeartbeats 2000000 in
theorem leviHyperbolicTorus_eq (a : Fˣ) :
    leviHyperbolicTorus a=leviDiagonal ![a,1,1] := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (Atlas.Orthogonal.hyperbolicReflection (Atlas.Orthogonal.formB 3 F)
      (leviSingularDirection 0) (leviSingularDirection 5)
      (leviSingularDirection_singular 0) (leviSingularDirection_singular 5)
      levi_first_pair 1 one_ne_zero).val
      ((Atlas.Orthogonal.hyperbolicReflection (Atlas.Orthogonal.formB 3 F)
        (leviSingularDirection 0) (leviSingularDirection 5)
        (leviSingularDirection_singular 0) (leviSingularDirection_singular 5)
        levi_first_pair (a : F) a.ne_zero).val x)=_
  rw [levi_hyperbolic_reflection_apply,levi_hyperbolic_reflection_apply]
  apply Prod.ext
  · ext i; cases i with
    | inl i => fin_cases i <;>
        simp [leviDiagonal,Atlas.Orthogonal.diagonalLinear,leviSingularDirection,
          leviShortDirection,QuadraticMap.polar,Atlas.Orthogonal.formD_apply,
          Fin.sum_univ_succ,Pi.single_apply] <;> field_simp <;> ring
    | inr i => fin_cases i <;>
        simp [leviDiagonal,Atlas.Orthogonal.diagonalLinear,leviSingularDirection,
          leviShortDirection,QuadraticMap.polar,Atlas.Orthogonal.formD_apply,
          Fin.sum_univ_succ,Pi.single_apply] <;> field_simp <;> ring
  · simp [leviDiagonal,leviSingularDirection]

theorem leviHyperbolicTorus_special (a : Fˣ) :
    leviHyperbolicTorus a∈Atlas.Orthogonal.specialSubgroup (Atlas.Orthogonal.formB 3 F) :=
  Atlas.Orthogonal.hyperbolicTorus_determinant _ _ _ _ _ _ _ _

theorem leviHyperbolicTorus_spinor (h2 : (2 : F)≠0) (a : Fˣ) :
    Atlas.Orthogonal.spinorNorm (Atlas.Orthogonal.formB 3 F)
      (Atlas.Orthogonal.polarB_nondegenerate h2) h2 (leviHyperbolicTorus a)=Atlas.squareClass F a := by
  have h := Atlas.Orthogonal.hyperbolicTorus_spinorNorm (Atlas.Orthogonal.formB 3 F)
    (Atlas.Orthogonal.polarB_nondegenerate h2) h2
    (leviSingularDirection 0) (leviSingularDirection 5)
    (leviSingularDirection_singular 0) (leviSingularDirection_singular 5)
    levi_first_pair (a : F) a.ne_zero
  have he : Units.mk0 (a : F) a.ne_zero=a := Units.ext rfl
  simpa only [he,leviHyperbolicTorus] using h

variable [Finite F]

/-- Every special orthogonal isometry of the actual seven-dimensional quotient
has a lift to the Albert marked-point stabilizer. This only asserts a lower inclusion. -/
theorem specialB3_le_parabolic_image :
    Atlas.Orthogonal.specialSubgroup (Atlas.Orthogonal.formB 3 F) ≤
      parabolicOrthogonalHom.range := by
  by_cases h2 : (2 : F)=0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    intro g _
    apply elementaryB3_le_parabolic_image
    rw [Atlas.Orthogonal.even_elementary_eq_top]
    trivial
  intro g hg
  let σ := Atlas.Orthogonal.spinorNorm (Atlas.Orthogonal.formB 3 F)
    (Atlas.Orthogonal.polarB_nondegenerate h2) h2
  obtain ⟨a,ha⟩ := Atlas.squareClass_surjective F (σ g)
  have ht : leviHyperbolicTorus a∈parabolicOrthogonalHom.range := by
    rw [leviHyperbolicTorus_eq]
    exact leviDiagonal_mem_parabolic_image _
  have he : g*(leviHyperbolicTorus a)⁻¹∈
      Atlas.Orthogonal.elementarySubgroup (Atlas.Orthogonal.formB 3 F) := by
    rw [Atlas.Orthogonal.elementaryB_eq_intrinsicKernel 1 h2]
    refine ⟨(Atlas.Orthogonal.specialSubgroup _).mul_mem hg
      ((Atlas.Orthogonal.specialSubgroup _).inv_mem (leviHyperbolicTorus_special a)),?_⟩
    change σ (g*(leviHyperbolicTorus a)⁻¹)=1
    rw [map_mul,map_inv]
    change σ g*(Atlas.Orthogonal.spinorNorm _ _ h2 (leviHyperbolicTorus a))⁻¹=1
    rw [leviHyperbolicTorus_spinor,ha,mul_inv_cancel]
  have hh := (parabolicOrthogonalHom.range).mul_mem (elementaryB3_le_parabolic_image he) ht
  simpa using hh

end Atlas.F4
