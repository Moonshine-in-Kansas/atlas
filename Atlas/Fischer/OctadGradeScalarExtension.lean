import Atlas.Fischer.OctadRealGrading

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped TensorProduct

def octadRationalGradeBasis (O : Octad) (S : Finset Omega) :
    Module.Basis (OctadRationalGradeIndex O S) ℚ (octadRationalGrade O S) :=
  Module.Basis.ofEquivFun (octadRationalGradeEquiv O S)

/-- Each real component is the scalar extension of the corresponding actual rational component. -/
def octadGradeScalarExtension (O : Octad) (S : Finset Omega) :
    (ℝ ⊗[ℚ] octadRationalGrade O S) ≃ₗ[ℝ] octadRealGrade O S :=
  ((octadRationalGradeBasis O S).baseChange ℝ).equivFun.trans
    (octadRealGradeEquiv O S).symm

theorem octadGradeScalarExtension_coordinate (O : Octad) (S : Finset Omega)
    (a : ℝ) (x : octadRationalGrade O S) (p : OctadRationalGradeIndex O S) :
    octadRealGradeEquiv O S (octadGradeScalarExtension O S (a ⊗ₜ[ℚ] x)) p =
      (octadRationalGradeEquiv O S x p : ℝ) * a := by
  change (octadRealGradeEquiv O S)
    ((octadRealGradeEquiv O S).symm
      (((octadRationalGradeBasis O S).baseChange ℝ).equivFun (a ⊗ₜ[ℚ] x))) p = _
  rw [LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply,
    Module.Basis.baseChange_repr_tmul]
  change (octadRationalGradeEquiv O S x p) • a = _
  exact Rat.smul_def _ _

/-- This equivalence is compatible with the ambient tensor scalar extension. -/
theorem octadGradeScalarExtension_tmul (O : Octad) (S : Finset Omega)
    (a : ℝ) (x : octadRationalGrade O S) :
    (octadGradeScalarExtension O S (a ⊗ₜ[ℚ] x)).val = a ⊗ₜ[ℚ] x.val := by
  classical
  apply realCoordinateEquiv.injective
  funext p
  rw [realCoordinateEquiv_tmul]
  by_cases hp : octadRationalLabel O p = S
  · exact octadGradeScalarExtension_coordinate O S a x ⟨p, hp⟩
  · rw [(octadGradeScalarExtension O S (a ⊗ₜ[ℚ] x)).prop p hp, x.prop p hp,
      Rat.cast_zero, zero_mul]

end Atlas.Fischer
