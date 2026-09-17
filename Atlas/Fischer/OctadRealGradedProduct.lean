import Atlas.Fischer.RealProduct
import Atlas.Fischer.OctadGradeScalarExtension
import Atlas.Fischer.OctadGradedProduct

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped TensorProduct symmDiff

def octadGradeScalarAmbient (O : Octad) (S : Finset Omega) :
    (ℝ ⊗[ℚ] octadRationalGrade O S) →ₗ[ℝ] RealCoordinates :=
  (octadRealGrade O S).subtype.comp (octadGradeScalarExtension O S).toLinearMap

/-- The symmetric-difference grading survives actual real extension of the product. -/
theorem octadRealGrade_product (O : Octad) (S T : Finset Omega)
    (x y : RealCoordinates) (hx : x ∈ octadRealGrade O S)
    (hy : y ∈ octadRealGrade O T) : realProduct x y ∈ octadRealGrade O (S ∆ T) := by
  have h (t : ℝ ⊗[ℚ] octadRationalGrade O S)
      (u : ℝ ⊗[ℚ] octadRationalGrade O T) :
      realProduct (octadGradeScalarAmbient O S t) (octadGradeScalarAmbient O T u) ∈
        octadRealGrade O (S ∆ T) := by
    induction t using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero, LinearMap.zero_apply]
      exact (octadRealGrade O (S ∆ T)).zero_mem
    | tmul a v =>
      induction u using TensorProduct.induction_on with
      | zero =>
        simp only [map_zero]
        exact (octadRealGrade O (S ∆ T)).zero_mem
      | tmul b w =>
        change realProduct (octadGradeScalarExtension O S (a ⊗ₜ[ℚ] v)).val
          (octadGradeScalarExtension O T (b ⊗ₜ[ℚ] w)).val ∈ _
        rw [octadGradeScalarExtension_tmul, octadGradeScalarExtension_tmul,
          realProduct_tmul]
        exact octadRealGrade_tmul O (S ∆ T) (a * b)
          (octadRationalGrade_product O S T v.val w.val v.prop w.prop)
      | add u₁ u₂ h₁ h₂ =>
        simp only [map_add]
        exact (octadRealGrade O (S ∆ T)).add_mem h₁ h₂
    | add t₁ t₂ h₁ h₂ =>
      simp only [map_add, LinearMap.add_apply]
      exact (octadRealGrade O (S ∆ T)).add_mem h₁ h₂
  have hxy := h ((octadGradeScalarExtension O S).symm ⟨x, hx⟩)
    ((octadGradeScalarExtension O T).symm ⟨y, hy⟩)
  simpa only [octadGradeScalarAmbient, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Submodule.subtype_apply] using hxy

end Atlas.Fischer
