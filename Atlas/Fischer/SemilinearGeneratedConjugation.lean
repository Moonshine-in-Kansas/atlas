import Atlas.Fischer.SemilinearGeneratedNormalizer
import Atlas.Fischer.RootRayClassInterface
import Atlas.Fischer.CommutingFrameConjugacy
import Atlas.GroupTheory.CommutingFrameTransport

noncomputable section
namespace Atlas.Fischer

/-- The actual conjugation automorphism of the root-generated ray group. -/
def semilinearGeneratedConjugation (e : SemilinearAlgebraAutomorphism) : MulAut rootGeneratedRayGroup where
  toFun g := ⟨semilinearDisplayedRayAction e*g.val*(semilinearDisplayedRayAction e)⁻¹,
    semilinear_ray_conjugate_mem e g.val g.property⟩
  invFun g := ⟨semilinearDisplayedRayAction e⁻¹*g.val*(semilinearDisplayedRayAction e⁻¹)⁻¹,
    semilinear_ray_conjugate_mem e⁻¹ g.val g.property⟩
  left_inv g := by apply Subtype.ext; simp [map_inv,mul_assoc]
  right_inv g := by apply Subtype.ext; simp [map_inv,mul_assoc]
  map_mul' g h := by apply Subtype.ext; simp [mul_assoc]

theorem semilinearGeneratedConjugation_parameter (e : SemilinearAlgebraAutomorphism)
    (i j : ReflectingRootParameter)
    (h : rootRay (e.val (reflectingRootParameterVector i))=reflectingRootParameterRay j) :
    semilinearGeneratedConjugation e (distinguishedRootElement i)=distinguishedRootElement j := by
  apply Subtype.ext
  exact displayedRootRayInvolution_covariance e i j h

theorem semilinearGeneratedConjugation_class (e : SemilinearAlgebraAutomorphism) :
    semilinearGeneratedConjugation e '' Set.range distinguishedRootElement=Set.range distinguishedRootElement := by
  have hf (e : SemilinearAlgebraAutomorphism) :
      ∀ x ∈ Set.range distinguishedRootElement,
        semilinearGeneratedConjugation e x ∈ Set.range distinguishedRootElement := by
    rintro _ ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := reflectingRootParameter_automorphism e i
    exact ⟨j,(semilinearGeneratedConjugation_parameter e i j hj).symm⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact hf e x hx
  · intro x hx
    refine ⟨semilinearGeneratedConjugation e⁻¹ x,hf e⁻¹ x hx,?_⟩
    apply Subtype.ext
    change semilinearDisplayedRayAction e *
      (semilinearDisplayedRayAction e⁻¹*x.val*(semilinearDisplayedRayAction e⁻¹)⁻¹) *
      (semilinearDisplayedRayAction e)⁻¹=x.val
    simp [map_inv,mul_assoc]

theorem semilinear_standard_image_isFrame (e : SemilinearAlgebraAutomorphism) :
    IsFischerFrame (semilinearGeneratedConjugation e '' standardCommutingFrame) :=
  Atlas.GroupTheory.IsCommutingFrame.image standardCommutingFrame_isFrame
    (semilinearGeneratedConjugation e) (semilinearGeneratedConjugation_class e)

end Atlas.Fischer
