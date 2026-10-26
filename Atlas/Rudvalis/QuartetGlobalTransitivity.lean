import Atlas.Rudvalis.QuartetLocalTransitivity
import Atlas.Rudvalis.QuartetCoupleSelection

namespace Atlas.Rudvalis

/-- Every intrinsic quartet is an image of the reference row under the actual generated lattice group. -/
theorem generated_quartet_transport (Q : Set MinimalCross) (hQ : IsQuartet Q) :
    ∃g : generatedGaussianGroup,gaussianImage g.val (coordinateRowFrame (rowLabel 0))=Q := by
  obtain ⟨c,hc,hcQ⟩ := isQuartet_contains_couple Q hQ
  obtain ⟨g,hg⟩ := generated_couple_transport c hc
  have hQ' : IsQuartet (gaussianImage g.val⁻¹ Q) :=
    (isQuartet_gaussianImage g.val⁻¹ Q).mpr hQ
  have hcQ' : referenceCouple⊆gaussianImage g.val⁻¹ Q := by
    have h := Set.image_mono (f:=fun z : MinimalCross=>g.val⁻¹ • z) hcQ
    change gaussianImage g.val⁻¹ c⊆gaussianImage g.val⁻¹ Q at h
    rwa [←hg,gaussianImage_inv] at h
  obtain ⟨a,ha⟩ := coupleFusion_reference_quartet_transport _ hQ' hcQ'
  refine ⟨⟨g.val*a.val,generatedGaussianGroup.mul_mem g.prop (coupleFusionGroup_le_generated a.prop)⟩,?_⟩
  change gaussianImage (g.val*a.val) _=Q
  rw [gaussianImage_mul,ha,gaussianImage_inv_right]

theorem generated_quartet_transitive (Q R : Set MinimalCross) (hQ : IsQuartet Q) (hR : IsQuartet R) :
    ∃g : generatedGaussianGroup,gaussianImage g.val Q=R := by
  obtain ⟨g,hg⟩ := generated_quartet_transport Q hQ
  obtain ⟨h,hh⟩ := generated_quartet_transport R hR
  refine ⟨h*g⁻¹,?_⟩
  change gaussianImage (h.val*g.val⁻¹) Q=R
  rw [gaussianImage_mul,←hg,gaussianImage_inv,hh]

end Atlas.Rudvalis
