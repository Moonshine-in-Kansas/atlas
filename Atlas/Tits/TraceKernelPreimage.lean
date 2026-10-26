import Atlas.Tits.TraceKernelContainment
import Atlas.Tits.LocalSignKernelContainment

namespace Atlas.Tits
open Atlas.Rudvalis

/-- Projected trace-zero containment lifts to the actual code group because
its full sign kernel has already been proved to lie in the normal closure. -/
theorem traceZero_translation_mem_codeNormalImage (g : codeGroup)
    (M : pointMatrixSpace) (ht : pointTrace M=0)
    (hg : codePermutationHom g=coordinateTranslationHom (Multiplicative.ofAdd M.val)) :
    g∈codeNormalImage := by
  obtain ⟨h,hh,hM⟩ := traceZero_mem_translationPreimage M ht
  have hk : g*h⁻¹∈codePermutationHom.ker := by
    change codePermutationHom (g*h⁻¹)=1
    rw [map_mul,map_inv,hg,hM,mul_inv_cancel]
  have hm := codeNormalImage.mul_mem (signKernel_le_codeNormalImage hk) hh
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hm

theorem pointNormalPreimage_iff_image (g : codeReferenceStabilizer) :
    g∈pointNormalPreimage ↔ g.val∈codeNormalImage := by
  constructor
  · intro h;exact ⟨g,h,rfl⟩
  · rintro ⟨h,hh,he⟩
    exact (Subtype.ext he : h=g) ▸ hh

theorem traceZero_translation_mem_pointNormalPreimage (g : codeReferenceStabilizer)
    (M : pointMatrixSpace) (ht : pointTrace M=0)
    (hg : codePermutationHom g.val=coordinateTranslationHom (Multiplicative.ofAdd M.val)) :
    g∈pointNormalPreimage :=
  (pointNormalPreimage_iff_image g).mpr (traceZero_translation_mem_codeNormalImage g.val M ht hg)

theorem traceZero_translation_mem_monomialNormalClosure (g : codeReferenceStabilizer)
    (M : pointMatrixSpace) (ht : pointTrace M=0)
    (hg : codePermutationHom g.val=coordinateTranslationHom (Multiplicative.ofAdd M.val)) :
    codePointToMonomial g∈monomialNormalClosure :=
  traceZero_translation_mem_pointNormalPreimage g M ht hg

/-- A form directly usable with the existing exact row-matrix homomorphism. -/
theorem traceZero_rowMatrix_mem_codeNormalImage (g : codeRowKernel)
    (hp : g.val∈codeReferenceStabilizer)
    (ht : pointTrace ⟨(codeRowMatrixHom g).toAdd,(rowMatrix_fixes_reference_iff g).mp hp⟩=0) :
    g.val∈codeNormalImage :=
  traceZero_translation_mem_codeNormalImage g.val
    ⟨(codeRowMatrixHom g).toAdd,(rowMatrix_fixes_reference_iff g).mp hp⟩ ht
    (rowMatrix_coordinates g)

end Atlas.Tits
