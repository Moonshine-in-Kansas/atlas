import Atlas.Tits.NormalClosureTranslations
import Atlas.Tits.LocalConjugationMatrix

namespace Atlas.Tits
open Atlas.Rudvalis
open scoped commutatorElement
set_option maxRecDepth 16384

theorem pointD_fourth_mem_normalPreimage : pointD ^ 4 ∈ pointNormalPreimage := by
  change codePointToMonomial (pointD ^ 4) ∈ monomialNormalClosure
  rw [map_pow]
  change monomialN ∈ monomialNormalClosure
  exact Subgroup.subset_normalClosure (Set.mem_singleton _)

theorem localMatrixDifference_mem_translationPreimage (M : pointMatrixSpace) :
    localMatrixDifference M.val ∈ translationPreimage codeNormalImage := by
  letI : monomialNormalClosure.Normal := Subgroup.normalClosure_normal
  letI : pointNormalPreimage.Normal := inferInstanceAs
    (monomialNormalClosure.comap codePointToMonomial).Normal
  obtain ⟨g, hg, hM⟩ := pointMatrix_lift M
  let k : codeReferenceStabilizer := ⟨g.val, hg⟩
  have hc : ⁅pointD ^ 4, k⁆ ∈ pointNormalPreimage :=
    Subgroup.commutator_le_left pointNormalPreimage ⊤
      (Subgroup.commutator_mem_commutator pointD_fourth_mem_normalPreimage (Subgroup.mem_top _))
  refine ⟨(⁅pointD ^ 4, k⁆).val, ⟨_, hc, rfl⟩, ?_⟩
  change codePermutationHom ⁅coupleCodeD ^ 4, g.val⁆ = _
  rw [map_commutatorElement, rowMatrix_coordinates, hM, binary_translation_commutator]
  change coordinateTranslationHom (Multiplicative.ofAdd
    (binaryMatrixConjugate (codeBlockLinearHom (coupleCodeD ^ 4)) M.val - M.val)) = _
  rw [localCodeN_matrix_difference]

theorem pointParamBasis_mem (i : Fin 7) : pointParamBasis i ∈ pointMatrixSpace := by
  change pointMatrixConstraints (pointParamBasis i) = 0
  decide +kernel +revert

/-- Every trace-zero translation occurs in the projection of the actual
normal-closure preimage. Kernel/sign containment is a separate obligation. -/
theorem traceZero_mem_translationPreimage (M : pointMatrixSpace) (ht : pointTrace M = 0) :
    M.val ∈ translationPreimage codeNormalImage := by
  let S := translationPreimage codeNormalImage
  have hI : (1 : BinaryMatrix) ∈ S := identity_mem_localTranslationPreimage
  have hu : uTranslationMatrix ∈ S := uMatrix_mem_localTranslationPreimage
  have hd (i : Fin 7) : localMatrixDifference (pointParamBasis i) ∈ S :=
    localMatrixDifference_mem_translationPreimage ⟨pointParamBasis i, pointParamBasis_mem i⟩
  change M.val ∈ S
  rw [← traceZeroParam_reconstruct M ht, local_trace_zero_span_certificate]
  exact S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem
    (S.smul_mem _ hI) (S.smul_mem _ hu)) (S.smul_mem _ (hd 0)))
    (S.smul_mem _ (hd 1))) (S.smul_mem _ (hd 5))) (S.smul_mem _ (hd 6))

end Atlas.Tits
