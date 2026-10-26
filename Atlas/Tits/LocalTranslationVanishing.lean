import Atlas.Tits.TraceKernelPreimage

namespace Atlas.Tits
open Atlas.Rudvalis Atlas.Codes.Quaternary
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def localUVWMatrix : Fin 3 → BinaryMatrix := ![
  nineTranslationMatrix 3,
  nineTranslationMatrix 1+nineTranslationMatrix 2+nineTranslationMatrix 3+
    nineTranslationMatrix 7+nineTranslationMatrix 6+nineTranslationMatrix 4+nineTranslationMatrix 5,
  nineTranslationMatrix 2+nineTranslationMatrix 4+nineTranslationMatrix 5+nineTranslationMatrix 6]

noncomputable def localUVWOriginal : Fin 3 → SignedCoordinates SeedCoordinate :=
  ![seedUMonomial,seedVMonomial,seedWMonomial]

/-- Three small marked-coordinate checks identify the actual inherited operators. -/
theorem originalUVW_translation (i : Fin 3) (z : SeedCoordinate) :
    originalCoordinateEquiv ((localUVWOriginal i).right z)=
      coordinateTranslation (localUVWMatrix i) (originalCoordinateEquiv z) := by
  decide +kernel +revert

theorem localUVW_constraints_trace (i : Fin 3) :
    pointMatrixConstraints (localUVWMatrix i)=0 ∧ pointTraceRaw (localUVWMatrix i)=0 := by
  decide +kernel +revert

theorem localCodeU_translation : codePermutationHom codeU=
    coordinateTranslationHom (Multiplicative.ofAdd (localUVWMatrix 0)) :=
  code_projection_of_original_translation _ seedUMonomial _ rfl (originalUVW_translation 0)

theorem localCodeV_translation : codePermutationHom codeV=
    coordinateTranslationHom (Multiplicative.ofAdd (localUVWMatrix 1)) :=
  code_projection_of_original_translation _ seedVMonomial _ codeV_transport (originalUVW_translation 1)

theorem localCodeW_translation : codePermutationHom codeW=
    coordinateTranslationHom (Multiplicative.ofAdd (localUVWMatrix 2)) :=
  code_projection_of_original_translation _ seedWMonomial _ codeW_transport (originalUVW_translation 2)

theorem code_fixes_reference_of_translation (g : codeGroup) (M : pointMatrixSpace)
    (hg : codePermutationHom g=coordinateTranslationHom (Multiplicative.ofAdd M.val)) :
    g∈codeReferenceStabilizer := by
  change g • localReferenceCross=localReferenceCross
  rw [localReferenceCross_eq,coordinateCross_action]
  have hc := congrArg (fun f : binaryPermutationGroup=>f.val (rowLabel 0,0)) hg
  change g.val.right (rowLabel 0,0)=coordinateTranslation M.val (rowLabel 0,0) at hc
  rw [hc]
  exact (pointMatrixSpace_iff_fixes_cross M.val 0).mp M.prop

theorem localCodeU_fixes_reference : codeU∈codeReferenceStabilizer :=
  code_fixes_reference_of_translation codeU ⟨localUVWMatrix 0,(localUVW_constraints_trace 0).1⟩
    localCodeU_translation

theorem localCodeW_fixes_reference : codeW∈codeReferenceStabilizer :=
  code_fixes_reference_of_translation codeW ⟨localUVWMatrix 2,(localUVW_constraints_trace 2).1⟩
    localCodeW_translation

theorem localCodeQ_fixes_reference : localCodeQ∈codeReferenceStabilizer :=
  code_fixes_reference_of_translation localCodeQ
    ⟨qTranslationMatrix,local_translation_point_constraints.1⟩ localCodeQ_translation

theorem localCodeU_mem_codeNormalImage : codeU∈codeNormalImage :=
  traceZero_translation_mem_codeNormalImage codeU
    ⟨localUVWMatrix 0,(localUVW_constraints_trace 0).1⟩ (localUVW_constraints_trace 0).2 localCodeU_translation

theorem localCodeV_mem_codeNormalImage : codeV∈codeNormalImage :=
  traceZero_translation_mem_codeNormalImage codeV
    ⟨localUVWMatrix 1,(localUVW_constraints_trace 1).1⟩ (localUVW_constraints_trace 1).2 localCodeV_translation

theorem localCodeW_mem_codeNormalImage : codeW∈codeNormalImage :=
  traceZero_translation_mem_codeNormalImage codeW
    ⟨localUVWMatrix 2,(localUVW_constraints_trace 2).1⟩ (localUVW_constraints_trace 2).2 localCodeW_translation

theorem localCodeDCube_mem_codeNormalImage : coupleCodeD^3∈codeNormalImage :=
  traceZero_translation_mem_codeNormalImage (coupleCodeD^3)
    ⟨dCubeTranslationMatrix,local_translation_point_constraints.2.1⟩
    local_translation_traces.2.1 localCodeDCube_translation

theorem localCodeD_mem_codeNormalImage : coupleCodeD∈codeNormalImage := by
  have h := codeNormalImage.mul_mem (codeNormalImage.inv_mem localCodeDCube_mem_codeNormalImage)
    localCodeN_mem_codeNormalImage
  have he : (coupleCodeD^3)⁻¹*coupleCodeD^4=coupleCodeD := by
    rw [show 4=3+1 from rfl,pow_succ coupleCodeD 3,inv_mul_cancel_left]
  rwa [he] at h

theorem code_translation_square_sign (g : codeGroup) (M : BinaryMatrix)
    (hg : codePermutationHom g=coordinateTranslationHom (Multiplicative.ofAdd M)) :
    g^2∈codePermutationHom.ker := by
  change codePermutationHom (g^2)=1
  rw [map_pow,hg,←map_pow]
  have hm : (Multiplicative.ofAdd M)^2=1 := by
    rw [pow_two]
    change M+M=0
    ext i j
    exact Atlas.Codes.bit_self_add _
  rw [hm,map_one]

theorem localCodeQ_square_mem_codeNormalImage : localCodeQ^2∈codeNormalImage :=
  signKernel_le_codeNormalImage (code_translation_square_sign _ _ localCodeQ_translation)

theorem monomialU_mem_normalClosure :
    codePointToMonomial ⟨codeU,localCodeU_fixes_reference⟩∈monomialNormalClosure :=
  (pointNormalPreimage_iff_image _).mpr localCodeU_mem_codeNormalImage

theorem monomialV_mem_normalClosure : monomialV∈monomialNormalClosure :=
  (pointNormalPreimage_iff_image ⟨codeV,localCodeV_fixes_reference⟩).mpr localCodeV_mem_codeNormalImage

theorem monomialW_mem_normalClosure :
    codePointToMonomial ⟨codeW,localCodeW_fixes_reference⟩∈monomialNormalClosure :=
  (pointNormalPreimage_iff_image _).mpr localCodeW_mem_codeNormalImage

theorem monomialD_mem_normalClosure : monomialD∈monomialNormalClosure :=
  (pointNormalPreimage_iff_image pointD).mpr localCodeD_mem_codeNormalImage

theorem monomialQ_square_mem_normalClosure :
    codePointToMonomial (⟨localCodeQ,localCodeQ_fixes_reference⟩^2)∈monomialNormalClosure :=
  (pointNormalPreimage_iff_image _).mpr localCodeQ_square_mem_codeNormalImage

end Atlas.Tits
